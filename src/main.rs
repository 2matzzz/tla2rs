//! tla2rs: compiles a TLA+ spec into an explicit-state model checker in Rust, specialized to that
//! spec.
//!
//!   tla2rs Spec.tla [-config Spec.cfg] [-o DIR] [--emit-only] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-tmpdir DIR] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [-dumpgraph FILE] [-lassocheck DIR]
//!   tla2rs --graph FILE | --graph-text FILE
//!   tla2rs --trace FILE | --trace-text FILE
//!   tla2rs --messages FILE | --messages-text FILE
//!
//! Builds the generated crate with `cargo build --release` and runs it. With --emit-only, it only
//! writes the Rust code. `--graph` reduces a state graph written by `-dumpgraph` or by TLC's
//! `-dump dot` to hashes (see graph.rs); `--trace` reduces the counterexample in the output of TLC
//! or of a checker to a hash (see trace.rs); `--messages` reduces the messages and printed lines
//! in such an output to a hash (see messages.rs).

mod ast;
mod cfg;
mod codegen;
mod compile;
mod expand;
mod graph;
mod lasso;
mod lexer;
mod messages;
mod std_modules;
mod live;
mod ltl;
mod metal;
mod parser;
mod pcal;
mod ppr;
mod runtime;
mod sany;
mod seqlen;
mod trace;
mod types;
mod value;

use std::path::{Path, PathBuf};
use std::process::{exit, Command};
use std::time::Instant;

/// The exit codes of a checker whose sets or sequences outgrew their capacity (CAP_EXIT + CAP_SET
/// and CAP_EXIT + CAP_SEQ in runtime.rs)
const CAP_EXIT_SET: i32 = 70;
const CAP_EXIT_SEQ: i32 = 71;

/// Key of a built checker: every file cargo reads in the generated crate, and the compiler version.
/// Two SipHash passes with different prefixes give 128 bits.
fn build_key(dir: &Path) -> String {
    use std::hash::{Hash, Hasher};
    let rustc = Command::new("rustc").arg("-V").output().map(|o| o.stdout).unwrap_or_default();
    let files: Vec<Vec<u8>> = ["Cargo.toml", "src/main.rs", "build.rs", "metal.m"]
        .iter()
        .map(|f| std::fs::read(dir.join(f)).unwrap_or_default())
        .collect();
    let half = |salt: u8| {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        salt.hash(&mut h);
        rustc.hash(&mut h);
        files.hash(&mut h);
        h.finish()
    };
    format!("{:016x}{:016x}", half(0), half(1))
}

fn usage() -> ! {
    eprintln!("usage: tla2rs Spec.tla [-config Spec.cfg] [-o DIR] [--emit-only] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-tmpdir DIR] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [-dumpgraph FILE] [-lassocheck DIR]");
    eprintln!("       tla2rs --graph FILE | --graph-text FILE");
    eprintln!("       tla2rs --trace FILE | --trace-text FILE");
    eprintln!("       tla2rs --messages FILE | --messages-text FILE");
    eprintln!("       tla2rs --pcal-text FILE");
    exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let [mode, path] = args.as_slice() {
        if mode == "--graph" || mode == "--graph-text" {
            exit(graph::main(mode, path));
        }
        if mode == "--trace" || mode == "--trace-text" {
            exit(trace::main(mode, path));
        }
        if mode == "--messages" || mode == "--messages-text" {
            exit(messages::main(mode, path));
        }
        if mode == "--pcal-text" {
            exit(pcal::main(path));
        }
    }
    let mut tla: Option<PathBuf> = None;
    let mut cfg: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut emit_only = false;
    let mut setcap: usize = 0;
    let mut seqcap: usize = 0;
    let mut fp128 = false;
    let mut metal = false;
    let mut pass = vec![];
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-config" | "--config" => {
                i += 1;
                cfg = Some(args.get(i).unwrap_or_else(|| usage()).into());
            }
            "-o" => {
                i += 1;
                out = Some(args.get(i).unwrap_or_else(|| usage()).into());
            }
            "--emit-only" => emit_only = true,
            "-fp128" => fp128 = true,
            // -metal affects both code generation (emits the Metal parts) and execution (uses the
            // GPU)
            "-metal" => {
                metal = true;
                pass.push("-metal".into());
            }
            "-batched" => pass.push("-batched".into()),
            "-deadlock" => pass.push("-deadlock".to_string()),
            "-setcap" => {
                i += 1;
                setcap = args.get(i).and_then(|x| x.parse().ok()).unwrap_or_else(|| usage());
            }
            // Maximum length of a sequence value
            "-seqcap" => {
                i += 1;
                seqcap = args.get(i).and_then(|x| x.parse().ok()).unwrap_or_else(|| usage());
            }
            // Candidate budget (MB) the checker holds at once (smaller values split each level into
            // more chunks), the spill directory, and the file to write the state graph to
            "-memlimit" | "-tmpdir" | "-dumpgraph" | "-lassocheck" => {
                pass.push(args[i].clone());
                i += 1;
                pass.push(args.get(i).unwrap_or_else(|| usage()).clone());
            }
            "-notrace" => pass.push("-notrace".into()),
            "-workers" => {
                i += 1;
                pass.push("-workers".into());
                pass.push(args.get(i).unwrap_or_else(|| usage()).clone());
            }
            "-h" | "--help" => usage(),
            a if tla.is_none() && !a.starts_with('-') => tla = Some(a.into()),
            a => {
                eprintln!("unknown argument {a}");
                usage()
            }
        }
        i += 1;
    }
    let tla = tla.unwrap_or_else(|| usage());
    let tla = if tla.extension().is_none() { tla.with_extension("tla") } else { tla };
    let cfg = cfg.unwrap_or_else(|| tla.with_extension("cfg"));
    let read = |p: &Path| {
        std::fs::read_to_string(p).unwrap_or_else(|e| {
            eprintln!("cannot read {}: {e}", p.display());
            exit(2)
        })
    };
    let (src, cfg_src) = (read(&tla), read(&cfg));
    let stem = cfg.file_stem().unwrap().to_string_lossy().to_string();
    let dir = out.unwrap_or_else(|| tla.parent().unwrap_or(Path::new(".")).join(".tla2rs").join(&stem));
    let crate_name = format!("check_{}", stem.to_lowercase().replace(|c: char| !c.is_ascii_alphanumeric(), "_"));
    // Sets held as arrays and sequences have a capacity fixed when the checker is built (-setcap and
    // -seqcap set where it starts). TLC has no such bound, so when a value outgrows it the checker
    // exits with CAP_EXIT + the kind, and the checker is built again with twice the room and run
    // from the start; a spec that stays within the capacity runs as fast as before. The line printed
    // before the new run marks where its output starts (scripts/crosscheck.sh reads from there)
    let (mut setcap, mut seqcap) = (setcap, seqcap);
    let mut first = true;
    loop {
        let t0 = Instant::now();
        let output = compile_spec(&tla, &src, &cfg_src, setcap, seqcap, fp128, metal);
        if first {
            for w in &output.warnings {
                eprintln!("warning: {w}");
            }
        }
        // A false ASSUME, or a temporal formula TLC cannot check: as in TLC, stop before exploring,
        // with the same message and exit code
        if let Some((msg, code)) = &output.rejected {
            // Nothing to explore (compile::NO_BEHAVIOR): the state graph is empty, and TLC ends its
            // file
            if *code == 0 {
                if let Some(f) = pass.iter().position(|a| a == "-dumpgraph").and_then(|i| pass.get(i + 1)) {
                    let empty = "strict digraph DiskGraph {\nnodesep=0.35;\nsubgraph cluster_graph {\ncolor=\"white\";\n}\n}";
                    std::fs::write(f, empty).expect("write the state graph");
                }
            }
            println!("{msg}");
            exit(*code);
        }
        let Some(bin) = build(&dir, &crate_name, &output.rust, metal, emit_only, t0) else { return };
        // The kinds of capacity that can still grow (see `capacity_exceeded` in runtime.rs)
        let (scap, qcap) = output.caps;
        let grow: String = [('s', scap), ('q', qcap)].iter().filter(|(_, c)| *c < types::MAX_CAP).map(|(k, _)| *k).collect();
        let st = Command::new(bin).args(&pass).env("TLA2RS_GROW", grow).status().expect("run checker");
        let code = st.code().unwrap_or(1);
        let (what, old, new) = match code {
            CAP_EXIT_SET => ("a set", scap, (scap * 2).min(types::MAX_CAP)),
            CAP_EXIT_SEQ => ("a sequence", qcap, (qcap * 2).clamp(8, types::MAX_CAP)),
            _ => exit(code),
        };
        if code == CAP_EXIT_SET {
            setcap = new;
        } else {
            seqcap = new;
        }
        println!("tla2rs: {what} grew beyond {old} elements; checking again from the start with room for {new}");
        first = false;
    }
}

/// Compiles the spec, stopping with exit 1 on an error. The compiler runs on a thread with a large
/// stack: evaluating a recursive operator at compile time nests deeply (up to value::REC_LIMIT
/// calls)
#[allow(clippy::too_many_arguments)]
fn compile_spec(tla: &Path, src: &str, cfg_src: &str, setcap: usize, seqcap: usize, fp128: bool, metal: bool) -> compile::Output {
    let (src, cfg_src) = (src.to_string(), cfg_src.to_string());
    let dir = tla.parent().unwrap_or(Path::new(".")).to_path_buf();
    let result = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || compile::compile(&src, &cfg_src, &dir, setcap, seqcap, fp128, metal))
        .expect("start the compiler thread")
        .join()
        .unwrap_or_else(|_| Err("internal error in the compiler".into()));
    result.unwrap_or_else(|e| {
        eprintln!("tla2rs: {e}");
        exit(1)
    })
}

/// Writes the generated crate to `dir` and builds it (or takes the checker built earlier from the
/// same sources, under TLA2RS_BUILD_CACHE). Returns the checker, or None with --emit-only
fn build(dir: &Path, crate_name: &str, rust: &str, metal: bool, emit_only: bool, t0: Instant) -> Option<PathBuf> {
    std::fs::create_dir_all(dir.join("src")).expect("create output dir");
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{crate_name}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[dependencies]\n\n[profile.release]\nopt-level = 3\ncodegen-units = 16\n\n[workspace]\n"
        ),
    )
    .expect("write Cargo.toml");
    std::fs::write(dir.join("src/main.rs"), rust).expect("write main.rs");
    if metal {
        std::fs::write(dir.join("metal.m"), metal::METAL_M).expect("write metal.m");
        std::fs::write(dir.join("build.rs"), metal::BUILD_RS).expect("write build.rs");
    }
    eprintln!("tla2rs: generated {} in {:.0} ms", dir.join("src/main.rs").display(), t0.elapsed().as_secs_f64() * 1e3);
    if emit_only {
        return None;
    }
    // TLA2RS_BUILD_CACHE=DIR reuses a checker built earlier from the same sources, so test runs only
    // compile the specs whose generated code changed
    let cache = std::env::var_os("TLA2RS_BUILD_CACHE").map(|c| PathBuf::from(c).join(build_key(dir)));
    if let Some(hit) = cache.as_ref().map(|c| c.join("checker")).filter(|b| b.is_file()) {
        eprintln!("tla2rs: reusing the checker in {}", hit.display());
        return Some(hit);
    }
    let t1 = Instant::now();
    let st = Command::new("cargo")
        .args(["build", "--release", "--quiet", "--offline"])
        .current_dir(dir)
        .status()
        .expect("run cargo");
    if !st.success() {
        eprintln!("tla2rs: building the generated checker failed (this is a tla2rs bug; please report the spec)");
        exit(1);
    }
    eprintln!("tla2rs: built in {:.1} s", t1.elapsed().as_secs_f64());
    let bin = dir.join("target/release").join(crate_name);
    if let Some(c) = &cache {
        // Copy under a unique name and rename, so a parallel run never sees a half-written file
        let tmp = c.with_extension(format!("tmp{}", std::process::id()));
        let stored = std::fs::create_dir_all(&tmp)
            .and_then(|_| std::fs::copy(&bin, tmp.join("checker")))
            .and_then(|_| std::fs::rename(&tmp, c));
        if stored.is_err() {
            let _ = std::fs::remove_dir_all(&tmp);
        }
    }
    Some(bin)
}
