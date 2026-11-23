//! tla2rs: compiles a TLA+ spec into an explicit-state model checker in Rust, specialized to that
//! spec.
//!
//!   tla2rs Spec.tla [-config Spec.cfg] [-o DIR] [--emit-only] [--emit-lib] [-deadlock] [-continue] [-difftrace] [-view] [-nowarning] [-dump [dot[,actionlabels]] FILE] [-workers N] [-memlimit MB] [-notrace] [-tmpdir DIR] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [-dumpgraph FILE] [-lassocheck DIR]
//!   tla2rs --graph FILE | --graph-text FILE
//!   tla2rs --trace FILE | --trace-text FILE
//!   tla2rs --messages FILE | --messages-text FILE
//!   tla2rs --dump FILE | --dump-text FILE
//!   tla2rs --trace-view FILE | --trace-view-text FILE
//!
//! Builds the generated crate with `cargo build --release` and runs it. With --emit-only, it only
//! writes the Rust code. `--graph` reduces a state graph written by `-dumpgraph` or by TLC's
//! `-dump dot` to hashes (see graph.rs); `--trace` reduces the counterexample in the output of TLC
//! or of a checker to a hash (see trace.rs); `--messages` reduces the messages and printed lines
//! in such an output to a hash (see messages.rs).

mod ast;
mod cfg;
mod codegen;
mod community;
mod community_modules;
mod compile;
mod conform;
mod expand;
mod graph;
mod lasso;
mod lexer;
mod messages;
mod std_modules;
mod live;
mod ltl;
mod metal;
mod options;
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
/// The exit code of a checker that made strings in another order than they were numbered in
/// (ORDER_EXIT in runtime.rs)
const ORDER_EXIT: i32 = 72;
/// How many times the checker is built again for the order of the strings it makes
const ORDER_RUNS: usize = 8;
/// The exit code of a checker that met an EXCEPT warning while exploring (WARN_EXIT in runtime.rs)
const WARN_EXIT: i32 = 74;

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
    eprintln!("usage: tla2rs Spec.tla [-config Spec.cfg] [-o DIR] [--emit-only] [--emit-lib] [-deadlock] [-continue] [-difftrace] [-view] [-nowarning] [-dump [dot[,actionlabels]] FILE] [-workers N] [-memlimit MB] [-notrace] [-tmpdir DIR] [-setcap N] [-seqcap N] [-fp128] [-metal] [-batched] [-dumpgraph FILE] [-lassocheck DIR]");
    eprintln!("       tla2rs --graph FILE | --graph-text FILE");
    eprintln!("       tla2rs --trace FILE | --trace-text FILE");
    eprintln!("       tla2rs --messages FILE | --messages-text FILE");
    eprintln!("       tla2rs --dump FILE | --dump-text FILE");
    eprintln!("       tla2rs --trace-view FILE | --trace-view-text FILE");
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
        if mode == "--dump" || mode == "--dump-text" {
            exit(options::main(mode, path));
        }
        if mode == "--trace-view" || mode == "--trace-view-text" {
            exit(options::trace_view(mode, path));
        }
        if mode == "--pcal-text" {
            exit(pcal::main(path));
        }
    }
    let mut tla: Option<PathBuf> = None;
    let mut cfg: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut emit_only = false;
    let mut emit_lib = false;
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
            // Writes the checker as a library crate instead of building and running it (see conform.rs)
            "--emit-lib" => {
                emit_lib = true;
                conform::want();
            }
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
            // TLC's options, with TLC's meaning and output (see README.md, "TLC's options")
            "-continue" | "-difftrace" | "-view" | "-nowarning" => pass.push(args[i].clone()),
            // TLC's `-dump FILE` lists the distinct states; `-dump dot[,options] FILE` writes the
            // state graph. TLC adds the extension .dump or .dot when the name lacks it
            "-dump" => {
                i += 1;
                let a = args.get(i).unwrap_or_else(|| usage());
                let dot = a == "dot" || a.starts_with("dot,");
                if dot {
                    // TLC 2.19 writes the attributes of a label on every edge, an empty one without
                    // actionlabels (`tests/tlc/OptDump-Dot`)
                    pass.push("-dumpattrs".into());
                    for o in a.split(',').skip(1) {
                        match o {
                            "actionlabels" => pass.push("-dumplabels".into()),
                            // Snapshots of the graph written while the search runs: the final file
                            // is the same
                            "snapshot" => {}
                            "colorize" => pass.push("-dumpcolors".into()),
                            _ => {
                                eprintln!("tla2rs: -dump dot,{o} is not supported (only actionlabels, colorize and snapshot)");
                                exit(2);
                            }
                        }
                    }
                    i += 1;
                }
                let f = if dot { args.get(i).unwrap_or_else(|| usage()) } else { a };
                let ext = if dot { ".dot" } else { ".dump" };
                let f = if f.ends_with(ext) { f.clone() } else { format!("{f}{ext}") };
                pass.push(if dot { "-dumpgraph" } else { "-dumpstates" }.into());
                pass.push(f);
            }
            // TLC's options that change only its files on disk or its memory and fingerprint
            // tuning, not what it reports: accepted and ignored
            "-cleanup" | "-gzip" | "-modelcheck" => {}
            "-metadir" | "-checkpoint" | "-fp" | "-fpbits" | "-fpmem" | "-lncheck" => {
                i += 1;
                let v = args.get(i).unwrap_or_else(|| usage());
                // The checker prints TLC's liveness counterexample only for TLC's first polynomial
                if args[i - 1] == "-fp" && v != "0" {
                    pass.push("-tlcfp".into());
                    pass.push(v.clone());
                }
            }
            // TLC's -userFile FILE: what the spec prints goes to FILE
            "-userFile" => {
                i += 1;
                pass.push("-userfile".into());
                pass.push(args.get(i).unwrap_or_else(|| usage()).clone());
            }
            "-simulate" | "-seed" | "-aril" | "-depth" | "-dfid" | "-generateSpecTE" | "-tool" | "-debug" | "-recover"
            | "-coverage" | "-terse" | "-maxSetSize" => {
                eprintln!("tla2rs: TLC's option {} is not supported (see README.md, \"TLC's options\")", args[i]);
                exit(2);
            }
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
    // A library goes to a directory of its own, so that building the checker does not build it too
    let dir = out.unwrap_or_else(|| tla.parent().unwrap_or(Path::new(".")).join(".tla2rs").join(if emit_lib { format!("{stem}-lib") } else { stem.clone() }));
    let crate_name = format!("{}_{}", if emit_lib { "spec" } else { "check" }, stem.to_lowercase().replace(|c: char| !c.is_ascii_alphanumeric(), "_"));
    if emit_lib && metal {
        eprintln!("tla2rs: --emit-lib does not go with -metal (a library does not search)");
        exit(2);
    }
    // Sets held as arrays and sequences have a capacity fixed when the checker is built (-setcap and
    // -seqcap set where it starts). TLC has no such bound, so when a value outgrows it the checker
    // exits with CAP_EXIT + the kind, and the checker is built again with twice the room and run
    // from the start; a spec that stays within the capacity runs as fast as before. The line printed
    // before the new run marks where its output starts (scripts/crosscheck.sh reads from there)
    let (mut setcap, mut seqcap) = (setcap, seqcap);
    // The strings the checker made while exploring, in the order it made them: TLC orders strings
    // by when it creates them, so when the checker made them in another order than they were
    // numbered in, it is built again with them numbered in that order (see "the order of strings
    // made" in runtime.rs)
    let mut made: Vec<String> = vec![];
    let mut order_runs = 0;
    let order_file = dir.join("strings-made.txt");
    // How many elements the value that outgrew its capacity needs, at least (see
    // `capacity_exceeded` in runtime.rs), and how many times sequences and each set type (by
    // `types::cap_key`; each has a capacity of its own) have grown, with the capacities given to the
    // set types that grew
    let need_file = dir.join("capacity-needed.txt");
    let mut grown_seq = 0u32;
    let mut grown_sets: std::collections::HashMap<String, (usize, u32)> = Default::default();
    // How many strings ToString may list for a type with more values than strings can be added,
    // by type (see TOSTR_CAP in codegen.rs), and how many times each has grown
    let mut tostr: std::collections::HashMap<String, (usize, u32)> = Default::default();
    // Whether the checker prints in TLC's order for the EXCEPT warnings it meets (see `compile`)
    let mut warn_order = false;
    let mut first = true;
    // The capacities the next growth gives if the kind that just grew outgrows its new capacity
    // too (QCAP, set types): the checker for them is built ahead, beside the one for this run (see
    // `build`)
    let mut predicted: Option<Caps> = None;
    loop {
        let t0 = Instant::now();
        let caps = grown_sets.iter().map(|(k, v)| (k.clone(), v.0)).collect();
        let tostr_caps: std::collections::HashMap<String, usize> = tostr.iter().map(|(k, v)| (k.clone(), v.0)).collect();
        let ahead = predicted.take().map(|(q, sets)| ((q, sets.clone()), compile_thread(&tla, &src, &cfg_src, setcap, q, sets, tostr_caps.clone(), fp128, metal, &made, warn_order)));
        let output = compile_spec(&tla, &src, &cfg_src, setcap, seqcap, caps, tostr_caps, fp128, metal, &made, warn_order);
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
                if let Some(f) = pass.iter().position(|a| a == "-dumpstates").and_then(|i| pass.get(i + 1)) {
                    std::fs::write(f, "").expect("write the states");
                }
            }
            // What the spec printed (marked by `compile::USER_MARK`) goes to the -userFile file
            let user_file = pass.iter().position(|a| a == "-userfile").and_then(|i| pass.get(i + 1));
            let mut user = String::new();
            for l in msg.lines() {
                match l.strip_prefix(compile::USER_MARK) {
                    Some(u) if user_file.is_some() => user += &format!("{}\n", compile::user_text(u, true)),
                    Some(u) => println!("{}", compile::user_text(u, false)),
                    None => println!("{l}"),
                }
            }
            if let Some(f) = user_file {
                if let Err(e) = std::fs::write(f, user) {
                    eprintln!("cannot write {f}: {e}");
                    exit(2);
                }
            }
            // No library for a spec TLC stops on before exploring; with nothing to explore (code 0)
            // that must not look like success
            if emit_lib {
                eprintln!("tla2rs: --emit-lib wrote no library: {}", if *code == 0 { "the spec has no behavior to check" } else { "TLC refuses the spec before exploring" });
                quit(if *code == 0 { 1 } else { *code });
            }
            quit(*code);
        }
        if emit_lib {
            match &output.lib {
                Ok(lib) => write_lib(&dir, &crate_name, &conform::lib_rs(&output.rust, lib)),
                Err(e) => {
                    eprintln!("tla2rs: {e}");
                    quit(1)
                }
            }
            eprintln!("tla2rs: generated {} in {:.0} ms", dir.join("src/lib.rs").display(), t0.elapsed().as_secs_f64() * 1e3);
            // Said here, since nothing in a test that passes would say it
            if output.rust.contains("\nconst LIVENESS: bool = true;") {
                eprintln!("tla2rs: note: the library does not check the temporal properties and fairness of the configuration (conform::temporal_properties lists them)");
            }
            return;
        }
        let Some(bin) = build(&dir, &crate_name, &output.rust, metal, emit_only, t0, ahead) else { return };
        // The kinds of capacity that can still grow (see `capacity_exceeded` in runtime.rs; the
        // checker knows which set types are at the maximum)
        let qcap = output.qcap;
        let grow: String = ['s'].into_iter().chain((qcap < types::MAX_CAP).then_some('q')).chain(['t', 'w']).collect();
        let mut cmd = Command::new(bin);
        cmd.args(&pass).env("TLA2RS_GROW", grow).env("TLA2RS_NEED", &need_file);
        let _ = std::fs::remove_file(&need_file);
        if order_runs < ORDER_RUNS {
            cmd.env("TLA2RS_ORDER", &order_file);
        }
        let st = cmd.status().expect("run checker");
        let code = st.code().unwrap_or(1);
        if code == ORDER_EXIT {
            let text = std::fs::read_to_string(&order_file).unwrap_or_default();
            made = text.lines().filter_map(|l| l.parse::<usize>().ok()).filter_map(|a| output.atoms.get(a).cloned()).collect();
            order_runs += 1;
            if order_runs == ORDER_RUNS {
                eprintln!("tla2rs: the strings made while exploring were made in another order each time; the last run may order them differently from TLC");
            }
            println!("tla2rs: strings were made in another order than they were numbered in; checking again from the start with them in that order");
            first = false;
            continue;
        }
        if code == WARN_EXIT {
            warn_order = true;
            println!("tla2rs: an EXCEPT warned while exploring; checking again from the start with the lines printed in TLC's order");
            first = false;
            continue;
        }
        if code == codegen::TOSTR_EXIT {
            // As capacities grow (below); the checker asks only while more can be listed
            let Ok(key) = std::fs::read_to_string(&need_file) else { quit(code) };
            let (cap, grown) = tostr.entry(key).or_insert((codegen::TOSTR_START, 0));
            let old = *cap;
            *grown += 1;
            *cap = old.saturating_mul(1 << (*grown).min(12)).min(types::MAX_CAP);
            println!("tla2rs: ToString met a value whose string is not among the {old} listed for its type; checking again from the start with room for {cap}");
            first = false;
            continue;
        }
        if code != CAP_EXIT_SET && code != CAP_EXIT_SEQ {
            quit(code)
        }
        // Twice the room the first time a sequence or a set type grows, four times the second,
        // eight times the third and so on: a value that keeps outgrowing its capacity is likely
        // far beyond it, and each build costs seconds (`SimplifiedFastPaxos` `FastPaxos` needs more
        // than 256: 3 rebuilds to 512 instead of 4 to 1024 at four times after the first). Never
        // less than the value needs. For a set, the checker also writes the capacity it outgrew and
        // the key of its type, which grows alone
        let text = std::fs::read_to_string(&need_file).unwrap_or_default();
        let mut lines = text.lines();
        let need = lines.next().and_then(|t| t.trim().parse::<usize>().ok());
        let grow = |old: usize, times: u32| old.saturating_mul(1 << times.min(12)).max(need.unwrap_or(old + 1)).clamp(8, types::MAX_CAP);
        // What the next growth of the same kind gives when the value then needs no more, for which
        // a checker is built ahead (see `build`)
        let ahead_cap = |cap: usize, times: u32| cap.saturating_mul(1 << (times + 1).min(12)).clamp(8, types::MAX_CAP);
        let sets_now = |grown_sets: &std::collections::HashMap<String, (usize, u32)>| -> std::collections::HashMap<String, usize> { grown_sets.iter().map(|(k, v)| (k.clone(), v.0)).collect() };
        let mut next = None;
        if code == CAP_EXIT_SEQ {
            grown_seq += 1;
            let new = grow(qcap, grown_seq);
            println!("tla2rs: a sequence grew beyond {qcap} elements; checking again from the start with room for {new}");
            seqcap = new;
            next = Some((ahead_cap(new, grown_seq), sets_now(&grown_sets)));
        } else {
            let old = lines.next().and_then(|t| t.trim().parse::<usize>().ok());
            match (old, lines.next().filter(|k| !k.is_empty())) {
                (Some(old), Some(key)) => {
                    let (cap, times) = grown_sets.entry(key.to_string()).or_insert((old, 0));
                    *times += 1;
                    *cap = grow(old, *times);
                    let what = output.set_names.get(key).map_or("a set", |n| n.as_str());
                    println!("tla2rs: {what} grew beyond {old} elements; checking again from the start with room for {cap}");
                    let bigger = ahead_cap(*cap, *times);
                    let mut sets = sets_now(&grown_sets);
                    sets.insert(key.to_string(), bigger);
                    next = Some((seqcap, sets));
                }
                // No set type named (a checker that did not write the file): every set type starts
                // higher
                _ => {
                    let old = old.unwrap_or(0).max(setcap).max(8);
                    let new = grow(old, 1);
                    println!("tla2rs: a set grew beyond {old} elements; checking again from the start with room for {new}");
                    setcap = new;
                }
            }
        }
        // A checker built ahead for these capacities runs next; one built for others is stopped,
        // and one is built ahead for the next growth of the kind that grew
        let now = (seqcap, sets_now(&grown_sets));
        if !AHEAD.lock().unwrap().as_ref().is_some_and(|a| a.caps == now) {
            stop_ahead();
            predicted = next.filter(|n| *n != now);
        }
        first = false;
    }
}

/// Compiles the spec, stopping with exit 1 on an error
#[allow(clippy::too_many_arguments)]
fn compile_spec(tla: &Path, src: &str, cfg_src: &str, setcap: usize, seqcap: usize, sets: std::collections::HashMap<String, usize>, tostr: std::collections::HashMap<String, usize>, fp128: bool, metal: bool, made: &[String], warn_order: bool) -> compile::Output {
    let result = compile_thread(tla, src, cfg_src, setcap, seqcap, sets, tostr, fp128, metal, made, warn_order).join().unwrap_or_else(|_| Err("internal error in the compiler".into()));
    result.unwrap_or_else(|e| {
        eprintln!("tla2rs: {e}");
        quit(1)
    })
}

type Compiling = std::thread::JoinHandle<Result<compile::Output, String>>;

/// QCAP and the capacities of the set types that grew
type Caps = (usize, std::collections::HashMap<String, usize>);

/// Starts compiling the spec. The compiler runs on a thread with a large stack: evaluating a
/// recursive operator at compile time nests deeply (up to value::REC_LIMIT calls)
#[allow(clippy::too_many_arguments)]
fn compile_thread(tla: &Path, src: &str, cfg_src: &str, setcap: usize, seqcap: usize, sets: std::collections::HashMap<String, usize>, tostr: std::collections::HashMap<String, usize>, fp128: bool, metal: bool, made: &[String], warn_order: bool) -> Compiling {
    let (src, cfg_src, made) = (src.to_string(), cfg_src.to_string(), made.to_vec());
    let dir = tla.parent().unwrap_or(Path::new(".")).to_path_buf();
    std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || compile::compile(&src, &cfg_src, &dir, setcap, seqcap, &sets, &tostr, fp128, metal, &made, warn_order))
        .expect("start the compiler thread")
}

/// A checker being built ahead, in `<dir>/ahead`, for the capacities the next growth would give
/// (see `build`)
struct Ahead {
    caps: Caps,
    rust: String,
    dir: PathBuf,
    cargo: std::process::Child,
}

static AHEAD: std::sync::Mutex<Option<Ahead>> = std::sync::Mutex::new(None);

/// Stops the checker being built ahead, if any. cargo leaves rustc running when it is killed, so
/// cargo is stopped, its children killed, and then cargo
fn stop_ahead() {
    let Some(mut a) = AHEAD.lock().unwrap_or_else(|e| e.into_inner()).take() else { return };
    if matches!(a.cargo.try_wait(), Ok(None)) {
        let pid = a.cargo.id().to_string();
        let _ = Command::new("kill").args(["-STOP", &pid]).status();
        let _ = Command::new("pkill").args(["-KILL", "-P", &pid]).status();
        let _ = a.cargo.kill();
    }
    let _ = a.cargo.wait();
}

/// Exits, stopping the checker being built ahead first
fn quit(code: i32) -> ! {
    stop_ahead();
    exit(code)
}

/// Writes the generated crate to `dir`. The checker is built without ThinLTO across codegen units:
/// the code of the spec's next-state relation is one function in one codegen unit, which ThinLTO
/// optimized a second time (a tenth to a fifth of a build), and the search was as fast without it
fn write_crate(dir: &Path, crate_name: &str, rust: &str, metal: bool) {
    std::fs::create_dir_all(dir.join("src")).expect("create output dir");
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{crate_name}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[dependencies]\n\n[profile.release]\nopt-level = 3\ncodegen-units = 16\nlto = \"off\"\n\n[workspace]\n"
        ),
    )
    .expect("write Cargo.toml");
    std::fs::write(dir.join("src/main.rs"), rust).expect("write main.rs");
    if metal {
        std::fs::write(dir.join("metal.m"), metal::METAL_M).expect("write metal.m");
        std::fs::write(dir.join("build.rs"), metal::BUILD_RS).expect("write build.rs");
    }
}

/// Writes a library crate (`--emit-lib`) to `dir`: the checker's code with the module `conform`
/// (see conform.rs), for the tests of an implementation to depend on by path. It has a workspace
/// of its own, as the checker's crate has, so it can sit inside the directory of another package
fn write_lib(dir: &Path, crate_name: &str, lib_rs: &str) {
    std::fs::create_dir_all(dir.join("src")).expect("create output dir");
    std::fs::write(dir.join("Cargo.toml"), format!("[package]\nname = \"{crate_name}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[lib]\npath = \"src/lib.rs\"\n\n[dependencies]\n\n[workspace]\n"))
        .expect("write Cargo.toml");
    std::fs::write(dir.join("src/lib.rs"), lib_rs).expect("write lib.rs");
}

/// Where TLA2RS_BUILD_CACHE=DIR keeps the checker built from the crate in `dir`, so test runs only
/// compile the specs whose generated code changed
fn cache_entry(dir: &Path) -> Option<PathBuf> {
    std::env::var_os("TLA2RS_BUILD_CACHE").map(|c| PathBuf::from(c).join(build_key(dir)))
}

fn cargo_build(dir: &Path) -> std::process::Child {
    Command::new("cargo").args(["build", "--release", "--quiet", "--offline"]).current_dir(dir).spawn().expect("run cargo")
}

/// Copies a checker into the build cache, under a unique name renamed into place, so a parallel run
/// never sees a half-written file
fn store(cache: &Option<PathBuf>, bin: &Path) {
    if let Some(c) = cache {
        let tmp = c.with_extension(format!("tmp{}", std::process::id()));
        let stored = std::fs::create_dir_all(&tmp)
            .and_then(|_| std::fs::copy(bin, tmp.join("checker")))
            .and_then(|_| std::fs::rename(&tmp, c));
        if stored.is_err() {
            let _ = std::fs::remove_dir_all(&tmp);
        }
    }
}

/// Writes the generated crate to `dir` and builds it (or takes the checker built earlier from the
/// same sources, under TLA2RS_BUILD_CACHE). Returns the checker, or None with --emit-only.
///
/// After a capacity grew, `ahead` compiles the spec with the capacities the next growth of that
/// kind would give. A build keeps one core busy for most of its time (the next-state relation is
/// one function, whose type check, borrow check and optimization are serial), so the checker for
/// those capacities is built beside this one, in `<dir>/ahead`; when the value outgrows the new
/// capacity too and the code generated next is the same, that checker runs without a build of its
/// own (a spec that grew 8 -> 16 -> 64 waits for two builds instead of three). Otherwise it is
/// stopped
#[allow(clippy::too_many_arguments)]
fn build(dir: &Path, crate_name: &str, rust: &str, metal: bool, emit_only: bool, t0: Instant, ahead: Option<(Caps, Compiling)>) -> Option<PathBuf> {
    write_crate(dir, crate_name, rust, metal);
    eprintln!("tla2rs: generated {} in {:.0} ms", dir.join("src/main.rs").display(), t0.elapsed().as_secs_f64() * 1e3);
    if emit_only {
        return None;
    }
    let cache = cache_entry(dir);
    let pending = AHEAD.lock().unwrap().take();
    if let Some(mut a) = pending {
        if a.rust == rust {
            let t1 = Instant::now();
            if a.cargo.wait().is_ok_and(|s| s.success()) {
                eprintln!("tla2rs: this checker was built ahead, while the one before was built and run");
                eprintln!("tla2rs: built in {:.1} s", t1.elapsed().as_secs_f64());
                let bin = a.dir.join("target/release").join(crate_name);
                store(&cache, &bin);
                return Some(bin);
            }
        } else {
            *AHEAD.lock().unwrap() = Some(a);
            stop_ahead();
        }
    }
    if let Some(hit) = cache.as_ref().map(|c| c.join("checker")).filter(|b| b.is_file()) {
        eprintln!("tla2rs: reusing the checker in {}", hit.display());
        return Some(hit);
    }
    let t1 = Instant::now();
    let mut cargo = cargo_build(dir);
    if let Some((caps, next)) = ahead.and_then(|(caps, h)| Some((caps, h.join().ok()?.ok()?))).filter(|(_, o)| o.rejected.is_none() && o.rust != rust) {
        let ahead_dir = dir.join("ahead");
        write_crate(&ahead_dir, crate_name, &next.rust, metal);
        if !cache_entry(&ahead_dir).is_some_and(|c| c.join("checker").is_file()) {
            *AHEAD.lock().unwrap() = Some(Ahead { caps, rust: next.rust, cargo: cargo_build(&ahead_dir), dir: ahead_dir });
        }
    }
    let st = cargo.wait().expect("run cargo");
    if !st.success() {
        eprintln!("tla2rs: building the generated checker failed (this is a tla2rs bug; please report the spec)");
        quit(1);
    }
    eprintln!("tla2rs: built in {:.1} s", t1.elapsed().as_secs_f64());
    let bin = dir.join("target/release").join(crate_name);
    store(&cache, &bin);
    Some(bin)
}
