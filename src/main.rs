//! tla2rs: compiles a TLA+ spec into an explicit-state model checker in Rust, specialized to that
//! spec.
//!
//!   tla2rs Spec.tla [-config Spec.cfg] [-o DIR] [--emit-only] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-tmpdir DIR] [-setcap N] [-fp128] [-metal] [-batched]
//!
//! Builds the generated crate with `cargo build --release` and runs it. With --emit-only, it only
//! writes the Rust code.

mod ast;
mod cfg;
mod codegen;
mod compile;
mod expand;
mod lexer;
mod metal;
mod parser;
mod runtime;
mod types;
mod value;

use std::path::{Path, PathBuf};
use std::process::{exit, Command};
use std::time::Instant;

fn usage() -> ! {
    eprintln!("usage: tla2rs Spec.tla [-config Spec.cfg] [-o DIR] [--emit-only] [-deadlock] [-workers N] [-memlimit MB] [-notrace] [-tmpdir DIR] [-setcap N] [-fp128] [-metal] [-batched]");
    exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut tla: Option<PathBuf> = None;
    let mut cfg: Option<PathBuf> = None;
    let mut out: Option<PathBuf> = None;
    let mut emit_only = false;
    let mut setcap: usize = 0;
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
            // Candidate budget (MB) the checker holds at once. Smaller values split each level into
            // more chunks
            "-memlimit" | "-tmpdir" => {
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
    let t0 = Instant::now();
    let output = match compile::compile(&read(&tla), &read(&cfg), tla.parent().unwrap_or(Path::new(".")), setcap, fp128, metal) {
        Ok(o) => o,
        Err(e) => {
            eprintln!("tla2rs: {e}");
            exit(1)
        }
    };
    for w in &output.warnings {
        eprintln!("warning: {w}");
    }
    // A false ASSUME. As in TLC, stop before exploring, with the same message and exit code (10)
    if let Some(msg) = &output.assume_failed {
        println!("{msg}");
        exit(10);
    }
    let stem = cfg.file_stem().unwrap().to_string_lossy().to_string();
    let dir = out.unwrap_or_else(|| tla.parent().unwrap_or(Path::new(".")).join(".tla2rs").join(&stem));
    let crate_name = format!("check_{}", stem.to_lowercase().replace(|c: char| !c.is_ascii_alphanumeric(), "_"));
    std::fs::create_dir_all(dir.join("src")).expect("create output dir");
    std::fs::write(
        dir.join("Cargo.toml"),
        format!(
            "[package]\nname = \"{crate_name}\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[dependencies]\n\n[profile.release]\nopt-level = 3\ncodegen-units = 16\n\n[workspace]\n"
        ),
    )
    .expect("write Cargo.toml");
    std::fs::write(dir.join("src/main.rs"), &output.rust).expect("write main.rs");
    if metal {
        std::fs::write(dir.join("metal.m"), metal::METAL_M).expect("write metal.m");
        std::fs::write(dir.join("build.rs"), metal::BUILD_RS).expect("write build.rs");
    }
    eprintln!("tla2rs: generated {} in {:.0} ms", dir.join("src/main.rs").display(), t0.elapsed().as_secs_f64() * 1e3);
    if emit_only {
        return;
    }
    let t1 = Instant::now();
    let st = Command::new("cargo")
        .args(["build", "--release", "--quiet", "--offline"])
        .current_dir(&dir)
        .status()
        .expect("run cargo");
    if !st.success() {
        eprintln!("tla2rs: building the generated checker failed (this is a tla2rs bug; please report the spec)");
        exit(1);
    }
    eprintln!("tla2rs: built in {:.1} s", t1.elapsed().as_secs_f64());
    let bin = dir.join("target/release").join(&crate_name);
    let st = Command::new(bin).args(&pass).status().expect("run checker");
    exit(st.code().unwrap_or(1));
}
