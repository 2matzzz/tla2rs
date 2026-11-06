//! Generated only with `-metal`. Offloads phase 2 (the "already visited?" lookup) to the GPU.
//!
//! The Rust side allocates the table page-aligned and exposes it to Metal as is, without copying.
//! On Apple Silicon the CPU and GPU share memory, so handing it over costs nothing.
//! The GPU only reads the table and never writes it, so no atomics are needed (Metal has no 64-bit
//! compare-and-swap anyway).

/// Objective-C source placed in the generated crate.
pub const METAL_M: &str = r##"
#import <Metal/Metal.h>
#import <stdlib.h>
#import <string.h>

// Probes within a single shard only. The table is read-only.
static const char *SRC =
"#include <metal_stdlib>\n"
"using namespace metal;\n"
"kernel void lookup(device const ulong* tbl [[buffer(0)]],\n"
"                   device const ulong* fps [[buffer(1)]],\n"
"                   device uchar* found [[buffer(2)]],\n"
"                   constant uint2& cfg [[buffer(3)]],\n"
"                   uint gid [[thread_position_in_grid]]) {\n"
"    ulong fp = fps[gid];\n"
"    uint slots = cfg.x, shift = cfg.y;\n"
"    uint m = slots - 1;\n"
"    uint base = (uint)(fp >> shift) * slots;\n"
"    uint i = (uint)fp & m;\n"
"    for (uint s = 0; s <= m; s++) {\n"
"        ulong x = tbl[base + i];\n"
"        if (x == 0)  { found[gid] = 0; return; }\n"
"        if (x == fp) { found[gid] = 1; return; }\n"
"        i = (i + 1) & m;\n"
"    }\n"
"    found[gid] = 0;\n"
"}\n";

static id<MTLDevice> g_dev;
static id<MTLCommandQueue> g_q;
static id<MTLComputePipelineState> g_pso;
static id<MTLBuffer> g_tbl;
static id<MTLBuffer> g_fps;
static id<MTLBuffer> g_found;
static unsigned long g_cap;   // capacity of g_fps / g_found, in entries

// Returns 1 once the GPU is ready to use.
int tla2rs_gpu_init(void) {
    if (g_pso) return 1;
    g_dev = MTLCreateSystemDefaultDevice();
    if (!g_dev) return 0;
    NSError *err = nil;
    id<MTLLibrary> lib = [g_dev newLibraryWithSource:[NSString stringWithUTF8String:SRC]
                                             options:nil error:&err];
    if (!lib) { fprintf(stderr, "warning: metal: %s\n", err.localizedDescription.UTF8String); return 0; }
    g_pso = [g_dev newComputePipelineStateWithFunction:[lib newFunctionWithName:@"lookup"] error:&err];
    if (!g_pso) { fprintf(stderr, "warning: metal: %s\n", err.localizedDescription.UTF8String); return 0; }
    g_q = [g_dev newCommandQueue];
    return 1;
}

// Exposes the table without copying. ptr must be page-aligned and bytes a multiple of the page
// size.
void tla2rs_gpu_set_table(void *ptr, unsigned long bytes) {
    g_tbl = [g_dev newBufferWithBytesNoCopy:ptr length:bytes
                                    options:MTLResourceStorageModeShared deallocator:nil];
}

// Buffer the fingerprints are written into. Makes room for n entries and returns it.
unsigned long long *tla2rs_gpu_fps(unsigned long n) {
    if (n > g_cap) {
        g_cap = n + n / 2 + 1024;
        g_fps = [g_dev newBufferWithLength:g_cap * 8 options:MTLResourceStorageModeShared];
        g_found = [g_dev newBufferWithLength:g_cap options:MTLResourceStorageModeShared];
    }
    return (unsigned long long *)g_fps.contents;
}

// The lookup in flight, if any.
static id<MTLCommandBuffer> g_inflight;

// Dispatches the lookup without waiting for it.
void tla2rs_gpu_start(unsigned long n, unsigned int slots, unsigned int shift) {
    unsigned int cfg[2] = { slots, shift };
    id<MTLCommandBuffer> cb = [g_q commandBuffer];
    id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
    [enc setComputePipelineState:g_pso];
    [enc setBuffer:g_tbl offset:0 atIndex:0];
    [enc setBuffer:g_fps offset:0 atIndex:1];
    [enc setBuffer:g_found offset:0 atIndex:2];
    [enc setBytes:cfg length:8 atIndex:3];
    NSUInteger tg = g_pso.maxTotalThreadsPerThreadgroup;
    if (tg > n) tg = n;
    [enc dispatchThreads:MTLSizeMake(n, 1, 1) threadsPerThreadgroup:MTLSizeMake(tg, 1, 1)];
    [enc endEncoding];
    [cb commit];
    g_inflight = cb;
}

// Waits for the dispatched lookup to finish and returns a pointer to the first result.
unsigned char *tla2rs_gpu_wait(void) {
    if (g_inflight) { [g_inflight waitUntilCompleted]; g_inflight = nil; }
    return (unsigned char *)g_found.contents;
}
"##;

/// build.rs for the generated crate.
pub const BUILD_RS: &str = r##"
fn main() {
    let out = std::process::Command::new("clang")
        .args(["-O2", "-fobjc-arc", "-c", "metal.m", "-o"])
        .arg(format!("{}/metal.o", std::env::var("OUT_DIR").unwrap()))
        .status();
    match out {
        Ok(s) if s.success() => {}
        _ => panic!("clang failed to compile metal.m (Xcode command line tools required)"),
    }
    let dir = std::env::var("OUT_DIR").unwrap();
    std::process::Command::new("ar")
        .args(["crs", &format!("{dir}/libtla2rsmetal.a"), &format!("{dir}/metal.o")])
        .status()
        .expect("ar");
    println!("cargo:rustc-link-search=native={dir}");
    println!("cargo:rustc-link-lib=static=tla2rsmetal");
    println!("cargo:rustc-link-lib=framework=Metal");
    println!("cargo:rustc-link-lib=framework=Foundation");
    println!("cargo:rerun-if-changed=metal.m");
}
"##;

/// Fallback used without `-metal`. No GPU; phase 2 runs on the CPU.
pub const NO_GPU: &str = r##"
// ---------------------------------------------------------------- no Metal (tla2rs)

fn gpu_ready() -> bool {
    false
}

fn gpu_set_table(_tbl: &Table) {}

fn gpu_start(_by_part: &[Vec<Vec<Cand>>], _tbl: &Table) -> usize {
    0
}

fn gpu_wait(_by_part: &[Vec<Vec<Cand>>], _flags: &mut [Vec<u8>], _total: usize) {}
"##;

/// Rust-side glue inserted into the generated code.
pub const GLUE: &str = r##"
// ---------------------------------------------------------------- Metal (tla2rs)

extern "C" {
    fn tla2rs_gpu_init() -> std::ffi::c_int;
    fn tla2rs_gpu_set_table(ptr: *mut std::ffi::c_void, bytes: usize);
    fn tla2rs_gpu_fps(n: usize) -> *mut u64;
    fn tla2rs_gpu_start(n: usize, slots: u32, shift: u32);
    fn tla2rs_gpu_wait() -> *const u8;
}

static GPU: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

/// Whether the GPU is usable. If not, the work falls back to the CPU.
fn gpu_ready() -> bool {
    *GPU.get_or_init(|| unsafe { tla2rs_gpu_init() == 1 })
}

fn gpu_set_table(tbl: &Table) {
    if gpu_ready() {
        unsafe { tla2rs_gpu_set_table(tbl.t.ptr as *mut std::ffi::c_void, tbl.t.bytes()) };
    }
}

/// Dispatches phase 2 to the GPU without waiting. Only the fingerprints are written to the GPU
/// buffer.
fn gpu_start(by_part: &[Vec<Vec<Cand>>], tbl: &Table) -> usize {
    let total: usize = by_part.iter().flat_map(|g| g.iter()).map(|v| v.len()).sum();
    if total == 0 {
        return 0;
    }
    unsafe {
        let dst = tla2rs_gpu_fps(total);
        let mut k = 0;
        for g in by_part {
            for v in g {
                for c in v {
                    *dst.add(k) = c.fp as u64;
                    k += 1;
                }
            }
        }
        tla2rs_gpu_start(total, tbl.slots as u32, (FP_BITS - 10) as u32);
    }
    total
}

/// Collects the results of the dispatched lookup.
fn gpu_wait(by_part: &[Vec<Vec<Cand>>], flags: &mut [Vec<u8>], total: usize) {
    if total == 0 {
        return;
    }
    unsafe {
        let src = tla2rs_gpu_wait();
        let mut off = 0;
        for (t, g) in by_part.iter().enumerate() {
            let n: usize = g.iter().map(|v| v.len()).sum();
            std::ptr::copy_nonoverlapping(src.add(off), flags[t].as_mut_ptr(), n);
            off += n;
        }
    }
}
"##;
