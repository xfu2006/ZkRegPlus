// TEST_MSM -- standalone benchmark to verify the per-job MSM regression
// hypothesis identified by the 947381 probes.
//
// Workload: BN254 G1 multi-scalar multiplication via
//   <G1Projective as VariableBaseMSM>::msm_bigint(&bases, &scalars_bigint)
// matching `veccom.rs:315`. Shared bases (Arc), per-thread scalars.
//
// For N in {1, 2, 4, 8}: spawn N threads, each calls MSM 3 times,
// barrier-synchronized. After each MSM batch, all threads also run a
// 256 MB stream-sum to measure per-thread DRAM bandwidth under N-way
// contention.

use std::sync::{Arc, Barrier};
use std::thread;
use std::time::Instant;

use ark_bn254::{Fr, G1Affine, G1Projective};
use ark_ec::{CurveGroup, Group, VariableBaseMSM};
use ark_ff::{PrimeField, UniformRand};
use ark_std::test_rng;
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};

const M: usize = 16 * 1024 * 1024; // 16 M elements
const REPS: usize = 3;
const N_VALUES: &[usize] = &[1, 2, 4, 8];
// 256 MB stream buffer per thread for the DRAM bandwidth probe.
const STREAM_U64S: usize = 32 * 1024 * 1024; // 32M * 8B = 256 MB

fn make_random_scalars(m: usize, seed_off: u64) -> Vec<Fr> {
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    let mut rng = StdRng::seed_from_u64(0x947381_0000_0000u64 ^ seed_off);
    (0..m).map(|_| Fr::rand(&mut rng)).collect()
}

fn make_random_bases(m: usize) -> Vec<G1Affine> {
    use ark_std::rand::{rngs::StdRng, SeedableRng};
    println!("[setup] generating {} random bases (~{} MB) in parallel...",
        m, m * 64 / 1024 / 1024);
    let t0 = Instant::now();
    // par_iter over chunks; each chunk uses its own seeded RNG.
    let proj: Vec<G1Projective> = (0..m).into_par_iter().map(|i| {
        let mut rng = StdRng::seed_from_u64(0xBA5E_0000u64 ^ i as u64);
        let s = Fr::rand(&mut rng);
        G1Projective::generator() * s
    }).collect();
    let bases = G1Projective::normalize_batch(&proj);
    println!("[setup]   bases ready in {:.1} s",
        t0.elapsed().as_secs_f64());
    bases
}

fn make_stream_buf() -> Vec<u64> {
    // non-zero pattern so pages are real DRAM, not zero-page
    let mut v = vec![0u64; STREAM_U64S];
    for (i, slot) in v.iter_mut().enumerate() {
        *slot = (i as u64).wrapping_mul(0x9E3779B97F4A7C15)
            .wrapping_add(0xCAFE_BABE_DEAD_BEEF);
    }
    v
}

/// Run MSM `reps` times in `pool`. Returns each rep's elapsed ns.
/// Improvement #2: BigInts are pre-converted ONCE before the timing
/// loop, so the timer captures only `msm_bigint` itself.
/// Improvement #4: bases is now an owned Vec per worker (replicated),
/// not an Arc<Vec> shared across workers.
fn run_msm_thread(
    bases: Vec<G1Affine>,
    scalars: Vec<Fr>,
    barrier: Arc<Barrier>,
    reps: usize,
    pool: &rayon::ThreadPool,
) -> Vec<u128> {
    let bigints: Vec<<Fr as PrimeField>::BigInt> =
        scalars.iter().map(|s| s.into_bigint()).collect();
    drop(scalars);
    let mut times = Vec::with_capacity(reps);
    for _ in 0..reps {
        barrier.wait();
        let t0 = Instant::now();
        // Improvement #1: confine the MSM's internal par_iter to this
        // worker's private rayon pool.
        let _commitment = pool.install(|| {
            <G1Projective as VariableBaseMSM>::msm_bigint(
                &bases[..], &bigints)
        });
        let dt = t0.elapsed().as_nanos();
        std::hint::black_box(_commitment);
        times.push(dt);
    }
    times
}

/// Stream-sum 256 MB and return ns elapsed.
fn run_stream_probe(buf: &[u64], barrier: Arc<Barrier>) -> u128 {
    barrier.wait();
    let t0 = Instant::now();
    let mut s: u64 = 0;
    for &v in buf.iter() {
        s = s.wrapping_add(std::hint::black_box(v));
    }
    std::hint::black_box(s);
    t0.elapsed().as_nanos()
}

fn median_ns(xs: &[u128]) -> u128 {
    let mut v = xs.to_vec();
    v.sort_unstable();
    v[v.len() / 2]
}

fn main() {
    let n_cores = rayon::current_num_threads();
    println!("[setup] rayon threads = {}", n_cores);

    // bases is generated once, then CLONED per worker (improvement #4:
    // replicated, not shared). The clone happens lazily per N below.
    let bases_master = make_random_bases(M);
    let bases_size_mb = (M * 64) as f64 / (1024.0 * 1024.0);
    println!("[setup] bases size = {:.0} MB per worker (replicated, NOT shared)",
        bases_size_mb);

    // per-N results
    let mut results: Vec<(usize, f64, f64, f64, f64)> = Vec::new();
    // (N, msm_ms_median, norm_vs_n1, dram_gbps_per_thread, total_gbps)
    let mut baseline_ms: Option<f64> = None;

    for &n in N_VALUES {
        println!("\n========== N = {} ==========", n);
        // Improvement #1: each worker gets a private rayon pool sized
        // cores/N so the N MSMs don't oversubscribe a shared pool.
        let pool_size = (n_cores / n).max(1);
        println!("  per-worker rayon pool size = {}", pool_size);

        // spawn N worker threads
        let barrier = Arc::new(Barrier::new(n));
        let bar_stream = Arc::new(Barrier::new(n));
        let mut handles = Vec::new();
        for tid in 0..n {
            // Improvement #4: clone bases into each worker so each
            // owns a private copy in its own pages (no shared read).
            let t_clone = Instant::now();
            let bases_local = bases_master.clone();
            println!("  [t{}] cloned bases ({:.0} MB) in {:.1} s",
                tid, bases_size_mb, t_clone.elapsed().as_secs_f64());
            let bar = Arc::clone(&barrier);
            let bar_s = Arc::clone(&bar_stream);
            let h = thread::spawn(move || {
                let pool = rayon::ThreadPoolBuilder::new()
                    .num_threads(pool_size)
                    .build()
                    .expect("rayon pool build failed");
                println!("  [t{}] generating {} scalars...", tid, M);
                let scalars = make_random_scalars(M, tid as u64);
                let stream_buf = make_stream_buf();
                println!("  [t{}] starting MSM batch ({} reps)...",
                    tid, REPS);
                let msm_times = run_msm_thread(
                    bases_local, scalars, bar, REPS, &pool);
                let stream_ns = run_stream_probe(&stream_buf, bar_s);
                let med = median_ns(&msm_times);
                println!("  [t{}] msm median = {:.1} ms, stream 256MB = {:.1} ms ({:.2} GB/s)",
                    tid, med as f64 / 1e6,
                    stream_ns as f64 / 1e6,
                    256.0 / (stream_ns as f64 / 1e9) / 1024.0);
                (med, stream_ns)
            });
            handles.push(h);
        }
        let per_thread: Vec<(u128, u128)> =
            handles.into_iter().map(|h| h.join().unwrap()).collect();

        // aggregate medians across threads
        let msm_meds: Vec<u128> =
            per_thread.iter().map(|x| x.0).collect();
        let stream_nss: Vec<u128> =
            per_thread.iter().map(|x| x.1).collect();
        let msm_med_ms = median_ns(&msm_meds) as f64 / 1e6;
        let stream_med_ns = median_ns(&stream_nss) as f64;
        // 256 MB / stream_med_s = GB/s per thread
        let dram_gbps_per_thread =
            256.0 / (stream_med_ns / 1e9) / 1024.0;
        let total_gbps = dram_gbps_per_thread * n as f64;

        if baseline_ms.is_none() { baseline_ms = Some(msm_med_ms); }
        let norm = msm_med_ms / baseline_ms.unwrap();

        results.push((n, msm_med_ms, norm,
            dram_gbps_per_thread, total_gbps));
        println!("  N={}: msm_med_ms={:.1}, norm={:.2}x, dram_per_thread={:.2} GB/s, total={:.2} GB/s",
            n, msm_med_ms, norm, dram_gbps_per_thread, total_gbps);
    }

    // final report
    println!("\n");
    println!("======================================================================");
    println!("TEST_MSM results (M={}, BN254 G1 MSM, {} reps/N, median per thread)",
        M, REPS);
    println!("======================================================================");
    println!("{:<5}{:>10}{:>14}{:>26}{:>14}",
        "N", "msm_ms", "norm_vs_N1", "dram_GBps_per_thread", "total_GBps");
    println!("----------------------------------------------------------------------");
    for (n, ms, norm, gbps, total) in &results {
        let bars = "#".repeat(((*gbps).round() as usize).min(40));
        println!("{:<5}{:>10.0}{:>13.2}x{:>10.2}    {:<14}{:>14.2}",
            n, ms, norm, gbps, bars, total);
    }
    println!("======================================================================");
}
