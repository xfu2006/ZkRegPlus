//! M11 per-chunk capacity ladder planner (aggressive SDE only). Given the
//! per-chunk demand -- universe = |failed_c|, plus the forward/active/live
//! propagation counts -- partition the chunks into <= k_max cost-bands and emit
//! one RungSpec per band. Each rung's caps are the per-axis MAX over its band
//! (monotone envelopes over universe), so the rung dominates every chunk routed
//! to it; a chunk routes to the cheapest band whose ceiling >= its universe.
//! Pure: no circuit/DB deps, fully unit-testable. The fold's per-seg planner
//! is the real router; correctness is independent of band optimality.

use crate::gadgets::discharge_adv::{FWD_COST, RES_SMALL_COST};

/// +25% headroom, matching the estimator back-solve (stats_helper).
const MARGIN_NUM: usize = 5;
const MARGIN_DEN: usize = 4;

/// One rung of the ladder: the SED universe ceiling plus the back-solved
/// perc/avg_active for chunks at that ceiling. `subsigs` is the raw universe;
/// the caller adds the +1 comp_sig dummy. All fields are clamped to P_max.
#[derive(Clone, Debug, PartialEq)]
pub struct RungSpec {
    pub subsigs: usize,
    pub perc_pats_expansion_rate: usize,
    pub avg_active_pats_per_subsig: usize,
}

#[inline]
fn cdiv(a: usize, b: usize) -> usize { (a + b.max(1) - 1) / b.max(1) }

/// Back-solve perc from the forward/live envelope counts (mirrors
/// stats_helper.rs:824-828). Clamped to P_max's perc (known-sufficient).
fn back_solve_perc(fwd: usize, live: usize, basis_pats: usize,
    seg_size: usize, pmax_perc: usize) -> usize {
    let scale = 100_000_000usize; // 1e8
    let (bp, seg) = (basis_pats.max(1), seg_size.max(1));
    let pf = cdiv(fwd * scale, bp * seg * FWD_COST);
    let pq = cdiv(live * scale, bp * seg * RES_SMALL_COST);
    (pf.max(pq).max(100) * MARGIN_NUM / MARGIN_DEN).min(pmax_perc.max(100))
}

/// Back-solve avg_active = ceil(active/subsigs) + headroom, clamped to P_max.
fn back_solve_avg(active: usize, subsigs: usize, pmax_avg: usize) -> usize {
    ((cdiv(active, subsigs.max(1)) * MARGIN_NUM / MARGIN_DEN).max(1))
        .min(pmax_avg.max(1))
}

/// A bucket of chunks sharing a (log-spaced) universe range. `ceiling` is the
/// bucket's max universe; fwd/active/live are the running-MAX (envelope) over
/// all chunks with universe <= ceiling, so they dominate every chunk in the band.
struct Bucket { ceiling: usize, count: usize, fwd: usize, active: usize, live: usize }

/// Log-bucket the per-chunk demand into <= n_buckets ascending buckets, each
/// carrying its universe ceiling, chunk count, and monotone fwd/active/live
/// envelopes. Shrinks M (distinct universe values) so the exact DP is cheap.
fn bucketize(universe: &[usize], fwd: &[usize], active: &[usize],
    live: &[usize], n_buckets: usize) -> Vec<Bucket> {
    let n = universe.len();
    if n == 0 { return vec![]; }
    let mut idx: Vec<usize> = (0..n).collect();
    idx.sort_by_key(|&i| universe[i]);
    let maxv = universe[idx[n - 1]];
    let nb = n_buckets.max(1);
    let lnmax = ((maxv + 1) as f64).ln();
    let bid = |u: usize| if maxv == 0 || lnmax == 0.0 { 0 }
        else { (((nb - 1) as f64) * ((u + 1) as f64).ln() / lnmax) as usize };
    let (mut cf, mut ca, mut cl, mut cur) = (0usize, 0usize, 0usize, usize::MAX);
    let mut out: Vec<Bucket> = vec![];
    for &i in &idx {                       // ascending universe => running max
        cf = cf.max(fwd[i]); ca = ca.max(active[i]); cl = cl.max(live[i]);
        let b = bid(universe[i]);
        if b != cur {
            out.push(Bucket { ceiling: 0, count: 0, fwd: cf, active: ca, live: cl });
            cur = b;
        }
        let last = out.last_mut().unwrap();
        last.ceiling = universe[i];        // ascending => last wins = bucket max
        last.count += 1;
        last.fwd = cf; last.active = ca; last.live = cl;
    }
    out
}

/// DP: partition buckets into <= k_max contiguous groups minimizing
/// sum over groups of cost(group_top_bucket) * group_chunk_count. The top group
/// always covers the max ceiling (sufficiency). Returns the group end indices.
fn dp_partition(buckets: &[Bucket], cost: &dyn Fn(usize) -> usize,
    k_max: usize) -> Vec<usize> {
    let b = buckets.len();
    if b == 0 { return vec![]; }
    let k = k_max.max(1).min(b);
    let mut pc = vec![0usize; b + 1];
    for i in 0..b { pc[i + 1] = pc[i] + buckets[i].count; }
    const INF: usize = usize::MAX / 4;
    let mut dp = vec![vec![INF; b + 1]; k + 1];
    let mut from = vec![vec![0usize; b + 1]; k + 1];
    dp[0][0] = 0;
    for j in 1..=k { for i in 1..=b { for g in (j - 1)..i {
        if dp[j - 1][g] == INF { continue; }
        let c = dp[j - 1][g] + cost(i - 1) * (pc[i] - pc[g]);
        if c < dp[j][i] { dp[j][i] = c; from[j][i] = g; }
    }}}
    // more groups never increase cost, but allow fewer if distinct < k.
    let (mut bj, mut best) = (1usize, dp[1][b]);
    for j in 2..=k { if dp[j][b] < best { best = dp[j][b]; bj = j; } }
    let (mut ends, mut j, mut i) = (vec![], bj, b);
    while j > 0 { ends.push(i); i = from[j][i]; j -= 1; }
    ends.reverse();
    ends
}

/// Plan the rung ladder + per-rung chunk histogram from the per-chunk demand.
/// `pmax_*` are the global-sufficient P_max caps (rungs are clamped to them);
/// `basis_pats`/`seg_size` drive the perc back-solve. Returns (rungs asc, hist).
pub fn plan_rungs(universe: &[usize], fwd: &[usize], active: &[usize],
    live: &[usize], basis_pats: usize, seg_size: usize,
    pmax_subsigs: usize, pmax_perc: usize, pmax_avg: usize,
    k_max: usize, n_buckets: usize) -> (Vec<RungSpec>, Vec<usize>) {
    let buckets = bucketize(universe, fwd, active, live, n_buckets);
    if buckets.is_empty() { return (vec![], vec![]); }
    // per-bucket back-solved caps (used by cost AND the final rungs).
    let pat_loc = (basis_pats * seg_size / 10000).max(1);
    let specs: Vec<RungSpec> = buckets.iter().map(|b| {
        let v = b.ceiling.min(pmax_subsigs);
        RungSpec {
            subsigs: v,
            perc_pats_expansion_rate:
                back_solve_perc(b.fwd, b.live, basis_pats, seg_size, pmax_perc),
            avg_active_pats_per_subsig: back_solve_avg(b.active, v, pmax_avg),
        }
    }).collect();
    // cost(i) = discharge::est_cost replicated (discharge_adv.rs:4865); compute_sig
    // is structural (pat_loc-driven, uniform) so it drops out of the argmin.
    let cost = |i: usize| {
        let s = &specs[i];
        (s.subsigs * s.avg_active_pats_per_subsig * 1000)
            .max(pat_loc * s.perc_pats_expansion_rate / 100)
    };
    let ends = dp_partition(&buckets, &cost, k_max);
    let (mut rungs, mut hist, mut start) = (vec![], vec![], 0usize);
    for &end in &ends {
        rungs.push(specs[end - 1].clone());                 // group top bucket
        hist.push(buckets[start..end].iter().map(|b| b.count).sum());
        start = end;
    }
    (rungs, hist)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(ceils: &[usize], counts: &[usize]) -> Vec<Bucket> {
        ceils.iter().zip(counts).map(|(&c, &n)|
            Bucket { ceiling: c, count: n, fwd: 0, active: 0, live: 0 }).collect()
    }
    fn total_cost(b: &[Bucket], ends: &[usize], cost: &dyn Fn(usize) -> usize) -> usize {
        let mut pc = vec![0usize; b.len() + 1];
        for i in 0..b.len() { pc[i + 1] = pc[i] + b[i].count; }
        let (mut t, mut s) = (0, 0);
        for &e in ends { t += cost(e - 1) * (pc[e] - pc[s]); s = e; }
        t
    }
    fn brute(b: &[Bucket], cost: &dyn Fn(usize) -> usize, k: usize) -> usize {
        let n = b.len();
        let mut pc = vec![0usize; n + 1];
        for i in 0..n { pc[i + 1] = pc[i] + b[i].count; }
        fn rec(s: usize, gl: usize, n: usize, pc: &[usize],
            cost: &dyn Fn(usize) -> usize) -> usize {
            if s == n { return 0; }
            if gl == 0 { return usize::MAX / 4; }
            let mut best = usize::MAX / 4;
            for e in (s + 1)..=n {
                let r = rec(e, gl - 1, n, pc, cost);
                if r < usize::MAX / 4 { best = best.min(cost(e - 1) * (pc[e] - pc[s]) + r); }
            }
            best
        }
        rec(0, k, n, &pc, cost)
    }

    #[test]
    fn dp_matches_brute() {                          // global optimality
        let cases = vec![
            (vec![10, 200, 600], vec![950, 45, 5]),
            (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]),
            (vec![1, 100, 101, 500], vec![100, 1, 1, 2]),
        ];
        for (ceils, counts) in cases {
            let b = mk(&ceils, &counts);
            let cost = |i: usize| b[i].ceiling;
            for k in 1..=b.len() {
                let ends = dp_partition(&b, &cost, k);
                assert_eq!(total_cost(&b, &ends, &cost), brute(&b, &cost, k),
                    "k={} {:?}", k, ceils);
                assert!(ends.len() <= k);
            }
        }
    }
    #[test]
    fn k2_worked_example() {                         // {10,600} not {200,600}
        let b = mk(&[10, 200, 600], &[950, 45, 5]);
        let cost = |i: usize| b[i].ceiling;
        let ends = dp_partition(&b, &cost, 2);
        assert_eq!(ends, vec![1, 3]);                // groups {10},{200,600}
        assert_eq!(total_cost(&b, &ends, &cost), 39500);
    }
    #[test]
    fn folding_monotone_in_k() {                     // folding(k+1) <= folding(k)
        let b = mk(&[1, 10, 100, 1000], &[80, 15, 4, 1]);
        let cost = |i: usize| b[i].ceiling;
        let mut prev = usize::MAX;
        for k in 1..=4 {
            let c = total_cost(&b, &dp_partition(&b, &cost, k), &cost);
            assert!(c <= prev); prev = c;
        }
    }
    #[test]
    fn edge_cases() {
        let e: Vec<usize> = vec![];
        assert_eq!(plan_rungs(&e, &e, &e, &e, 700, 15872, 1000, 8000, 12, 4, 2048),
            (vec![], vec![]));
        let z = vec![0usize; 5];                     // all-empty universe
        let (r, h) = plan_rungs(&z, &z, &z, &z, 700, 15872, 1000, 8000, 12, 4, 2048);
        assert_eq!(r.len(), 1); assert_eq!(r[0].subsigs, 0); assert_eq!(h, vec![5]);
        let u = vec![1, 10, 100];                    // k_max >= distinct
        let (r, _) = plan_rungs(&u, &u, &u, &u, 700, 15872, 1000, 8000, 12, 9, 2048);
        assert!(r.len() <= 3);
        for w in r.windows(2) { assert!(w[0].subsigs <= w[1].subsigs); } // ascending
    }
    #[test]
    fn envelope_is_running_max() {                   // low-universe high-fwd outlier
        let u = vec![0, 0, 5, 200]; let fwd = vec![0, 0, 9000, 1000];
        let a = vec![0, 0, 10, 10]; let l = vec![0, 0, 0, 0];
        let (r, _) = plan_rungs(&u, &fwd, &a, &l, 700, 15872, 1000, 100000, 100, 4, 2048);
        assert!(r.last().unwrap().perc_pats_expansion_rate > 100); // lifted by fwd_env
    }
    #[test]
    fn rungs_clamped_to_pmax() {
        let u = vec![10, 500]; let big = vec![1_000_000, 2_000_000];
        let (r, _) = plan_rungs(&u, &big, &big, &big, 700, 15872, 300, 5000, 12, 2, 2048);
        for s in &r { assert!(s.subsigs <= 300 && s.perc_pats_expansion_rate <= 5000
            && s.avg_active_pats_per_subsig <= 12); }
    }
    #[test]
    fn histogram_sums_to_chunks() {
        let u = vec![0, 0, 0, 50, 200, 200, 5];
        let (_, h) = plan_rungs(&u, &u, &u, &u, 700, 15872, 1000, 8000, 12, 3, 2048);
        assert_eq!(h.iter().sum::<usize>(), u.len());
    }
}
