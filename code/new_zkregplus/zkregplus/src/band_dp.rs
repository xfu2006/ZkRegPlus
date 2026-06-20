//! M11 per-chunk capacity ladder planner (aggressive SDE only). Given the
//! per-chunk demand -- universe = |failed_c|, the forward/active/live
//! propagation counts, and the per-chunk FSM/CP structural peaks -- partition
//! the chunks into <= k_max cost-bands and emit one RungSpec per band. Each
//! rung's caps are the per-axis MAX over its band (monotone envelopes over
//! universe), so the rung dominates every chunk routed to it; a chunk routes to
//! the cheapest band whose ceiling >= its universe. perc/avg_active are anchored
//! to P_max (StepFwdPrf-validated) and scaled down by the band's fwd/active
//! ratio. Pure: no circuit/DB deps, fully unit-testable.

use crate::gadgets::discharge_adv::{FWD_COST, RES_SMALL_COST};

/// One rung of the ladder: the SED universe ceiling, the P_max-anchored
/// perc/avg_active for chunks at that ceiling, and the band's raw FSM/CP
/// structural peaks (to_basis-converted by assemble_ladder). `subsigs` is the
/// raw universe; the caller adds the +1 comp_sig dummy. All clamped to P_max.
#[derive(Clone, Debug, PartialEq)]
pub struct RungSpec {
    pub subsigs: usize,
    pub perc_pats_expansion_rate: usize,
    pub avg_active_pats_per_subsig: usize,
    // per-rung raw FSM/CP demand (band envelope max). 0 when per-chunk arrays
    // are absent (non-estimator path); assemble_ladder then keeps P_max.
    pub max_unique_acc_pats: usize,
    pub max_acc_states: usize,
    pub max_pats_in_trace: usize,
    pub max_cp_unique_states: usize,
}

#[inline]
fn cdiv(a: usize, b: usize) -> usize { (a + b.max(1) - 1) / b.max(1) }

/// Pre-clamp forward/live demand proxy (mirrors stats_helper back-solve,
/// without margin/clamp). perc is linear in this, so the per-rung perc is
/// pmax_perc scaled by raw/top_raw -- top band == pmax_perc exactly.
fn raw_perc(fwd: usize, live: usize, basis_pats: usize,
    seg_size: usize) -> usize {
    let scale = 100_000_000usize; // 1e8
    let (bp, seg) = (basis_pats.max(1), seg_size.max(1));
    let pf = cdiv(fwd * scale, bp * seg * FWD_COST);
    let pq = cdiv(live * scale, bp * seg * RES_SMALL_COST);
    pf.max(pq).max(1)
}

/// A bucket of chunks sharing a (log-spaced) universe range. `ceiling` is the
/// bucket's max universe; the rest are running-MAX (envelope) over all chunks
/// with universe <= ceiling, so they dominate every chunk in the band.
struct Bucket {
    ceiling: usize, count: usize,
    fwd: usize, active: usize, live: usize,            // cumulative envelopes
    uniq: usize, acc: usize, pats: usize, cpu: usize,
    // per-bucket maxes (this bucket's OWN chunks only) -- used by the
    // exact-per-rung sizing path; 0 when no chunk contributes.
    m_fwd: usize, m_active: usize, m_live: usize,
    m_uniq: usize, m_acc: usize, m_pats: usize, m_cpu: usize,
}

/// Log-bucket the per-chunk demand into <= n_buckets ascending buckets, each
/// carrying its universe ceiling, chunk count, and monotone envelopes (incl.
/// the FSM/CP structural arrays). Empty structural arrays contribute 0.
fn bucketize(universe: &[usize], fwd: &[usize], active: &[usize],
    live: &[usize], uniq: &[usize], acc: &[usize], pats: &[usize],
    cpu: &[usize], n_buckets: usize) -> Vec<Bucket> {
    let n = universe.len();
    if n == 0 { return vec![]; }
    let mut idx: Vec<usize> = (0..n).collect();
    idx.sort_by_key(|&i| universe[i]);
    let maxv = universe[idx[n - 1]];
    let nb = n_buckets.max(1);
    let lnmax = ((maxv + 1) as f64).ln();
    let bid = |u: usize| if maxv == 0 || lnmax == 0.0 { 0 }
        else { (((nb - 1) as f64) * ((u + 1) as f64).ln() / lnmax) as usize };
    let g = |a: &[usize], i: usize| a.get(i).copied().unwrap_or(0);
    let (mut cf, mut ca, mut cl) = (0usize, 0usize, 0usize);
    let (mut cu, mut cc, mut cp, mut cq) = (0usize, 0usize, 0usize, 0usize);
    let mut cur = usize::MAX;
    let mut out: Vec<Bucket> = vec![];
    for &i in &idx {                       // ascending universe => running max
        cf = cf.max(fwd[i]); ca = ca.max(active[i]); cl = cl.max(live[i]);
        cu = cu.max(g(uniq, i)); cc = cc.max(g(acc, i));
        cp = cp.max(g(pats, i)); cq = cq.max(g(cpu, i));
        let b = bid(universe[i]);
        if b != cur {
            out.push(Bucket { ceiling: 0, count: 0, fwd: cf, active: ca,
                live: cl, uniq: cu, acc: cc, pats: cp, cpu: cq,
                m_fwd: 0, m_active: 0, m_live: 0,
                m_uniq: 0, m_acc: 0, m_pats: 0, m_cpu: 0 });
            cur = b;
        }
        let last = out.last_mut().unwrap();
        last.ceiling = universe[i];        // ascending => last wins = bucket max
        last.count += 1;
        last.fwd = cf; last.active = ca; last.live = cl;
        last.uniq = cu; last.acc = cc; last.pats = cp; last.cpu = cq;
        // per-bucket max over THIS bucket's own chunks (not cumulative).
        last.m_fwd = last.m_fwd.max(fwd[i]);
        last.m_active = last.m_active.max(active[i]);
        last.m_live = last.m_live.max(live[i]);
        last.m_uniq = last.m_uniq.max(g(uniq, i));
        last.m_acc = last.m_acc.max(g(acc, i));
        last.m_pats = last.m_pats.max(g(pats, i));
        last.m_cpu = last.m_cpu.max(g(cpu, i));
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
/// `pmax_*` are the global-sufficient P_max caps (rungs clamped/anchored to
/// them); the FSM/CP arrays (uniq/acc/pats/cpu) may be empty (-> 0, P_max kept).
/// Returns (rungs asc, hist).
pub fn plan_rungs(universe: &[usize], fwd: &[usize], active: &[usize],
    live: &[usize], uniq: &[usize], acc: &[usize], pats: &[usize],
    cpu: &[usize], basis_pats: usize, seg_size: usize,
    pmax_subsigs: usize, pmax_perc: usize, pmax_avg: usize,
    k_max: usize, n_buckets: usize) -> (Vec<RungSpec>, Vec<usize>) {
    let buckets = bucketize(universe, fwd, active, live, uniq, acc, pats,
        cpu, n_buckets);
    if buckets.is_empty() { return (vec![], vec![]); }
    // P_max anchors: the top (max-universe) band carries the global-max
    // fwd/active envelopes, so anchoring to it makes the top rung == P_max.
    let top = buckets.last().unwrap();
    let top_raw = raw_perc(top.fwd, top.live, basis_pats, seg_size);
    let top_active = top.active.max(1);
    let pat_loc = (basis_pats * seg_size / 10000).max(1);
    let specs: Vec<RungSpec> = buckets.iter().map(|b| {
        let v = b.ceiling.min(pmax_subsigs);
        let rp = raw_perc(b.fwd, b.live, basis_pats, seg_size);
        RungSpec {
            subsigs: v,
            perc_pats_expansion_rate:
                cdiv(pmax_perc * rp, top_raw).min(pmax_perc).max(1),
            avg_active_pats_per_subsig:
                cdiv(pmax_avg * b.active, top_active).min(pmax_avg).max(1),
            max_unique_acc_pats: b.uniq,
            max_acc_states: b.acc,
            max_pats_in_trace: b.pats,
            max_cp_unique_states: b.cpu,
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
    let n_b = buckets.len();
    let (mut rungs, mut hist, mut start) = (vec![], vec![], 0usize);
    for &end in &ends {
        // Exact-per-rung sizing for NON-top rungs: cap = max over the rung's
        // OWN member buckets' per-bucket maxes (de-saturates the cumulative
        // envelope). The top rung keeps the P_max-anchored spec -- it cannot
        // CapErr-bump, so it retains the estimator's safety margin.
        let spec = if end != n_b {
            let grp = &buckets[start..end];
            let mx = |sel: fn(&Bucket) -> usize|
                grp.iter().map(sel).max().unwrap_or(0);
            let (mf, ml, mac) = (mx(|b| b.m_fwd), mx(|b| b.m_live),
                mx(|b| b.m_active));
            let sub = buckets[end - 1].ceiling.min(pmax_subsigs);
            // basis_pats the GADGET will use (assemble_ladder clamps
            // RungSpec.max_pats_in_trace to pmax). Derive perc from THIS so the
            // size_trace buffer (basis_pats*perc) matches the demand.
            let bpc = mx(|b| b.m_pats).min(basis_pats).max(1);
            let (hn, hd) = (5usize, 4usize);
            // perc/avg_active are PRODUCT-coupled (size_trace=basis_pats*perc,
            // size_pat=subsigs*avg_active). Derive each from the rung's OWN
            // coupled cap + member-max demand (+25% leg room); then clamp the
            // PRODUCT to the P_max budget so a rung never exceeds the top.
            // (Was ratio-scaled vs a global anchor -> under-sized non-top
            // rungs and avalanched them to the top.)
            let perc = (raw_perc(mf, ml, bpc, seg_size) * hn / hd)
                .min(basis_pats * pmax_perc / bpc).max(1);
            let avg = (cdiv(mac, sub.max(1)) * hn / hd)
                .min(pmax_subsigs * pmax_avg / sub.max(1)).max(1);
            RungSpec {
                subsigs: sub,
                perc_pats_expansion_rate: perc,
                avg_active_pats_per_subsig: avg,
                max_unique_acc_pats: mx(|b| b.m_uniq),
                max_acc_states: mx(|b| b.m_acc),
                max_pats_in_trace: mx(|b| b.m_pats),
                max_cp_unique_states: mx(|b| b.m_cpu),
            }
        } else {
            specs[end - 1].clone()                          // legacy / top rung
        };
        // DEBUG USE 64400 (ZKR_PROBE_CAPS): per-rung member breakdown -- the
        // universe range, chunk count, derived perc/avg_act, and WHICH member
        // bucket (by universe) pins the max fwd/active that sets perc/avg_act.
        // Reveals the universe<->fwd decoupling: a low-universe bucket with a
        // high max_fwd is why a "bulk" rung gets a huge perc.
        if std::env::var("ZKR_PROBE_CAPS").is_ok() {
            let grp = &buckets[start..end];
            let cnt: usize = grp.iter().map(|b| b.count).sum();
            let (mf_u, mf) = grp.iter().map(|b| (b.ceiling, b.m_fwd))
                .max_by_key(|&(_, f)| f).unwrap_or((0, 0));
            let (ma_u, ma) = grp.iter().map(|b| (b.ceiling, b.m_active))
                .max_by_key(|&(_, a)| a).unwrap_or((0, 0));
            let u_lo = grp.first().map(|b| b.ceiling).unwrap_or(0);
            let u_hi = grp.last().map(|b| b.ceiling).unwrap_or(0);
            println!("DEBUG USE 64400.rung {}: univ=[{}..{}] chunks={} \
                perc={} avg_act={} basis_pats={} | max_fwd={}@univ{} \
                max_active={}@univ{}", rungs.len(), u_lo, u_hi, cnt,
                spec.perc_pats_expansion_rate,
                spec.avg_active_pats_per_subsig, spec.max_pats_in_trace,
                mf, mf_u, ma, ma_u);
        }
        rungs.push(spec);
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
            Bucket { ceiling: c, count: n, fwd: 0, active: 0, live: 0,
                uniq: 0, acc: 0, pats: 0, cpu: 0,
                m_fwd: 0, m_active: 0, m_live: 0,
                m_uniq: 0, m_acc: 0, m_pats: 0, m_cpu: 0 }).collect()
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

    // plan_rungs over universe arrays, reusing `u` for the FSM/CP arrays (the
    // tests assert DP/envelope/clamp behavior, not structural-cap values).
    fn plan(u: &[usize], fwd: &[usize], a: &[usize], l: &[usize],
        bp: usize, seg: usize, ps: usize, pp: usize, pa: usize,
        k: usize, nb: usize) -> (Vec<RungSpec>, Vec<usize>) {
        plan_rungs(u, fwd, a, l, u, u, u, u, bp, seg, ps, pp, pa, k, nb)
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
        assert_eq!(plan(&e, &e, &e, &e, 700, 15872, 1000, 8000, 12, 4, 2048),
            (vec![], vec![]));
        let z = vec![0usize; 5];                     // all-empty universe
        let (r, h) = plan(&z, &z, &z, &z, 700, 15872, 1000, 8000, 12, 4, 2048);
        assert_eq!(r.len(), 1); assert_eq!(r[0].subsigs, 0); assert_eq!(h, vec![5]);
        let u = vec![1, 10, 100];                    // k_max >= distinct
        let (r, _) = plan(&u, &u, &u, &u, 700, 15872, 1000, 8000, 12, 9, 2048);
        assert!(r.len() <= 3);
        for w in r.windows(2) { assert!(w[0].subsigs <= w[1].subsigs); } // ascending
    }
    #[test]
    fn envelope_is_running_max() {                   // low-universe high-fwd outlier
        let u = vec![0, 0, 5, 200]; let fwd = vec![0, 0, 9000, 1000];
        let a = vec![0, 0, 10, 10]; let l = vec![0, 0, 0, 0];
        // top band's fwd envelope (9000) anchors perc; with high pmax it lifts.
        let (r, _) = plan(&u, &fwd, &a, &l, 700, 15872, 1000, 100000, 100, 4, 2048);
        assert!(r.last().unwrap().perc_pats_expansion_rate > 100); // lifted by fwd_env
    }
    #[test]
    fn rungs_clamped_to_pmax() {
        // Non-top rungs no longer clamp perc/avg_active individually -- a
        // small-basis rung legitimately needs a higher RATE. The bounded
        // quantity is the step BUFFER (the product): basis_pats*perc and
        // subsigs*avg_active must not exceed the P_max budget.
        let u = vec![10, 500]; let big = vec![1_000_000, 2_000_000];
        let (r, _) = plan(&u, &big, &big, &big, 700, 15872, 300, 5000, 12, 2, 2048);
        for s in &r {
            assert!(s.subsigs <= 300);
            assert!(s.subsigs * s.avg_active_pats_per_subsig <= 300 * 12);
            assert!(s.max_pats_in_trace.min(700) * s.perc_pats_expansion_rate
                <= 700 * 5000);
        }
    }
    #[test]
    fn top_rung_anchored_to_pmax() {                 // B1: top rung == pmax_perc
        let u = vec![10, 500]; let fwd = vec![100, 5000];
        let a = vec![2, 9]; let l = vec![0, 0];
        let (r, _) = plan(&u, &fwd, &a, &l, 700, 15872, 1000, 2738, 12, 2, 2048);
        assert_eq!(r.last().unwrap().perc_pats_expansion_rate, 2738);
        assert!(r.first().unwrap().perc_pats_expansion_rate < 2738); // cheaper
    }
    #[test]
    fn histogram_sums_to_chunks() {
        let u = vec![0, 0, 0, 50, 200, 200, 5];
        let (_, h) = plan(&u, &u, &u, &u, 700, 15872, 1000, 8000, 12, 3, 2048);
        assert_eq!(h.iter().sum::<usize>(), u.len());
    }
    #[test]
    fn exact_rung_caps_desaturate_middle() {
        // A LOW-NEEDS chunk (u=10) carries a HIGH basis_pats (9000); the mid
        // chunk (u=500) carries only 80. The old cumulative envelope would
        // pin the mid rung to 9000; exact-per-rung gives it its OWN 80. The
        // top rung stays anchored (cumulative => 9000).
        let u    = vec![10, 10, 500, 500, 9000, 9000];
        let pats = vec![9000, 50, 80, 80, 200, 200];
        let lo   = vec![0usize; 6];
        let (r, _) = plan_rungs(&u, &lo, &lo, &lo, &lo, &lo, &pats, &lo,
            700, 15872, 10000, 5000, 12, 3, 2048);
        assert_eq!(r.len(), 3);
        assert_eq!(r[1].max_pats_in_trace, 80,        // de-saturated mid rung
            "mid rung must carry its own pats, not the inherited global max");
        assert_eq!(r[2].max_pats_in_trace, 9000);     // top stays anchored
    }
}
