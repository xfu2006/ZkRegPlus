//! T9906 PROBE -- READ ONLY. Why the neo non-aggressive clam ladder
//! ships a rung 1 that is no cheaper than rung 0, and what a
//! non-aggr-gated budget policy would save. It loads a real
//! ladder.json, rebuilds both rungs exactly as build_circs_adv does
//! (zkp_driver.rs:399-416), and reports the T_qm budget split. No
//! gadget, mapper or driver is modified; nothing here runs in
//! production.
//!
//! ZKR_T9906_LADDER selects the ladder.json (default the clam part-0
//! path the driver writes).

#[cfg(test)]
pub mod tests_probe_t9906 {
	use ark_bn254::Fr;

	use crate::circs::cp_mapper::CpCapacity;
	use crate::circs::sed_mapper::SedCapacity;
	use crate::determine_config::{caps_from_params_general, CapParams};
	use crate::gadgets::discharge_adv::{DischargeAdvCapacity,
		StepQueue, StepQueueType};
	use crate::gadgets::discharge_adv_neo::StepQueueNeo;
	use utils::consts::{get_global_config, min_subsigs_for};

	fn ladder_path() -> String {
		std::env::var("ZKR_T9906_LADDER")
			.unwrap_or_else(|_| "/tmp/bora/clam_neo_p0/ladder.json"
				.to_string())
	}

	/// ladder.json is a JSON ARRAY of CapParams (save_ladder writes
	/// the whole ladder); CapParams::load_json reads a single object,
	/// so parse the array directly.
	fn load_ladder(path: &str) -> Vec<CapParams> {
		let s = std::fs::read_to_string(path)
			.unwrap_or_else(|e| panic!("read {}: {}", path, e));
		serde_json::from_str::<Vec<CapParams>>(&s)
			.unwrap_or_else(|_| vec![CapParams::load_json(path)])
	}

	/// The nine GlobalConfig floors decreased_copy reads. Set from the
	/// run's own `---- global config ----` dump so the descent this
	/// probe replays is the descent the run shipped.
	fn install_floors(p: &CapParams) {
		let mut g = get_global_config();
		// The tuner's own write-back (bora_data_driver.rs:2385-2389):
		// the converged subsigs BECOME the ladder floors.
		g.min_subsigs = p.subsigs;
		g.min_subsigs_igc = p.subsigs_igc;
		g.min_cp_subsigs = p.cp_subsigs;
		// CLAM spec floors (bora_data_driver.rs:700-706).
		g.min_basis_unique_states = 1054;
		g.min_basis_acc_states = 268;
		g.min_basis_pats_in_trace = 295;
		g.min_avg_pats_per_subsig = 8;
		g.min_avg_active_pats_per_subsig = 2;
		g.min_perc_pats_expansion_rate = 1;
		g.min_sigs_sed = 2;
		g.min_perc_comp_subsigs = 10;
		g.min_dfa_sigs = 3;
		g.min_dfa_subsigs = 3;
	}

	/// (name, rung0, rung1) for every sizing axis decreased_copy(2)
	/// touches, so an axis that RISES on the lower rung is visible.
	fn axes(a: &SedCapacity, b: &SedCapacity, ca: &CpCapacity,
		cb: &CpCapacity) -> Vec<(&'static str, usize, usize)> {
		let (da, db) = (a.da_capacity(), b.da_capacity());
		vec![
			("sed.subsigs", da.subsigs, db.subsigs),
			("sed.universe_subsigs", da.universe_subsigs,
				db.universe_subsigs),
			("sed.avg_active_pats", da.avg_active_pats_per_subsig,
				db.avg_active_pats_per_subsig),
			("sed.basis_pats_in_trace", da.basis_pats_in_trace,
				db.basis_pats_in_trace),
			("sed.perc_pats_expansion", da.perc_pats_expansion_rate,
				db.perc_pats_expansion_rate),
			("sed.qm_real_rows", da.qm_real_rows, db.qm_real_rows),
			("sed.max_nibble_len", da.max_nibble_len,
				db.max_nibble_len),
			("cp.basis_unique_states", ca.basis_unique_states,
				cb.basis_unique_states),
			("cp.subsigs", ca.subsigs, cb.subsigs),
			("cp.avg_pats_per_subsig", ca.avg_pats_per_subsig,
				cb.avg_pats_per_subsig),
		]
	}

	/// Dense ResLarge bound -- what the LEGACY arm budgets, and what
	/// the descent would fall back to if qm_real_rows were not carried
	/// (Self::new leaves it 0; sed_mapper.rs:205).
	fn dense_rows(d: &DischargeAdvCapacity) -> usize {
		let mut c = d.clone();
		c.qm_real_rows = 0;
		let (n, sp, st) = StepQueue::<Fr>::vec_size(
			&StepQueueType::ResLarge, &c);
		let _ = (sp, st);
		n
	}

	fn real_cap(d: &DischargeAdvCapacity) -> usize {
		StepQueueNeo::<Fr>::qm_real_cap(d)
	}

	/// T9906.1: replay the shipped descent and show, per axis, what
	/// rung 1 actually gets. Proves (a) qm_real_rows is carried flat,
	/// (b) whether any axis RISES, (c) what the legacy dense bound
	/// would have been on each rung.
	#[test]
	fn probe_t9906_1_descent_replay() {
		let path = ladder_path();
		let v = load_ladder(&path);
		let p = &v[0];
		install_floors(p);
		println!("DEBUG USE 69906.1: ladder={} rungs_in_file={}",
			path, v.len());

		let (cp0, sed0, dfa0, _cpi0, _sedi0) =
			caps_from_params_general(p);
		let sed1 = sed0.decreased_copy(2, min_subsigs_for(false));
		let cp1 = cp0.decreased_copy(2);
		let dfa1 = dfa0.decreased_copy(2);

		println!("DEBUG USE 69906.2: {:<26} {:>12} {:>12}  {}",
			"axis", "rung0(Pmax)", "rung1(desc)", "verdict");
		for (n, a, b) in axes(&sed0, &sed1, &cp0, &cp1) {
			let v = if b > a { "*** RISES ***" }
				else if b == a { "FLAT" } else { "falls" };
			println!("DEBUG USE 69906.2: {:<26} {:>12} {:>12}  {}",
				n, a, b, v);
		}
		println!("DEBUG USE 69906.3: dfa.subsigs {} -> {} \
			 (0 would DROP the DFA gadget)", dfa0.subsigs,
			dfa1.subsigs);

		let (d0, d1) = (sed0.da_capacity(), sed1.da_capacity());
		println!("DEBUG USE 69906.4: qm_real_cap  rung0={} rung1={} \
			 (carried: {})", real_cap(d0), real_cap(d1),
			real_cap(d0) == real_cap(d1));
		println!("DEBUG USE 69906.5: dense_bound  rung0={} rung1={} \
			 ratio={:.4}", dense_rows(d0), dense_rows(d1),
			dense_rows(d1) as f64 / dense_rows(d0).max(1) as f64);
	}

	/// T9906.2: score candidate rung-1 T_qm budget policies against
	/// the shipped carry. `wrap` is supplied from a MEASURED run
	/// (n_total - qm_real_cap - 1), because wrap_budget needs the
	/// live SubsigStepStore this probe deliberately does not build.
	#[test]
	fn probe_t9906_2_policy_scores() {
		let v = load_ladder(&ladder_path());
		let p = &v[0];
		install_floors(p);
		let (_cp0, sed0, _d, _ci, _si) = caps_from_params_general(p);
		let sed1 = sed0.decreased_copy(2, min_subsigs_for(false));
		let (d0, d1) = (sed0.da_capacity(), sed1.da_capacity());

		// measured, from the run under test; override per box.
		let n0 = knob("ZKR_T9906_N0", 90);
		let n1 = knob("ZKR_T9906_N1", 94);
		let w0 = n0.saturating_sub(real_cap(d0) + 1);
		let w1 = n1.saturating_sub(real_cap(d1) + 1);
		println!("DEBUG USE 69906.6: MEASURED n_total rung0={} \
			 rung1={}; implied wrap rung0={} rung1={}",
			n0, n1, w0, w1);

		// P0 shipped: carry.
		let shipped = real_cap(d1);
		// P1 dense fallback: what legacy budgets on rung 1.
		let dense = dense_rows(d1);
		// P2 legacy-ratio scale: shrink the carried budget by the
		// ratio the dense bound itself shrinks across the rungs.
		let r = dense_rows(d1) as f64
			/ dense_rows(d0).max(1) as f64;
		let scaled = ((real_cap(d0) as f64 * r).ceil() as usize)
			.max(2);
		// P3 min(carry, dense): never above either bound.
		let capped = shipped.min(dense.max(2));

		for (name, cap) in [("P0 shipped carry", shipped),
				("P1 dense fallback", dense),
				("P2 legacy-ratio scale", scaled),
				("P3 min(carry,dense)", capped)] {
			let tot = cap + w1 + 1;
			println!("DEBUG USE 69906.7: {:<24} real_cap={:>8} \
				 n_total={:>8}  vs shipped {:+.1}%", name, cap, tot,
				100.0 * (tot as f64 / (shipped + w1 + 1) as f64
					- 1.0));
		}
		println!("DEBUG USE 69906.8: wrap share of rung1 table = \
			 {:.1}%", 100.0 * w1 as f64 / n1.max(1) as f64);
	}

	fn knob(name: &str, dflt: usize) -> usize {
		std::env::var(name).ok().and_then(|s| s.parse().ok())
			.unwrap_or(dflt)
	}
}
