/// This modules contains the discharge proof (for the 5-stage) scheme
/* 
	Created 07/25/2024
*/

use std::collections::HashSet;

/// record of discharges (e.g., the approach
/// failed to discharge the string, that is the string
/// is regarded to approximate match using the approach.
/// usually it's regarded as false positive (that is
/// a file which is actually NOT a match of sig patter, but is
/// reported as Maybe or Yes by the approximation approach 
/// (pm-reg, bag, critical patterns).
/// NOTE the name is misleading: if discharged, it also has
/// the record.
#[derive(Clone,Debug)]
pub struct FailDischargeRecord{
	pub fname: String,
	pub flen: usize,
	pub crit: HashSet<String>, //sigs NOT discharged by crit pattern
	pub bag: HashSet<String>, //sigs NOT discharged by bag approach
	pub pm: HashSet<String>, //sigs NOT discharged by PM approach
	pub all_dfa: HashSet<String>, //after applying DFA to what is left of 3 approaches
	pub total_unique_states: usize,//the number of total unique states
									//along the path
	pub total_acc_path_len: usize, //the sum of all acc path len
	pub total_hs_size: usize, //the size of the hash map for accepted strings
								//this is the total number of accepted strings
	pub total_accepted: usize, //the number of accepted states along acc path 
				//this is the TOTAL number of accepted states
				//regardless of the FILTER results after CP approach(
				//it includes ALL states from ALL sigs) along
				//PM approach DFAacceptance path.
	pub total_pm_witness_len: usize, //total witness len for pm-reg
				//this is more realistic
	pub ind_pm_reg: HashSet<String>, //the set sigs cannot be discharged by INDIVIDUAL pm-reg
	pub most_freq_sed_cs_pats: Option<HashSet<String>>, //only
		//available for those accept states ratio >10%
		//these are most frequent patterns
		//context sensitve only as igc is usually must lower

	pub seg_size: usize, //the seg_size for the following analysis
	pub max_seg_acc_rate: f32, //the max ratio of accept rate in a segment
	pub max_seg_pat_rate: f32, //the max ratio of pat ratio in a segment
	pub most_freq_seg_cs_pats: Option<Vec<(String,f32,f32)>>,// optiona,
		//the set of frequent pattersn using segment eval approach
		//and the corresponding acc_rate and pat_rate

	pub chunk_peaks: ChunkPeaks, //per-chunk-max circuit-sizing peaks
		//(chunk = seg_word_len*62 nibbles). Feeds estimate_config().
}

/// Per-file circuit-sizing peaks. Each metric is computed PER CHUNK
/// (one chunk = seg_word_len*62 nibbles, matching the ZK word chunk)
/// and the MAX over all chunks of the file is kept (cs + igc summed,
/// consistent with total_unique_states / total_accepted). The circuit
/// must hold the worst chunk, so the per-chunk MAX is the right basis.
/// estimate_config() aggregates these across files into a percentile-
/// coverage capacity ladder.
#[derive(Clone,Debug,Default)]
pub struct ChunkPeaks{
	pub seg_size: usize, //nibbles per chunk (= seg_word_len*62)
	pub max_unique_states: usize, //distinct DFA states in a chunk
	pub max_acc_states: usize, //accepted-state count in a chunk
	pub max_pats_in_trace: usize, //sum of freq*#patterns in a chunk
	pub perc_pats_expansion_rate: usize, //100*avg #chunks a pattern
		//spans (>=100; 100 = every pattern lives in one chunk only)
	//AGGRESSIVE M5 (b_aggressive_sde_for_rep only; 0 otherwise). Max over
	//chunks of the per-chunk NEEDS count = universe subsigs whose keyword
	//anchor is present that chunk. Sizes aggr_needs_subsigs (forward step
	//queue). 0 when flag-off so non-aggressive estimate is unchanged.
	pub max_needs_subsigs: usize,
	//Chunk index (0-based) achieving max_needs_subsigs. Lets the cap
	//tuner slice a giant file down to its densest chunk window when
	//probing (aggressive resets per chunk, so one chunk's demand is
	//self-contained). 0 when flag-off / single-chunk.
	pub max_needs_chunk_idx: usize,
	//Per-chunk NEEDS array (full profile; max() == max_needs_subsigs).
	//Empty when flag-off; populated only under b_aggressive_sde_for_rep
	//for the needs-distribution study.
	pub needs_per_chunk: Vec<usize>,
	//SED forward-propagation peaks (measured; 0 when not discharged).
	//Per-chunk count of forward-proof (subsig,step,loc) entries summed
	//across survivor subsigs, max over chunks. Sizes StepFwdPrf.
	pub max_fwd_entries_per_chunk: usize,
	//Per-chunk carried live-location count summed across subsigs, max
	//over chunks. Sizes the carried StepQueue (general-mode carry).
	pub max_carried_live_per_chunk: usize,
	//Per-chunk total active pattern-steps (non-empty loc set) summed
	//across subsigs, max over chunks. Estimator divides by subsigs to
	//size avg_active_pats_per_subsig.
	pub max_active_steps_per_chunk: usize,
	//Distinct crit-pattern DFA states per chunk (max over chunks, cs/igc
	//max) -> sizes cp_basis_unique_states (CP pack imm_buf). 0 unless
	//b_estimate_caps, so non-aggressive discharge is byte-identical.
	pub max_cp_unique_states: usize,
	//M11: per-chunk profiles (not just the max) for the capacity-ladder DP.
	//Aggressive estimator pass only; empty otherwise. 1-1 with needs_per_chunk
	//by chunk index. fwd sizes perc, active sizes avg_active, live sizes the
	//carried StepQueue (perc_q).
	pub fwd_entries_per_chunk: Vec<usize>,
	pub active_steps_per_chunk: Vec<usize>,
	pub carried_live_per_chunk: Vec<usize>,
	//Aggressive estimator pass only; empty otherwise. 1-1 with needs_per_chunk
	//by chunk index. Per-chunk FSM/CP structural demand so the rung ladder can
	//size basis caps per rung instead of cloning P_max's global max.
	pub unique_acc_pats_per_chunk: Vec<usize>,
	pub acc_states_per_chunk: Vec<usize>,
	pub pats_in_trace_per_chunk: Vec<usize>,
	pub cp_unique_states_per_chunk: Vec<usize>,
	//PROBE (ZKR_DIGIT_PROBE only; empty otherwise): hypothetical
	//digit-anchored NEEDS per chunk -- same get_needs_per_chunk count
	//but anchored on the OPPOSITE-end pm token (where a fanned digit
	//sits) instead of the keyword. Lets us compare keyword vs digit
	//anchoring without changing any functional path. Measurement only.
	pub digit_needs_per_chunk: Vec<usize>,
}

impl FailDischargeRecord{
	pub fn is_fail(&self)->bool{
		self.all_dfa.len()>0
	}
}

/// The configuration of prover (all numbers are power of 2)
#[derive(Clone,Debug)]
pub struct DischargeByCPConfig{
	/// size of transitions
	pub size_trans: usize,
	/// size of acc_states
	pub size_acc_states: usize,
	/// size of left
	pub size_left_sigid: usize
}

/// DischareProof for the Critical Section Proof
#[derive(Clone,Debug)]
pub struct DischargeProofByCP{
	/// trace of AC-DFA (fixed to power of 2), tuple structure:
	/// (src, ch, dst, is_final, proof_final).
	/// proof_final is computed as: 
	/// is_final*(max_final_state)  + (1-final)*(max_final_state - dst)
	/// src, dst in range proof for states.
	/// ch in range proof of 4 bits.
	/// is_final is a boolean.
	/// proof_final is in range proof of states.
	pub trans: Vec<(usize, usize, usize, usize)>, 
	/// vector of (set of acc states). The prover's interest is to minimize
	/// it as a standard set, however, duplicates are allowed and we
	/// do not spend extra to prove its elements are unique.
	pub vec_acc_states: Vec<usize>,
	/// set of signatures IDs that are left over
	pub vec_left_sigid: Vec<usize>,
}

/// The configuration of discharge prover (mainly deciding
/// the circuit size via several parameter setting)
pub struct DischargeConfig{
	/// configuration for CP approach
	pub config_cp: DischargeByCPConfig,
	/// configuration for CP approach (ignore case)
	pub config_cp_igc: DischargeByCPConfig,
}

/// The discharge proof for a file
#[derive(Clone,Debug)]
pub struct DischargeProof{
	/// the name of the file
	pub fname: String,
	/// the length of the file 
	pub flen: usize,
	/// the discharge proof using critical patterns 
	pub cp_proof: DischargeProofByCP,
	/// the discharge proof using critical patterns for ignore case
	pub cp_proof_igc: DischargeProofByCP,
}
