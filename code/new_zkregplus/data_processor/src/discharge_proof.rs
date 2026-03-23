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
