/// Hexidecimal AC-DFA.
/// This is an adaptor of the aho-crasick package of DFA version
/// with the restriction that the alphabet is 4-bit nibble set (16 elements)
/* Created 01/23/2024
 	Revised: 06/08/2024. Added serde serialization
 	Revised: 06/10/2024. Added handling of case-insensitivity
	Refactored: 07/24/2024
*/

extern crate aho_corasick;
extern crate serde;
use rayon::iter::{IntoParallelRefIterator,ParallelIterator,IntoParallelIterator};
use std::collections::{HashMap,HashSet};
use aho_corasick::{
	automaton::{Automaton},dfa::DFA as ACDFA,Anchored, 
		state_id_to_usize, pattern_id_to_usize};
use serde::{Serialize, Deserialize};
use utils::{logger::{flog,log,LOG6,LOG1,log_perf}, 
	data::{hex_to_u8, hex_to_str},
	timer::Timer
};
use crate::{clam_db::{RANGE2_BIT}};


pub const DEFAULT_ACDFA_DA_BITS:usize = 2; //bits to represent id
pub const B_DEBUG:bool = false;

#[derive(Serialize, Deserialize,Clone)]
pub struct HexACDFA{
	/// DFA ID
	pub id: usize,
	/// the number of bits to represent DFA ID
	pub id_bits: usize,
	/// number of states
	pub num_states: usize,
	/// state_bits. id_bits + state_bits is the TOTAL bits for state ID
	pub state_part_bits: usize,
	/// patterns
	pub patterns: Vec<String>,
	/// outputs (from ID to pattern ID)
	pub outputs: HashMap<usize,Vec<usize>>,
	/// transitions (from ID to vector of 16 element)
	pub trans: HashMap<usize, Vec<usize>>,
	/// init state
	pub init_state: usize,
	/// number of accept states
	pub num_acc_states: usize,
	/// whether this ACDFA is for case insensitivity
	pub b_case_ignore: bool,
	/// maps from pattern to its id in patterns	
	pub pattern_to_id: HashMap<String, usize>,
	/// accept states ID for pattern
	pub pattern_to_accept_ids: Vec<Vec<usize>>,
}

impl HexACDFA{
	/// create a new HexACDFA (default case sensitive)
	pub fn new(dfa_id: usize, patterns: &Vec<String>)->HexACDFA{
		Self::new_adv(dfa_id, patterns, false)
	}

	/// We generate subsig_id combined within state_part_bits
	/// NOTE: subsig_id should be ADJUSTED value (+1).
	/// Keep it for legacy, call gen_subsig_id_worker
	pub fn gen_subsig_id(&self, sig_id: usize, subsig_id: usize)->usize{
		assert!(sig_id!=0 && subsig_id!=0);
		Self::gen_subsig_id_worker(sig_id, subsig_id)
	}

	/// We generate subsig_id combined within state_part_bits
	/// NOTE: subsig_id should be ADJUSTED value (+1).
	pub fn gen_subsig_id_worker(sig_id: usize, subsig_id: usize)->usize{
		let bits = RANGE2_BIT;
		let bit_part1 = bits*2/3; //16 for accomodating 64k sigs for bits 24
		let bit_part1 = if bits>19 {16} else {bit_part1};
		let bit_part2 = bits - bit_part1;
		assert!(sig_id < (1<<bit_part1), "sig_id: {}, bit_part1: {}", sig_id, bit_part1);
		assert!(subsig_id < (1<<bit_part2), "subsig_id: {}, bit_part2: {}", subsig_id, bit_part2);
		let res = (sig_id<<bit_part2) + subsig_id;

		res
	}

	/// convert a hex string to its lower version
	/// e.g. [6,1, 4, 1] ("aA") 
	/// is converted to [6,1,6,1] ("aa") and keep other chars
	/// the same as they are. 
	/// This is to prevent the capitical case letters in 
	/// the pattern string causes trouble for others.
	/// For instance, if the system processes "Ab" first, it will
	///    redirect transitions for "a".
	/// But then if the system processes "ac" next, it will redirect
	///    "A" agagin, which causes incorrect translation when future
	/// patterns depend on "A" and "a".
	pub fn to_v8_lower(s_src: &Vec<u8>)->Vec<u8>{
		let mut s = s_src.clone(); 
		for i in (0..s.len()).step_by(2){
			let ch1 = s[i];
			if i+1>=s.len() {break;}
			let ch2 = s[i+1];
			let val = ch1*16 + ch2;
			if val>=0x41 && val<=0x5a{
				let newval = val-0x41 + 0x61;
				let newch1 = newval/16;
				let newch2 = newval%16;
				s[i] = newch1;
				s[i+1] = newch2;
			} 
		}

		s
	}

	pub fn new_adv(dfa_id: usize, patterns: &Vec<String>, b_case_ignore: bool)->HexACDFA{
		let b_old = false; //old means use old algorithm (for comparison only)
		if b_old{
			Self::new_adv_old(dfa_id, patterns, b_case_ignore)
		}else{
			if b_case_ignore{
				//only new works for igc but slower.
				Self::new_adv_new(dfa_id, patterns, b_case_ignore)
			}else{//for case sensitive use the old alg which is correct
				//also the old version is better at handling odd number
				//of chars
				Self::new_adv_old(dfa_id, patterns, b_case_ignore)
			}
		}
	}

	/// create a new HexACDFA
	/// We pack the patterns into alphabet 256 (every two hex nibbles into
	/// one char). We process the IGNORE CASE handling at the regular
	/// char level (2-hex nibbles). Then we convert this ACDFA into one
	/// one 16-hex nibble charset. This allows safe handling of
	/// ignore case.
	///
	/// Assumption: patterns have even len (hex_nibbles)
	pub fn new_adv_new(dfa_id: usize, patterns: &Vec<String>, b_case_ignore: bool)->HexACDFA{
		let b_debug = false;
		let log_level = LOG6;
		assert!(b_case_ignore, concat!("This function for ignore case only. ",
			"Running time is slow for case sensitive DFA,",
			" which is much larger. ",
			" Call the new_adv_old for case sensitive instead")
		);

		//0. process patterns for ACDFA ignore case
		if b_debug{
			println!(concat!(
				"DEBUG USE 6200: HexACDFA::new_adv b_igc: {}, ",
				"patterns: {:#?}"), 
				b_case_ignore, patterns
			);
		}
		for pat in patterns{ 
			if pat.len()%2==1{ println!("WARN: pattern len is odd: {}", pat); }
		}
		let new_patterns = patterns.iter().map(|s| hex_to_str(s))
			.collect::<Vec<String>>();
		let pats_in_bytes:Vec<Vec<u8>> = new_patterns.iter().map(|s| 
			s.clone().into_bytes()).collect();

		//1. build the ACDFA (ignore case) version
		assert!(dfa_id<(1<<DEFAULT_ACDFA_DA_BITS));
		let dfa = ACDFA::builder()
			.ascii_case_insensitive(true).
			build(&pats_in_bytes).unwrap();
		if b_case_ignore{
			if b_debug{
				println!("PERFORMANCE 2000.1: constructed raw ACDFA states: {}, trans: {}", dfa.num_states(), dfa.trans.len());
			}
		}

		//2. for each existing state in dfa: compute the list of intermediate
		//state info: note that they are not numbered yet. 
		//each state has a vector of 16 elements leading to destination states
		// NOTE: dfa_outputs matches the final state [0, acc_states-1]
		// in the AFTER MAPPED processing. So, state 2 now becomes 0, etc.
		//2.1 collect the basic stats
		let alpha_size = dfa.alphabet_len; //number of equivalent classes
		let alpha_size2 = alpha_size.next_power_of_two();
		let alpha_size2 = if alpha_size.is_power_of_two() {alpha_size}
			else {alpha_size2};
		let num_states = dfa.num_states();
		let dfa_outputs = &dfa.matches;
		let acc_states = dfa.get_max_match_id()/alpha_size2-1;

		assert!(num_states * alpha_size2 == dfa.trans.len());
		let dfa_init = state_id_to_usize(
			dfa.start_state(Anchored::No).unwrap()
		)/alpha_size2;
		assert!(num_states<(1<<RANGE2_BIT), 
			"num_states: {}> 1<<RANGE2_BIT", num_states);

		//2.2 build the information of intermediate state for each state
		//(1) each state has a mapping from 16 chars to intermediate states
		//(2) each intermediate state has a vector of 16 transitions to the
		let dfa_trans = &dfa.trans;
		let mut vec_imm_state_info = (0..num_states).into_par_iter().map(|s|{
			// trans1[i] means for nibble i, its destination immediate state
			// (not finalized yet, just start from 0)
			let mut trans1 = vec![0usize;16];

			// vec_trans2[i] means that for intermediate state i
			// its destination state for all 16 hex-nibbles.
			// vec_trans2.len() relfects the real number of intermediate state
			let mut vec_trans2: Vec<Vec<usize>> = Vec::new();

			// map from dest_info to the immediate state id
			// so that we can avoid adding redundant intermediate state.
			let mut map:HashMap<Vec<usize>, usize> = HashMap::new();

			let idx = s * alpha_size2;
			let mut count_imm_state = 0;
			for ch1 in 0..16u8{
				let mut trans2 = vec![0usize;16];
				for ch2 in 0..16u8{
					let ch = ch1*16 + ch2;
					let equiv = dfa.byte_classes.get(ch) as usize;
					#[cfg(test)]{ assert!(equiv<alpha_size2);}
					let dest = state_id_to_usize(dfa_trans[idx+equiv])
						/alpha_size2;
					trans2[ch2 as usize] = dest;
				}
				let imm_state = if map.contains_key(&trans2){
					let id = map.get(&trans2).unwrap();
					*id
				}else{
					let new_id = count_imm_state;
					count_imm_state += 1;
					map.insert(trans2.clone(), new_id);
					vec_trans2.push(trans2);

					new_id
				};
				trans1[ch1 as usize] = imm_state;
			}
			assert!(vec_trans2.len()==count_imm_state);
			(trans1, vec_trans2)
		}).collect::<Vec<_>>();

		//2.3 now label the intermediate states
		let mut imm_start = num_states;
		for i in 0..vec_imm_state_info.len(){
			for j in 0.. vec_imm_state_info[i].0.len(){
				vec_imm_state_info[i].0[j] += imm_start;
			}
			imm_start += vec_imm_state_info[i].1.len(); //that's the actual cnt
		}
		let count_imm_states = imm_start - num_states;
		let old_num_states = num_states;
		let num_states = old_num_states + count_imm_states;

		//2.4 build a state map which maps from original ACDFA states to
		//new state. In the original ACDFA state [0,1] are NOT final
		//states, then [2, 2+acc_states) are the final states, then
		//the rest are non-accepting states
		//we map [0,1] -> [acc_states, acc_states+1]
		//		 [2, acc_states+1] -> [0, acc_states-1]
		//		 [acc_states+2, END] -> [acc_states+2, END] the same
		// NOTE: dfa_outputs matches EXACTLY the new range of accept
		// states from [0, acc_states-1]. e.g., original state 2 is mapped
		// to 0, and the dfa_outputs[0] contains all the pattern IDs that
		// are accepted at that state.
		let mut map_states = HashMap::<usize, usize>::new();
		for i in 0..num_states{
			if i<2{
				map_states.insert(i, acc_states+i);
			}else if i>=2 && i<=acc_states+1{
				map_states.insert(i, i-2);
			}else{
				map_states.insert(i, i);
			}
		}

		//2.5 compute the reachable states from init state.
		// This is used to prune transition table. Note that
		// for consecutive state sequence, UNREACHABLE states are
		// stil there (will be stored in lkup table), but all their
		// layer transitions are pruned for saving cost.
		//note that we are using vec_imm_information, this DOES NOT
		//invole mapping yet, all are raw format in the original ACDFA
		//* reachable contains [0..old_num_states], not intermediate
		let next_state = |state: usize| -> HashSet<usize>{
			let vec_trans2 = &vec_imm_state_info[state].1;
			let all_dest = vec_trans2.par_iter().map(|vec|{
				vec.iter().map(|&x| x).collect::<HashSet<usize>>()
			}).reduce(HashSet::new, |mut a,b|{
				a.extend(b);
				a
			});
			all_dest
		};
		let mut reachable = HashSet::<usize>::new();
		let mut to_add = next_state(dfa_init); 
		reachable.insert(dfa_init);
		while to_add.len()>0{
			//(a). expand from reachable set
			let next_to_add: HashSet<usize> = to_add.par_iter().map(|&state|
				next_state(state)
			).reduce(HashSet::new, |mut a,b|{
				a.extend(b);
				a
			});
			reachable.extend(to_add);

			//(b) determine if to continue or not
			to_add = next_to_add.difference(&reachable).cloned().collect();
		}

		//2.6 redefine reachable by map_states
		let reachable = reachable.iter().map(|x|{
			Self::state_id(dfa_id, map_states[x])
		}).collect::<HashSet<usize>>();

		//3. build up the transitions
		// since now one (8-bit char) transition are split into two
		// we need to dischard all transitions. For each state
		// in the ORIGINAL state set, add two layers of transitions:
		// one for intermediate and the second layer from intermediate
		// states to the next states
		// 
		// deadstate at 0 (which is now mapped to acc_state) has just
		// one layer, every transition leads back to itself
		let mut timer = Timer::new();
		let mut hash_trans = HashMap::<usize,Vec<usize>>::new();
		for raw_src in 1..old_num_states{
			let src = Self::state_id(dfa_id, map_states[&raw_src]); 
			if !reachable.contains(&src) { continue; } 
			let trans1 = &vec_imm_state_info[raw_src].0;	 
			let vec_trans2 = &vec_imm_state_info[raw_src].1;
			let mut vec_layer1 = vec![];
			let start_imm = trans1.iter().map(|&i| i).min().unwrap();
			for imm_idx in 0..trans1.len(){
				let raw_imm = trans1[imm_idx];
				let imm = Self::state_id(dfa_id, map_states[&raw_imm]);
				vec_layer1.push(imm);
				//trans1 might have dupliate entries
				//avoid duplicate work
				if !hash_trans.contains_key(&imm){
					let trans2 = &vec_trans2[raw_imm-start_imm];
					let mut vec_layer2 = vec![];
					for raw_dst in trans2{
						let dst = Self::state_id(dfa_id, map_states[&raw_dst]);
						vec_layer2.push(dst); 
					}
					hash_trans.insert(imm, vec_layer2);
				}
			}
			if hash_trans.contains_key(&src){ panic!("src: {} exists", src); }
			hash_trans.insert(src, vec_layer1);
		}
		let state0 = Self::state_id(dfa_id, map_states[&0]); //0->acc_state now
		hash_trans.insert(state0, vec![state0; 16]); //loop to dead state itself
		let total_trans = hash_trans.par_iter().map(|(_k,v)| v.len())
			.sum::<usize>();
		log_perf(log_level, 
			&format!("PERF 2001.1 build trans time for states:: {}, trans: {}",
			num_states, total_trans), &mut timer
		);

		//4. build up the outputs table
		//AS we noted earlier, dfa_outputs matches nicely the mapped 
		// accpet states.
		let mut hash_outputs = HashMap::<usize,Vec<usize>>::new();
		let mut pattern_to_accept_ids = vec![vec![]; patterns.len()]; 
		for i in 0..acc_states{
			let state_id = Self::state_id(dfa_id, i);
			let mut vec = vec![];
			for pat_id in &dfa_outputs[i]{
				vec.push( pattern_id_to_usize(*pat_id) );
				pattern_to_accept_ids[*pat_id].push(state_id);
			}
			vec.sort();
			hash_outputs.insert(state_id, vec);
		}
		let pattern_to_id = patterns.iter().enumerate().map(|(i,p)|
			(p.to_string(), i)).collect::<HashMap<String,usize>>();

		let init_state =  Self::state_id(dfa_id, map_states[&dfa_init]);
		assert!(num_states<(1<<RANGE2_BIT), "RANGE2_BITS too small, reset!");

		HexACDFA{
			id: dfa_id,
			id_bits: DEFAULT_ACDFA_DA_BITS,
			num_states: num_states,
			state_part_bits: RANGE2_BIT,
			patterns: patterns.clone(),
			num_acc_states: hash_outputs.keys().len(),
			outputs: hash_outputs,
			trans: hash_trans,
			init_state: init_state,
			b_case_ignore: b_case_ignore,
			pattern_to_id,
			pattern_to_accept_ids,
		}
	}

	/// create a new HexACDFA
	/// OLD version (not quite reliable in handling ignore case), assuming
	/// even id state number for handling chars.
	pub fn new_adv_old(dfa_id: usize, patterns: &Vec<String>, b_case_ignore: bool)->HexACDFA{
		let b_debug = false;
		if b_debug{
			println!("DEBUG USE 6200: HexACDFA::new_adv b_igc: {}, patterns: {:#?}", b_case_ignore, patterns);
		}
		//1. build the ACDFA DFA version
		assert!(dfa_id<(1<<DEFAULT_ACDFA_DA_BITS), "DEFAULT_ACDFA_DA_BITS:{} too small! id: {} >= (1<<DEFAULT_ACDFA_DA_BIS)", DEFAULT_ACDFA_DA_BITS, dfa_id);
		let vecu8 = patterns.iter().map(|s| {hex_to_u8(s)}).collect::<Vec<Vec<u8>>>();
		let vecu8 = if b_case_ignore{
				//need to convert all strings to lower case to avoid
				//confusion, see comment v8_to_lower
				vecu8.par_iter().map(|s| Self::to_v8_lower(s))
					.collect::<Vec<Vec<u8>>>() 
		}else{
			vecu8
		};
		let dfa = ACDFA::new(&vecu8).unwrap();
		let dfa_init = state_id_to_usize(dfa.start_state(Anchored::No).unwrap())/32;

		let alpha_size = dfa.alphabet_len;
		assert!(alpha_size==17, "alpha_size: {} !=17, consider providing patterns covering all 16 hex digits!", alpha_size); //implies: each state has 32 transitions
		let num_states = dfa.num_states();
		let dfa_trans = &dfa.trans;
		assert!(num_states*32==dfa_trans.len(), "states*32!=trans_len. states: {}, trans: {}", num_states, dfa_trans.len());
		let dfa_outputs = &dfa.matches;
		let acc_states = dfa.get_max_match_id()/32-1;
		assert!(acc_states==dfa_outputs.len(), "acc_states!=dfa_outputs.len()");
		assert!(num_states<(1<<RANGE2_BIT), "num_states: {}> 1<<RANGE2_BIT", num_states);

		//1.5 build a state map which maps from original ACDFA states to
		//new state. In the original ACDFA state [0,1] are NOT final
		//states, then [2, 2+acc_states) are the final states, then
		//the rest are non-accepting states
		//we map [0,1] -> [acc_states, acc_states+1]
		//		 [2, acc_states+1] -> [0, acc_states-1]
		//		 [acc_states+2, END] -> [acc_states+2, END] the same
		let mut map_states = HashMap::<usize, usize>::new();
		for i in 0..num_states{
			if i<2{
				map_states.insert(i, acc_states+i);
			}else if i>=2 && i<=acc_states+1{
				map_states.insert(i, i-2);
			}else{
				map_states.insert(i, i);
			}
		}
		//1.6 build set of reachable states from the initial state
		//later use it to prune transitions.
		let next_state = |state: usize| -> HashSet<usize>{
			let mut res = HashSet::new();
			let idx = state * 32;
			for j in 0..16{res.insert(state_id_to_usize(dfa_trans[idx+j])/32);}
			res
		};
		let mut reachable = HashSet::new();
		reachable.insert(dfa_init);
		let mut to_add = next_state(dfa_init); 
		while to_add.len()>0{
			//(a). expand from reachable set
			let next_to_add: HashSet<usize> = to_add.par_iter().map(|&state|
				next_state(state)
			).reduce(HashSet::new, |mut a,b|{
				a.extend(b);
				a
			});
			reachable.extend(to_add);

			//(b) determine if to continue or not
			to_add = next_to_add.difference(&reachable).cloned().collect();
		}
		let reachable = reachable.iter().map(|x|{
			Self::state_id(dfa_id, map_states[x])
		}).collect::<HashSet<usize>>();
		if b_debug{
			println!("DEBUG USE 6723.1: reachable: {}, num_states: {}", reachable.len(), num_states);
		}


		//2. build up the transitions
		// keep the original state (but ignore deadsstead 0, and ignore
		// all other alphabet char other than 16
		let mut hash_trans = HashMap::<usize,Vec<usize>>::new();
		for i in 1..num_states{
			let idx = i * 32;
			let mut vec = vec![];
			let new_state = Self::state_id(dfa_id, map_states[&i]);
			if reachable.contains(&new_state){
				//process the reachable state only!
				for j in 0..16{
					let dst = state_id_to_usize(dfa_trans[idx+j])/32;
					let new_dst = Self::state_id(dfa_id, map_states[&dst]);
					vec.push(new_dst);
				}
				if hash_trans.contains_key(&new_state){
					panic!("ERROR already hash state: {} for i: {}", new_state, i);
				}
				hash_trans.insert(new_state, vec);
			}
		}
		let state0 = Self::state_id(dfa_id, map_states[&0]);
		hash_trans.insert(state0, vec![state0; 16]); //loop to dead state itself

		//3. if b-ignore case update the transition table
		//assumption: each alpha_numeric char is located at EVEN pos!
		//NOTE - the followig code are incorrect. 
		//In production mode, this part will not be reached
		//in new_adv(..) set the b_old to FALSE! to avoid enter this chunk.
		let init_state =  Self::state_id(dfa_id, map_states[&dfa_init]);
		if b_case_ignore{
			for s in &vecu8{
				let mut cur_state = init_state;
				for i in (0..s.len()).step_by(2){
					let ch1 = s[i];
					let next_state = hash_trans.get(&cur_state)
						.unwrap()[usize::from(ch1)];
					if i+1>=s.len() {break;}
					let ch2 = s[i+1];
					let next_state2 = hash_trans.get(&next_state)
						.unwrap()[usize::from(ch2)];
					let val = ch1*16 + ch2;
					if (val>=0x41 && val<=0x5a) || (val>=0x61 && val<=0x7a){
						let newval = if val>=0x41 && val<=0x5a 
							{(val - 0x41) + 0x61} else {(val-0x61) + 0x41};
						let newch1 = newval/16;
						let newch2 = newval%16;
						hash_trans.entry(cur_state).and_modify(|v| v[usize::from(newch1)] = next_state);
						hash_trans.entry(next_state).and_modify(|v| v[usize::from(newch2)] = next_state2);
					} 
					cur_state = next_state2;
				}
			}
		}


		//3. build up the outputs table
		let mut hash_outputs = HashMap::<usize,Vec<usize>>::new();
		let mut pattern_to_accept_ids = vec![vec![]; patterns.len()]; 
		for i in 0..acc_states{
			let state_id = Self::state_id(dfa_id, i);
			let mut vec = vec![];
			for pat_id in &dfa_outputs[i]{
				vec.push( pattern_id_to_usize(*pat_id) );
				pattern_to_accept_ids[*pat_id].push(state_id);
			}
			vec.sort();
			hash_outputs.insert(state_id, vec);
		}

		//4. build the pattern to IDs
		let pattern_to_id = patterns.iter().enumerate().map(|(i,p)|
			(p.to_string(), i)).collect::<HashMap<String,usize>>();
		assert!(num_states<(1<<RANGE2_BIT), "RANGE2_BITS too small, reset!");

		//4. return
		HexACDFA{
			id: dfa_id,
			id_bits: DEFAULT_ACDFA_DA_BITS,
			num_states: num_states,
			state_part_bits: RANGE2_BIT,
			patterns: patterns.clone(),
			num_acc_states: hash_outputs.keys().len(),
			outputs: hash_outputs,
			trans: hash_trans,
			init_state: init_state,
			b_case_ignore: b_case_ignore,
			pattern_to_id,
			pattern_to_accept_ids,
		}

	}

	/// if word is accepted by the DFA, return the corresponding IDs.
	/// if word is not an accepted word, panic
	pub fn word_to_state_id(&self, w: &String)->Vec<usize>{
		let pat_id: usize = *self.pattern_to_id.get(w).expect(
			&format!("canot find word: {}", w));
		self.pattern_to_accept_ids[pat_id].to_vec()
	}

	/// print stats
	pub fn log_stats(&self, prefix: &str, vlog: &mut Vec<String>){
		flog(LOG1, &format!("==== Status of ACDFA {} =====\n HEX-AC-DFA id: {}, num_states: {}, patterns: {}, accept_states: {}, init_state: {}", prefix, self.id, self.num_states, self.patterns.len(), self.outputs.keys().len(), self.init_state), vlog);
		let mut max_output_size = 0;
		let mut total_output_size = 0;
		for i in 0..self.num_acc_states{
			let state_id = Self::state_id(self.id, i);
			let ilen = self.outputs.get(&state_id).unwrap().len();
			if ilen>max_output_size{max_output_size = ilen;}
			total_output_size += ilen;
		}
		flog(LOG1, &format!("MAX output words for a final state: {}, avg: {}", 
			max_output_size, total_output_size/self.num_acc_states), vlog);
	}

	/// return a hashset, which given a critical pattern map (to sigs),
	/// return for each state, a vector of signatures that are triggered. 
	pub fn state_to_sig_ids(&self, map_crit_pat: &HashMap<String,Vec<String>>, sig_to_id: &HashMap<String,usize>) -> HashMap<usize, Vec<usize>>{
		(0..self.num_acc_states).map(|x| {
			let sid = self.long_state_id(x);
			let vout = self.outputs.get(&x)
				.expect(&format!("Unable to get pattern for state: {}", x));
			let mut set_sigs = HashSet::<String>::new();
			for pat_id in vout{
				let pat = &self.patterns[*pat_id];
				let sigs = map_crit_pat.get(pat).expect(
					&format!("Unable to get {} from map_crit_pat", pat));
				for sig in sigs {set_sigs.insert(sig.clone());}
			}
			let mut v_sigid= set_sigs.iter()
				.map(|s| *sig_to_id.get(s).expect(
					&format!("Unable to find id for {}", s)))
				.collect::<Vec<usize>>();
			v_sigid.sort();
			(sid, v_sigid)
		}).collect::<HashMap::<usize, Vec<usize>>>()
	}

	/// print stats
	pub fn log_stats_adv(&self, prefix: &str, map_crit_pat: &HashMap<String,Vec<String>>, sig_to_id: &HashMap<String, usize>, vlog: &mut Vec<String>){
		flog(LOG1, &format!("==========Adv Stats of ACDFA {} ==========================", prefix), vlog);
		flog(LOG1, &format!("HEX-AC-DFA id: {}, num_states: {}, patterns: {}, accept_states: {}, init_state: {}", self.id, self.num_states, self.patterns.len(), self.outputs.keys().len(), self.init_state), vlog);
		let mut max_output_size = 0;
		let mut total_output_size = 0;
		let states_to_sigs = self.state_to_sig_ids(map_crit_pat, sig_to_id);
		for i in 0..states_to_sigs.len(){
			let vec = states_to_sigs.get(&self.long_state_id(i)).expect(
				&format!("can't get output vec for state: {}", i)).to_vec();
			total_output_size += vec.len();
			max_output_size = if max_output_size>vec.len() {max_output_size}
				else {vec.len()};
		}
		flog(LOG1, &format!("  MAX output sig: {}, avg sigs/acc state: {}", max_output_size, total_output_size/states_to_sigs.len()), vlog);
		flog(LOG1, &format!("=================================="), vlog);
	}

	/// generate the acceptance path for a vector of nibbles
	/// return the vector of state IDs
	pub fn acc_path(&self, s: &Vec<u8>)->Vec<usize>{
		let mut src = self.init_state;
		let mut dst;
		let mut vec = vec![];
		vec.push(src);
		for i in 0..s.len(){
			let ch = s[i];
			dst = self.trans.get(&src).unwrap()[usize::from(ch)];
			if B_DEBUG{
				if self.is_accept(dst){
					log(LOG1, &format!("{} - {} -> {}: {:?}", src, ch, dst, &self.outputs.get(&dst).unwrap()));
				}else{
					log(LOG1, &format!("{} -{} -> {}", src, ch, dst));
				}
			}
			vec.push(dst);
			src = dst;
		}

		vec
	}

	/// each element of return is a tuple of (state_id, step_id)
	pub fn packed_acc_path(&self, s: &Vec<u8>)->Vec<(usize, usize)>{
		let path = self.acc_path(s);
		let mut res = vec![];
		for id in 0..path.len(){
			let state = path[id];
			if self.is_accept(state){
				res.push( (state, id) );
			}
		}
		res
	}

	/// return whether state_idx is a final state
	pub fn is_final(&self, state_idx: usize)-> bool{
		state_idx < self.num_acc_states
	}
	/// given the final state indiex, return the related 
	/// signature names
	pub fn final_to_patterns(&self, final_state_idx: usize)->HashSet<String>{
		assert!(self.is_accept(final_state_idx));
		let vec = &self.outputs[&final_state_idx];
		let mut res = HashSet::<String>::new();
		for id_pat in vec{
			res.insert( self.patterns[*id_pat].clone() );
		}
		res
	}

	/// from the acceptance path, collects the set of patterns
	pub fn get_patterns(&self, acc_path: &Vec<usize>)->HashSet<String>{
		let mut res = HashSet::<String>::new();
		for state in acc_path{
			if self.is_accept(*state){
				let vec = &self.outputs[&state];
				for id_pat in vec{
					res.insert( self.patterns[*id_pat].clone() );
				}
			}
		}

		res
	}

	/// for each string show the vector of positions
	pub fn get_pattern_pos(&self, acc_path: &Vec<usize>)->HashMap<String,Vec<usize>>{
		let mut res = HashMap::<String, Vec<usize>>::new();
		for (i, state) in acc_path.iter().enumerate(){
			if self.is_accept(*state){
				let vec = &self.outputs[&state];
				if vec.len()>10 {println!("WARN: vec.len: {} for state: {:?}", vec.len(), state);}
				for id_pat in vec{
					let pat = self.patterns[*id_pat].clone();
					let entry = res.entry(pat).or_insert_with(|| vec![]);
					entry.push(i);
				}
			}
		}
		res

	}

	/// from the acceptance path, collects the stats of patterns
	pub fn get_pattern_stats(&self, acc_path: &Vec<usize>)->HashMap<String, usize>{
		let mut res = HashMap::<String, usize>::new();
		for state in acc_path{
			if self.is_accept(*state){
				let vec = &self.outputs[&state];
				for id_pat in vec{
					let pat = self.patterns[*id_pat].clone();
					let entry = res.entry(pat).or_insert_with(|| 0);
					*entry += 1;
				}
			}
		}

		res
	}


	/// get the state id given dfa_id
	fn state_id(_dfa_id: usize, state_id: usize)->usize{
		let dfa_id = 0; //Since lookup table is 2D in proof, we do not build it
						//in state any more.
		(dfa_id<<RANGE2_BIT) + state_id
	}

	/// get the LONG VERSION of state id given dfa_id
	fn long_state_id(&self, state_id: usize)->usize{
		(self.id <<RANGE2_BIT) + state_id
	}

	/// map from state id to index in transition
	#[inline]
	pub fn state_to_idx(&self, state_id: usize) -> usize{
		//we do not embed dfaid into state id anymore
		state_id 
	}

	/// check if it is accept state
	#[inline]
	pub fn is_accept(&self, state_idx: usize) -> bool{
		// from state [2, 2+num_accept_states-1]
		// self.state_to_idx(state_idx) <= self.num_acc_states+1
		// from state [0, 0+num_accept_states-1]
		self.state_to_idx(state_idx) <= self.num_acc_states-1
	}
}

#[cfg(test)]
mod tests_hex_acdfa{
	use crate::hex_acdfa::*;
	use std::collections::{HashSet};
	use utils::data::{str_to_u8};

	// test if s generates the expected pattern set
	// bval means the expected value whether the patterns collected
	//  along the accept path matches the provided "exp" set. 
	fn test_one_case(pats: &Vec<&str>, exp: &Vec<&str>, s: &str, bval: bool){
		let patterns = pats.into_iter().map(|s| {String::from(*s)}).collect();
		let dfa = HexACDFA::new(1, &patterns);
		let exp_set = exp.into_iter().map(|s| {String::from(*s)}).collect::<HashSet<String>>();
		let vu8 = hex_to_u8(&s);
		let set1 = dfa.get_patterns( &dfa.acc_path(&vu8) );
		assert!((set1==exp_set)==bval, "failed on s: {}", s);
	}

	#[test]
	fn test_word_to_accept_id(){
		let pats = vec!["0123456789abcdef1", "123", "abc", "345"].iter().
			map(|s| s.to_string()).collect::<Vec<String>>();
		let dfa = HexACDFA::new(1, &pats);
		for w in pats{
			let final_states = dfa.word_to_state_id(&w);
			for f in &final_states{
				let vec_word = dfa.outputs.get(&f).unwrap();
				let wid = dfa.pattern_to_id.get(&w).unwrap();
				let word2 = &dfa.patterns[*wid];
				assert!(vec_word.contains(wid), "vec_word: {:#?} not containing: {}", vec_word, wid);
				assert!(word2==&w, "word2: {} != w: {}", word2, w);
			}
		}
	}

	#[test]
	fn test_v8_lower(){
		let samples = ["123ABC", "A4a5678"];
		for sample in samples{
			let s2 = sample.to_lowercase();
			let v8_1 = str_to_u8(&sample);
			let v8_2 = str_to_u8(&s2);
			let act_val = HexACDFA::to_v8_lower(&v8_1);
			assert!(act_val == v8_2);
		}
	}

	#[test]
	fn test_state_id(){
		//1. build up the acdfa and state_to_sigid
		let patterns = vec!["abc", "dabc", "cde", "1234567890abefdcaa"]
			.iter().map(|s|
			{String::from(*s)}).collect();
		let dfa = HexACDFA::new(1, &patterns);
		let mut map_crit_pat = HashMap::<String, Vec<String>>::new();
		map_crit_pat.insert(String::from("abc"), vec![
			String::from("sig1")]);
		map_crit_pat.insert(String::from("cde"), vec![
			String::from("sig0"),
			String::from("sig2")]);
		map_crit_pat.insert(String::from("dabc"), vec![
			String::from("sig0"),
			]);
		map_crit_pat.insert(String::from("1234567890abefdcaa"), vec![
			String::from("sig2"),
			]);
		let mut sig_to_id = HashMap::<String,usize>::new();
		sig_to_id.insert(String::from("sig0"), 0);
		sig_to_id.insert(String::from("sig1"), 1);
		sig_to_id.insert(String::from("sig2"), 2);
		sig_to_id.insert(String::from("sig3"), 3);
		let states_to_id = dfa.state_to_sig_ids(&map_crit_pat, &sig_to_id);
		let mut vlog = vec![];
		dfa.log_stats_adv("ACDFA", &map_crit_pat, &sig_to_id, &mut vlog);

		//2. test
		let arr_cases = vec![
			//test string and then expected sig ids
			("eabc", vec![1]),
			("edabc", vec![0, 1]),
			("aa1234567890abefdcaa", vec![2]),

		];
		for tc in arr_cases{
			let s = tc.0;
			let sigs = tc.1;
			let acc_path = dfa.acc_path(&hex_to_u8(&s));
			let acc_state = dfa.long_state_id(acc_path[acc_path.len()-1]);
			let act_sigs = states_to_id.get(&acc_state).unwrap().clone();
			assert!(sigs==act_sigs, "ERROR for s: {}, expected sigs: {:?}, actual: {:?}", s, sigs, act_sigs);
		}
		println!("DUMP states_to_id: {:?}", states_to_id);
	}

	// test if s generates the expected pattern set, ignore case
	fn test_one_case_ig(pats: &Vec<&str>, exp: &Vec<&str>, s: &str, bval: bool){
		let patterns = pats.into_iter().map(|s| {String::from(*s)}).collect();
		let dfa = HexACDFA::new_adv(1, &patterns, true);
		let exp_set = exp.into_iter().map(|s| {String::from(*s)}).collect::<HashSet<String>>();
		let vu8 = hex_to_u8(&s);
		let set1 = dfa.get_patterns( &dfa.acc_path(&vu8) );
		assert!((set1==exp_set)==bval, "failed on s: {}. set1: {:#?}, exp_set: {:#?}", s, set1, exp_set);
	}

	#[test]
	fn test_simple_hex_dfa1(){
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012356", false);
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012346", true);
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012a123a123a6", false);
		test_one_case(&vec!["0123456789abcdef1", "123", "1234", "345"],
			&vec!["123", "1234"], "012a123a12346", true);
		test_one_case(&vec!["0123456789abcdef1", "6162", "6263", "6364"],
			&vec!["6162", "6263", "6364"], "aa61626364bb", true);
		test_one_case(&vec!["0123456789abcdef1", "6162", "6263", "6364"],
			&vec!["6364"], "aa61426364bb", true);
		test_one_case(&vec!["0123456789abcdef1", "616263", "6263"],
			&vec!["616263", "6263"], "aa61626364bb", true);
		test_one_case(&vec!["0123456789abcdef1", "616263", "6263"],
			&vec!["6263"], "aa62626364bb", true);
		test_one_case(&vec!["0123456789abcdef1", "616263", "6263"],
			&vec!["6263"], "aa41626364bb", true);
		test_one_case(&vec!["0123456789abcdef1", "616263", "6263"],
			&vec![], "aa41624364bb", true);
	}

	#[test]
	fn test_simple_hex_dfa_ignore_case(){
		//A - 0x41
		//a - 0x61
		//2nd entry is actually 'AbC'
		test_one_case_ig(&vec!["01234567789abcdefa", "416243", "1235", "3451"],
			&vec!["416243", "3451"], "6162633451", true);
		test_one_case_ig(&vec!["01234567789abcdefa", "416243", "1235", "3451"],
			&vec!["416243", "3451"], "5162633451", false);
		test_one_case_ig(&vec!["01234567789abcdefa", "416243", "1235", "3451"],
			&vec!["416243", "3451"], "6142433451", true);
		test_one_case_ig(&vec!["01234567789abcdefa", "3031416243", "1235", "3451"],
			&vec!["3031416243", "3451"], "112230316142433451", true);
		test_one_case_ig(&vec!["01234567789abcdefa", "3031416243", "1235", "3451"], &vec!["3031416243", "3451"], "112230311142433451", false);
		test_one_case_ig(&vec!["01234567789abcdefa", "3031416243", "1235", "3451"], &vec!["3031416243", "3451"], "112230316242433451", false);
		test_one_case_ig(&vec!["3031416243", "30414362", "3451"], 
			&vec!["3031416243", "3451"], "3331414342443451", false);
		test_one_case_ig(&vec!["3031416243", "30414362", "3451"], 
			&vec!["3031416243", "3451"], "303161424344345177", true);
		test_one_case_ig(&vec!["3031416243", "30414362", "3451"], 
			&vec!["3451"], "a2303162424344345177", true);
		test_one_case_ig(&vec!["3031416243", "30414362", "3451"], 
			&vec!["3031416243" ], "303161424344345277", true);
		test_one_case_ig(&vec!["3031416243", "30414362", "3451"], 
			&vec!["3031416243", "30414362", "3451"], 
			"aa303161424344345177bb30416342aa3452", true);
		test_one_case_ig(&vec!["6162", "6263", "6364"], &vec!["6162"], 
			"41414162646264aa", true);
		test_one_case_ig(&vec!["6162", "6263", "6364"], &vec!["6162", "6263"], 
			"41414162636363aa", true);
		test_one_case_ig(&vec!["6162", "6263", "6364"], &vec!["6162", "6364"], 
			"41414142646344aa", true);
		test_one_case_ig(&vec!["6162", "6263", "6364"], &vec!["6162", "6263"], 
			"41614142424363aa", true);
		test_one_case_ig(&vec!["616263", "6263", "6364"], 
			&vec!["616263", "6263"], 
			"41624342424363aa", true);
		test_one_case_ig(&vec!["616263", "6263", "6364"], 
			&vec!["6263"], 
			"4143624351424363aa", true);
		test_one_case_ig(&vec!["6162", "6263", "6364"], 
			&vec!["6162", "6263", "6364"], 
			"4141624364424363aa", true);
		test_one_case_ig(&vec!["6162", "6263", "6364"], 
			&vec!["6263"], 
			"4143624351424363aa", true);
	}

	#[test]
	fn debug_hex_dfa(){
		//A - 0x41
		//a - 0x61
		//2nd entry is actually 'AbC'
		test_one_case_ig(&vec!["61"], &vec!["61"], "626163", true);
	}

}
