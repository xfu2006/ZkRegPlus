/// This module models a collection of clamav signatures. Its load
/// function builds up the ACDFA and related data structures. The load
/// also allow fast load from cache

/* Created: 07/25/2024. Adapted from old driver.rs file in data_proc
	Modified: 04/07/2025. Added store_subsig_to_state
*/

extern crate rayon;
extern crate serde_json;
extern crate aho_corasick;
extern crate rustomaton;
extern crate utils;

use self::rayon::prelude::*;
//use ark_ff::{BigInteger};
use ark_ff::{PrimeField};
//use hex;
use std::{collections::{HashMap,HashSet}};
use std::sync::{Arc};
use std::fmt;
use crate::{
	strings::{is_match,extract_nums,find_only},
	hex_acdfa::{HexACDFA},
	type_def::{ClamavSig,ClamavApproxConfig,ClamSigType,SubsigPatternStore, SubsigPatternStoreItem,SubsigStepStore, SubsigStepStoreItem, BundleSubsigStore, SubSigType,SubsigInfoStore, SubsigInfoStoreItem,CompOp,TriVal,TriOp},
	clamav::{gen_clamav_sig,default_clamav_cfg},
	fsa_utils::{build_trap_dfa},
};
use rustomaton::dfa::DFA;
use utils::{
	os::{read_lines,create_new_cache_dir,write_to_file,proj_root,read,write_sigs_to_dir,file_exists},
	timer::{Timer},
	logger::{flog,flog_perf,LOG2,LOG1},
	consts::{read_global_config, B_DEBUG},
};
use folding_schemes::{
	Error,
	folding::foldpot::sigma_ir1cs::{LookupTableTwoCol_Inst}
};

/// Table Ids - actual col1 of the 2-column lookup table.
/// NOTE: for each (AC)DFA, it has four sub-tables: non_final_states,
/// final_states, transitions. They MUST BE consecutive numbers, for
/// convninence of implementation in building ClamDB LookupTable.
/// Each should be defined as a POSITIVE i32 number (which is later
/// converted to u32).
#[allow(non_camel_case_types)]
/// number of bits allocated for state in generating transition
/// setting to 24 allows 16 million states at most. This leads to
/// transition: 24 * 2 + 4 = 50 bits.
pub const STATE_BIT:usize =  24;

/// The bit-width of RANGE2 table 
/// IN PRODUCTION NEEDS TO CHANGE THE SAME SIZE OF STATE_BIT

// the following are trival related sub-table ids
// they are located at the very beginning of the entire lkup
pub const TRI_VAL:u32 = 0x20000001;
pub const TRI_OP:u32 = 0x20000002;
pub const TRI_TRUTH_TBL:u32 = 0x20000003;

// the following are sub-table ids
pub const CHAR:u32 = 0x70000001;
pub const RANGE2:u32 = 0x70000002;
pub const CHAR_MAP:u32 = 0x7000A001; //used for 16-element translation table
									 //from [0,...F] -> ['0', ..., 'F']

pub const CRIT_INIT:u32 = 0x10000001;
pub const CRIT_NON_FINAL:u32 = 0x10000002;
pub const CRIT_FINAL:u32 = 0x10000003;
pub const CRIT_TRANSITIONS:u32 = 0x10000004;
pub const CRIT_STATE_2_SIG:u32 = 0x10000005;
pub const CRIT_STATE_SIG_COUNT:u32 = 0x10000006;
pub const CRIT_STATES:u32 = 0x10000007;

pub const CRIT_IGC_INIT:u32 = 0x10000101;
pub const CRIT_IGC_NON_FINAL:u32 = 0x10000102;
pub const CRIT_IGC_FINAL:u32 = 0x10000103;
pub const CRIT_IGC_TRANSITIONS:u32 = 0x10000104;
pub const CRIT_IGC_STATE_2_SIG:u32 = 0x10000105;
pub const CRIT_IGC_STATE_SIG_COUNT:u32 = 0x10000106;
pub const CRIT_IGC_STATES:u32 = 0x10000107;

// offset definitino for each acdfa in lkup.
pub const INIT:u32= 0;
pub const NON_FINAL:u32=1;
pub const FINAL:u32=3;
pub const TRANSITIONS:u32=4;
pub const STATE_2_SIG:u32=5;
pub const STATE_SIG_COUNT:u32=6;
pub const STATES:u32=7;
pub const STORE_SUBSIG:u32=8; //for subsig-state-pat info
pub const STORE_SUBSIG_STEP:u32=9; //for subsig-step info
pub const STORE_SUBSIG_INFO:u32=10; //for subsig-step component subsig and other
// the following are piece ids for StepInfoStore
pub const ID_SUBSIG_TYPE:u32=0x70130001;
pub const ID_COMP_OP:u32=0x70130002;
pub const ID_COMP_NUM:u32=0x70130003;
pub const ID_MIN_REQUIRED:u32=0x70130004;
pub const ID_COMP_SUBSIG:u32=0x70130005;
// the following are pice ids for SubsigStepStore's encoded_to_attribute table
pub const ID_ENCODED_SUBSIG:u32=0x71090001;
pub const ID_ENCODED_NORMAL_STEP:u32=0x71090002;
pub const ID_ENCODED_PAT:u32=0x71090003;
pub const ID_ENCODED_RG_START:u32=0x71090004;
pub const ID_ENCODED_RG_END:u32=0x71090005;
pub const ID_ENCODED_LAST_STEP:u32=0x71090006;
pub const ID_ENCODED_PREV_ENCODED:u32=0x71090007;
pub const ID_SUBSIG_IGC:u32=0x71090008;
/// Aggressive mode: per-subsig backward-direction flag table.
pub const ID_SUBSIG_IS_BACKWARD:u32=0x71090009;

pub const ID_SIG_NO_CRIT:u32 = 0x73010001;
pub const ID_SIG_NO_CRIT_COUNT:u32 = 0x73020001;

/* COMMENT: each bag acdfa has the following entries see above.
	INIT (offset: 0), NON_FINAL, FINAL, 
	TRANSITIONS, STATE_2_SIG, STATE_SIG_COUNT, 
	STATE_SIG_COUNT, STATES, SUBSIG_PATTEN_STORE (offset: 8)
*/

/// check the percentage of non-zero items (assuming padded item
/// are located at the beginning of col
/// if too many padding, warn or err
pub fn check_pad_ratio<F:PrimeField>(col: &Vec<F>, param: &str){
	let n = col.len();
	for i in 0..col.len(){//check size
		if !col[i].is_zero(){
			if i>2*n/3{
				let msg = format!("Consider adjust {}. Real items: {} << Padded Capaicty:{}", param, n-i, n);
				if i>7*n/8{
					println!("WARN!!!: {}", &msg);
				}else{
					println!("WARN: {}", &msg);
				}
			}
			break;
		}
	}
}


/// database of ClamAV signatures
#[derive(Clone)]
pub struct ClamavDB<F: PrimeField>{
	/// vector of signatures
	pub vec_sigs: Vec<Arc<ClamavSig>>,
	/// vector of those signatures who do NOT have critical patterns
	/// which have to be passed to bag of words or SED.
	pub vec_sigs_no_critical_pat: Vec<Arc<ClamavSig>>,
	/// critical pattersn
	vec_crit_pat: Vec<String>,
	/// critical patterns (for ignore case),
	vec_crit_pat_igc: Vec<String>,
	/// bag of words patters (also including PM-words)
	vec_bag_words: Vec<String>,
	/// bag of words (ignore case)
	vec_bag_words_igc: Vec<String>,
	/// map from critical pattern to a vector of related sigs
	pub map_crit_pat: HashMap<String,Vec<String>>,
	/// map from critical pattern to a vector of related sigs (ignore case)
	pub map_crit_pat_igc: HashMap<String,Vec<String>>,
	/// ACDFA for critical pattern
	pub dfa_crit: HexACDFA, 
	/// ACDFA for critical pattern (for ignore case)
	pub dfa_crit_igc: HexACDFA,
	// ----------------------------------------------
	// NOTE: acdfa for PM and BAG of words are moved
	// as element 0 of bundle_subsig(_igc).vec_acdfa[0]
	// -------------------------------------------------
	/// signature to ID (id starts from 1)
	pub sig_to_id: HashMap<String, usize>,

	/// the lookup table instance
	pub lkup: LookupTableTwoCol_Inst<F>,

	/// the bundle of subsig info (such as subsig to states to patterns
	/// their corresponding ACDFA. This bundle info is used
	/// for both SED and ISED approach
	pub bundle_subsig: Arc<BundleSubsigStore>,

	/// the ignore case version of the bundle of subsig.
	pub bundle_subsig_igc: Arc<BundleSubsigStore>,
	/// Aggressive mode (b_aggressive_sde_for_rep) global halo span:
	/// max match length in nibbles over all subsigs. 0 when flag off.
	/// M1b sizes the forward halo from this DB self-mark.
	pub aggressive_max_span_nibbles: usize,
}

impl <F:PrimeField> fmt::Debug for ClamavDB<F>{
	fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
		//just a dummy impl
        fmt.debug_struct("ClamDB").finish()
    }
}

impl SubsigPatternStoreItem{
	/// input tuple: state_id and its patten IDs
	pub fn new(subsig_id: usize, tuples: Vec<(usize, Vec<usize>)>)
	->Self{
		let mut state_ids = vec![];
		let mut state_to_pattern_ids = HashMap::new();
		for t in tuples{
			let (state_id,mut vec) = t;
			vec.sort();
			state_ids.push(state_id);
			state_to_pattern_ids.insert(state_id, vec);
		}
		state_ids.sort();

		Self{subsig_id, state_ids, state_to_pattern_ids}
	}

	pub fn dump(&self){
		println!("==== subsig_id: {}", self.subsig_id);	
		let mut total = 0;
		for state_id in &self.state_ids{
			println!(" -- state_id: {}", state_id);
			let pats = self.state_to_pattern_ids.get(&state_id).unwrap();
			for pat in pats{
				println!(" -- -- {}", pat);
			}
			total += pats.len();
		}
		println!(" ==== Summary: subsig: {}, total pats: {}", self.subsig_id, total);
	}
}


impl SubsigPatternStore{
	pub fn new()->Self{
		Self{subsig_ids: vec![], subsig_to_rec: HashMap::new()}
	}
	pub fn add(&mut self, item: &SubsigPatternStoreItem){
		let subsig_id = item.subsig_id;
		assert!(!self.subsig_ids.contains(&subsig_id), 
			"subsig_id already exists: {}", subsig_id);
		self.subsig_ids.push(subsig_id);	
		self.subsig_to_rec.insert(subsig_id, item.clone());
	}
	pub fn finalize(&mut self){
		self.subsig_ids.sort();
	}

	/// generate encoded lookup entry which encodes the
	/// following fields:
	/// <subsig_id, id1, state_id, id2, pat_id>
	/// where state_id and pat_id are adjusted values (+1).
	/// For each entry, its wrapped by 2 dummy entries (0 entry and
	/// max entry), where `max = 2^read_global_config().range2_bitS-1`. All fields 
	/// in range value RANGE2. In each `atomic table` values
	/// are all sorted in ascending order.
	/// Example.
	/// subsig_id    id1    state_id    id2   pat_id
	/// g1           0      0           0     0         # dummy entry for g1
	/// g1           1      s1          0     0         # dummy for s1
	/// g1           2      s1          1     100
	/// g1           3      s1          2     200
	/// g1           4      s1          3     MAX       # end dummy for s1
	/// g1           5      s2          0     0         # dummy for s2
	/// g1           6      s2          1     201       
	/// g1           7      s2          2     MAX       # end dummy for s2
	/// g1           8      MAX         MAX   MAX       # end dummy for g1
	/// Comment: such dummy entries make range query easy to implement.
	/// For instance, to search for pat_id related to s1 in rane (50,105)
	/// one can provide one entry before and one entry after the result,
	/// to prove the valdity. Compared with an additional column of `total".
	/// This eventually saves more in reasonging about SED.
	/// Adds all entries to the given tbl_id.
	/// for acdfa_id: see pm_acdfa_id()
	pub fn add_store_to_lkup<F:PrimeField>(&self, 
		lkup: &mut LookupTableTwoCol_Inst<F>, 
		acdfa_id: u32,
		state_part_bits: usize,
	) -> Result<(), Error>{
		let cols = self.gen_cols(state_part_bits, None)?;
		let tbl_id = F::from(acdfa_id + STORE_SUBSIG);

		let mut tuples = cols[5].par_iter().map(|v|{
			(tbl_id, *v)
		}).collect::<Vec<(F,F)>>();
		lkup.vals.append(&mut tuples);
		Ok( () )
	}

	/// Generate a new store by projecting to subsigs_id
	/// the subsigs_id are the results of acdfa.gen_subsig_id(sig_id, subsig_id)
	/// NOTE: a dummy 0 entry is added at the beginning if inp_subsigs_id
	/// contains dummy 0's as padding values.
	pub fn project_by(&self, inp_subsigs_id: &Vec<usize>)->Self{
		let max_val:usize = (1<<read_global_config().range2_bit) - 1;
		let mut new_map = inp_subsigs_id.par_iter().filter(|id|
			**id!=0usize && **id!=max_val
		).map(|id|
			(*id,  self.subsig_to_rec.get(id).expect(
				&format!("cannot find store item for id: {}", id)).clone())
		).collect::<HashMap<usize, SubsigPatternStoreItem>>();
		
		if  inp_subsigs_id.contains(&0){
			let dummy_item =  SubsigPatternStoreItem::new(0, vec![]); 
			new_map.insert(0, dummy_item);
		}

	
		let mut subsig_ids = inp_subsigs_id.clone();
		subsig_ids.sort();

		Self{subsig_ids, subsig_to_rec: new_map}
	}

	/// generate the following columsn:
	/// <subsig_id, id1, state, id2, pattern_id, encoded>
	/// The projected table should be padded to n if it is Some. 
	/// If padding too much
	/// we'll print warning (for tbl_len 2 times larger than actual tbl
	/// length, and panic if 8 times larger).
	///
	/// might throw CapErr: proj_store:n
	pub fn gen_cols<F:PrimeField>(&self, state_part_bits: usize, n: Option<usize>)->Result<Vec<Vec<F>>, Error>{
		//NOTE: entry format
		// (subsig_id, id1, state_id, id2, pat_id)
		//1. define the encode function
		let factor = F::from(1u32<<state_part_bits);
		let encode_vec = |vec: &Vec<usize>| -> F{
			if B_DEBUG {assert!(vec.len()==5);}
			vec.iter().fold(F::zero(), |s,v| {
				if B_DEBUG {assert!(*v<(1<<state_part_bits));}
				s*factor + F::from(*v as u32)
			})
		};
		let max:usize = (1<<state_part_bits) - 1;
		let new_subsig_ids = if self.subsig_ids.contains(&0) {
			self.subsig_ids.clone()
		}else{ vec![ vec![0], self.subsig_ids.clone() ].concat() };
		if B_DEBUG {//assert sorted
			for i in 0..new_subsig_ids.len()-1{
				assert!(new_subsig_ids[i]<=new_subsig_ids[i+1]);
			}
		}

		//2. a sanitty check of its own subsigs
		if B_DEBUG {//no duplicate non-zero items
			let mut hs = HashSet::new();
			for i in 0..new_subsig_ids.len(){
				if new_subsig_ids[i]!=0{
					assert!(hs.contains(&new_subsig_ids[i]));
					hs.insert(new_subsig_ids[i]);

					let item = self.subsig_to_rec
						.get(&new_subsig_ids[i]).unwrap();
					let set_state_ids = item.state_ids.iter().map(|x|
						*x).collect::<HashSet<usize>>();
					assert!(set_state_ids.len() == item.state_ids.len());
				}
			}
		}
		let estimated_len: usize = new_subsig_ids.iter().filter(|x| **x!=0)
		.map(|x|{
			let item = self.subsig_to_rec.get(&x).unwrap();
			item.state_ids.iter().map(|sid| {
				let pat_ids = item.state_to_pattern_ids.get(sid).unwrap();
				pat_ids.len() + 2 //for 2 dummy entries for each state
			}).sum::<usize>() + 2 //for 2 dummy entries for each subsig
		}).sum::<usize>() + 2; //because of subsig-0 

/*
		if n.is_some(){
			let n = n.unwrap();
			assert!(n>estimated_len, 
				"n: {} too small. need to be at least: {}", n, estimated_len);
			let msg = format!("Adjust FsmAdvCapacity.avg_pats_per_subsig to a lower number: currently projected store: actual size {} padded to {}. ", estimated_len, n); 
			if n>2*estimated_len {println!("WARNING: {}", &msg);}
			assert!(n<=8*estimated_len, "ERROR: {}", &msg);
		}
		*/
		if n.is_some(){
			let n = n.unwrap();
			if n<estimated_len{
				return Err(Error::CapErr(vec![(format!("proj_store::n"), 
					estimated_len
				)]));
			}
			assert!(n>=estimated_len, "ProjStore buffer len too small. n: {}, estimated: {}, Consider increasing the properties such as  avg_pats_per_subsig or subsigs in FsmAdvCapacity config.", n, estimated_len);
		}
		let inner_zero_entries = if n.is_some() {n.unwrap()- estimated_len}
			else {0};
		

		//3. collect the tuples
		let mut entries = vec![];
		let mut zero_processed = false;
		for i in 0..new_subsig_ids.len(){
			let mut id1 = 0;
			//1. generate the dummy entry record
			let subsig_id = new_subsig_ids[i];
			if subsig_id==0 {
				if zero_processed {continue;}
				zero_processed = true; //only process one time avoid duplicates
			}
			entries.push(vec![subsig_id, id1, 0, 0, 0]);
			id1+=1;
			if subsig_id==0{//push the extras
				// here we insert a collection of pure 0 entries
				// note that they DO NOT follow the id+=1 rule 
				// (well-formed table)
				// this makes it easier to handle intiliazation.
				// these 0 entries will be ignored in 
				// assert_well_formed function in db.rs.
				for _j in 0..inner_zero_entries{ 
					entries.push(vec![subsig_id, 0, 0, 0, 0]);
				}
			}else{
				//2. generate the records for SubsigPattenItem for subsig
				let item = &self.subsig_to_rec.get(&subsig_id).unwrap();
				for state_id in &item.state_ids{
					let adj_sid = *state_id;//don't adjust, already adjusted
					let pat_ids = item.state_to_pattern_ids.get(&state_id)
						.expect("err get state");
					let mut id2 = 0usize;
					//2.1 dummy begin entry
					entries.push(vec![subsig_id, id1, adj_sid, id2, 0]);
					id1+=1;
					id2+=1;

					//2.2 for each patten id
					for pid in pat_ids{
						let adj_pid = *pid; //don't adjust already adjusted
						entries.push(vec![subsig_id, id1, adj_sid, id2, adj_pid]);
						id1+=1;
						id2+=1;
					}

					//2.3 dummy exit entry
					entries.push(vec![subsig_id, id1, adj_sid, id2, max]);
					id1+=1;
				}//for state_id
			}

			//3. generate the dummy END record
			entries.push(vec![subsig_id, id1, max, max, max]);
		}


		//4. assemble encodes
		let encodes = entries.par_iter().map(|v|{
			encode_vec(v)
		}).collect::<Vec<F>>();

		//5. construct results
		let getidx = |i: usize,vec: &Vec<Vec<usize>>| -> Vec<F>{
			vec.par_iter().map(|v| F::from(v[i] as u32))
				.collect::<Vec<F>>()
		};
		if n.is_some(){ assert!(entries.len()==n.unwrap()); }

		let res = 
			vec![getidx(0, &entries), getidx(1, &entries), getidx(2, &entries),
				getidx(3, &entries), getidx(4, &entries), encodes];

		//RECOVER LATER  -----------
		//check_pad_ratio(&res[0], "FsmAdvCapacity.avg_pat_per_subsig"); 
		//RECOVER LATER  ABOVE
		Ok( res )
	}

	pub fn dump(&self){
		for subsig in &self.subsig_ids{
			let rec = self.subsig_to_rec.get(&subsig).unwrap();
			rec.dump();
		}
	}
}

/// Forward pm-bounds chain -> keyword-first backward chain
/// (aggressive mode). The stored chain stays forward; this is applied
/// at lookup-generation / processing time when is_backward is set.
///   new step 1 = keyword (forward's LAST pat), begin = `begin_anywhere`;
///   each reversed step takes its forward neighbor's gap as a positive
///   backward magnitude (abs value; direction is carried by the
///   is_backward flag, never a sign). The forward step-1 begin is
///   DROPPED (sound under the DLP begin-guard, which requires it to be
///   the vacuous "anywhere" begin).
/// Generic over the pattern key so both the stored (pat_id: usize) and
/// the content (word: String) representations reuse it.
/// Involution: reverse(reverse(C)) == C on the begin-normalized domain
/// (i.e. when C's step-1 begin already equals `begin_anywhere`).
pub fn reverse_pm_bounds<T: Clone>(
	fwd: &[(T, (usize, usize))],
	begin_anywhere: (usize, usize),
) -> Vec<(T, (usize, usize))> {
	let k = fwd.len();
	if k == 0 { return vec![]; }
	let mut out = Vec::with_capacity(k);
	out.push((fwd[k - 1].0.clone(), begin_anywhere));      // keyword anchor
	for j in 1..k {
		out.push((fwd[k - 1 - j].0.clone(), fwd[k - j].1)); // shift gap back one
	}
	out
}

impl SubsigStepStoreItem{
	pub fn new(subsig_id: usize, igc: bool,
		vec_pm_bounds: Vec<(usize,(usize,usize))>)->Self{
		Self{subsig_id, vec_pm_bounds, igc, is_backward: false}
	}

	pub fn dump(&self){
		println!("subsig_id: {}", self.subsig_id);
		for i in 0..self.vec_pm_bounds.len(){
			let (pat_id, (rg1, rg2)) = self.vec_pm_bounds[i];
			println!(" -- step: {}, pat_id: {}, rg1: {}, rg2: {}", i+1, pat_id, rg1, rg2);
		}
	}
}

impl SubsigStepStore{
	pub fn new()->Self{
		Self{subsig_ids: vec![], subsig_to_steps: HashMap::new(),
			b_aggressive: false}
	}
	pub fn add(&mut self, item: &SubsigStepStoreItem){
		let subsig_id = item.subsig_id;
		assert!(!self.subsig_ids.contains(&subsig_id), 
			"subsig_id already exists: {}", subsig_id);
		self.subsig_ids.push(subsig_id);	 //note: not sorted yet!
		self.subsig_to_steps.insert(subsig_id, item.clone());
	}
	pub fn finalize(&mut self){
		self.subsig_ids.sort();
	}

	/// generate encoded lookup entry which encodes the
	/// following fields:
	/// <subsig_id, id1, pat_id, range_start, range_end>
	/// All "value" fields have range in RANGE2 (note: may include max =
	///  `2^read_global_config().range2_bit-1`).
	/// Dummy entries are marked as 0 and max in patid_field.
	/// Example.
	/// subsig_id    id    pat_id 		rg_stt	rg_endpat_id
	/// g1           0      0           0     	0         # dummy entry for g1
	/// g1           1      p1          1     	20        # range (1,20) for p1
	/// g1           2      p2          2       max       # here "max" is real
	/// g1           3      max         max		max		  # dummy end entry
	/// before valid entries it's padded with 0 entries.
	///
	/// We also add another table
	/// <subsig_id, b_igc>
	pub fn add_store_to_lkup<F:PrimeField>(&self, 
		lkup: &mut LookupTableTwoCol_Inst<F>, 
		acdfa_id: u32,
		state_part_bits: usize,
	) {
		let max_val:usize = (1<<read_global_config().range2_bit) - 1;
		let max = F::from(max_val as u32);
		let cols = self.gen_cols(state_part_bits, None);
		let _tbl_id = F::from(acdfa_id + STORE_SUBSIG_STEP);

		/*
		// DEPRECATED, REMOVE LATER --------------
		//cols[5] is encoded
		let mut tuples = cols[5].par_iter().map(|v|{
			(tbl_id, *v)
		}).collect::<Vec<(F,F)>>();

		lkup.vals.append(&mut tuples);
		// DEPRECATED, REMOVE LATER -------------- ABOVE
	
		if B_DEBUG {//encoded part be sorted to speed up insertion
			//becaues when encoded col is sorted, the gen_step_tbl_id()
			//will generated sorted sub-table ID given piece id is sorted
			let encoded = &cols[5];
			for i in 0..encoded.len()-1{ assert!(encoded[i]<=encoded[i+1]); }
		}
		*/

		//1. use a loop add sub-table for encoded-subsig, encoded_step, 
		// encoded_pat_id, encoded_rg_start, encoded_rg_end,
		let subcats = [
			ID_ENCODED_SUBSIG,  //cat_id = 0
			ID_ENCODED_NORMAL_STEP, //1
			ID_ENCODED_PAT, //2
			ID_ENCODED_RG_START,  //3
			ID_ENCODED_RG_END,  //4
			ID_ENCODED_PREV_ENCODED, //5
		];
		let encoded:&Vec<F> = &cols[5];
		let pats = &cols[2];
		let steps = &cols[1];
		let subsigs = &cols[0];
		// process each column row for column: cat_id in (0..5).
		// pid is the real category ID like ID_ENCODED_SUB ... 
		let mut all_tuples = subcats.par_iter().enumerate().map(|(cat_id,pid)|{
			//process each column row
			//b_add indicates whether the tuple should be added.
			let info_col = &cols[cat_id]; //the column being processed
			let tuples = if cat_id<5 {//except ID_ENCODED_PREV_ENCODED
			  encoded.iter().zip(info_col.iter()).enumerate()
			  .map(|(row_id,(&encode, &val))|{
				//b_dummy: dummy entry
			    let b_dummy = pats[row_id].is_zero() || pats[row_id]==max;  
				let (b_include,tbl_id) = if cat_id!=1 {
					//ENCODED_SUBSIG, ENCODED_PAT ...
					//excluding ENCODED_NORMAL_STEP
					//e..g when cat_id is 0, pid is ID_ENCODED_SUBSIG
					(!b_dummy, Self::gen_step_tbl_id(encode, *pid))
				}else{//cat_id is 1 (normal step) 
					//recall the structure of cols (e.g., for 2 steps)
					//   0  0
					//   step 1
					//   step 2 (last)
					//   max max
					// We need to tag step_0, step 1 as NORMAL_STEP,
					//  step 2 as LAST_STEP
					// ignore max (set b_include to false), but NOT for 0
					// For another instance, for dummy subsig 0
					// it has two rows
					// ... 0  0 ....
					// ... max max ...
					// in this case, it has tag LAST_STEP for step 0,
					//     and no NORMAL STEP.
					//
					// note: variable val represents the step
					let tab_id = if row_id<pats.len()-1 && pats[row_id+1]==max{
						let res=Self::gen_step_tbl_id(
							encode,ID_ENCODED_LAST_STEP
						);

						res
					}else{
						let res=Self::gen_step_tbl_id(
							encode,ID_ENCODED_NORMAL_STEP
						);

						res
					};
					let b_last= pats[row_id] == max;
					(!b_last, tab_id)
				};
				//add a dummy entry for subsig 0 dummy record
				let b_include = b_include || subsigs[row_id].is_zero();
				(b_include, tbl_id, val) 
			  }).collect::<Vec<(bool, F,F)>>()
			}else{//ID_ENCODED_PREV_ENCODED
			  let res = encoded.iter().zip(steps.iter()).enumerate()
			  	.map(|(row_id,(&encode_word,&step))|{
					let tbl_id = Self::gen_step_tbl_id(encode_word,*pid);
					if !step.is_zero() { 
						if row_id>=1{
							(true, tbl_id, encoded[row_id-1]) 
						}else{//dummy one, will NOT be added
							(false, tbl_id, encoded[row_id]) 
						}
					} else { 
						//if it's not dummy subsig 0, we do not include it
						// set bInclude to False.
						//but for dummy subsig=0, include a zero record
						//for dummy record.
						(subsigs[row_id].is_zero(), tbl_id, F::zero()) 
					}
				}).collect::<Vec<(bool, F,F)>>();

			  res
			};

			let tuples = tuples.iter()
				.filter(|(b_include,_tag_id, _encoded)| *b_include)
				.map(|(_,tag_id, encoded)| (*tag_id, *encoded))
				.collect::<Vec<(F,F)>>();

			tuples
		}).collect::<Vec<Vec<(F,F)>>>().concat();

		//2. generate subtl subsig_id -> igc 
		let tbl_id_start = F::from(1u64<<32) * F::from(ID_SUBSIG_IGC);
		let tuples2 = self.subsig_ids.par_iter().map(|subsig_id|{
			let item = self.subsig_to_steps.get(subsig_id)
				.expect(&format!("cannot find subsigid: {}", subsig_id));
			let f_igc = if item.igc {F::one()} else {F::zero()};
			let tbl_id = tbl_id_start + F::from(*subsig_id as u64);
			(tbl_id, f_igc)
		}).collect::<Vec<(F,F)>>();

		all_tuples = [&all_tuples[..], &tuples2[..]].concat();

		//2b. aggressive mode only: commit per-subsig backward flag.
		// Flag-off => b_aggressive=false => zero rows => byte-identical
		// lookup. Covers ALL subsigs (0/1) so the gadget authenticates
		// each subsig's direction by simple membership.
		if self.b_aggressive {
			let tbl_id_start = F::from(1u64<<32)
				* F::from(ID_SUBSIG_IS_BACKWARD);
			let mut tuples3 = self.subsig_ids.par_iter().map(|subsig_id|{
				let item = self.subsig_to_steps.get(subsig_id)
					.expect(&format!("cannot find subsigid: {}",
						subsig_id));
				let f = if item.is_backward {F::one()} else {F::zero()};
				let tbl_id = tbl_id_start + F::from(*subsig_id as u64);
				(tbl_id, f)
			}).collect::<Vec<(F,F)>>();
			//subsig 0 is the pad/dummy referenced by padded prf rows in the
			//gadget; commit it as is_backward=0 so those rows authenticate.
			if !self.subsig_ids.contains(&0){
				tuples3.push((tbl_id_start, F::zero()));
			}
			all_tuples.append(&mut tuples3);
		}

		all_tuples.sort();

		if B_DEBUG {//key of all_tuples should be sorted
			for i in 0..all_tuples.len(){
				assert!(all_tuples[i].0<=all_tuples[i].1);
			}
		}
		lkup.vals.append(&mut all_tuples);
	}

	/// NOTE that this is a static function. It generates the table id
	/// given the acdfa_id, encoded (of subsig-id-pat-rg_start-rg_end)
	/// It generates a 194-bit table_id (which mainly encodes
	/// the encoded work and the subcategory). This is used to
	/// verify the validity of (subsig, step, rg_start ...) and 
	/// and see if they are included in the encoded word.
	///
	/// For example, given encoded=500 is 
	/// an encoding of (subsig=100, step=2, ..)
	/// if one needs to verify that step 2 is really included in the
	/// encoded 500, one just needs to enreate the table_id using
	/// subtbl_id = gen_step_tbl_id(500, ID_ENCODED_SUBSIG), 
	/// and verify (subtbl_id, 2)
	/// in the lookup
	#[inline(always)]
	pub fn gen_step_tbl_id<F:PrimeField>(
		encoded: F,  //actually 26*5 = 180 bit
		piece_id: u32,  //like ENCODED_SUBSIG, ENCODED_STEP ...
	)->F{
		//we set f1 to f4 order so that the entries when added
		//are easily sorted.
		let info_id= F::from(0x23001101u32); //tag to avoid collision
		let f1 = F::from(1u64<<read_global_config().range2_bit);
		let factor1 = f1*f1*f1*f1*f1; //models encoded
		let factor2 = F::from(1u64<<32); //32-bit 

		let res = info_id*factor1*factor2 + F::from(piece_id)*factor1+
				encoded; //encoded in this way avoid validate() function
						 //to perform multiplication on encoded

		//toal 26*5 + 2*32 = 194 bit
		res
	}


	/// Generate a new store by projecting to subsigs_id
	/// the subsigs_id are the results of acdfa.gen_subsig_id(sig_id, subsig_id)
	///   NOTE: a dummy 0 entry is added at the beginning if inp_subsigs_id
	/// contains dummy 0's as padding values.
	pub fn project_by(&self, inp_subsigs_id: &Vec<usize>)->Self{
		let max_val:usize = (1<<read_global_config().range2_bit) - 1;
		let mut new_map = inp_subsigs_id.par_iter().filter(|id|
			**id!=0usize && **id!=max_val
		).map(|id| (*id,  self.subsig_to_steps.get(id).expect(
				&format!("cannot find store item for id: {}", id)).clone())
		).collect::<HashMap<usize, SubsigStepStoreItem>>();
	
		if  inp_subsigs_id.contains(&0){
			//set igc to false is ok because it's dummy item
			let dummy_item =  SubsigStepStoreItem::new(0, false, vec![]); 
			new_map.insert(0, dummy_item);
		}

		let mut subsig_ids = inp_subsigs_id.clone();
		subsig_ids.sort();

		let res = Self{subsig_ids, subsig_to_steps: new_map,
			b_aggressive: self.b_aggressive};

		res
	}

	/// generate the following columsn:
	/// NOTE pat_id is adjusted by plus one
	/// <subsig_id, id, pat_id, rg_start, rg_end, encoded>
	/// The projected table should be padded to n if it is Some. 
	/// If padding too much, warning or panic
	pub fn gen_cols<F:PrimeField>(&self, state_part_bits: usize, n: Option<usize>)->Vec<Vec<F>>{
		//NOTE: entry format
		// (subsig_id, id1, pat_id, rg_start, rg_end)
		//1. define the encode function
		assert!(state_part_bits == read_global_config().range2_bit); //for legacy code
		let factor = F::from(1u32<<state_part_bits);
		let encode_vec = |vec: &Vec<usize>| -> F{
			if B_DEBUG {assert!(vec.len()==5);}
			vec.iter().fold(F::zero(), |s,v| {
				if B_DEBUG {assert!(*v<(1<<state_part_bits));}
				s*factor + F::from(*v as u32)
			})
		};
		let max:usize = (1<<state_part_bits) - 1;
		let new_subsig_ids = if self.subsig_ids.contains(&0) {
			self.subsig_ids.clone()
		}else{ vec![ vec![0], self.subsig_ids.clone() ].concat() };
		if B_DEBUG {//assert sorted
			for i in 0..new_subsig_ids.len()-1{
				assert!(new_subsig_ids[i]<=new_subsig_ids[i+1]);
			}
		}
			

		//2. estimate the effective table
		let estimated_len: usize = new_subsig_ids.iter().filter(|x| **x!=0)
		.map(|x|{ 
			self.subsig_to_steps.get(&x).unwrap().vec_pm_bounds.len() + 2 })
		.sum::<usize>() + 2; //because of subsig-0 

		if n.is_some(){
			let n = n.unwrap();
			assert!(n>estimated_len, 
				"n: {} too small. need to be at least: {}", n, estimated_len);
		}
		let inner_zero_entries = if n.is_some() 
			{n.unwrap()- estimated_len} else {0};
		

		//3. collect the tuples
		let mut entries = vec![];
		let mut zero_processed = false;
		for i in 0..new_subsig_ids.len(){
			let mut id1 = 0;
			//1. generate the dummy entry record
			let subsig_id = new_subsig_ids[i];
			if subsig_id==0 {
				if zero_processed {continue;}
				zero_processed = true; //only process one time avoid duplicates
			}
			entries.push(vec![subsig_id, id1, 0, 0, 0]);
			id1+=1;
			if subsig_id==0{//push the extras
				// here we insert a collection of pure 0 entries
				// note that they DO NOT follow the id+=1 rule 
				// (well-formed table)
				// this makes it easier to handle intiliazation.
				// these 0 entries will be ignored in 
				// assert_well_formed function in db.rs.
				for _j in 0..inner_zero_entries{ 
					entries.push(vec![subsig_id, 0, 0, 0, 0]);
				}
			}else{
				//2. generate the records for SubsigStepItem
				let item = &self.subsig_to_steps.get(&subsig_id).unwrap();
				// Aggressive backward subsig: emit the reversed,
				// keyword-first chain so the gadget reads it in
				// backward-walk order (id1 increments in emission
				// order => keyword becomes step 1). Forward items
				// and flag-off builds keep the stored order.
				let reversed;
				let steps: &Vec<(usize,(usize,usize))> =
					if item.is_backward {
						reversed = reverse_pm_bounds(
							&item.vec_pm_bounds, (0, max));
						&reversed
					} else { &item.vec_pm_bounds };
				for step in steps{
					let pat_id = step.0; //no adjust (already did in table)
					let (r_s, r_e) = (step.1.0, step.1.1);
					entries.push(vec![subsig_id, id1, pat_id, r_s, r_e]);
					id1+=1;
				}//for step
			}//end of else

			//3. generate the dummy END record
			entries.push(vec![subsig_id, id1, max, max, max]);
		}

		//4. assemble encodes
		let encodes = entries.par_iter().map(|v|{
			encode_vec(v)
		}).collect::<Vec<F>>();

		//5. construct results
		let getidx = |i: usize,vec: &Vec<Vec<usize>>| -> Vec<F>{
			vec.par_iter().map(|v| F::from(v[i] as u32))
				.collect::<Vec<F>>()
		};
		if n.is_some(){ assert!(entries.len()==n.unwrap()); }

		let res = 
			vec![getidx(0, &entries), getidx(1, &entries), getidx(2, &entries),
				getidx(3, &entries), getidx(4, &entries), encodes];

		check_pad_ratio(&res[0], "FsmAdvCapacity.avg_pat_per_subsig"); 
		res
	}

	pub fn dump(&self){
		for subsig in &self.subsig_ids{
			let item = self.subsig_to_steps.get(&subsig).unwrap();
			item.dump();
		}
	}
}

impl SubsigInfoStoreItem{
	pub fn dump(&self){
		println!("==== SubsigInfoStoreItem subsig_id: {}====", self.subsig_id);
		println!("  subsig_type: {} -> {:#?}, op: {} -> {:#?}, comp_num: {}, min_req: {}, component_subsig.len: {}", 
			self.subsig_type, 
			SubSigType::from(self.subsig_type),
			self.comp_op,
			CompOp::from(self.comp_op),
			self.comp_num,
			self.min_required,
			self.component_subsigs.len()
		);
		for i in 0..self.component_subsigs.len(){
			println!(" -- i: {}, comp_subsig: {}",i,self.component_subsigs[i]);
		}
	}
}


impl SubsigInfoStore{
	pub fn new()->Self{
		Self{subsig_ids: vec![], subsig_to_rec: HashMap::new()}
	}

	pub fn add(&mut self, item: &SubsigInfoStoreItem){
		let subsig_id = item.subsig_id;
		assert!(!self.subsig_ids.contains(&subsig_id), 
			"subsig_id already exists: {}", subsig_id);
		self.subsig_ids.push(subsig_id);	 //note: not sorted yet!
		self.subsig_to_rec.insert(subsig_id, item.clone());
	}

	pub fn finalize(&mut self){
		self.subsig_ids.sort();
	}

	/// NOTE that this is a static function. It generates the table id
	/// given the acdfa_id and piece id (such as subsig_type, comp_op, ...).
	/// It generates a 128-bit table_id which is unique for each subsig.
	/// Note that subsig_id is actually read_global_config().range2_bit (26), which can
	/// fit in u32.
	#[inline(always)]
	pub fn gen_info_tbl_id<F:PrimeField>(
		_acdfa_id: u32, //the acdfa_id of the bundle 
		subsig_id: usize,  //actually 26 bit
		piece_id: u32,  //like SUBSIG_TYPE_ID, COMP_OP_ID ...
	)->F{
		//we set f1 to f4 order so that the entries when added
		//are easily sorted.
		let info_id:u32 = 0x13752405; //just random tag to avoid collision
		let f1 = F::from(info_id);
		//let f2 = F::from(acdfa_id);
		let f3 = F::from(subsig_id as u32);
		let f4 = F::from(piece_id);
		let factor = F::from(0x100000000 as u64); //32-bit 

		//let res = f1*factor*factor*factor + f2*factor*factor + f3*factor + f4;
		let res = f1*factor*factor + f3*factor + f4;

		//toal 128-bit
		res
	}

	/// Encode the following colums each as a separate table for eacy 
	/// query: the table id is generated based on <subsig_id, acdfa_id>
	///   subsig_type, comp_op, comp_num, min_required
	/// Then for each subsig its compnent subsigs are encoded using 
	/// a separate table of the following structure (note: one table for
	/// each subsig>
	///    <id, comp_subsig>
	/// if a subsig has k componnet subsigs, the table has k+2 entry.
	/// there are two dummy entries: <0,0>, <k+1, max>. In between
	/// are real entries.
	pub fn add_store_to_lkup<F:PrimeField>(&self, 
		lkup: &mut LookupTableTwoCol_Inst<F>, 
		acdfa_id: u32,
		_state_part_bits: usize, //deprecated. use read_global_config().range2_bit directly
	) {
		let factor = F::from(1u32 << read_global_config().range2_bit);
		let max_val:usize = (1<<read_global_config().range2_bit) - 1;
		let max = F::from(max_val as u64);

		assert!(!self.subsig_ids.contains(&0), 
				"StoreInfoStore.subsig_id should not contain subsig 0");
		let subsig_ids = [&[0usize][..], &self.subsig_ids[..]].concat();
		let mut tuples = subsig_ids.par_iter().map(|subsig_id|{
			let rec = if *subsig_id==0{
				SubsigInfoStoreItem{
					subsig_id: 0,
					subsig_type: SubSigType::GeneralRegex as u8,
					comp_op: CompOp::NONE as u8,
					comp_num: 0u32,
					min_required: 0usize,
					component_subsigs: vec![]
				}
			}else{
				self.subsig_to_rec.get(subsig_id).expect(
					&format!("cannot find subsig_id: {}", subsig_id)).clone()
			};
			//1. the subsig_type
			let tbl_id = Self::gen_info_tbl_id::<F>(acdfa_id, *subsig_id, 
				ID_SUBSIG_TYPE); 
			let t_subsig_type = (tbl_id, F::from(rec.subsig_type));

			//2. the comp_op 
			let tbl_id = Self::gen_info_tbl_id::<F>(acdfa_id, *subsig_id, 
				ID_COMP_OP); 
			let t_comp_op= (tbl_id, F::from(rec.comp_op));

			//3. the comp_num 
			let tbl_id = Self::gen_info_tbl_id::<F>(acdfa_id, *subsig_id, 
				ID_COMP_NUM); 
			let t_comp_num= (tbl_id, F::from(rec.comp_num));

			//4. the min_required 
			let tbl_id = Self::gen_info_tbl_id::<F>(acdfa_id, *subsig_id, 
				ID_MIN_REQUIRED); 
			let t_min_required= (tbl_id, F::from(rec.min_required as u64));

			//5. related subsigs 
			let tbl_id = Self::gen_info_tbl_id::<F>(acdfa_id, *subsig_id, 
				ID_COMP_SUBSIG); 
			let mut vec_comp_subsigs = vec![(tbl_id, F::zero())];
			let k = rec.component_subsigs.len(); //already sorted
			for i in 0..k{
				let f1 = F::from((i+1) as u32); //starts from 1
				let f2 = F::from(rec.component_subsigs[i] as u32);
				let encoded = f1 + f2*factor;
				vec_comp_subsigs.push( (tbl_id, encoded) )
			}
			let encoded_last = F::from((k+1) as u32) + max*factor;
			vec_comp_subsigs.push( (tbl_id, encoded_last) );

			vec![
				vec![t_subsig_type, t_comp_op, t_comp_num, t_min_required],
				vec_comp_subsigs
			].concat()
		}).flatten().collect::<Vec<(F,F)>>();

		lkup.vals.append(&mut tuples);
	}

}


impl <F:PrimeField> ClamavDB<F>{
	/// this adds a map from [0,...,F] -> ['0', ..., 'F']
	fn add_char_map(lk:&mut LookupTableTwoCol_Inst<F>){
		let charset:Vec<char> = vec!['0','1','2','3','4','5','6','7','8',
			'9','a','b','c','d','e','f'];
		assert!(charset.len()==16);
		let f_char_map = F::from(CHAR_MAP);
		let mut tuples = (0..16).collect::<Vec<usize>>().into_iter().map(|i|{
			let val = F::from(i as u32);
			let ch = charset[i];
			let id = f_char_map + F::from(ch as u8);	

			(id,val)
		}).collect::<Vec<(F,F)>>();
		lk.vals.append(&mut tuples);
	}


	/// This adds 3 small sections to lkup table:
	/// (1) 3 TriVal (False, True, Maybe),
	/// (2) 3 TriOp (Not, And, Or)
	/// (3) Encoded rows of truth table for Not, And, Or
	fn add_trival_rules(lk: &mut LookupTableTwoCol_Inst<F>){
		//1. add the 3 TriVal
		let tbl_id = F::from(TRI_VAL);
		let vals = [TriVal::False, TriVal::True, TriVal::Maybe];
		let mut tuples = vals.into_iter().map(|x| 
			(tbl_id, F::from(x as u8))
		).collect::<Vec<(F,F)>>();
		lk.vals.append(&mut tuples);

		//2. add the three TriOp
		let tbl_id = F::from(TRI_OP);
		let vals = [TriOp::Not, TriOp::BitAnd, TriOp::BitOr];
		let mut tuples = vals.into_iter().map(|x| 
			(tbl_id, F::from(x as u8))
		).collect::<Vec<(F,F)>>();
		lk.vals.append(&mut tuples);

		//3. add the BitNot
		let factor = F::from(1u32 << read_global_config().range2_bit);
		let tbl_id = F::from(TRI_TRUTH_TBL);
		let vals = [
			(TriOp::Not, TriVal::False, TriVal::True),
			(TriOp::Not, TriVal::True, TriVal::False),
			(TriOp::Not, TriVal::Maybe, TriVal::Maybe),
		];
		let mut tuples = vals.iter().map(|t|{
			let f_op = F::from(t.0 as u8);
			let f_v1 = F::from(t.1 as u8);
			let f_v2 = F::from(t.2 as u8);
			let encoded = f_op + f_v1*factor + f_v2*factor*factor;

			(tbl_id, encoded)
		}).collect::<Vec<(F,F)>>();
		lk.vals.append(&mut tuples);

		//4. add the BitAnd and BitOr
		let vals = [
			(TriOp::BitAnd, TriVal::True, TriVal::True, TriVal::True),
			(TriOp::BitAnd, TriVal::True, TriVal::False, TriVal::False),
			(TriOp::BitAnd, TriVal::True, TriVal::Maybe, TriVal::Maybe),

			(TriOp::BitAnd, TriVal::False, TriVal::True, TriVal::False),
			(TriOp::BitAnd, TriVal::False, TriVal::False, TriVal::False),
			(TriOp::BitAnd, TriVal::False, TriVal::Maybe, TriVal::False),

			(TriOp::BitAnd, TriVal::Maybe, TriVal::True, TriVal::Maybe),
			(TriOp::BitAnd, TriVal::Maybe, TriVal::False, TriVal::False),
			(TriOp::BitAnd, TriVal::Maybe, TriVal::Maybe, TriVal::Maybe),

			(TriOp::BitOr, TriVal::True, TriVal::True, TriVal::True),
			(TriOp::BitOr, TriVal::True, TriVal::False, TriVal::True),
			(TriOp::BitOr, TriVal::True, TriVal::Maybe, TriVal::True),

			(TriOp::BitOr, TriVal::False, TriVal::True, TriVal::True),
			(TriOp::BitOr, TriVal::False, TriVal::False, TriVal::False),
			(TriOp::BitOr, TriVal::False, TriVal::Maybe, TriVal::Maybe),

			(TriOp::BitOr, TriVal::Maybe, TriVal::True, TriVal::True),
			(TriOp::BitOr, TriVal::Maybe, TriVal::False, TriVal::Maybe),
			(TriOp::BitOr, TriVal::Maybe, TriVal::Maybe, TriVal::Maybe),
		];
		let mut tuples = vals.iter().map(|t|{
			let f_op = F::from(t.0 as u8);
			let f_v1 = F::from(t.1 as u8);
			let f_v2 = F::from(t.2 as u8);
			let f_v3 = F::from(t.3 as u8);
			let encoded = f_op + f_v1*factor + f_v2*factor*factor + 
				f_v3*factor*factor*factor;

			(tbl_id, encoded)
		}).collect::<Vec<(F,F)>>();
		lk.vals.append(&mut tuples);

	}

	/// add the init, non-final states, final states, and transitions
	/// into its lookup table. Note that they are 4 separate
	/// sub-tables and the init is a table with one entry.
	/// of the non-final states (see TblId). required all subsequent
	/// two ids in TblId represent its final states and transitions.
	fn add_acdfa_to_lkup(lk: &mut LookupTableTwoCol_Inst<F>, acdfa: &HexACDFA, tbl_id_init: u32, pat_to_sigs: &HashMap<String, Vec<String>>, sig_to_id: &HashMap<String, usize>){
		//1. set up the table IDs
		let init_tbl_id = tbl_id_init;
		let nonfinal_tbl_id = tbl_id_init+1;
		let final_tbl_id = tbl_id_init+2;
		let trans_tbl_id = tbl_id_init+3;
		let state_2_sig_id = tbl_id_init+4;
		let state_sig_count_id = tbl_id_init+5;
		let all_states_id = tbl_id_init+6;
		let state_2_pat = tbl_id_init+7;

		//2. build the single entry sub-table for init
		let init_st = acdfa.init_state as u32;
		let vec_init = vec![(F::from(init_tbl_id), F::from(init_st))]; 

		//3. build the non-final states (index)
		// final states: [0,num_acc_states-1]
		// non-finals: [num_acc_states, 1]
		// here: we just store "state indexes" no need to store their
		// encoded form as sub-table ID distinguish states from different DFAs
		// NOTE: all states starting from 1 (0 used as dummy value)
		let f_nonfinal_tbl_id = F::from(nonfinal_tbl_id);
		let vec_non_final = (acdfa.num_acc_states..acdfa.num_states)
			.into_par_iter().map(|i| (f_nonfinal_tbl_id, F::from((i+1) as u32))
		).collect::<Vec<(F,F)>>();


		//3. final states
		let f_final_tbl_id = F::from(final_tbl_id);
		let vec_final = (0..acdfa.num_acc_states).
			into_par_iter().map(|i| (f_final_tbl_id, F::from((i+1) as u32))
		).collect::<Vec<(F,F)>>();

		//4. all states
		let f_allstates_id = F::from(all_states_id as u32);
		let n_states = vec_non_final.len() + vec_final.len();
		let vec_all_states = (0..n_states).
			into_par_iter().map(|i| (f_allstates_id, F::from((i+1) as u32))
		).collect::<Vec<(F,F)>>();

		//4. transitions
		let f_trans_id = F::from(trans_tbl_id);
		let unit = acdfa.state_part_bits;
		let _num_states = acdfa.num_states;
		if B_DEBUG {
			assert!(unit*2 + 4 < 64);
			assert!( (1<<unit) > _num_states );
		}
		let vec_trans = acdfa.trans.par_iter().
			map( |(k, v)|{
				let src = k;
				let mut vec_res = vec![];
				for c in 0..16{
					let dst = v[c];
					let idx_src = acdfa.state_to_idx(*src);
					let idx_dst = acdfa.state_to_idx(dst);
					let trans = c + ((idx_src+1)<<4) + ((idx_dst+1)<<(4+unit));
					if B_DEBUG {
						assert!(idx_src<_num_states && idx_dst<_num_states);
					}

					vec_res.push((f_trans_id, F::from(trans as u64)))
				}
				vec_res
			}).flatten().collect::<Vec<(F,F)>>();

		//5. encode the finals to sigs
		let f_final_2_sig = F::from(state_2_sig_id);
		let f_final_sig_count = F::from(state_sig_count_id);
		let sigbit_factor = F::from(1u32 << read_global_config().range2_bit);
		let sigbit_fac2 = sigbit_factor * sigbit_factor;
		let sigbit_fac3 = sigbit_fac2 * sigbit_factor;

		let vec_temp =  (0..acdfa.num_acc_states).into_par_iter().map(|i|
		//let vec_temp =  (0..acdfa.num_acc_states).into_iter().map(|i|
		{
			let pats = acdfa.final_to_patterns(i);
			let vec_sigs = pats.iter().map(|pat|{
				pat_to_sigs.get(pat).
				expect(&format!("err at get pat: {} for i: {}", pat,i)).to_vec()
			}).flatten().collect::<Vec<String>>();
			let vec_sigs_id = vec_sigs.iter().map(|s|
				*sig_to_id.get(s).expect("sig_2_id err")
			).collect::<Vec<usize>>();
			let res = vec_sigs_id.into_iter().enumerate().map(|(id,sig_id)| {
				// encoded is final_state_idx || id || sig_id 
				let encoded = F::from((i+1) as u32)*sigbit_fac2+ 
							F::from((id+1) as u32) * sigbit_factor+
							F::from(sig_id as u32);  
				(f_final_2_sig, encoded)
			}).collect::<Vec<(F,F)>>();

			( (i+1), res)
		}).collect::<Vec<(usize, Vec<(F,F)>)>>();
		let vec_final_2_sig = vec_temp.par_iter().map(|(_fid, vec)|
			vec.clone()
		).flatten().collect::<Vec<(F,F)>>();

		let vec_final2sig_count = vec_temp.par_iter().map(|(fid, vec)|{
			let f_count = F::from(vec.len() as u32);
			assert!(vec.len()< (1<<read_global_config().range2_bit));
			// encoded as final_state_idx || sig_count
			let encoded = F::from(*fid as u32) * sigbit_factor + f_count;
			(f_final_sig_count, encoded)
		}).collect::<Vec<(F,F)>>();

		//5. encode the finals to pats
		// each encoded word has structure
		// final_state - pat_id -id - count
		// where id starts from 0 and count is the real count -1
		// sig - pat - id - count
		// s1 -  p1  - 0  - 0  (last record)
		// s2 -  p2  - 0  - 1
		// s2 -  p3  - 1  - 1   (last record)
		// NOTE that state_id and pat_id all starts from 1, i.e.,
		// they have +1 from their real ID in acdfa
		let f_final_2_pat = F::from(state_2_pat);
		//5.1 real state to pat tuples
		let mut vec_final_2_pat =  (0..acdfa.num_acc_states).into_par_iter().map(|i|
		{
			let mut pats = acdfa.outputs.get(&i).unwrap().clone();
			pats.sort(); //actually not really necessary.
			let pats = pats.iter().map(|x| F::from(*x as u32) + F::one())
				.collect::<Vec<F>>();
			assert!(pats.len()>0, "pats.len() 0 for raw acc state: {}", i);
			let count_1 = F::from( (pats.len() - 1) as u32);
			let res = pats.into_iter().enumerate().map(|(id,pat_id)| {
				// encoded is (final_state+1) || (pat_id+1) || id || count
				let f_state = F::from((i+1) as u32);
				let encoded = f_state*sigbit_fac3+ 
					pat_id *sigbit_fac2 + 
					F::from(id as u32) * sigbit_factor + 
					count_1;
				(f_final_2_pat, encoded)
			}).collect::<Vec<(F,F)>>();
			res
		}).flatten().collect::<Vec<(F,F)>>();


		//5.2 build the padding tuple (1-tuple for state "0" - dummy entry)
		let f_state = F::zero();
		let pat_id = F::zero();
		let f_id = F::zero();
		let f_count = F::zero(); //1 count -1 is 0from(id as u32);
		let encoded = f_state*sigbit_fac3+ 
				pat_id *sigbit_fac2 + 
				f_id * sigbit_factor + 
				f_count;
		vec_final_2_pat.push( (f_final_2_pat, encoded) );

		//5. assemble
		let v2d = vec![ vec_init, vec_non_final, vec_final, vec_trans,
			vec_final_2_sig, vec_final2sig_count, vec_all_states,
			vec_final_2_pat];
		let mut res = v2d.concat();
		lk.vals.append(&mut res);
	}

	/// add a range table to lookup (the range are INCLUDED, i.e.,
	/// for range (a,b) both a and b are included.
	fn add_range_to_lkup(lk: &mut LookupTableTwoCol_Inst<F>, tbl_id: F, range: (usize,usize)){
		let mut col2 = (range.0..range.1+1).into_par_iter().map(|x|{
			let xval = F::from(x as u32);
			(tbl_id, xval)
		}).collect::<Vec<(F,F)>>();
		lk.vals.append(&mut col2);
	}

	/// mainly add the information of EvalDNF
	/// builds two tables:
	/// (sig, eval_dnf_id) -> count
	/// (sig, eval_dnf_id, step) -> subsig_id
	/// NOTE that the subsig_id is the "REAL" subsig_id without
	/// the part of acdfa_id embedded, as it applies to ALL (instead of
	///    acdfa).
	pub fn add_sig_evaldnf_to_lkup(
		lk: &mut LookupTableTwoCol_Inst<F>, 
		vec_sig_obj: &Vec<Arc<ClamavSig>>,
		sig_to_id: &HashMap<String,usize>
	) {
		//1. generate (sig, eval_dnf_id) -> count
		let info_id:u32 = 0x98882405; 
		let f1 = F::from(info_id);
		let factor = F::from(0x100000000 as u64); //32-bit 
		let mut tuples = vec_sig_obj.par_iter().map(|sig|{
			let sig_name = &sig.name;
			let sig_id = sig_to_id.get(sig_name).expect(
				&format!("cannot find sig: {}", sig_name));
			let f_sig_id = F::from(*sig_id as u64);

			let sig_tuples = sig.eval_dnf.vec_disjunc
				.iter().enumerate().map(|(i,v)|{
				let dnf_id = F::from(i as u64);
				let tbl_id = f1*factor*factor*factor + 
					f_sig_id*factor*factor + dnf_id*factor;
				let count = F::from(v.len() as u64);
				(tbl_id, count)	
			}).collect::<Vec<(F,F)>>();

			sig_tuples
		}).flatten().collect::<Vec<(F,F)>>();
		//add dummy entry for sig 0
		tuples.push((f1*factor*factor*factor, F::zero()));
		lk.vals.append(&mut tuples);

		//2. generate (sig, eval_dnf_id, id) -> subsig_id
		let info_id:u32 = 0x99992405; 
		let f1 = F::from(info_id);
		let mut tuples = vec_sig_obj.par_iter().map(|sig|{
			let sig_name = &sig.name;
			let sig_id = sig_to_id.get(sig_name).expect(
				&format!("cannot find sig: {}", sig_name));
			let f_sig_id = F::from(*sig_id as u64);

			let sig_tuples = sig.eval_dnf.vec_disjunc
				.iter().enumerate().map(|(i,v)|{
				let dnf_id = F::from(i as u64);
				let tbl_id = f1*factor*factor*factor + 
					f_sig_id*factor*factor + dnf_id*factor;

				let step_tuples = v.iter().enumerate().map(|(step,subsig)|{
					let subtbl_id = tbl_id + F::from(step as u64);
					let real_subsig_id = F::from((*subsig+1) as u64);
					(subtbl_id, real_subsig_id)

				}).collect::<Vec<(F,F)>>();

				step_tuples
			}).flatten().collect::<Vec<(F,F)>>();

			sig_tuples
		}).flatten().collect::<Vec<(F,F)>>();
		//add dummy entry for sig 0
		tuples.push((f1*factor*factor*factor, F::zero()));
		lk.vals.append(&mut tuples);
	}

	/// add the init, non-final states, final states, and transitions
	/// of a standard (note not ACDFA) into lookup table.
	/// This is similar to add_acdfa_to_lkup
	fn gen_dfa_lkup(
		dfa: &DFA<char>, 
		tbl_id_init: u32,  //the starting ID of four sub-tables
	)->Vec<(F,F)>
	{
		//1. set up the table IDs
		let init_tbl_id = tbl_id_init;
		let nonfinal_tbl_id = tbl_id_init+1;
		let final_tbl_id = tbl_id_init+2;
		let trans_tbl_id = tbl_id_init+3;
		let all_states_id = tbl_id_init+6;

		//2. build the single entry sub-table for init
		let init_st = dfa.initial as u32;
		let vec_init = vec![(F::from(init_tbl_id+1), F::from(init_st))]; 
		let num_states = dfa.transitions.len();
		let set_states = (0..num_states).collect::<HashSet<usize>>();
		let set_finals = &dfa.finals;
		let set_non_finals = set_states.difference(set_finals)
			.copied()
			.collect::<HashSet<usize>>();

		//3. build the non-final states (index)
		// final states: [0,num_acc_states-1]
		// non-finals: [num_acc_states, 1]
		// here: we just store "state indexes" no need to store their
		// encoded form as sub-table ID distinguish states from different DFAs
		// NOTE: all states starting from 1 (0 used as dummy value)
		let f_nonfinal_tbl_id = F::from(nonfinal_tbl_id);
		let vec_non_final = set_non_finals
			.par_iter().map(|i| (f_nonfinal_tbl_id, F::from((*i+1) as u64))
		).collect::<Vec<(F,F)>>();

		//3. final states
		let f_final_tbl_id = F::from(final_tbl_id);
		let vec_final = set_finals
			.par_iter().map(|&i| (f_final_tbl_id, F::from((i+1) as u32))
		).collect::<Vec<(F,F)>>();

		//4. all states
		let f_allstates_id = F::from(all_states_id as u32);
		let vec_all_states = (0..num_states).
			into_par_iter().map(|i| (f_allstates_id, F::from((i+1) as u32))
		).collect::<Vec<(F,F)>>();

		//4. transitions
		let f_trans_id = F::from(trans_tbl_id);
		let unit = read_global_config().range2_bit;
		if B_DEBUG {
			assert!(unit*2 + 4 < 64);
			assert!( (1<<unit) > num_states );
		}
		let vec_trans = dfa.transitions.par_iter().enumerate()
			.map(|(src,hm)|{
				let vec = hm.iter().map(|(ch, dst)|{
					let trans = (*ch as usize) 
						+ ((src+1)<<4) + ((dst+1)<<(4+unit));
					(f_trans_id, F::from(trans as u64))
				}).collect::<Vec<(F,F)>>();
				vec	
			}).flatten().collect::<Vec<(F,F)>>();

		//5. assemble
		let v2d = vec![vec_init,vec_non_final,vec_final,vec_trans, 
			vec_all_states];

		v2d.concat()
	}

	/// For those sigs which has DFA for its subsigs,
	/// add the encoding of transition and states for each DFA
	pub fn add_sig_dfa_to_lkup(
		lk: &mut LookupTableTwoCol_Inst<F>, 
		vec_sig_obj: &Vec<Arc<ClamavSig>>,
		sig_to_id: &HashMap<String,usize>
	) {
		let b_debug = B_DEBUG;
	
		//1. generate (sig, eval_dnf_id) -> count
		let tuples_all = vec_sig_obj.par_iter()
			.filter(|sig| sig.vec_subsig_automaton.len()>0)
			.map(|sig|{
				let sig_name = &sig.name;
				let sig_id = sig_to_id.get(sig_name).expect(
					&format!("cannot find sig: {}", sig_name));
				assert!(sig.vec_subsig_obj.len()==
					sig.vec_subsig_automaton.len());
				
				let tuples = sig.vec_subsig_automaton.iter().enumerate()
				.map(|(subsig_id,dfa)|{
					let tbl_id = Self::dfa_id(*sig_id as u32, subsig_id as u32);
					if b_debug{
						println!("DEBUG USE 8877.2: produce dfa for {}, subsig_id: {}", sig_name, subsig_id);
					}
					Self::gen_dfa_lkup(&dfa, tbl_id)
				}).flatten().collect::<Vec<(F,F)>>();

				tuples
			}).flatten().collect::<Vec<(F,F)>>();

		//2. generate for dummy (sig=0, subsig=0, dfa=dummy)
		let dummy_dfa = build_trap_dfa();
		let tbl_id = Self::dfa_id(0, 0);
		let tuples_dummy = Self::gen_dfa_lkup(&dummy_dfa, tbl_id);
		let mut tuples = [&tuples_dummy[..], &tuples_all[..]].concat();
		lk.vals.append(&mut tuples);
	}

	/// Save the sig IDs of those that for sure cannot pass
	/// critical pattern approach (usually because of too short patterns)
	pub fn add_sig_no_crit_pat(
		lk: &mut LookupTableTwoCol_Inst<F>, 
		vec_sig_obj: &Vec<Arc<ClamavSig>>,
		sig_to_id: &HashMap<String,usize>
	) {
		let mut vec_sig_ids = vec_sig_obj.iter().map(|sig|
			*sig_to_id.get(&sig.name)
				.expect(&format!("cannot find sig: {}", sig.name))
		).collect::<Vec<usize>>();
		vec_sig_ids.sort();
		let count = vec_sig_ids.len();
		let tuples = vec_sig_ids.iter().enumerate().map(|(i, id)|{
			(
				F::from((ID_SIG_NO_CRIT + i as u32 +1u32) as u32), 
				F::from(*id as u64)
			)
		}).collect::<Vec<(F,F)>>();
		let count_tuple = (F::from(ID_SIG_NO_CRIT_COUNT),F::from(count as u64));
		let mut tuples = [&tuples[..], &[count_tuple]].concat();
		lk.vals.append(&mut tuples);
	}

	#[inline(always)]
	pub fn gen_sig_info_id(
		sig_id: usize,
		piece_id: u32, //like ID_SIG_DNVEVAL_COUNT
	)->F{
		//we set f1 to f4 order so that the entries when added
		//are easily sorted.
		let info_id:u32 = 0x99992405; //compared with other entries, the largest
		let f1 = F::from(info_id);
		let f3 = F::from(sig_id as u32);
		let f4 = F::from(piece_id);
		let factor = F::from(0x100000000 as u64); //32-bit 

		let res:F = f1*factor*factor + f3*factor + f4; //96-bit
		res
	}


	/// add the corresponding ACDFA and subsig_store to the lkup
	/// might throw CapErr: proj_store::n
	fn add_bundle_subsig_to_lkup(lkup: &mut LookupTableTwoCol_Inst<F>, 
		sig_to_id: &HashMap<String,usize>, 
		bundle: &BundleSubsigStore,
		b_igc: bool,
	)->Result<(), Error>{
		let state_bits = bundle.vec_acdfa[0].state_part_bits;
		for i in 0..bundle.vec_sig_names.len(){
			let sig_id:usize = if i==0 {0} 
				else {*sig_to_id.get(&bundle.vec_sig_names[i]).expect(
					&format!("can't find sig: {}",bundle.vec_sig_names[i]))};
			let dfa_id = Self::pm_acdfa_id(sig_id, b_igc); 
			Self::add_acdfa_to_lkup(lkup,&bundle.vec_acdfa[i],
				dfa_id, &bundle.vec_map_pattern_sig[i], sig_to_id);
			//bundle.vec_subsig_stores[i]
			//	.add_store_to_lkup(lkup, dfa_id, state_bits)?;
			// SubsigPatternStore no longer needed
			// replaced by state_2_pat in acc_dfa.
			bundle.vec_subsig_step_stores[i]
				.add_store_to_lkup(lkup, dfa_id, state_bits);
			bundle.vec_subsig_info_stores[i]
				.add_store_to_lkup(lkup, dfa_id, state_bits);
		}
		Ok( () )
	}

	/// return the subsig_id to the state id in ACDFA for the
	/// given selected sigs (assuming their patten words are
	/// already contained in acdfa.
	/// We assume that each selected sig has ALREADY got 
	/// gen_approx_bounds for appropriage CONFIG called BEFORE this call.  
	/// NOTE: ISED has LOWER min_word_bound cfg!, but general
	/// SED has the default cfg.
	/// SPECIFIC note: WE assume that sigs NEVER have same names
	/// Return(the Store, map_pat). where map pat returns
	/// a vector of sigs for a given word pattern
	fn build_store(
		sig_to_id: &HashMap<String,usize>,
		selected_sigs: &Vec<Arc<ClamavSig>>,
		acdfa: &HexACDFA,
		b_igc: bool
	)-> ((SubsigPatternStore,SubsigStepStore,SubsigInfoStore), 
		HashMap<String, Vec<String>>)
	{
		//1. generate tuples to insert for each sig, and subsig object
		let b_debug = B_DEBUG;
		let b_debug_subsig = false;
		let set_subsig_to_debug = vec![
			"36551681", "36598786", "36556803", "37690369", "36552705", 
			"37897218", "19382275", "36260869", "19377157", "36260865", 
			"19191811", "37218306", "37218307", "37218308", "37218309", 
			"37218310", "37218311", "37214209", "36553731", "36164609", 
			"35836932", "35442690", "129"
		].iter().map(|x| format!("{}",x)).collect::<HashSet<String>>();
		let store_items = selected_sigs.par_iter().map(|s|{
			let sig_id = sig_to_id.get(&s.name)
				.expect(&format!("can't find sig: {}", s.name));
			let mut store_items = vec![]; //for store_pat
			let mut store_step_items = vec![]; //for store_steps
			let mut store_info_items = vec![]; //for SubsigInfoStore
			for i in 0..s.vec_subsig_obj.len(){
				//1. generate the subsig id
				let subsig_id = acdfa.gen_subsig_id(*sig_id, i+1);
				if b_debug{
					println!("DEBUG USE 6101: add: SIG_ID: {}, igc: {}, subsig_id: {}, details:{} ", sig_id, s.vec_subsig_obj[i].b_ignore_case, subsig_id, s.vec_subsig_obj[i].value);
				}
				if b_debug_subsig && 
				  set_subsig_to_debug.contains(&format!("{}",subsig_id)){
					println!("DEBUG USE 9101: add: SIG: {}, igc: {}, subsig_id: {}, details:{} ", s.name, s.vec_subsig_obj[i].b_ignore_case, subsig_id, s.vec_subsig_obj[i].value);
				}

				//2. retrieve the words from the pattern.
				let words = s.vec_subsig_pm_bounds[i].iter().map(|x|
					x.0.clone()).collect::<Vec<String>>();
				let words = if b_igc==s.vec_subsig_obj[i].b_ignore_case{
					words
				}else{ vec![] };
				let set_words = words.iter().map(|x| x.clone()).
					collect::<HashSet<String>>();
				let set_word_ids = set_words.iter().map(|s|
					*acdfa.pattern_to_id.get(s)
						.expect(&format!("err find {}",s))
				).collect::<HashSet<usize>>();

				//3. convert the words to state IDs in acdfa
				let set_state_ids= set_words.iter().map(|w|{
					let state_id = acdfa.word_to_state_id(w);
					state_id
				}).flatten().collect::<HashSet<usize>>();
				//4. from each state -> vec_word_id (but restricts to set_words)
				let tuples = set_state_ids.iter().map(|s|{
					//1. get the words
					let output_word_ids = 
						acdfa.outputs.get(s).expect("err oup")
						.iter().map(|x| *x)
						.collect::<HashSet<usize>>();

					//2. restrict to set_words
					//now adjust id+1
					let mut restricted_word_ids = output_word_ids
						.intersection(&set_word_ids)
						.map(|x| *x+1).collect::<Vec<usize>>();
					restricted_word_ids.sort();
			
					//3. construct the tuples
					(*s+1, restricted_word_ids)
				}).collect::<Vec<(usize, Vec<usize>)>>();
				let item = SubsigPatternStoreItem::new(subsig_id, tuples); 
				store_items.push(item);

				//4. build the store_items for step item 
				let max:usize = (1<<read_global_config().range2_bit) - 1;
				let vec_bounds = if b_igc!=s.vec_subsig_obj[i].b_ignore_case{
					vec![]
				}else{//process it
					s.vec_subsig_pm_bounds[i].iter().map(|x|{
						let word = x.0.clone();
						let (a,b) = (x.1.0, x.1.1);
						let word_id = *acdfa.pattern_to_id.get(&word).unwrap();
						let wlen = word.len();
						let (na,nb) = (
							if a!=usize::MAX {a+wlen} else {max}, 
							if b!=usize::MAX {b+wlen} else {max}
						);
						let (na,nb) = (if na>max {max} else {na},
							if nb>max {max} else {nb});
							
						(word_id+1,(na,nb))
					
					}).collect::<Vec<(usize,(usize,usize))>>()
				};
				// DEBUG USE 64009: per-(sig,subsig) dump of the
				// CIRCUIT-side pat_id (= acdfa word_id + 1) for
				// each pm-bound entry. Use this to resolve the
				// StepQueueItem.pat field back to a literal word.
				if std::env::var("ZKR_PROBE_64009").is_ok()
					&& s.name == "Bora.Email.DLProx.SSN.B1" {
					for (j, x) in s.vec_subsig_pm_bounds[i]
						.iter().enumerate() {
						let word = &x.0;
						let wid_raw = *acdfa.pattern_to_id
							.get(word).unwrap();
						println!("DEBUG USE 64009.c sig={} \
							subsig_idx={} step_idx={} \
							circ_pat_id={} word={} \
							rg=({},{})",
							s.name, i, j+1,
							wid_raw+1, word, x.1.0, x.1.1);
					}
				}
				// DEBUG USE 69200.c.patmap: circuit-side
				// (pat_id <-> word) for the two known-failing
				// sig_ids. Emitted once per (sig, subsig, igc)
				// at SubsigStepStore construction time. Pairs
				// with 69200.h.bounds (host side) and lets the
				// offline verifier resolve circuit pat_ids back
				// to the original byte/hex words.
				if std::env::var("ZKR_PROBE_69200").is_ok()
					&& (*sig_id == 34555usize
						|| *sig_id == 35355usize) {
					for (j, x) in s.vec_subsig_pm_bounds[i]
						.iter().enumerate() {
						let word = &x.0;
						let wid_raw = *acdfa.pattern_to_id
							.get(word).unwrap();
						let wid_circ = wid_raw + 1;
						println!("DEBUG USE \
							69200.c.patmap: \
							sig_id={} subsig_idx={} \
							subsig_id={} igc={} \
							chain_idx={} \
							pat_id_raw={} \
							pat_id_circ={} \
							word=\"{}\" \
							orig_rg=({},{})",
							sig_id, i, subsig_id,
							b_igc, j, wid_raw,
							wid_circ, word,
							x.1.0, x.1.1);
					}
				}
				let item = SubsigStepStoreItem{subsig_id: subsig_id,
					igc: s.vec_subsig_obj[i].b_ignore_case,
					vec_pm_bounds: vec_bounds,
					// keyword-rightmost (anchor_dir==1) => backward.
					// anchor_dir is only populated under aggressive
					// mode, so this is false (empty) when flag-off.
					is_backward:
						s.vec_subsig_anchor_dir.get(i)==Some(&1)};
				store_step_items.push(item);

				//5. build the subsig_step_info_store_item 
				let subsig_obj = &s.vec_subsig_obj[i];
				if subsig_obj.b_ignore_case==b_igc{
					//only add it when the same igc mode
					let subsig_type = subsig_obj.subsig_type.clone() as u8;
					let (comp_op, comp_num, min_required, 
						component_subsigs) = match subsig_obj.subsig_type{
						SubSigType::GeneralRegex=>{
							//dummy values 0 for all
							//comp_op, comp_num, min_required, vec_component_subsig
							(0u8, 0u32, 0usize, vec![])
						},
						SubSigType::CounterConstraint=>{
							let sig = &subsig_obj.value;
							if !is_match(r"^\d+( *)(=|<|>|==)( *)\d+$", sig){
								panic!("INVALID counter sig: {}", sig);
							}
							let num = extract_nums(&sig)[1]; 
							let sop = find_only(r">|<|=", &sig);
							let (op, num) = ClamavSig::strop_to_comp_op(&sop, num);
							let op = op as u8;
							let num = num as u32;
							(op, num, 0usize, vec![])
						},
						SubSigType::SubsigCountConstraint=>{
							let min_req = subsig_obj.min_required;
							let mut vec_component_subsig_ids = subsig_obj
								.set_subsigs.iter().map(|cid|
									acdfa.gen_subsig_id(*sig_id, cid+1)
								).collect::<Vec<usize>>();
							vec_component_subsig_ids.sort();
							(0, 0, min_req, vec_component_subsig_ids)
						},
					};
					let item = SubsigInfoStoreItem{subsig_id,
						subsig_type,
						comp_op,
						comp_num,
						min_required,
						component_subsigs,
					};
					store_info_items.push(item);
				}//end of check IGC
			}
			(store_items,store_step_items, store_info_items)
		}).collect::<Vec<(Vec<SubsigPatternStoreItem>,
			Vec<SubsigStepStoreItem>,Vec<SubsigInfoStoreItem>)>>();
		let store_items_pat = store_items.par_iter().map(|t|
			t.0.clone()).flatten().collect::<Vec<SubsigPatternStoreItem>>();
		let store_items_step = store_items.par_iter().map(|t|
			t.1.clone()).flatten().collect::<Vec<SubsigStepStoreItem>>();
		let store_items_info= store_items.par_iter().map(|t|
			t.2.clone()).flatten().collect::<Vec<SubsigInfoStoreItem>>();

		//2. build the store
		let mut store_pat = SubsigPatternStore::new();
		for item in store_items_pat{
			store_pat.add(&item);
		}
		store_pat.finalize();

		//3. build the store2: SubsigStepStore
		let mut store_step = SubsigStepStore::new();
		// DB self-mark: anchor_dir is populated only under aggressive
		// mode (build_db Step 1b), so a non-empty anchor_dir on any
		// selected sig means this is an aggressive build.
		store_step.b_aggressive = selected_sigs.iter()
			.any(|s| !s.vec_subsig_anchor_dir.is_empty());
		for item in store_items_step{
			store_step.add(&item);
		}
		store_step.finalize();

		//4. build the store3: SubsigInfoStore
		let mut store_info = SubsigInfoStore::new();
		for item in store_items_info{
			store_info.add(&item);
		}
		store_info.finalize();

		//3. build the map from words to sigs
		let mut map = HashMap::<String,Vec<String>>::new();
		let tuples = selected_sigs.par_iter().map(|s|{
			let words = s.collect_bagwords_from_pmreg(b_igc);
			words.iter().map(|w| (w.clone(), s.name.clone()))
				.collect::<Vec<(String,String)>>()
		}).flatten().collect::<Vec<(String,String)>>();
		for t in tuples{
			map.entry(t.0).or_insert(vec![]).push(t.1);
		}
		//add a dummy entry for the alpha bet string for ACDFA to cover
		//all alphabet (required by underling lib).
		let dfa_alpha_str = "0123456789abcdef190918230981212fa".to_string();
		if !map.contains_key(&dfa_alpha_str){
			map.insert(dfa_alpha_str, vec![]);
		}

		((store_pat, store_step, store_info), map)
	}


	/// Given the file which has the list of signatures that needs
	/// ISED (indisidual SED approach), generates:
	/// (1) lsit of signature names
	/// (2) correspoding BAG word ACDFA (using no word- lower-bound limit 
	///	restriction.
	/// (3) for each: the subpatten store (subsig, sate, pat)
	/// (4) patten_to_sig map 
	/// To save efforts, the 0'th entry of all is for the GENERAL SED
	/// approach (sigs for all).
	fn build_ised_bundle(
		sigs: &Vec<Arc<ClamavSig>>, //vec of sig objects
		sig_to_id: &HashMap<String,usize>,
		needs_ised_list_file: &str, //filename that needs ised handling
		b_igc: bool,  //whether it's ignore cases
		cfg: &ClamavApproxConfig,  //cfg used by build_db
	) -> BundleSubsigStore{
		let b_debug = B_DEBUG;
		//1. read the signatures
		let sig_names_need_ised
			=read_lines(needs_ised_list_file).iter().filter(|s|
			!s.starts_with("#")).map(|s| s.trim().to_string())
			.collect::<Vec<String>>();

		//2. locate the sigs for sigs_needs_ised
		// as there are up to 200 sigs to process, we simply do linear search
		// only 50 ms.
		let sigs_needed = sig_names_need_ised.iter().map(|s|{
			//1. find the sig
			let res:Vec<Arc<ClamavSig>> = 
				sigs.par_iter().filter(|g| g.name==*s)
				.map(|g| g.clone()).collect();
			assert!(res.len()==1, "either not find or multiple for: {}", s);
			let mut sig = res[0].as_ref().clone();

			//2. instrument the sig for pm bounds
			let mut new_cfg = cfg.clone();
			new_cfg.min_pm_word_len= 0;
			sig.gen_approx_pm_bounds(&new_cfg); //for ISED specifically.

			Arc::new(sig)
		}).collect::<Vec<Arc<ClamavSig>>>();
		let mut sigs_needed_2d = sigs_needed.par_iter().map(|x|
			vec![x.clone()]).collect::<Vec<Vec<Arc<ClamavSig>>>>();

		//3. build the ISED ACDFA for the signature
		let vec_ised_acdfa = sigs_needed.par_iter().map(|s|{
			let bag_pm = s.collect_bagwords_from_pmreg(b_igc); 
			let mut vec_pm = bag_pm.iter().map(|s| s.clone())
				.collect::<Vec<String>>();
			vec_pm.push("0123456789abcdef190918230981212fa"
				.to_owned());//to satisfy hex alphbet
			let dfa_pm = HexACDFA::new(0, &vec_pm);

			dfa_pm
		}).collect::<Vec<HexACDFA>>();

		//5. build the store
		let (vec_store, vec_map_pat)= sigs_needed
			.par_iter().zip(vec_ised_acdfa.par_iter()).map(|(s,a)|{
				Self::build_store(&sig_to_id, &vec![s.clone()],a, b_igc) 
			}).collect();

		//6. build the general case
		//6.1 build the dfa for ALL sigs with REGULAR config
		let mut pats = (&sigs).into_par_iter().map(|s| 
			s.collect_bagwords_from_pmreg(b_igc)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		pats.sort();
		//TODO: fix later: needs to use new_adv with igc
		if b_debug && b_igc{
			println!("DEBUG USE 6105: in build_sed_bundle 0: b_igc: {}, pats: {:#?}", b_igc, pats);
		}
		let all_acdfa = HexACDFA::new_adv(0, &pats, b_igc);

		//6.2 build the store and append it to all
		let (store_0,map_pat_0) = Self
			::build_store(&sig_to_id, sigs, &all_acdfa, b_igc);
		let names = vec![vec!["all".to_string()], sig_names_need_ised].concat();
		let n = names.len();
		let dfas = vec![vec![all_acdfa.clone()], vec_ised_acdfa].concat();
		let stores = vec![vec![store_0], vec_store].concat();
		let stores_pat = stores.par_iter().map(|x| x.0.clone()).collect();
		let stores_step = stores.par_iter().map(|x| x.1.clone()).collect();
		let stores_info = stores.par_iter().map(|x| x.2.clone()).collect();
		let map_pats = vec![vec![map_pat_0], vec_map_pat].concat();
		let mut vec_2d_sigs = vec![sigs.clone()]; 
		vec_2d_sigs.append(&mut sigs_needed_2d);
		assert!(stores.len()==n && map_pats.len()==n && vec_2d_sigs.len()==n
			&& dfas.len()==n);

		BundleSubsigStore{
			b_igc,
			vec_sig_names: names,
			vec_sigs: vec_2d_sigs, 
			vec_map_pattern_sig: map_pats,
			vec_acdfa: dfas,
			vec_subsig_stores: stores_pat,
			vec_subsig_step_stores: stores_step,
			vec_subsig_info_stores: stores_info,
		}

	}

	/// generate the store tbl_id for the sig_id.
	/// Note that for individual SIG, its id starts from 1.
	/// when sig_id is 0, it stands for ALL. 
	/// It returns the corresponding ACDFA sub-tbl_id
	/// This id stands for the INIT state of that ACDFA.
	/// following that we have 
	/// (INIT, NON_FINAL, TRANSITIONS, STATE_2_SIG, STATE_SIG_COUNT
	///  CRIT_STATES, STORE_SUBSIG) 
	pub fn pm_acdfa_id(sig_id: usize, b_igc: bool)->u32{
		let start:u32 = if !b_igc {0x20000000} else {0x30000000};
		let mixed = start + ((sig_id as u32)<<8); //leave about 16 subtbls

		mixed
	}

	/// Here we assume sig_id is at most 13-bit,
	/// subsig_id is at most 6-bit
	/// there will be no-conflicts with pm_acdfa_id
	pub fn dfa_id(sig_id: u32, subsig_id: u32)-> u32{
		//allows about 256 subtbls
		let start:u32 = 0x40000000;
		let mixed = start + ((sig_id as u32)<<8) + subsig_id; 

		mixed
	}

	/// Given a collection of signatures, write them to disk
	/// and  build the DB
	pub fn build_test_db(
		cfg: &ClamavApproxConfig, 
		sigs_dir: &str,
		sigs: &Vec<String>, 
		needs_dfa: &Vec<String>,
		needs_ised: &Vec<String>,
		needs_ised_igc: &Vec<String>)
	-> Result<Self, Error>{
		//padded sig to enforce full alphabet
		let sigs = vec![
			sigs.clone(),
			vec!["sig_alpha01;Engine:51-255,Target:0;0|1;123456789abcdef0123;432345678901abcdef::i".to_string()], 
		].concat(); 
		write_sigs_to_dir(&sigs, sigs_dir, needs_dfa, 
			needs_ised, needs_ised_igc);
		let db = Self::build_db_from_dir_adv(sigs_dir, &cfg);

		db
	}

	/// This is the easy version for build_db. We assume the
	/// dir is RELATIVE path to project root/data, 
	/// and it consits of the following:
	/// sigs.db - signatures
	/// needs_dfa.txt - the list of sigs that need dfa
	/// needs_ised.txt - the list of sigs that need ised (regular)
	/// needs_ised_igc.txt - the list of sigs that need ised (ignore case)
	/// This function is mainly for debugging purpose. It does NOT save
	/// or load
	pub fn build_db_from_dir(dir: &str)->Result<Self, Error>{
		let cfg = default_clamav_cfg(); 
		Self::build_db_from_dir_adv(dir, &cfg)
	}
	pub fn build_db_from_dir_adv(dir: &str, cfg: &ClamavApproxConfig)->Result<Self, Error>{
		let cfg = cfg.clone();
		let rt = proj_root();
		let sig_file= format!("{}/data/{}/sigs.db",rt,dir);
		let needs_dfa_file = format!("{}/data/{}/needs_dfa.txt",rt , dir);
		let needs_ised_file= format!("{}/data/{}/needs_ised.txt",rt , dir);
		let needs_ised_igc_file=format!("{}/data/{}/needs_ised_igc.txt",rt,dir);
		let mut vlog = vec![];


		Self::build_db(&sig_file, &needs_dfa_file, &needs_ised_file,
			&needs_ised_igc_file, &cfg, &mut vlog)
	}

	/// build DB from two files: (1) a list of signatures (2) a list
	/// of signature names that need DFA built (in practice, only several
	/// signatures would need DFA), and also
	/// the list of sigs that needs ised and ised_igc. 
	/// Returns a ClamavDB object
	pub fn build_db(sig_file: &str, 
		needs_dfa_list_file: &str, 
		needs_ised_list_file: &str,
		needs_ised_igc_list_file: &str,
		cfg: &ClamavApproxConfig, vlog: &mut Vec<String>)->Result<Self, Error>{
		let log_level = LOG2;
		let b_perf = true && log_level>=read_global_config().log_level;
		let b_debug = B_DEBUG;
		let mut timer = Timer::new();
		//1. generate all signatures
		let set_need_dfa = read_lines(needs_dfa_list_file).iter().filter(|s|
			!s.starts_with("#")).map(|s| s.trim().to_string())
			.collect::<HashSet<String>>();
		let subset_lines = read_lines(sig_file).iter().filter(|s|
			!s.starts_with("#") && !s.trim().is_empty())
			.map(|s| s.to_string())
			.collect::<Vec<String>>();
		let v_sigs:Vec<Arc<ClamavSig>> = subset_lines.iter().map(
			|s| Arc::new(gen_clamav_sig(s, ClamSigType::General,cfg)) )
			.collect();
		let mut v_sigs = v_sigs.par_iter().map(|s1| {
			let mut s = s1.as_ref().clone();
			s.gen_approx_bagwords(cfg);
			s.gen_approx_pm_bounds(cfg);
			if set_need_dfa.contains(&s.name){
				s.set_vec_automaton(cfg);
			}
			s
		}).collect::<Vec<ClamavSig>>();
		//1b. aggressive shape guard + global halo span (flag-on only).
		let mut aggressive_max_span_nibbles = 0usize;
		if cfg.b_aggressive_sde_for_rep {
			for s in v_sigs.iter_mut() {
				let (span, anchors) = s.compute_aggressive_shape(cfg)
					.map_err(|e| Error::Other(format!(
						"AggressiveShapeErr in sig {}: {:?}",
						s.name, e)))?;
				s.vec_subsig_anchor_dir = anchors;
				// DLP restriction: reversal of a keyword-rightmost
				// (backward) chain drops the leftmost begin-offset.
				// Dropping it is discharge-sound (only broadens
				// candidate positions => more Maybe => fewer
				// discharges). An UPPER-UNBOUNDED begin (begin.1==MAX,
				// "anywhere") is also exactly equivalent; a lower-
				// bounded (k,MAX) begin (e.g. the degenerate '000'
				// fan-out variant whose digit bagword was dropped) is
				// a sound over-approximation. Reject only a genuine
				// upper-BOUNDED absolute anchor (begin.1 finite, like
				// ^.{0,10}), which is not a DLP proximity shape.
				for (i, &d) in s.vec_subsig_anchor_dir.iter().enumerate() {
					if d != 1 { continue; }
					if let Some(first) = s.vec_subsig_pm_bounds.get(i)
						.and_then(|v| v.first()) {
						if first.1.1 != usize::MAX {
							return Err(Error::Other(format!(
								"AggressiveShapeErr: backward subsig {} \
								 of sig '{}' has upper-bounded begin {:?}; \
								 not a DLP proximity shape", i, s.name,
								first.1)));
						}
					}
				}
				aggressive_max_span_nibbles =
					aggressive_max_span_nibbles.max(span);
				s.assert_aggressive_consistent();
			}
		}
		if b_perf {flog_perf(0, log_level, &format!("Build_DB: Step 1: Generate signatures"), &mut timer,
			vlog);}
		if b_perf {flog_perf(0, log_level, &format!("Bluld_DB: Step 2: Writing signatures"), &mut timer,
			vlog);}

		//2. collect critical pattern
		let mut map_crit_pat = HashMap::<String,Vec<String>>::new();
		let mut map_crit_pat_igc = HashMap::<String,Vec<String>>::new();
		for i in 0..v_sigs.len(){ 
			let b_res = v_sigs[i]
				.add_critical_pattern(&mut map_crit_pat,&mut map_crit_pat_igc); 
			v_sigs[i].b_no_crit_pat = !b_res;
		}
		let v_sigs = v_sigs.iter().map(|s|
			Arc::new(s.clone())
		).collect::<Vec<Arc<ClamavSig>>>();
		let v_sigs_no_critical_pat = v_sigs.iter().filter(|s| s.b_no_crit_pat)
			.map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();

		if b_perf {flog_perf(0, log_level, &format!("Build_DB: Step 3: Extract Critial Patterns."), 
				&mut timer, vlog);}
		if b_debug{
			//check if each signature is contained in map_crit_pat
			//or map_crit_pat_igc
			let set_sigs_gc = map_crit_pat.values().cloned()
				.collect::<Vec<Vec<String>>>().
				iter().flat_map(|s| s.clone()).
				collect::<HashSet<String>>();
			let set_sigs_igc = map_crit_pat_igc.values().cloned()
				.collect::<Vec<Vec<String>>>().
				iter().flat_map(|s| s.clone()).
				collect::<HashSet<String>>();
			let set_sigs = set_sigs_gc.union(&set_sigs_igc).cloned().
				collect::<HashSet<String>>();
			let set_sigs2 = v_sigs.iter().map(|v| v.name.clone())
				.collect::<HashSet<String>>();
			let set_diff = set_sigs2.difference(&set_sigs).cloned()
				.collect::<HashSet<String>>();
			if set_diff.len()>0{//if different it's because v_sigs_no_crit_pat
				assert!(v_sigs_no_critical_pat.len() == set_diff.len());	
				//println!("ERROR: set_diff of computed: {:?}", set_diff);
				//assert!(set_sigs==set_sigs2, 
				//	"set_sigs.len(): {} != set_sigs2: {}",
				//	set_sigs.len(), set_sigs2.len() );
			}
		}

		//3. build dfas for critical pattern	
		let vec_crit_pat = map_crit_pat.keys().cloned()
			.collect::<Vec<String>>();
		println!("DEBUG USE 60777.1: vec_crit_pat (CS) len={} \
			pats={:?}", vec_crit_pat.len(), vec_crit_pat);
		let dfa_crit = HexACDFA::new(0, &vec_crit_pat);
		println!("DEBUG USE 60777.2: dfa_crit num_states={} \
			num_acc_states={} outputs.len={}",
			dfa_crit.num_states, dfa_crit.num_acc_states,
			dfa_crit.outputs.len());
		let vec_crit_pat_igc = map_crit_pat_igc.keys().cloned()
				.collect::<Vec<String>>();
		//RECOVER LATER: we changed false to true. Keep it
		//if data is correct.
		println!("DEBUG USE 60777.3: vec_crit_pat_igc len={} \
			pats={:?}", vec_crit_pat_igc.len(), vec_crit_pat_igc);
		let dfa_crit_igc = HexACDFA::new_adv(0, &vec_crit_pat_igc, true);
		println!("DEBUG USE 60777.4: dfa_crit_igc num_states={} \
			num_acc_states={} outputs.len={}",
			dfa_crit_igc.num_states, dfa_crit_igc.num_acc_states,
			dfa_crit_igc.outputs.len());
		if b_perf {flog_perf(0, log_level, 
			&format!("Build_DB: Step 4: Build ACDFA of Critial Patterns."),&mut timer,vlog);
		}
		if b_debug{
			println!("DEBUG USE 6100: build_store: crit pat: {:#?}\n, crit_pat_igc: {:#?}", vec_crit_pat, vec_crit_pat_igc);
		}

		//4. generate bag of words
		let pats = (&v_sigs).into_iter().map(|s| 
			s.collect_bagwords_from_pmreg(false)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();

		let pats_igc = (&v_sigs).into_iter().map(|s| 
			s.collect_bagwords_from_pmreg(true)).flat_map(|s| s).
			collect::<HashSet<String>>().into_iter().map(|s| s)
			.collect::<Vec<String>>();
		if b_perf {flog_perf(0, log_level, &format!("Build_DB: Step 5: Build Bag-of-Words."), &mut timer, vlog);}

		if b_debug{
			println!("DEBUG USE 6101: BAGWORDS pats: {:#?}\n -- pats_igc: {:#?}", pats, pats_igc);
		}

		//5. build DFA for bag of words (also for pm)
		// -- SKIPPED, it is vec_acdfa[0] of bundle_subsig now.

		//6. build sig_to_id
		let mut sig_to_id = HashMap::<String,usize>::new();
		for (id, s) in v_sigs.iter().enumerate(){
			sig_to_id.insert(s.name.clone(), id+1);
		}
		if std::env::var("ZKR_PROBE_64006").is_ok() {
			let mut rows: Vec<(usize, String)> = sig_to_id.iter()
				.map(|(n, id)| (*id, n.clone())).collect();
			rows.sort_by_key(|r| r.0);
			for (id, name) in &rows {
				println!("DEBUG USE 64006 sig_id={} name={}",
					id, name);
			}
		}
		if std::env::var("ZKR_PROBE_64007").is_ok() {
			//pm_bounds dump for SSN.B1 (sig_id=5), subsig_id=2.
			let target = "Bora.Email.DLProx.SSN.B1";
			for s in v_sigs.iter() {
				if s.name != target { continue; }
				let n = s.vec_subsig_pm_bounds.len();
				println!("DEBUG USE 64007.head sig={} \
					n_subsigs={}", s.name, n);
				let target_sub = 2usize;
				if target_sub >= n { continue; }
				let pm = &s.vec_subsig_pm_bounds[target_sub];
				println!("DEBUG USE 64007 sig={} subsig={} \
					n_pats={}",
					s.name, target_sub, pm.len());
				for (k, (w, (lo, hi))) in pm.iter().enumerate() {
					println!("DEBUG USE 64007.row sig={} \
						subsig={} pat_id={} word={} \
						min_gap={} max_gap={}",
						s.name, target_sub, k+1, w, lo, hi);
				}
			}
		}

		//7. build the stores of information for SED and ISED
		let bundle_subsig= 
			Self::build_ised_bundle(&v_sigs, &sig_to_id, 
				needs_ised_list_file, false, cfg); 
		let bundle_subsig_igc=
			Self::build_ised_bundle(&v_sigs, &sig_to_id, 
				needs_ised_igc_list_file, true, cfg); 
		if b_perf {flog_perf(0, log_level, &format!("Build_DB: Step 6: Build SED bundles."), &mut timer, vlog);}

		//8. build lkup
		let mut lkup = LookupTableTwoCol_Inst::<F>::dummy();
		Self::add_char_map(&mut lkup);
		Self::add_trival_rules(&mut lkup);
		Self::add_acdfa_to_lkup(&mut lkup, &dfa_crit, CRIT_INIT, &map_crit_pat, &sig_to_id);
		Self::add_acdfa_to_lkup(&mut lkup, &dfa_crit_igc, CRIT_IGC_INIT, &map_crit_pat_igc, &sig_to_id);
		Self::add_range_to_lkup(&mut lkup, F::from(CHAR), (0,16));
		Self::add_range_to_lkup(&mut lkup, F::from(RANGE2), (0,1<<read_global_config().range2_bit));
		Self::add_bundle_subsig_to_lkup(&mut lkup, &sig_to_id, &bundle_subsig, false)?;
		Self::add_bundle_subsig_to_lkup(&mut lkup, &sig_to_id, &bundle_subsig_igc, true)?;
		Self::add_sig_evaldnf_to_lkup(&mut lkup, &v_sigs, &sig_to_id); 
		Self::add_sig_dfa_to_lkup(&mut lkup, &v_sigs, &sig_to_id);
		Self::add_sig_no_crit_pat(&mut lkup, &v_sigs_no_critical_pat, 
			&sig_to_id);
		lkup.vals.sort();
		if b_perf {flog_perf(0, log_level, &format!("Build_DB: Step 7: ADD all to lkup. Lkup size: {}", lkup.vals.len()), &mut timer, vlog);}

		//9. build the object
		let res = Self{
			vec_sigs: v_sigs,
			vec_sigs_no_critical_pat: v_sigs_no_critical_pat,
			map_crit_pat: map_crit_pat,
			map_crit_pat_igc: map_crit_pat_igc,
			vec_crit_pat: vec_crit_pat,
			vec_crit_pat_igc: vec_crit_pat_igc,
			dfa_crit: dfa_crit,
			dfa_crit_igc: dfa_crit_igc,
			vec_bag_words: pats,
			vec_bag_words_igc: pats_igc,
			sig_to_id: sig_to_id,
			lkup: lkup,
			
			bundle_subsig: Arc::new(bundle_subsig),
			bundle_subsig_igc: Arc::new(bundle_subsig_igc),
			aggressive_max_span_nibbles,

		};

		Ok(res)
	}
	
	/// print summary in console, and append to vlog
	pub fn print_summary(&self, vlog: &mut Vec<String>){
		flog(0, LOG1, &format!("==== Summary of ClamavSig Database ===="), vlog);
		flog(0, LOG1, &format!("#critical patterns: {} (CS) {} (IGC), #sigs: {}, ACDFA for Critical Pattenrs State: {} (CS) {} (IGC)", self.map_crit_pat.len(), self.map_crit_pat_igc.len(), self.vec_sigs.len(), self.dfa_crit.num_states, self.dfa_crit_igc.num_states), vlog);
		flog(0, LOG1, &format!("Signatures:{}, Fixed Patterns: {}, Pattners IGC: {}", self.vec_sigs.len(), self.vec_bag_words.len(), self.vec_bag_words_igc.len()), vlog);
		flog(0, LOG1, &format!("ACDFA for BagWords: states (cs): {}, states (igc): {}", self.bundle_subsig.vec_acdfa[0].num_states, self.bundle_subsig_igc.vec_acdfa[0].num_states), vlog);
		self.dfa_crit.log_stats_adv("dfa_crit", &self.map_crit_pat, &self.sig_to_id, vlog);
		self.dfa_crit_igc.log_stats_adv("dfa_crit_igc", &self.map_crit_pat_igc, &self.sig_to_id, vlog);
		self.bundle_subsig.vec_acdfa[0].log_stats("dfa_patterns", vlog);
		self.bundle_subsig_igc.vec_acdfa[0].log_stats("dfa_patterns_igc", vlog);
	}

	/// dir_name has to be an alphanum file name (no path separators and ..)
	pub fn save(&self, dir_name: &str){
		create_new_cache_dir(dir_name); //it validates that it's a valid name
		let sdir = format!("{}/data/cache/{}/", &proj_root(), dir_name);

		let s_sigs= serde_json::to_string(&self.vec_sigs).unwrap();
		write_to_file(&format!("{}/vec_sigs.txt", &sdir), &s_sigs);
		let s_crit_pat= serde_json::to_string(&self.vec_crit_pat).unwrap();
		write_to_file(&format!("{}/vec_crit_pat.txt", &sdir), &s_crit_pat);
		let s_crit_pat_igc= serde_json::to_string(&self.vec_crit_pat_igc).unwrap();
		write_to_file(&format!("{}/vec_crit_pat_igc.txt", &sdir), &s_crit_pat_igc);
		let s_bag_words= serde_json::to_string(&self.vec_bag_words).unwrap();
		write_to_file(&format!("{}/vec_bag_words.txt", &sdir), &s_bag_words);
		let s_bag_words_igc= serde_json::to_string(&self.vec_bag_words_igc).unwrap();
		write_to_file(&format!("{}/vec_bag_words_igc.txt", &sdir), &s_bag_words_igc);
		let s_map_crit_pat= serde_json::to_string(&self.map_crit_pat).unwrap();
		write_to_file(&format!("{}/map_crit_pat.txt", &sdir), &s_map_crit_pat);
		let s_map_crit_pat_igc= serde_json::to_string(&self.map_crit_pat_igc).unwrap();
		write_to_file(&format!("{}/map_crit_pat_igc.txt", &sdir), &s_map_crit_pat_igc);
		let s_dfa_crit= serde_json::to_string(&self.dfa_crit).unwrap();
		write_to_file(&format!("{}/dfa_crit.txt", &sdir), &s_dfa_crit);
		let s_dfa_crit_igc= serde_json::to_string(&self.dfa_crit_igc).unwrap();
		write_to_file(&format!("{}/dfa_crit_igc.txt", &sdir), &s_dfa_crit_igc);
		let s_sig_to_id= serde_json::to_string(&self.sig_to_id).unwrap();
		write_to_file(&format!("{}/sig_to_id.txt", &sdir), &s_sig_to_id);

		let s_lkup = format!("{}/lkup.txt", sdir);
		self.lkup.serialize_to(&s_lkup).expect("serialize lkup fails");

		let s_bundle_subsig= serde_json::to_string(
			&self.bundle_subsig).unwrap();
		write_to_file(&format!("{}/bundle_subsig.txt", &sdir), 
			&s_bundle_subsig);

		let s_bundle_subsig_igc= serde_json::to_string(
			&self.bundle_subsig_igc).unwrap();
		write_to_file(&format!("{}/bundle_subsig_igc.txt", &sdir),
			&s_bundle_subsig_igc);

		let s_agg = serde_json::to_string(
			&self.aggressive_max_span_nibbles).unwrap();
		write_to_file(&format!("{}/aggressive_meta.txt", &sdir),
			&s_agg);

	}

	/// Load from saved cached
	pub fn load(dir_name: &str) -> ClamavDB<F>{
		let sdir = format!("{}/data/cache/{}/", &proj_root(), dir_name);

		let s_vec_sigs= read(&format!("{}/vec_sigs.txt", sdir));
		let vec_sigs:Vec<Arc<ClamavSig>> = serde_json::from_str(&s_vec_sigs)
				.expect("Convert vec_sigs fails");

		let s_vec_crit_pat= read(&format!("{}/vec_crit_pat.txt", sdir));
		let vec_crit_pat:Vec<String> = serde_json::from_str(&s_vec_crit_pat).expect("Convert vec_crit_pat fails");

		let s_vec_crit_pat_igc= read(&format!("{}/vec_crit_pat_igc.txt", sdir));
		let vec_crit_pat_igc:Vec<String> = serde_json::from_str(&s_vec_crit_pat_igc) .expect("Convert vec_crit_pat_igc fails");


		let s_vec_bag_words= read(&format!("{}/vec_bag_words.txt", sdir));
		let vec_bag_words:Vec<String> = serde_json::from_str(&s_vec_bag_words) .expect("Convert vec_bag_words fails");


		let s_vec_bag_words_igc= read(&format!("{}/vec_bag_words_igc.txt", sdir));
		let vec_bag_words_igc:Vec<String> = serde_json::from_str(&s_vec_bag_words_igc).expect("Convert vec_bag_words_igc fails");

		let s_map_crit_pat= read(&format!("{}/map_crit_pat.txt", sdir)); 
		let map_crit_pat:HashMap<String,Vec<String>> = serde_json::from_str(&s_map_crit_pat).expect("Convert map_crit_pat fails");

		let s_map_crit_pat_igc= read(&format!("{}/map_crit_pat_igc.txt", sdir));
		let map_crit_pat_igc:HashMap<String,Vec<String>> = serde_json::from_str(&s_map_crit_pat_igc) .expect("Convert map_crit_pat_igc fails");

		let s_dfa_crit= read(&format!("{}/dfa_crit.txt", sdir));
		let dfa_crit:HexACDFA= serde_json::from_str(&s_dfa_crit)
				.expect("Convert dfa_crit fails");

		let s_dfa_crit_igc= read(&format!("{}/dfa_crit_igc.txt", sdir));
		let dfa_crit_igc:HexACDFA= serde_json::from_str(&s_dfa_crit_igc)
				.expect("Convert dfa_crit_igc fails");

		let s_sig_to_id = read(&format!("{}/sig_to_id.txt", sdir));
		let sig_to_id:HashMap<String, usize>= serde_json::from_str(&s_sig_to_id)
				.expect("Convert dfa_patterns_igc fails");

		let s_lkup = format!("{}/lkup.txt", sdir);
		let lkup = LookupTableTwoCol_Inst::deserialize_from(&s_lkup)
				.expect("Convert dfa_patterns_igc fails");

		let s_bundle_subsig 
			= read(&format!("{}/bundle_subsig.txt", sdir));
		let bundle_subsig= 
			serde_json::from_str(&s_bundle_subsig)
				.expect("Convert bundle_subsig fails");

		let s_bundle_subsig_igc 
			= read(&format!("{}/bundle_subsig_igc.txt", sdir));
		let bundle_subsig_igc =  
			serde_json::from_str(&s_bundle_subsig_igc)
				.expect("Convert bundle_subsig_igc fails");

		let vec_sigs_no_critical_pat = vec_sigs.iter().filter(|s| s.b_no_crit_pat)
			.map(|s| s.clone()).collect::<Vec<Arc<ClamavSig>>>();

		let agg_path = format!("{}/aggressive_meta.txt", sdir);
		let aggressive_max_span_nibbles = if file_exists(&agg_path) {
			serde_json::from_str(&read(&agg_path)).unwrap_or(0)
		} else { 0 };

		let res = ClamavDB{
			vec_sigs: vec_sigs,
			vec_sigs_no_critical_pat: vec_sigs_no_critical_pat,
			vec_crit_pat: vec_crit_pat,
			vec_crit_pat_igc: vec_crit_pat_igc,
			vec_bag_words: vec_bag_words,
			vec_bag_words_igc: vec_bag_words_igc,
			map_crit_pat: map_crit_pat,
			map_crit_pat_igc: map_crit_pat_igc,
			dfa_crit: dfa_crit,
			dfa_crit_igc: dfa_crit_igc,
			sig_to_id: sig_to_id,
			lkup,
			bundle_subsig,
			bundle_subsig_igc,
			aggressive_max_span_nibbles,
		};

		res
	}

	/// Check if all required cache files exist
	pub fn cache_exists(dir_name: &str) -> bool {
		let sdir = format!("{}/data/cache/{}/", &proj_root(), dir_name);
		let files = vec![
			"vec_sigs.txt", "vec_crit_pat.txt", "vec_crit_pat_igc.txt",
			"vec_bag_words.txt", "vec_bag_words_igc.txt", "map_crit_pat.txt",
			"map_crit_pat_igc.txt", "dfa_crit.txt", "dfa_crit_igc.txt",
			"sig_to_id.txt", "lkup.txt", "bundle_subsig.txt", "bundle_subsig_igc.txt"
		];
		for f in files {
			if !file_exists(&format!("{}{}", sdir, f)) {
				return false;
			}
		}
		true
	}

	/// build or load db based on b_read_cache. Note 
	/// all file path are relative to the project root.
	pub fn build_or_load(
		cfg: &ClamavApproxConfig, 
		sig_file: &str, 
		needs_dfa_list_file: &str, 
		needs_ised_list_file: &str, 
		needs_ised_igc_list_file: &str, 
		vlog: &mut Vec<String>,
		cache_dir: &str,
		b_read_cache: bool,
		b_write_cache: bool)->Result<Self, Error>{
			let proot = proj_root();
			
			let mut effective_write_cache = b_write_cache;
			let effective_read_cache = if b_read_cache {
				if Self::cache_exists(cache_dir) {
					true
				} else {
					flog(0, LOG1, &format!("cache {} not found or incomplete, will rebuild and save.", cache_dir), vlog);
					effective_write_cache = true;
					false
				}
			} else {
				false
			};

			let db = if effective_read_cache{
				flog(0, LOG1, &format!("loadClamDB from: {}", cache_dir),vlog);
				Self::load(cache_dir)
			}else{
				let db = Self::build_db(
					&format!("{}/{}",proot,sig_file),
					&format!("{}/{}", proot, needs_dfa_list_file), 
					&format!("{}/{}", proot, needs_ised_list_file), 
					&format!("{}/{}", proot, needs_ised_igc_list_file), 
					&cfg, vlog)?;
				if effective_write_cache {db.save(cache_dir);}
				db	
			};
			Ok(db)
	}

}

#[cfg(test)]
mod tests_clam_db{
	extern crate utils;

	use crate::{clam_db::{ClamavDB, SubsigStepStore, SubsigStepStoreItem,
		reverse_pm_bounds}, clamav::{default_clamav_cfg}};
	use crate::type_def::ClamSigType;
	use utils::{os::{proj_root}, consts::read_global_config};
	use ark_bn254::{Fr};
	use ark_ff::PrimeField;

	/// T1+T2: reverse_pm_bounds golden output + involution on the
	/// begin-normalized domain.
	#[test]
	fn test_m3_reverse_golden(){
		let max = usize::MAX;
		//3-step forward chain [p1,p2,p3=kw].
		let fwd: Vec<(usize,(usize,usize))> =
			vec![(1,(99,99)), (2,(10,20)), (3,(30,40))];
		let bwd = reverse_pm_bounds(&fwd, (0, max));
		//keyword(3) first w/ anywhere begin; gaps shifted back one;
		//forward begin (99,99) dropped.
		assert_eq!(bwd, vec![(3,(0,max)), (2,(30,40)), (1,(10,20))]);
		//2-step case.
		let f2: Vec<(usize,(usize,usize))> = vec![(7,(5,5)), (9,(0,4))];
		assert_eq!(reverse_pm_bounds(&f2,(0,max)),
			vec![(9,(0,max)), (7,(0,4))]);
		//involution on begin-normalized domain (step-1 begin already
		//anywhere): reverse(reverse(C)) == C.
		let norm: Vec<(usize,(usize,usize))> =
			vec![(1,(0,max)), (2,(10,20)), (3,(30,40))];
		let rr = reverse_pm_bounds(&reverse_pm_bounds(&norm,(0,max)),
			(0,max));
		assert_eq!(rr, norm);
		//empty chain.
		assert!(reverse_pm_bounds::<usize>(&[], (0,max)).is_empty());
	}

	/// T3+T5: gen_cols emits reversed rows for an is_backward item
	/// (keyword becomes step 1) and forward order otherwise.
	#[test]
	fn test_m3_gen_cols_backward(){
		let rb = read_global_config().range2_bit;
		let f = |u: usize| Fr::from(u as u64);
		let mut store = SubsigStepStore::new();
		store.b_aggressive = true;
		//forward subsig 100: pats 5,6 in stored order.
		store.add(&SubsigStepStoreItem{subsig_id:100, igc:false,
			vec_pm_bounds: vec![(5,(1,2)),(6,(3,4))], is_backward:false});
		//backward subsig 200: stored fwd [7,8] -> emitted reversed [8,7].
		store.add(&SubsigStepStoreItem{subsig_id:200, igc:false,
			vec_pm_bounds: vec![(7,(1,2)),(8,(3,4))], is_backward:true});
		store.finalize();
		let cols = store.gen_cols::<Fr>(rb, None);
		//cols: [subsig, step, pat, rg_s, rg_e, encoded]; collect pat
		//order per subsig (skip dummy 0/max rows).
		let max = (1usize<<rb)-1;
		let pats_of = |sid: usize| -> Vec<usize> {
			let mut v = vec![];
			for r in 0..cols[0].len(){
				if cols[0][r]==f(sid) {
					let p = &cols[2][r];
					if *p!=Fr::from(0u64) && *p!=f(max) {
						//recover small pat id by trial (<=8).
						for cand in 1..16usize{
							if *p==f(cand){ v.push(cand); break; }
						}
					}
				}
			}
			v
		};
		assert_eq!(pats_of(100), vec![5,6], "forward unchanged");
		assert_eq!(pats_of(200), vec![8,7], "backward reversed (kw=8 first)");
	}

	#[test]
	fn test_load_clam_db(){
		let cfg = default_clamav_cfg(); 
		let sig_file= format!("{}/data/src_sig/clamav/debug/debug.ldb"
			,proj_root());
		let needs_dfa_file = format!("{}/data/src_sig/clamav/debug/debug_needs_dfa.txt" ,proj_root());
		let needs_ised_file = format!("{}/data/src_sig/clamav/debug/debug_needs_ised.txt" ,proj_root());
		let needs_ised_igc_file = format!("{}/data/src_sig/clamav/debug/debug_needs_ised_igc.txt" ,proj_root());
		let mut vlog = vec![];
		let db = ClamavDB::<Fr>::
			build_db(&sig_file, &needs_dfa_file, &needs_ised_file,
				&needs_ised_igc_file, &cfg,&mut vlog).expect("build db err");
		assert!(db.vec_sigs.len()==3, "ERROR loaded: vec_sigs: {:?}", 
			db.vec_sigs);
		db.save("debug1");
		let mut vlog1 = vec![];
		db.print_summary(&mut vlog1);
		let db2 = ClamavDB::<Fr>::load("debug1");
		let mut vlog = vec![];
		db2.print_summary(&mut vlog);
		assert!(db2.vec_sigs.len()==3, "ERROR reading file vec_sigs: {:?}",
			db.vec_sigs);
	}

	/// M1a build_db integration: F1 forward / F2 backward anchors +
	/// global halo span persisted; gate-off inert; unbounded errors.
	/// build_test_db appends an alphabet-padding sig (full hex DFA).
	#[test]
	fn tests_sde_rep_shape_guard_db(){
		let proot = proj_root();
		let lines = |fx: &str| -> Vec<String> {
			let p = format!(
				"{}/data/debug/sde_aggressive/{}/main.dat", proot, fx);
			std::fs::read_to_string(&p).expect("read main.dat")
				.lines().map(|l| l.trim().to_string())
				.filter(|l| !l.is_empty() && !l.starts_with('#'))
				.collect()
		};
		let mut cfg_on = default_clamav_cfg();
		cfg_on.b_aggressive_sde_for_rep = true;
		//fan-out is orthogonal to M1a (span/anchor/M come from the
		//ORIGINAL subsig); keep it off so the DFA stays small.
		cfg_on.sde_rep_fanout_cap = 1;
		let mut cfg_off = default_clamav_cfg();
		cfg_off.b_aggressive_sde_for_rep = false;
		let none: Vec<String> = vec![];
		//work dir under data/ (write_to_file won't create parents).
		let wdir = |d: &str| -> String {
			std::fs::create_dir_all(
				format!("{}/data/{}", proot, d)).unwrap();
			d.to_string()
		};

		//T7 F1 flag-ON: global M=156 nibbles, forward anchor (0).
		let db = ClamavDB::<Fr>::build_test_db(&cfg_on,
			&wdir("debug/sde_aggressive/m1a_f1"), &lines("F1"),
			&none, &none, &none).expect("F1 build");
		assert_eq!(db.aggressive_max_span_nibbles, 156);
		assert!(db.vec_sigs.iter().any(|s|
			s.vec_subsig_anchor_dir.iter().any(|&d| d==0)));

		//T8 F2 flag-ON: M=180 (multi-leg dominates), backward (1).
		let db = ClamavDB::<Fr>::build_test_db(&cfg_on,
			&wdir("debug/sde_aggressive/m1a_f2"), &lines("F2"),
			&none, &none, &none).expect("F2 build");
		assert_eq!(db.aggressive_max_span_nibbles, 180);
		assert!(db.vec_sigs.iter().any(|s|
			s.vec_subsig_anchor_dir.iter().any(|&d| d==1)));

		//T10 F1 flag-OFF: inert (M=0, no anchors).
		let db = ClamavDB::<Fr>::build_test_db(&cfg_off,
			&wdir("debug/sde_aggressive/m1a_f1_off"), &lines("F1"),
			&none, &none, &none).expect("F1 off build");
		assert_eq!(db.aggressive_max_span_nibbles, 0);
		assert!(db.vec_sigs.iter().all(|s|
			s.vec_subsig_anchor_dir.is_empty()));

		//T9 unbounded sig (.* gap) -> build_test_db Err (step-1b,
		//before DFA build) regardless of alphabet padding.
		let bad = vec![
			"Bad.Unbounded;Engine:81-255,Target:0;0;/SSN.*[0-9]{3}/s"
				.to_string()];
		let r = ClamavDB::<Fr>::build_test_db(&cfg_on,
			&wdir("debug/sde_aggressive/m1a_bad"), &bad,
			&none, &none, &none);
		assert!(r.is_err(), "unbounded sig must error build_db");
	}
}
