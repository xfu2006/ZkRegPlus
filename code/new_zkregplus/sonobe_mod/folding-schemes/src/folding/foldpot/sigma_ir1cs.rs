use std::sync::{Arc, Mutex};


macro_rules! lock_unwrap {
    ($mutex:expr) => {
        $mutex.lock().unwrap_or_else(|e| panic!("Mutex poisoned at {}:{}: {}", file!(), line!(), e))
    };
}

/// Sigma-I-R1CS is a 3-move restricted fragment of the
/// I-R1CS model. See our paper Section 6.
/* Created 08/05/2024 
	Modified: 08/15/2024. Added statement structure, and support for
		large inter-circuit input/output buffer.
	Modified: 08/19/2024. Updated cmF computation.
	Revised: 10/08/2024. Added support of CyclePair. Allow dual mode.
	Revised: 12/24/2024. Add support for computing sum of w, l, vec_r, vec_v
	Revised: 08/06/2025 added failed_sigs, discharged_sigs, their m_tbl
		and the corresonding logic to set up the final output based on
		that failed_sigs is a subset of discharged_sigs (or the samples
		are discharged).
*/
use utils::{consts::ADD_CHAIN_SIZE, logger::{log, log_perf, emit_stdout, LOG6,LOG7}, timer::Timer as GTimer};
use crate::folding::foldpot::utils::{sum3,alloc_fpvar_mul,var_to_tuple, var_to_tuple_adv, B_DEBUG, B_DEBUG3, B_DEBUG2, check_cs, POW_LE_BITS, alloc_le_bits};
use serde::{Serialize,Deserialize};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use crate::commitment::CommitmentScheme;
use core::marker::PhantomData;
use std::collections::HashMap;
use std::any::Any;
use ark_ec::{CurveGroup,pairing::Pairing};
use ark_ff::{PrimeField,ToConstraintField,Field};
use num_bigint::{BigUint};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError, 
	LinearCombination, Variable};
use ark_crypto_primitives::sponge::{
	constraints::CryptographicSpongeVar,
    poseidon::{PoseidonConfig, PoseidonSponge, constraints::PoseidonSpongeVar},
    Absorb, CryptographicSponge,
};
use ark_r1cs_std::{
	fields::{fp::FpVar,FieldVar},
	alloc::AllocVar, 
	eq::EqGadget,
    R1CSVar, ToBitsGadget,
	boolean::{Boolean},
};
//use std::borrow::BorrowMut;
use crate::{
	Error,
	frontend::{FCircuit},
	transcript::{Transcript,TranscriptVar,AbsorbNonNative},
	transcript::poseidon::poseidon_canonical_config,
	folding::{
		circuits::{nonnative::uint::{NonNativeUintVar,LimbVar}},
		foldpot::{
			utils::{f1_to_f2_limbs, get_stack_space,check_logup, print_vec_var,
				var_to_lb , gen_vec_inverse},
			container_config::{ContainerConfig,ColEle},
			circuits_super::field_to_usize,
		},
	}
};
use std::{fmt,fmt::{Debug,Formatter}};
use rayon::prelude::*;
use ark_ff::{One};
use std::fs::File;
use std::io::prelude::*;


/// i.e., information related to discharge Sig using
/// SED or ISED
#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct DischargeSigInfo{
	/// the name of the signature
	pub sig_name: String,
	/// for verification purpose
	pub b_success: bool,
	/// minimum cost
	pub min_cost: usize, 
	/// minimum cost using dnf_id  
	pub min_dnf_id: usize,
	/// list of raw subsigs in the dnv item (raw IDs starting from 0)
	/// NOTE that for most regular ones, these are min dnf items.
	/// but when subsigs are COUNTER SUBSIGS, these are all atomic
	/// subsigs.
	pub subsig_ids: Vec<usize>,
	/// whether the above subsig is ignore case 
	pub subsig_igc: Vec<bool>,
}


/// Represents a pre-processed information about word,
/// i.e., failed signatures by each approach.
#[derive(Clone,Debug,Serialize,Deserialize)]
pub struct WordInfo{
	/// the list of signatures to be discharged by sed approach,
	/// signature IDs starting from 1
	pub vec_sed_sigs: Vec<usize>,
	/// the list of signatures to be discharged by dfa
	pub vec_dfa_sigs: Vec<usize>,
	/// the list of signatures to be discharged by ised
	pub vec_ised_sigs: Vec<usize>,

	/// one to one corresponds to vec_sed_sigs
	pub vec_sed_sigs_info: Vec<DischargeSigInfo>,
	/// one to one corresponds to vec_ised_sigs (NOT USED ANY MORE)
	/// will always be EMPTY.
	pub vec_ised_sigs_info: Vec<DischargeSigInfo>,

	/// one to one corresponds to vec_dfa_sigs
	pub vec_dfa_sigs_info: Vec<DischargeSigInfo>,

	/// Raw file nibble count (length of `nibbles` passed to
	/// discharge_prover). Mappers use this to compute the
	/// starting offset `A = (62 - file_nibble_len % 62) % 62`
	/// for the F-level pad (so within-F pad from pack_nibbles
	/// and F-level pad from the mapper share one contiguous
	/// slice of the canonical pad stream).
	pub file_nibble_len: usize,

	/// Aggressive-mode forward halo: this segment's successor's first
	/// nibbles (raw 0..15), set by the driver per segment. Empty for the
	/// last segment / non-aggressive runs. SED truncates to M.
	#[serde(default)]
	pub halo_nibbles: Vec<u8>,

	/// Aggressive: per-segment CP failed_c (sig ids = the gadget's
	/// failed_sigs for that segment), indexed by seg_id. Empty =>
	/// non-aggressive / not built => SED falls back to vec_sed_sigs.
	#[serde(default)]
	pub failed_c_all_segs: Vec<Vec<usize>>,
	/// 1-1 with failed_c_all_segs[seg]: each segment's DischargeSigInfo.
	#[serde(default)]
	pub failed_c_info_all_segs: Vec<Vec<DischargeSigInfo>>,
}

impl WordInfo{
	pub fn dummy()->Self{
		Self{
			vec_sed_sigs: vec![],
			vec_dfa_sigs: vec![],
			vec_ised_sigs: vec![],
			vec_sed_sigs_info: vec![],
			vec_ised_sigs_info: vec![],
			vec_dfa_sigs_info: vec![],
			file_nibble_len: 0,
			halo_nibbles: vec![],
			failed_c_all_segs: vec![],
			failed_c_info_all_segs: vec![],
		}
	}

	pub fn is_success(&self)->bool{
		self.vec_ised_sigs.len() == 0	//this implies there
			//are failed sigs by DFA approach which is the last step
	}
}

/// Two column lookup table. The first entry is always
/// (0,0). All entries are sorted in ascending order
/// Col1 is serving as sub-table ID, Col2 serves as entry
/// No duplicate entries. Two columns always have the same length.
pub trait LookupTableTwoCol<F:PrimeField>: Debug +Clone + Send + Sync{
	/// constructor
	fn new(vals: Vec<(F,F)>) -> Self;

	/// get the size
	fn get_size(&self) -> usize;

	/// return values in two columns
	fn get_cols(&self) -> (Vec<F>,Vec<F>);

	/// find the entry location (if not found, return the position
	/// where it should be inserted)
	fn find(&self, tbl_id: F, val: F)->Result<usize, usize>;

	/// return the two columns
	fn get_cols_slice(&self, start_idx: usize, end_idx: usize) -> (Vec<F>, Vec<F>);

	/// Given entries defined in tbl_ids and vals, update the corresponding
	/// hashmaps (the occurence entries)
	fn fill_mvec(&self, tbl_ids: &Vec<F>, vals: &Vec<F>, map: &mut HashMap<usize, usize>);
}

/// assert that b1 implies b2
pub fn assert_imply<F:PrimeField>(b1: &Boolean<F>,  b2: &Boolean<F>)
->Result<(), Error>{
	let b3 = b1.not().or(&b2)?;
	b3.enforce_equal(&Boolean::TRUE)?;
	if B_DEBUG {assert!(b3.value()?);}
	Ok( () )
}

#[derive(Clone,Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct LookupTableTwoCol_Inst<F:PrimeField>{
	pub vals: Vec<(F,F)>,
}

impl <F: PrimeField> LookupTableTwoCol_Inst<F>{
	/// write the serialized object to file (maybe later improved
	/// to small chunks with more parallelism)
	pub fn serialize_to(&self, sfile: &str)->Result<(), Error>{
		let mut bytes= Vec::new();
		self.serialize_compressed(&mut bytes).unwrap();
		let mut file = File::create(sfile)?;
        file.write_all(&bytes)?;
		Ok( () )
	}
	pub fn deserialize_from(s_file: &str)->Result<Self, Error>{
		let mut file = File::open(s_file)?;
        let mut buffer = Vec::<u8>::new();
        file.read_to_end(&mut buffer)?;
		Ok( Self::deserialize_uncompressed(&*buffer)? )
	}

	/// perform self check (required all entries in order, as big-uint)
	pub fn self_check(&self) -> Result<(), Error>{
		for i in 0..self.vals.len()-1{
			let v1 = self.vals[i];
			let v2 = self.vals[i+1];
			if v1.0>v2.0 || 
			  (v1.0==v2.0 && v1.1>=v2.1){
				return Err(Error
					::Other("self check fails not in order".to_string()));
			}
		}
		Ok( () )
	}


	/// generate the share of m_vec for slice [idx_start..idx_end] (idx_end
	/// is not included
	pub fn gen_m_share(idx_start: usize, idx_end: usize, map: &HashMap<usize, usize>)->Vec<F>{
		(idx_start .. idx_end).into_par_iter().map(|x|
			F::from(*map.get(&x).unwrap_or(&0) as u32)
		).collect::<Vec<F>>()
	}
}

impl <F:PrimeField> LookupTableTwoCol_Inst<F>{
	pub fn dummy() -> Self{
		Self{vals: vec![(F::zero(), F::zero())]}
	}
}

impl <F:PrimeField> LookupTableTwoCol<F> for LookupTableTwoCol_Inst<F>{
	/// Given entries defined in tbl_ids and vals, update the corresponding
	/// hashmaps (the occurence entries)
	fn fill_mvec(&self, tbl_ids: &Vec<F>, vals: &Vec<F>, map: &mut HashMap<usize, usize>){
		assert!(tbl_ids.len()==vals.len(), "tbl_id.len != vals.len");
		let idx = tbl_ids.par_iter().zip(vals.par_iter()).enumerate()
			.map(|(i, (x,y))|{
			//if subtbl_id is 0, ignore any entry just return idx 0
			if x.is_zero(){ 0usize}
			else{
				let res = self.find(*x,*y);
				res.expect(&format!("Cannot find entry for tbl_id[{}]: ({}, {})",i, *x,*y))
			}
		}).collect::<Vec<usize>>();
		for i in idx{
			//IGNORE the 0 entries as we have made sure that
			//subtbl_id (non-constant) will NOT have 0 id's
			//in this case, ignore (0,0) entries
			//see the improve of case 3 of sum_hab22_left and sum_hab22_right
			if i!=0{
				map.entry(i).and_modify(|c| *c +=1).or_insert(1);
			}
		}
	}
	/// return the two columns
	fn get_cols_slice(
		&self, start_idx: usize, end_idx: usize) -> (Vec<F>, Vec<F>){
		let (col1, col2):(Vec<F>,Vec<F>) = 
			self.vals[start_idx..end_idx].into_iter()
			.map(|(x,y)| (*x,*y)).unzip();
		(col1, col2)
	}

	fn new(vals: Vec<(F,F)>) -> Self{
		LookupTableTwoCol_Inst{vals}
	}

	fn get_size(&self) -> usize{
		self.vals.len()
	}

	fn get_cols(&self) -> (Vec<F>,Vec<F>){
		self.vals.iter().map(|(x,y)| (*x,*y)).unzip()
	}

	/// find the entry location (if not found, return Err with the position
	/// where it should be inserted). Here we assume 
	/// assume both tbl_id and tbl_value are no longer than 64-bit!
	fn find(&self, tbl_id: F, val: F)->Result<usize, usize>{
		let seek = (tbl_id, val);
		let res = self.vals.binary_search_by(|t| { t.cmp(&seek) });

		res
	}
}

/// Just for syntactic enforce the use of struct SigmaIR1CS
pub trait SigmaIR1CS<const H: bool, F: PrimeField, LK: LookupTableTwoCol<F>, GM: GadgetMapper<F,LK> + Debug + std::clone::Clone>{
	type C: CurveGroup<ScalarField=F>;
	type CS: CommitmentScheme<Self::C, H>;  //commitment scheme

	/// return the statement config
	fn get_stmt_config(&self)->StatementConfig;

	fn is_cyclepair(&self)->bool;

	fn is_check_lkup(&self)->bool;

	/// return the lkup_share_size
	fn get_lkup_share_size(&self)->usize;

	/// is full_mode (supporting cyclepair)
	fn is_full_mode(&self) -> bool;

	/// return name of the SigmaIR1CS instance
	fn get_name(&self) -> String; 

	/// return the mapper
	fn get_mapper(&self) -> Arc<Mutex<GM>>;

	/// Create a new instance (need to pass a gadget mapper
	/// which is responsible for managing all relations, e..g,
	/// projecting the relation as a ``join" of components.
	/// fq_bits is the bit width of base prime field, it is
	/// needed for calculating limbs of NonNativeUint,
	fn new_adv(name: String, poseidon_config: PoseidonConfig<F>, 
		g_mapper: Arc<Mutex<GM>>, b_full_mode: bool, lkup_share_size: usize,
		b_cyclepair: bool, b_check_lkup: bool)
		->Result<Self,Error> where Self: Sized;

	/// Similar to step_native to allow self to modify itself.
	/// This is to allow self to STORE inside itself the generated
	/// witness for all subprotocols (in case there are non-deterministic
	///  generation of msg1 by sub-protocols), which will cause
	/// inconsistency of generate_constraints when the same witness
	/// is generated again; also saves generation time by caching the
	/// witness generated. It needs z_i_part2 instance to generate the
	/// zi1.1 (zi1.0 is left to augmented circuit to generate hashchain
	/// on cmF). Returns the ZiPartTwoInst for zi1.1 (next step).
	/// Although, it's a bit redundant because the instance is already
	/// in Witness, just return it for convenience.
	/// the external_inputs is the seralized StatementInst.
	fn step_native_mut(&mut self, _i: usize, z_i: &ZiPartTwoInst<F>, external_inputs: Vec<F>) -> Result<ZiPartTwoInst<F>, Error>;

	/// generate the dummy statement (external inputs).
	fn gen_dummy_stmt(&self) -> Vec<F>;

	/// set its own dummy statement
	fn set_dummy_stmt(&mut self, stmt: StatementInst<F,LK>);

	/// set job_id for logging isolation
	fn set_job_id(&mut self, job_id: usize);

	/// get job_id
	fn get_job_id(&self) -> usize;

	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, advice: &Arc<dyn NdAdvice + Send + Sync>); 


	/// Given the  problem statement (actually non-determisnitc advice
	/// provided by the prover)
	/// and z_i.1 (part 2 of pub input, z_i.0 is
	/// hashchain of cmF), generate a witness,
	/// its signature, and z_i1.1 (next pub input). 
	/// Note that this is problem specific, the 
	/// relation mapper needs to know how to map the i/o statement
	/// to the sub-protocols.
	/// the precomputed_group_cmF is provided if we already know
	/// the commitment t othe fixed fragment of stmt.
	fn gen_witness(&self, stmt: &Vec<F>, zi_part2: &ZiPartTwoInst<F>, precomputed_group_cmF: Option<Self::C>) -> (WitnessSigmaIR1CS<F>, WitnessSigmaIR1CSConfig, ZiPartTwoInst<F>);

	/// Generate the commitment to the fixed segment
	fn gen_cmF(&self, stmt: &Vec<F>, zi_part2: &ZiPartTwoInst<F>) -> Result<Self::C, Error>;

	/// return the size of F (problem statement (including 
	/// non-determinstic prover
	/// advice) + msg1)
	fn get_size_f(&self) -> usize;

	/// length of the cmF-committed vector (stmt + msg1); the
	/// commitment key must cover at least this many generators.
	fn get_cmf_len(&self) -> usize;

	/// the maximal length of word that can be processed,
	/// this request is essentially related to relation mapper which is
	/// algorihtm specific.
	fn max_word_len(&self) -> usize;

	/// return the estimated cost in terms of number of constraints.
	/// This is mainly used to apply heurstics to pick the applicable
	/// circuit with minimal cost for a given word
	fn est_cost(&self)->usize;

	/// (component_name, gadget_count) spans in get_gadgets() order, for
	/// cost reporting. Default empty; SigmaIR1CS_Inst delegates to mapper.
	fn component_spans(&self) -> Vec<(String, usize)> { vec![] }
}

/// One circuit's R1CS-constraint capture, filled by
/// generate_step_constraints while armed. entry_nc/end_nc bracket the
/// per-step (inner) circuit; gadgets = (name, cs-delta) in gadget order.
pub struct CostCapture{
	pub entry_nc: usize,
	pub end_nc: usize,
	pub gadgets: Vec<(String, usize)>,
}
thread_local!{
	static COST_SINK: std::cell::RefCell<Option<CostCapture>> =
		std::cell::RefCell::new(None);
}
/// Arm the per-gadget cost sink (clears any prior capture).
pub fn cost_capture_begin(){
	COST_SINK.with(|s| *s.borrow_mut() =
		Some(CostCapture{entry_nc:0, end_nc:0, gadgets:vec![]}));
}
/// Disarm and return the collected capture (None if not armed).
pub fn cost_capture_take() -> Option<CostCapture>{
	COST_SINK.with(|s| s.borrow_mut().take())
}
fn cost_capture_set_entry(nc: usize){
	COST_SINK.with(|s| if let Some(c)=s.borrow_mut().as_mut(){ c.entry_nc=nc; });
}
fn cost_capture_set_end(nc: usize){
	COST_SINK.with(|s| if let Some(c)=s.borrow_mut().as_mut(){ c.end_nc=nc; });
}
fn cost_capture_push(name: &str, delta: usize){
	COST_SINK.with(|s| if let Some(c)=s.borrow_mut().as_mut(){
		c.gadgets.push((name.to_string(), delta)); });
}

/// Format one circuit's captured cost as a `circ` block grouped by
/// component (CP/SED/DFA), with per-component subtotals, a framework
/// remainder, and the per-step total. `spans` = (component_name,
/// n_gadgets) aligned with cap.gadgets order. Returns the per-step total.
/// Append #1/#2/... to names that repeat (the cs vs igc variants), so
/// duplicate component/gadget names are distinguishable. Unique names
/// are returned unchanged. O(n^2) but n is small.
fn tag_dups(names: &[String]) -> Vec<String>{
	let mut out = Vec::with_capacity(names.len());
	for (i, n) in names.iter().enumerate(){
		let total = names.iter().filter(|x| *x==n).count();
		if total > 1{
			let k = names[..=i].iter().filter(|x| *x==n).count();
			out.push(format!("{}#{}", n, k));
		} else { out.push(n.clone()); }
	}
	out
}

pub fn print_cost_report(label: &str, cap: &CostCapture,
	spans: &[(String, usize)]) -> usize{
	let inner_total = cap.end_nc.saturating_sub(cap.entry_nc);
	let gadget_sum: usize = cap.gadgets.iter().map(|(_,c)| *c).sum();
	let framework = inner_total.saturating_sub(gadget_sum);
	emit_stdout(format!(
		"==== COST {} (R1CS constraints) ====   total = {}",
		label, inner_total));
	let comp_names: Vec<String> = spans.iter().map(|(n,_)| n.clone()).collect();
	let comp_tags = tag_dups(&comp_names);
	let mut gi = 0;
	for (idx, (_cname, n)) in spans.iter().enumerate(){
		let end = (gi + *n).min(cap.gadgets.len());
		let slice = &cap.gadgets[gi.min(cap.gadgets.len())..end];
		let sub: usize = slice.iter().map(|(_,c)| *c).sum();
		emit_stdout(format!("  {:<12} subtotal = {}", comp_tags[idx], sub));
		let gnames: Vec<String> = slice.iter().map(|(n,_)| n.clone()).collect();
		let gtags = tag_dups(&gnames);
		for (j, (_, c)) in slice.iter().enumerate(){
			emit_stdout(format!("    {:<26} {:>12}", gtags[j], c));
		}
		gi = end;
	}
	emit_stdout(format!(
		"  framework (poseidon/logup/io)        {:>12}", framework));
	inner_total
}

/// Helper supertrait that lets us deep-clone a `dyn SigmaGadget`
/// through a trait object. The blanket impl below fires for every
/// concrete gadget that is `Clone + 'static`, so adding this
/// supertrait does not force new code in each gadget impl.
/// Returns `Arc<Mutex<...>>` directly so callers get an independent
/// lock on the cloned gadget.
pub trait SigmaGadgetCloneBox<F:PrimeField>: Send + Sync {
	fn clone_arc_sigma_gadget(&self)
		-> Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>>;
}

impl<F:PrimeField, T> SigmaGadgetCloneBox<F> for T
where T: 'static + SigmaGadget<F> + Clone,
{
	fn clone_arc_sigma_gadget(&self)
		-> Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>> {
		Arc::new(Mutex::new(self.clone()))
	}
}

/// Components of SigmaIR1CS (their 3-messages are integrated
/// to cut the recursion overhead)
pub trait SigmaGadget<F:PrimeField>: Debug + Send + Sync
	+ SigmaGadgetCloneBox<F> {
	/// return a name
	fn get_name(&self)->&str;

	/// set job_id
	fn set_job_id(&mut self, job_id: usize);

	/// get job_id
	fn get_job_id(&self)->usize;

	/// set the container cfg. This is only needed for those gadgets
	/// in SED approach. Pass a sharee copy of all ContainerConfigs
	/// for all gadgets in one circuit (or one component mapper, depending
	/// on the context), so that a gadget could use relative gadget idx
	/// in Location to refer to the source column in another gadget in
	/// the same (component mapper or circuit).
	/// Parameter `idx` indicates its own ContainerCfg in the cfg_context,
	/// this `idx` is context dependent (it may refer to its index
	/// in the SED component or circuit, take caution when interpreting
	/// its semantics).
	fn set_container_cfg(&mut self, cfgs_context: Arc<Vec<ContainerConfig>>, idx: usize);

	/// retrieve its conainer config
	fn get_container_config(&self)->ContainerConfig;

	/// return the estimated cost in terms of number of constraints.
	/// This is mainly used to apply heurstics to pick the applicable
	/// circuit with minimal cost for a given word
	fn est_cost(&self)->usize;

	/// return the number of field elements for statement, msg1, 2, and 3.
	fn get_msg_size(&self) -> (usize, usize, usize, usize);

	/// return the size to add to the inp/oup/data/failed_sigs/discharged_sigs
	/// (similarly
	/// for subtbl_id_inp, subtbl_id_oup, subtbl_id_data) segments,
	/// NOTE: it does not apyly ti failed_sigs and discharged_sig
	/// as these two do not have sid.
	/// 
	/// The info is later collected by the upper layer GadgetMapper.
	/// Note that the sum of these segments do not correspond
	/// to the ProblemStatement length as some part of the FULL
	/// data segements can be mapped from other gadgets.
	/// The size ONLY refects the the size to ADD TO the existing
	/// inp/oup/data segements collected by the GadgetMapper.
	///
	/// NOTE: This function is ONLY needed for those in SedGadgetMapper,
	/// others are handled by legacy mode of data checking.
	fn get_to_add_size(&self)->(usize, usize, usize, usize, usize);

	/// Get the instructions for build its statement.
	/// NOTE: this is only needed for those used in SedGadgetMapper.
	/// Others are handled by legacy code in their gadget mapper.
	///
	/// Returns a vector of multiple tuples and each tuple has the form
	/// (idx_gadget_offset, component_offset, idx_start, len)
	/// E.g., (-1, 1, 100, 20)
	/// means to extract a data segement of 20 elements from
	/// the previous gadget, output_buf_to_append, starting idex 100 of it.
	/// Here for the 2nd element, its range is in [0,1,2,3,4,5,6]
	/// which indicates: word/inp/oup/data/subtbl_id_inp/subtbl_id_oup/subtbl_id_data
	fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>;

	/// generate the msg1, maybe non-deterministic. The stmt_vec
	/// is the combined vec of statements for ALL (sibling) subprotocols,
	/// use the v_idx to retrieve the subprotocol related statement.
	/// NOTE that each element of v_idx is a tuple (start, end) both
	/// ends included, e.g., [100, 101] is a range of 2 element.
	/// Concatenation of these ranges represents all available
	/// statement elements. Its statement may come from the entire
	/// word of the composite protocol (which includes subtable_id as well).
	fn gen_msg1(&self, stmt_vec: &Vec<F>, v_idx: &Vec<(usize,usize)>)->Vec<F>; 

	/// generate the msag3. Similarly, msg1_vec is the combined
	/// msg1 for all siblines, use idx_start to retrieve its own msg2,
	/// len_msg1 indicates the length of the segment in the combined array.
	/// Similar for message2.
	fn gen_msg3(&self, stmt_vec: &Vec<F>, stmt_idx: &Vec<(usize,usize)>,
		msg1_vec: &Vec<F>, idx_msg1: usize, len_msg1: usize,
		msg2_vec: &Vec<F>, idx_msg2: usize, len_msg2: usize) -> Vec<F>;

	/// Assert the validity of msg3, given
	/// the combined witness (use cfg to retrieve the corresponding
	/// messages). i is the index of the gadget in the
	/// vector of gadget. Use i to retrieve its message /stmt locations.
	/// Note that this function might add additional
	/// constraints. 
	fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
		wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig,
		word_id: FpVar<F>, subsig_id: FpVar<F>) 
		-> Result<(), SynthesisError>;
}

/// Non-deministic advice (e.g., discharging proof)
/// a word. This is application specific, but we require that
/// all circuits in the same driver should have the same NdAdvice.
/// NOTE: needs to support dynamic cast when later used in composite
/// gadget mapper.
pub trait NdAdvice: Debug{
	fn as_any(&self) -> &dyn Any;
}

#[derive(Debug)]
pub struct DummyNdAdvice{}
impl NdAdvice for DummyNdAdvice {
	fn as_any(&self) -> &dyn Any{ self }
}

/// Capacity object that represents the resource requirement
/// of a discharge proof, or the circuit can handle. 
/// Later, in composite gadget mapper, it may have to be caseted.
/// So require Any here.
pub trait Capacity: Debug + Send + Sync{
	/// Self represents the capacity of the circuit, other
	/// represents the capacity requirement of a discharge proof (NdAdvice)
	/// It is essentially a comparison operation.
	fn can_satisfy(&self, other: &Arc<dyn Capacity + Send + Sync>) -> bool;

	/// to get around the requirement on Clone trait which require Sized
	/// (which cause trouble why use dyn Capacity + Send + Sync in Rc),
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>;

	/// needed for downcasting for composite gadget mapper
	fn as_any(&self) -> &dyn Any;

	/// Aggressive-mode forward-halo width in nibbles (0 = none).
	/// Lets the driver source per-chunk look-ahead without a downcast.
	fn halo_nibbles(&self) -> usize { 0 }
}

#[derive(Clone,Debug,Copy)]
pub struct DummyCapacity{
	/// When used as the capacity of a circuit, it represents the
	/// word segment len the circuit could handle; when represented as
	/// a capacity requirement, it represents the word length of the segment. 
	pub word_seg_len: usize,
}

impl Capacity for DummyCapacity{
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>)->bool{
		let other = r_other.as_any().downcast_ref::<DummyCapacity>(); 
		self.word_seg_len >= other.expect("downcast err").word_seg_len
	}
	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		Arc::new(DummyCapacity{word_seg_len: self.word_seg_len})
	}
	fn as_any(&self) -> &dyn Any{ self }
}



/// A trait for modeling the join relation that maps 
/// Optional deep-clone trait for a GadgetMapper. Concrete mappers
/// that want per-job replication with independent locks (e.g.
/// `CompositeGadgetMapper`) implement this. Mappers that don't
/// (e.g. test-only `SumMapper`) simply omit it; callers that
/// rely on deep cloning must add this bound.
pub trait GadgetMapperDeepClone {
	fn clone_deep_mapper(&self) -> Self where Self: Sized;
}

/// Trait to let callers deep-clone a circuit through a generic
/// type parameter. Implemented on `SigmaIR1CS_Inst` when its `GM`
/// supports deep cloning via `GadgetMapperDeepClone` (see the
/// impl block just after `SigmaIR1CS_Inst::clone_deep`).
pub trait CloneDeep {
	fn clone_deep_self(&self) -> Self where Self: Sized;
}

/// a SigmaIR1CS_Inst object to its components, and map the I/O
/// It is mainly responsible for defining the logic and
/// SigmaIR1CS_Inst just executes gadgets one by one (without
/// knowing their details)
pub trait GadgetMapper<F:PrimeField, LK: LookupTableTwoCol<F>>: Send + Sync{
	/// set job_id
	fn set_job_id(&mut self, job_id: usize);

	/// get job_id
	fn get_job_id(&self) -> usize;

	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, advice: &Arc<dyn NdAdvice + Send + Sync>); 

	/// return the capacity of this circuit
	fn get_capacity(&self) -> Arc<dyn Capacity + Send + Sync>;

	/// return the name
	fn get_name(&self) -> String;

	/// Return the components. The config is contained
	/// in the relation mapper object, and should be passed
	/// by the corresonding constructor. 
	fn get_gadgets(&self) -> Vec<Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>>>;  

	/// generate the structure of statment (total len, structure of statement,
	/// and statement mapping, extra_join_constraints, map of 
	/// 160 elements of CyclePairInpVar in ZiPartTwoInst to the indices
	/// in Witness)
	/// Note specifically for statement mapping: for each
	/// component gadget, it provides a Vector of ranges that
	/// map from its problem statement to the GLOBAL statement vector.
	/// E.g., for two compoments, its compoment map may look at
	/// [ [(100,199), (200,299)], [100, 199] ]
	/// the first component has altogether 100 elements for its statement,
	/// the second compoment has 100 elements.:w
	///
	/// NOTE that to cut state size (only 2 in zi), the GLOBAL
	/// statement is also treated as a part of witness (and be hashed
	/// into zi). The extra_join_constraints are a collection
	/// of (idx1,idx2) where statement_vector[idx1]=statment_vector[idx2]
	/// will be enforced. Here all idx are RELATIVE to the beginning
	/// of the STATMENT VECTOR. Last map of CyclePairInptVarMap is optional
	/// only required for full_mode).
	fn gen_statement_structure(&self, lkup_share_size: usize) 
		-> (usize, StatementConfig, 
		Vec<Vec<(usize,usize)>>,  //component stmt map
		Vec<((usize,usize), (usize,usize))>,  //optional extra join 
											  // constraints: two ranges
		Vec<usize> //optional map of CyclePairInput
	);

	/// given word input, previous witness, try to construct
	/// the full problem statement (including non-deterministic witness). 
	/// NOTE that the real i/o has only two elements in z_i array.
	///
	/// b_dummy_mode is added specifically for composable_gadget_mapper
	/// the other legacy code can ignore it.
	/// `job_id` is passed for logging purposes.
	fn build_statement(&self, word: &Vec<F>, prev_stmt: &Option<StatementInst<F,LK>>, lkup: Arc<LK>, extra_info: &StatementExtraInfo<F>, advice: Arc<dyn NdAdvice + Send + Sync>, lkup_size: usize, b_dummy_mode: bool, job_id: usize) -> Result<StatementInst<F,LK>, Error>;

	/// return the max word length that can be processed
	fn max_word_len(&self) -> usize;

	/// Generate the advice using its own capacity.
	/// If return nil, it means it cannot handle it
	/// seg_id is used for debugging purpose usually.
	/// `job_id` is passed for logging purposes.
	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, seg_id: usize, job_id: usize)
		->Result<Arc<dyn NdAdvice + Send + Sync>, Error>;

	/// (component_name, gadget_count) spans in get_gadgets() order.
	/// Default: a single span over all gadgets. CompositeGadgetMapper
	/// overrides this to expose per-component (CP/SED/DFA) boundaries.
	fn component_spans(&self) -> Vec<(String, usize)>{
		vec![(self.get_name(), self.get_gadgets().len())]
	}
}

/// Extra (mostly sequence) info for build statement
/// In 3 passes of driver, some returns and some uses it
#[derive(Clone,Debug,PartialEq)]
pub struct StatementExtraInfo<F:PrimeField>{
	/// circ_id starting from 0
	pub pc_i: F,
	/// the next circ_id
	pub pc_i1: F,
	/// total words
	pub total_words: F,
	/// subseg_id, starting from 1
	pub subseg_id: F,
	/// total_word_len
	pub total_word_len: F,
	/// word_id: starting from 1
	pub word_id: F,
	/// n_circ:
	pub n_circ: F,
	/// total_word_segs
	pub total_word_segs: F,
	/// the actual word_subsegment size
	pub act_word_subseg_size: F,
	/// random the challenge in SnarkAdvice (used for finger printing

	// - the following added for supporting batch proof
	/// vec_r[i] for batch proof (i is the current word ID)
	pub batch_r: F,
	/// vec_v[i] for batch proof
	pub batch_v: F,
	/// ONLY used once for the initial statement instance
	pub r_all_words: F,
	/// ONLY used once for the initial (random vector for kzg len)
	pub r_kzg_len: F,
	/// ONLY used once for the initial
	pub r_vec_r: F,
	/// ONLY used once for the initial
	pub r_vec_v: F,
	/// used very time for encoding kzg_w_i (individual proof),
	/// retrived from rands[i] from SnarkAdvice
	pub r_word_i: F,
	/// accumuated word length (for the current word)
	pub accumulated_word_len: F,
}

impl <F:PrimeField> StatementExtraInfo<F>{
	pub fn dump(&self){
		emit_stdout(format!(
			"StmtExtra: pc_i: {}, pc_i1: {}, total_words: {}, \
			subseg_id: {}, total_word_len: {}, word_id: {}, \
			n_circ: {}, total_word_segs: {}, \
			act_word_subseg_size: {}",
			self.pc_i, self.pc_i1, self.total_words,
			self.subseg_id, self.total_word_len, self.word_id,
			self.n_circ, self.total_word_segs,
			self.act_word_subseg_size));
	}

	pub fn dummy(n_circ: F, _ch: F) -> Self{
		let zero = F::zero();
		let one = F::one();
		Self{
			pc_i: n_circ - one,
			pc_i1: n_circ - one,
			total_words: zero,
			subseg_id: zero,
			total_word_len: zero,
			word_id: zero,
			n_circ: n_circ,
			total_word_segs: zero,
			act_word_subseg_size: zero,

			batch_r: zero,
			batch_v: zero,
			r_all_words: zero,
			r_kzg_len: zero,
			r_vec_r: zero,
			r_vec_v: zero,
			r_word_i: zero,
			accumulated_word_len: zero
		}
	}
}

/// Non-deterministic advice, used for build witness.
/// The structure of statement, which consists of
/// FIXED size (per circuit-type) input output buffers,
/// shares of lookup (right equation of Hab22 approach),
/// fragment of words. (Note that each Statement/circuit
/// supports one sub-segment of a word (a word may span over
/// multiple statements). So it has a word_id and also
/// the sugeg_id. 
///
/// Note that StatementInst is essentially a vector of external_inputs 
/// (witness, non-deterministic advice). The real I/O has only
/// 2 elements in z_i. We reason about StatementInst as the input
/// that results in hashed info in z_i. Note that ALL members of
/// StatementInst are part of FIXED MEMORY committed in the first pass.
#[derive(Clone,Debug)]
pub struct StatementInst<F:PrimeField, LK: LookupTableTwoCol<F>>{
	/// current PC. Note that in our application context, any pc could be valid,
	/// the Driver will pick the best, starting from 0
	/// pc_i is the circuit id to perform folding on (U_i,u_i)
	pub pc_i: F,
	/// next PC i (needs to be provided as a nondeterministic advice),
	/// see the Driver class.  It is the `j` in the SuperNova paper
	/// which performs the calculation `z_{i+1} = F_j(z_i, w_i)`.
	pub pc_i1: F,
	/// the number of circs
	pub n_circ: F,
	/// n_circ - pc_i - 1, which facilitates range check (must be 0 or positive)
	pub n_circ_minus_pc: F, 

	/// actual elements in input buffer (must be smaller than
	/// hard coded max_input_size.
	pub act_input_size: F,
	/// actual elements in output buffer
	pub act_output_size: F,
	/// actual elements in lookup buffer
	pub act_lookup_share_size: F,
	/// actual word subsegment size 
	pub act_word_subseg_size: F,
	/// word id, starting from 1
	pub word_id: F,
	/// sugseg_id (each circuit covers), starting from 1
	pub subseg_id: F, 
	/// word_len (the total len of word)
	pub total_word_len: F,
	/// total number segments of the current word
	pub total_word_segs: F,
	/// total number of words (of the entire batch job),
	/// by comparing (word_id, subseg_id) with (total_words, total_word_segs)
	/// we can tell if this is the LAST module in the job.
	pub total_words: F,
	/// r_F (this should be a random) - non-deterministic witness,
	/// we pull it up here to avoid non-deterministic behavior
	/// in prover to generate hashchain of cmF
	pub r_F: F,

	// - the following added for supporting batch proof
	/// vec_r[i] for batch proof (i is the current word ID)
	pub batch_r: F,
	/// vec_v[i] for batch proof
	pub batch_v: F,
	/// ONLY used once for the initial statement instance
	pub r_all_words: F,
	/// ONLY used once for the initial (random vector for kzg len)
	pub r_kzg_len: F,
	/// ONLY used once for the initial
	pub r_vec_r: F,
	/// ONLY used once for the initial
	pub r_vec_v: F,
	/// used very time for encoding kzg_w_i (individual proof),
	/// retrived from rands[i] from SnarkAdvice
	pub r_word_i: F,
	/// accumuated word length (for the current word)
	pub accumulated_word_len: F,
	/// the logical result of the current step (it reflects the
	/// logical processing of the current step), will be passed onto
	/// ZiPartTwo
	pub f_result: F,

	// --- actual data below ---
	/// input buffer. 
	pub inp_buf: Vec<F>,
	/// output buffer
	pub oup_buf: Vec<F>,
	/// one segment of a word (this maybe one of many segments of a long word)
	pub word_subseg: Vec<F>,
	/// other problem statement data
	pub data: Vec<F>,
	/// sub_table ID (its size should be inp_buf + oup_buf + subseg + data), 
	/// i.e.,
	/// only inp_buf, oup_buf, subseg, data can be tagged with lookup table info.
	/// when subtable_id for an entry is 0, it means not in table.
	pub subtable_id: Vec<F>,
	/// the Mangrove approach to distribute col1 entries of lookup table
	/// the size of col1_share, col2_share, and m_share are both of
	/// act_lookup_share_size and maxed by lookup_share
	pub col1_share: Vec<F>,
	/// col2 share
	pub col2_share: Vec<F>,
	/// the vec m value share, later it computes m_i/(col1 * beta + col2 + gamma) using the Hab'22 logup approach. 
	pub m_share: Vec<F>,

	/// the failed sigs, required to be padded by 0,
	/// all elements should be distinct!
	pub failed_sigs: Vec<F>,
	/// the discharged sigs. except 0 padding,
	/// it should be EXACTLY failed_sigs.
	/// Avoid generating duplicatings when generating WordInfo
	/// and DischargeSigInfo, when constructing the proof.
	pub discharged_sigs: Vec<F>,
	/// to prove that failed_sigs is a subset of discharged_sigs (as multi-set)
	/// this is essentially a lookup relation and its size is
	/// the size of discharged_sig
	pub mtbl_sigs: Vec<F>,

	pub _lk: PhantomData<LK>
}

/// The R1CS Var version (one to one corresponding to StatementInst)
#[derive(Clone,Debug)]
pub struct StatementInstVar<F:PrimeField>{
	/// current PC. Note that in our application context, any pc could be valid,
	/// the Driver will pick the best
	pub pc_i: FpVar<F>,
	/// next PC i (needs to be provided as a nondeterministic advice),
	/// see the Driver class. 
	pub pc_i1: FpVar<F>,
	/// the number of circs
	pub n_circ: FpVar<F>,
	/// n_circ - pc_i, which facilitates range check
	pub n_circ_minus_pc: FpVar<F>, 

	/// actual elements in input buffer (must be smaller than
	/// hard coded max_input_size.
	pub act_input_size: FpVar<F>,
	/// actual elements in output buffer
	pub act_output_size: FpVar<F>,
	/// actual elements in lookup buffer
	pub act_lookup_share_size: FpVar<F>,
	/// actual word subsegment size 
	pub act_word_subseg_size: FpVar<F>,
	/// word id
	pub word_id: FpVar<F>,
	/// sugseg_id (each circuit covers 
	pub subseg_id: FpVar<F>,
	/// word_len (the total len of word)
	pub total_word_len: FpVar<F>,
	/// total number segments of the current word
	pub total_word_segs: FpVar<F>,
	/// total number of words (of the entire batch job),
	/// by comparing (word_id, subseg_id) with (total_words, total_word_segs)
	/// we can tell if this is the LAST module in the job.
	pub total_words: FpVar<F>,
	/// r_F (this should be a random) - non-deterministic witness,
	/// we pull it up here to avoid non-deterministic behavior
	/// in prover to generate hashchain of cmF
	pub r_F: FpVar<F>,

	// - the following added for supporting batch proof
	/// vec_r[i] for batch proof (i is the current word ID)
	pub batch_r: FpVar<F>,
	/// vec_v[i] for batch proof
	pub batch_v: FpVar<F>,
	/// ONLY used once for the initial statement instance
	pub r_all_words: FpVar<F>,
	/// ONLY used once for the initial (random vector for kzg len)
	pub r_kzg_len: FpVar<F>,
	/// ONLY used once for the initial
	pub r_vec_r: FpVar<F>,
	/// ONLY used once for the initial
	pub r_vec_v: FpVar<F>,
	/// used very time for encoding kzg_w_i (individual proof),
	/// retrived from rands[i] from SnarkAdvice
	pub r_word_i: FpVar<F>,
	/// accumuated word length (for the current word)
	pub accumulated_word_len: FpVar<F>,

	/// the logical result of the current step (it reflects the
	/// logical processing of the current step), will be passed onto
	/// ZiPartTwo
	pub f_result: FpVar<F>,


	// --- actual data below ---
	/// input buffer. 
	pub inp_buf: Vec<FpVar<F>>,
	/// output buffer
	pub oup_buf: Vec<FpVar<F>>,
	/// one segment of a word (this maybe one of many segments of a long word)
	pub word_subseg: Vec<FpVar<F>>,
	/// other problem statement data
	pub data: Vec<FpVar<F>>,
	/// sub_table ID (its size should be inp_buf + oup_buf + subseg + data), 
	/// i.e.,
	/// only inp_buf, oup_buf, data can be tagged with lookup table info.
	/// when subtable_id for an entry is 0, it means not in table.
	pub subtable_id: Vec<FpVar<F>>,
	/// the Mangrove approach to distribute col1 entries of lookup table
	/// the size of col1_share, col2_share, and m_share are both of
	/// act_lookup_share_size and maxed by lookup_share
	pub col1_share: Vec<FpVar<F>>,
	/// col2 share
	pub col2_share: Vec<FpVar<F>>,
	/// the vec m value share, later it computes m_i/(col1 * beta + col2 + gamma) using the Hab'22 logup approach. 
	pub m_share: Vec<FpVar<F>>,

	/// the failed sigs
	pub failed_sigs: Vec<FpVar<F>>,
	/// the discharged sigs
	pub discharged_sigs: Vec<FpVar<F>>,
	/// same length of discharged_sigs
	pub mtbl_sigs: Vec<FpVar<F>>,
}

/// The configure structure of StatementInstance.
/// A StatementInstance is essentially the non-deterministic 
/// advice (witness)
#[derive(Debug,Clone,PartialEq)]
pub struct StatementConfig{
	/// fixed allocation of input buffer
	pub input_size: usize,
	/// fixed allocation of output buffer
	pub output_size: usize,
	/// size of the word_subseg
	pub word_subseg_size: usize,
	/// size of the data section
	pub data_size: usize, 
	/// fixed allocation of lookup buffer
	pub lookup_share_size: usize,

	/// start idx of input buffer in vectorized statement
	pub idx_inp: usize,
	/// start idx of output buffer
	pub idx_oup: usize,
	/// start idx of word subsegment
	pub idx_word_subseg: usize,
	/// start idx of data
	pub idx_data: usize,
	/// start idx of subtable_id
	pub idx_subtable_id: usize,
	/// start idx of col1_share
	pub idx_col1_share: usize,
	/// start idx of col2_share
	pub idx_col2_share: usize,
	/// start index of m_share
	pub idx_m_share: usize,

	/// the buffer size of failed_sig
	pub failed_sigs_size: usize,
	/// the buffer size of discharged_sigs buffer
	pub discharged_sigs_size: usize,
	/// the mtable sigs len (=discharged_sigs_size)
	pub mtbl_sigs_size: usize,
	/// the starting idx of failed_sigs
	pub idx_failed_sigs: usize,
	/// the starting idx of the discharged_sigs
	pub idx_discharged_sigs: usize,
	/// the starting location of mtbl_sigs
	pub idx_mtbl_sigs: usize,

	/// the chunk info of the si_data
	/// bool indicates if it's const segment.
	/// usize is the length of the segment
	pub si_data_info: Vec<(usize,bool)>,
	pub si_inp_info: Vec<(usize,bool)>,
	pub si_oup_info: Vec<(usize,bool)>,

	/// if true, si_data, inp, and oup will be set to constant
	pub b_cyclepair: bool,
}

impl StatementConfig{
	pub fn new(input_size: usize, output_size: usize,
		word_subseg_size: usize, data_size: usize, 
		lookup_share_size: usize, 
		failed_sigs_size: usize, discharged_sigs_size: usize,
		b_cyclepair: bool)
	->Self{
		let idx_inp = 23;
		let idx_oup = idx_inp + input_size;
		let idx_word_subseg = idx_oup + output_size;
		let idx_data = idx_word_subseg + word_subseg_size;
		let idx_subtable_id = idx_data + data_size;
		let subtable_size = input_size + output_size + data_size;
		let idx_col1_share = idx_subtable_id + subtable_size;
		let idx_col2_share = idx_col1_share + lookup_share_size;
		let idx_m_share = idx_col2_share + lookup_share_size;
		let idx_failed_sigs = idx_m_share + lookup_share_size;
		let idx_discharged_sigs = idx_failed_sigs + failed_sigs_size;
		let idx_mtbl_sigs = idx_discharged_sigs + discharged_sigs_size;
		let mtbl_sigs_size = discharged_sigs_size;
		let b_val = if b_cyclepair {true} else {false};
		let si_data_info = vec![(data_size, b_val)];
		let si_inp_info = vec![(input_size, b_val)]; //by default,
		let si_oup_info = vec![(output_size, b_val)]; //by default,
			//cover entire sid_data table and not constant (no optimization)

		Self{ input_size, output_size, data_size, word_subseg_size, 
			lookup_share_size, 
			idx_inp, idx_oup, idx_word_subseg, 
			idx_data, idx_subtable_id, idx_col1_share,
			idx_col2_share, idx_m_share, 
			failed_sigs_size, discharged_sigs_size,
			idx_failed_sigs, idx_discharged_sigs,
			idx_mtbl_sigs, mtbl_sigs_size,
			si_data_info,
			si_inp_info,
			si_oup_info,
			b_cyclepair
		}
	}

	pub fn reset_si_info(&mut self, 
		info_data: Vec<(usize, bool)>,
		info_inp: Vec<(usize, bool)>,
		info_oup: Vec<(usize, bool)>
	){
		let total_data_size = info_data.iter().map(|(x,_)| x).sum::<usize>();
		assert!(total_data_size == self.data_size);
		let total_inp_size = info_inp.iter().map(|(x,_)| x).sum::<usize>();
		assert!(total_inp_size == self.input_size);
		let total_oup_size = info_oup.iter().map(|(x,_)| x).sum::<usize>();
		assert!(total_oup_size == self.output_size);

		self.si_data_info = info_data;
		self.si_inp_info = info_inp;
		self.si_oup_info = info_oup;
	}

	pub fn total_size(&self)-> usize{
		let log_level = LOG7;
		let b_perf = true;
		let sub_table_size = self.input_size + self.output_size + 
			self.data_size;

		if b_perf{
			log(0, log_level, &format!(" ### Statement Total Size = inp: {} + oup: {} + data: {} + word: {} + lkup_share: {} x 3 + subtbl: {} + idx_inp: {} + failed_sig: {} + discharged_sig: {} +  mtbl_sigs: {}", 
				self.input_size,
				self.output_size,
				self.data_size,
				self.word_subseg_size,
				self.lookup_share_size,
				sub_table_size,
				self.idx_inp,
				self.failed_sigs_size,
				self.discharged_sigs_size,
				self.mtbl_sigs_size
			));
		}
		self.input_size + self.output_size + self.data_size + 
			self.word_subseg_size + self.lookup_share_size * 3
			+ sub_table_size +  self.idx_inp 
			+ self.failed_sigs_size 
			+ self.discharged_sigs_size 
			+ self.mtbl_sigs_size
	}
}

impl <F:PrimeField, LK: LookupTableTwoCol<F>> StatementInst<F, LK>{
	/// static function: update a vector of statments using lookup,
	/// return the HashMap of the m_vector for Hab'22 function
	/// Call this function when the RAM can store all statements.
	pub fn update_with_lkup(lk: &Arc<LK>, vec_stmt: &mut Vec<StatementInst<F,LK>>){
		//1. build the m_vec hash based on existing statements
		let n_steps = vec_stmt.len();
		let mut m_map = HashMap::<usize,usize>::new();
		for i in 0..n_steps{
			let stmt = &vec_stmt[i];
			stmt.fill_lkup_mvec(&mut m_map, lk);
		}

		//2. update the statements for m_vec and share
		let lk_len = lk.get_size();
		let share_size = if lk_len>n_steps {lk_len/n_steps} else {1usize};
		for i in 0..n_steps{
			//update_lookup will auto-correct index
			let start = i*share_size;
			let end = if i==n_steps-1 {lk_len} else {(i+1)*share_size};
			vec_stmt[i].update_lookup(start,end,lk,&m_map);
		}

	}

	/// generate the extra info part
	pub fn to_extra_info(&self)->StatementExtraInfo<F>{
		StatementExtraInfo::<F>{
			pc_i: self.pc_i,
			pc_i1: self.pc_i1,
			total_words: self.total_words,
			subseg_id: self.subseg_id,
			total_word_len: self.total_word_len,
			word_id: self.word_id,
			n_circ: self.n_circ,
			total_word_segs: self.total_word_segs,
			act_word_subseg_size: self.act_word_subseg_size,

			batch_r: self.batch_r,
			batch_v: self.batch_v,
			r_all_words: self.r_all_words,
			r_kzg_len: self.r_kzg_len,
			r_vec_r: self.r_vec_r,
			r_vec_v: self.r_vec_v,
			r_word_i: self.r_word_i,
			accumulated_word_len: self.accumulated_word_len,
		}
	}


	pub fn gen_config(&self, b_cyclepair: bool)->StatementConfig{
		assert!(self.col1_share.len() == self.col2_share.len() 
			&& self.col1_share.len() == self.m_share.len() );
		assert!(self.subtable_id.len()==self.inp_buf.len() + self.oup_buf.len()+  self.data.len());
		StatementConfig::new(
			self.inp_buf.len(),
			self.oup_buf.len(),
			self.word_subseg.len(),
			self.data.len(),
			self.col1_share.len(),
			self.failed_sigs.len(),
			self.discharged_sigs.len(),
			b_cyclepair
		)
	}

	/// print up to 10 elements
	fn print_vec(v: &Vec<F>, name: &str){
		let max_n = 165;
		assert!(v.len()<max_n);
		let n = if v.len()<max_n {v.len()} else {max_n};
		// Build the full line in one String so the drainer emits
		// it atomically (one `send` per logical output line).
		let mut line = format!("{}: ", name);
		for i in 0..n{
			line.push_str(&format!("{}, ", v[i]));
		}
		emit_stdout(line);
	}
	/// mainly for printing purpose
	pub fn dump(&self){
		emit_stdout(
			"--- DUMP of Statement Instance ---".to_string());
		emit_stdout(format!("word_id: {}", self.word_id));
		emit_stdout(format!("subseg_id: {}", self.subseg_id));
		Self::print_vec(&self.word_subseg, "subseg");
		emit_stdout(format!("pc_i: {}", self.pc_i));
		emit_stdout(format!("pc_i1: {}", self.pc_i1));
		emit_stdout(format!("n_circ: {}", self.n_circ));
		emit_stdout(format!(
			"n_circ_minus_pc: {}", self.n_circ_minus_pc));
		emit_stdout(format!(
			"act_input_size: {}", self.act_input_size));
		emit_stdout(format!(
			"act_output_size: {}", self.act_output_size));
		emit_stdout(format!(
			"act_lookup_share_size: {}",
			self.act_lookup_share_size));
		emit_stdout(format!(
			"act_word_subseg_size: {}",
			self.act_word_subseg_size));
		emit_stdout(format!(
			"total_word_len: {}", self.total_word_len));
		emit_stdout(format!(
			"total_word_segs: {}", self.total_word_segs));
		emit_stdout(format!("total_words: {}", self.total_words));
		emit_stdout(format!("r_F: {}", self.r_F));
		emit_stdout(format!(
			"failed_sigs len: {}", self.failed_sigs.len()));
		emit_stdout(format!(
			"discharged_sigs len: {}",
			self.discharged_sigs.len()));
		Self::print_vec(&self.inp_buf, "inp_buf");
		Self::print_vec(&self.oup_buf, "oup_buf");
		Self::print_vec(&self.word_subseg, "word_subseg");
		Self::print_vec(&self.data, "data");
		Self::print_vec(&self.subtable_id, "subtable_id");
		Self::print_vec(&self.col1_share, "col1_share");
		Self::print_vec(&self.col2_share, "col2_share");
		Self::print_vec(&self.m_share, "m_share");
		Self::print_vec(&self.failed_sigs, "failed_sigs");
		Self::print_vec(&self.discharged_sigs, "discharged_sigs");
		Self::print_vec(&self.mtbl_sigs, "mtbl_sigs");
		emit_stdout(
			"---- DUMP COMPLETED ---------\n".to_string());
	}

	/// serialize into one vector
	pub fn to_vec(&self) -> Vec<F>{
		assert!(self.subtable_id.len() == self.inp_buf.len()  + 
			self.oup_buf.len() + self.data.len());
		let res = vec![
			vec![
				self.pc_i,
				self.pc_i1,
				self.n_circ,
				self.n_circ_minus_pc,

				self.act_input_size.clone(), 
				self.act_output_size.clone(), 
				self.act_lookup_share_size.clone(), 
				self.act_word_subseg_size.clone(), 
				self.word_id.clone(),
				self.subseg_id.clone(), 
				self.total_word_len.clone(),
				self.total_word_segs.clone(),
				self.total_words.clone(),
				self.r_F.clone(),

				self.batch_r.clone(),
				self.batch_v.clone(),
				self.r_all_words.clone(),
				self.r_kzg_len.clone(),
				self.r_vec_r.clone(),
				self.r_vec_v.clone(),
				self.r_word_i.clone(),
				self.accumulated_word_len.clone(),

				self.f_result.clone(),
			],
			self.inp_buf.clone(), 
			self.oup_buf.clone(), 
			self.word_subseg.clone(),
			self.data.clone(),
			self.subtable_id.clone(), 
			self.col1_share.clone(), 
			self.col2_share.clone(), 
			self.m_share.clone(),
			self.failed_sigs.clone(),
			self.discharged_sigs.clone(),
			self.mtbl_sigs.clone(),
		].concat();

		res
	}

	/// deserialize from one vec
	pub fn from_vec(cfg: &StatementConfig, vec: &Vec<F>)->Self{
		let pc_i = vec[0];
		let pc_i1 = vec[1];
		let n_circ = vec[2];
		let n_circ_minus_pc = vec[3];

		let act_input_size = vec[4];
		let act_output_size = vec[5];
		let act_lookup_share_size = vec[6];
		let act_word_subseg_size = vec[7];
		let word_id = vec[8];
		let subseg_id = vec[9];
		let total_word_len = vec[10];
		let total_word_segs = vec[11];
		let total_words = vec[12];
		let r_F = vec[13];
	
		let batch_r = vec[14];
		let batch_v = vec[15];
		let r_all_words = vec[16];
		let r_kzg_len = vec[17];
		let r_vec_r = vec[18];
		let r_vec_v = vec[19];
		let r_word_i = vec[20];
		let accumulated_word_len = vec[21];

		let f_result= vec[22];

		let inp_buf = (&vec[cfg.idx_inp..cfg.idx_inp+cfg.input_size]).to_vec();
		let oup_buf = (&vec[cfg.idx_oup..cfg.idx_oup+cfg.output_size]).to_vec();
		let word_subseg = (&vec[cfg.idx_word_subseg..cfg.idx_word_subseg+cfg.word_subseg_size]).to_vec();
		let data= (&vec[cfg.idx_data..cfg.idx_data+cfg.data_size]).to_vec();
		let subtable_id= (&vec[cfg.idx_subtable_id..cfg.idx_subtable_id+cfg.input_size+cfg.output_size+cfg.data_size]).to_vec();
		let col1_share = (&vec[cfg.idx_col1_share..cfg.idx_col1_share+cfg.lookup_share_size]).to_vec(); 
		let col2_share = (&vec[cfg.idx_col2_share..cfg.idx_col2_share+cfg.lookup_share_size]).to_vec(); 
		let m_share = (&vec[cfg.idx_m_share..cfg.idx_m_share+cfg.lookup_share_size]).to_vec(); 
		let failed_sigs= (&vec[cfg.idx_failed_sigs..cfg.idx_failed_sigs+cfg.failed_sigs_size]).to_vec(); 
		let discharged_sigs= (&vec[cfg.idx_discharged_sigs..cfg.idx_discharged_sigs+cfg.discharged_sigs_size]).to_vec(); 
		let mtbl_sigs= (&vec[cfg.idx_mtbl_sigs..cfg.idx_mtbl_sigs+cfg.mtbl_sigs_size]).to_vec(); 
		Self{
			pc_i, pc_i1, n_circ, n_circ_minus_pc,
			act_input_size, act_output_size, act_lookup_share_size,
			act_word_subseg_size, word_id, subseg_id, total_word_len,
			total_word_segs,
			total_words, r_F,
			batch_r, batch_v,r_all_words, r_kzg_len, r_vec_r, 
				r_vec_v, r_word_i, accumulated_word_len,
				f_result,
			inp_buf, oup_buf, word_subseg, data, subtable_id,
			col1_share, col2_share, m_share, 
			failed_sigs, discharged_sigs,
			mtbl_sigs,
			_lk: PhantomData,

		}
	}

	/// update the lookup shares (usually we need a first pass of all steps
	/// statements to compute m_vec. Then distribute the shares again).
	/// The end_idx is not included.
	/// will auto-correct start and end_idx if out of bound
	pub fn update_lookup(&mut self, start_idx: usize, end_idx: usize, lk: &Arc<LK>, map_m: &HashMap<usize, usize>){
		//1. from lkup table retrieve col1, col2
		let lk = lk;
		if start_idx>=lk.get_size() {
			self.act_lookup_share_size = F::zero();
			return;
		}
		let end_idx = if end_idx>=lk.get_size() {lk.get_size()} else {end_idx};
		let size = end_idx - start_idx;
		assert!(self.col1_share.len()==self.col2_share.len() 
			&& self.m_share.len()==self.col1_share.len() 
			&& self.m_share.len()>=size);
		let (mut col1, mut col2):(Vec<F>,Vec<F>) = lk.get_cols_slice(start_idx, end_idx);
		let left_over = self.col1_share.len()-size;
		col1.extend(std::iter::repeat(F::zero()).take(left_over));
		col2.extend(std::iter::repeat(F::zero()).take(left_over));


		//2. compute the m_shares
		let mut m_shares = LookupTableTwoCol_Inst::<F>
			::gen_m_share(start_idx, end_idx, map_m);
		m_shares.extend(std::iter::repeat(F::zero()).take(left_over));
		self.col1_share = col1;
		self.col2_share = col2;
		self.m_share = m_shares;
		self.act_lookup_share_size = F::from(size as u32);
	}

	/// fill up the m_vec of lookup table using the inp, oup,
	/// word_seg, data, and also also the info for unused_inp_buf
	/// etc which are in the witness before the statement.
	pub fn fill_lkup_mvec(&self, m_map: &mut HashMap<usize, usize>, 
		lk: &Arc<LK>){
		//1. fill in the data using problem statement data
		let lk_ref = lk;
		let tbl_ids = self.subtable_id.clone();
		let mut vec_val  = vec![self.inp_buf.clone(), self.oup_buf.clone(), 
			self.data.clone()].concat();

		assert!(tbl_ids.len()==vec_val.len());

		for j in 0..tbl_ids.len(){ 
			//if tbl_id is 0, make the entry to be 0 to fit null entry
			if tbl_ids[j].is_zero() {vec_val[j] = F::zero();} 
		}

		//2. prepare the witness for extra_vars:
		// unused_inp_size and unused_oup_size
		// subtable 1 is used as range table. We assert that they are in
		// range
		let (zero,_one) = (F::zero(), F::one());
		let tbl_ids_wit = vec![zero, zero]; 
		let vals_wit= vec![
			F::from(self.inp_buf.len() as u32) - self.act_input_size,
			F::from(self.oup_buf.len() as u32) -self.act_output_size];
		//even though vals_wit is simulated, it gives correct update
		//to m_map because we exect unused_input_size and unused ouput_size
		//in range.


		lk_ref.fill_mvec(&tbl_ids, &vec_val, m_map);
		lk_ref.fill_mvec(&tbl_ids_wit, &vals_wit, m_map);
	}
}

impl <F:PrimeField> StatementInstVar<F>{
	/// deserialize from one vec
	pub fn from_vec(cfg: &StatementConfig, vec: &Vec<FpVar<F>>)->Self{
		let pc_i = vec[0].clone();
		let pc_i1 = vec[1].clone();
		let n_circ = vec[2].clone();
		let n_circ_minus_pc = vec[3].clone();

		let act_input_size = vec[4].clone();
		let act_output_size = vec[5].clone();
		let act_lookup_share_size = vec[6].clone();
		let act_word_subseg_size = vec[7].clone();
		let word_id = vec[8].clone();
		let subseg_id = vec[9].clone();
		let total_word_len = vec[10].clone();
		let total_word_segs = vec[11].clone();
		let total_words = vec[12].clone();
		let r_F = vec[13].clone();

		let batch_r = vec[14].clone();
		let batch_v = vec[15].clone();
		let r_all_words = vec[16].clone();
		let r_kzg_len = vec[17].clone();
		let r_vec_r = vec[18].clone();
		let r_vec_v = vec[19].clone();
		let r_word_i = vec[20].clone();
		let accumulated_word_len = vec[21].clone();
		let f_result = vec[22].clone();

		let inp_buf = (&vec[cfg.idx_inp..cfg.idx_inp+cfg.input_size]).to_vec();
		let oup_buf = (&vec[cfg.idx_oup..cfg.idx_oup+cfg.output_size]).to_vec();
		let word_subseg = (&vec[cfg.idx_word_subseg..cfg.idx_word_subseg+cfg.word_subseg_size]).to_vec();
		let data= (&vec[cfg.idx_data..cfg.idx_data+cfg.data_size]).to_vec();
		let subtable_id= (&vec[cfg.idx_subtable_id..cfg.idx_subtable_id+cfg.input_size+cfg.output_size+cfg.data_size]).to_vec();
		let col1_share = (&vec[cfg.idx_col1_share..cfg.idx_col1_share+cfg.lookup_share_size]).to_vec(); 
		let col2_share = (&vec[cfg.idx_col2_share..cfg.idx_col2_share+cfg.lookup_share_size]).to_vec(); 
		let m_share = (&vec[cfg.idx_m_share..cfg.idx_m_share+cfg.lookup_share_size]).to_vec(); 
		let failed_sigs= (&vec[cfg.idx_failed_sigs..cfg.idx_failed_sigs+cfg.failed_sigs_size]).to_vec(); 
		let discharged_sigs= (&vec[cfg.idx_discharged_sigs..cfg.idx_discharged_sigs+cfg.discharged_sigs_size]).to_vec(); 
		let mtbl_sigs= (&vec[cfg.idx_mtbl_sigs..cfg.idx_mtbl_sigs+cfg.mtbl_sigs_size]).to_vec(); 
		Self{
			pc_i, pc_i1, n_circ, n_circ_minus_pc,
			act_input_size, act_output_size, act_lookup_share_size,
			act_word_subseg_size, word_id, subseg_id, total_word_len,
			total_word_segs,
			inp_buf, oup_buf, word_subseg, data, subtable_id,
			col1_share, col2_share, m_share, total_words, r_F,
			batch_r, batch_v, r_all_words, r_kzg_len, r_vec_r, r_vec_v, 
				r_word_i, accumulated_word_len, f_result,
			failed_sigs, discharged_sigs, mtbl_sigs
		}
	}
}

/// Block of information that hashes to z_i.1 (we call it
/// part two of z_i). Note that z_i.0 is the hashchain of cmF.
///
/// The contents are mainly used to support input/output buffer
/// and batch word processing, i.e., information to be passed
/// between sequential circuits, that depends on the
/// Fiat-shamir challenges (randoms) that depends on FIXED MEMORY
/// segment (e.g., accumulated sum of Hab22 equation
/// for lookup). We choose to HASH them into one element for saving cost.
/// In SuperNova: this would save the cost because for each step
/// all other non-active step circuit just copies over z_i which
/// is only two field elements (hashchain of cmF and hash of ZiPartTwoInst), 
/// this saves the linear hash cost
/// for supernova. Note that hashchain is necessary, as
/// the folded commitment relies on the nonce that is the random
/// oracle of all (including msg3 and ZiPartTwoInst).
/// We also include an optional CyclePairInputVar (160 FpVar)
/// when it is running in full mode. This incurs extra cost of 40k R1CS
/// however, not impacting the main circuit (only used in driver stage 2).
#[derive(Clone,Debug)]
pub struct ZiPartTwoInst<F:PrimeField>{
	/// random nonce for computing sum of input and output
	/// it should be equal to ro(hashchain(fixed segment), kzg_all_words,
	/// kzg_all_len, kzg_vec_i, kzg_vec_v)
	pub ch: F,
	/// Random combination for folding kzg evaluations
	pub rc: F,
	/// sum from i to n of `r^(n-i) inp_i` across chain,
	/// computed using Holmer method.
	pub sum_inp: F,
	/// Homer's method computed weighted sum of `r^(n-i)  oup_i`
	pub sum_oup: F,

	/// alpha and beta used for Hab'22 lookup scheme.
	/// left: 1/(alpha +col1val*beta + col2val) of query table.
	/// right: m_i/(alpha + col1val*beta + cal2val) of lookup table.
	/// then sum up m_i and the 1's for the lookup table
	pub alpha: F,
	/// beta used for lookup
	pub beta: F,
	/// the sum of Hab'22 equation for query table
	pub sum_hab22_left: F,
	/// the sum of Hab'22 equation for lookup table
	pub sum_hab22_right: F,
	/// sum of the randombly combined evaluation of kzg for
	/// [lkup1, lkup2, all_words, all_len, vec_r, vec_v]
	/// All vectors are REVERSED, as we use Homer's method for computing
	/// because we compute it as: ((a_0 * r) + a_1)*r ...) + a_n,
	/// (See BatchProof in batch_proc.rs).
	/// Part 1 is the sum of lkup1, lkup2 with rc applied

	pub sum_kzg_eval_lk: F,
	/// Part 2 is the sum of concatenated words
	pub sum_kzg_eval_word: F,
	/// Part 3 is the sum of all_len, vec_r, vec_v as they were
	/// accumulated only once per word
	pub sum_kzg_eval_others: F,
	/// current value of vec_v_i, for computing vec_v[i] for each word,
	/// when a word has multiple segments
	pub sum_vec_v_i: F,

	/// the total length of the CURRENT word
	/// will be set up at the FIRST subsegement of the word
	pub total_word_len: F,
	/// The accumulated LENGTH of all processed segment
	/// until the current one. For example, if the 1st segment
	/// is 5 in length, the acc_word_len is 5 for it.
	/// total_word_len and accumulated_word_len is used to
	/// determine the VALIDITY of the updates of word_id and
	/// subseg_id in the StatementInstance, e.g., when accumulated_word_len
	/// is equal to the act_segement_len in the Statement instance,
	/// this implies that it is the beginning segment of a word.
	/// To save cost, we do not save other attributes such as
	/// word_id, segment_id in ZiPartTwo (instead, leave them in the 
	/// witness and verify they are valid).
	pub accumulated_word_len: F,

	/// word_id starting from 1
	pub word_id: F,
	/// subseg_id starting from 1 
	pub subseg_id: F,
	/// total number of segs in the current word
	pub total_word_segs: F,
	/// total number of words
	pub total_words: F,

	/// the F's logical output (if there are more, compress them using hash)
	pub f_result: F,

	/// input represented as field elements optional only when Zi is full mode
	pub cyclepair_input: Option<CyclePairInput<F>>,
}

#[derive(Clone,Debug)]
pub struct CyclePairInput<F: PrimeField>{
	/// [gt1, a, b, gt2] encoded as F.
	/// For BN254, gt1, a, b, gt2 corresponds to
	/// 12, 3, 5, 12 Fq (base prime field) elements.
	/// Based on NonNativeUInt limb setting (55 bits), they
	/// are encoded using 5 limbs each. Thus altogether (32x5 = 160) Fr
	/// elements. 
	pub x: Vec<F>,
	/// the bits of Fq (base prime field) modulus
	pub fq_bits: usize,
}


impl <F:PrimeField> CyclePairInput<F>
{
	/// fq_bits: moduls bits of Fq (which the gt, a, b, gt2 are actually 
	/// encoded)
	pub fn dummy(fq_bits: usize)->Self{
		let size = Self::total_size(fq_bits);
		Self{ x: vec![F::zero(); size], fq_bits: fq_bits }
	}

	/// constructor from the [gt1, a, b, gt2] instance. 
	pub fn from<E:Pairing<G1=C1>,C1:CurveGroup<ScalarField=F,BaseField=F2>,
		F2: PrimeField>(gt1: &E::TargetField, a: &E::G1, 
		b: &E::G2, gt2: &E::TargetField) ->Self
		where E::G1: ToConstraintField<F2>,
				E::G2: ToConstraintField<F2>,
				E::TargetField: ToConstraintField<F2>
	{
		let vec_a = a.to_field_elements().unwrap();
		let vec_b = b.to_field_elements().unwrap();
		let vec_gt1 = gt1.to_field_elements().unwrap();
		let vec_gt2 = gt2.to_field_elements().unwrap();
		let vec1 = vec![vec_gt1, vec_a, vec_b, vec_gt2].concat();
		let res = vec1.iter().map(|x|
			f1_to_f2_limbs::<F2, F>(x)
		).collect::<Vec<Vec<F>>>()
		.concat();

		Self{x: res, fq_bits: F2::MODULUS_BIT_SIZE as usize}
	}


	/// estimate the total size given fq_bits (fr_bits from F)
	/// fq_bits should be Fq::MODULUS_BIT_SIZE
	pub fn total_size(fq_bits: usize)->usize{
		let num_fq = 32usize; //gt1, gt2 12 each, a 3, b 5 => 32
		let limb_size = NonNativeUintVar::<F>::bits_per_limb() as usize;
		let limbs = fq_bits.div_ceil(limb_size);

		num_fq * limbs
	}

}

/// Pack a collection of FpVar into a NonNativeUintVar,
/// Treat each as a LimbVar. Assuming that they are
/// already well formed in range of 55-bit uint.
pub fn pack_fp_nonnative<F:PrimeField>(v: &Vec<FpVar<F>>)
	->NonNativeUintVar<F>{
	let limb_size = NonNativeUintVar::<F>::bits_per_limb() as usize;
	let ub =  (BigUint::one() << limb_size) - BigUint::one();
	let vec_limbs = v.into_iter().map(|x|{
		LimbVar::<F>{v: x.clone(), ub: ub.clone()}
	}).collect::<Vec<LimbVar<F>>>();
	let res = NonNativeUintVar::<F>( vec_limbs );

	res
}


/// Represents cycle pair instance. It represents
/// the CyclePair instance: [gt1, a, b, gt2] 
/// where gt1 and gt2 are 12 field elements, a,b are 3 and 5 each
/// Total size: 32 NonNativeUintVar field elements.
/// As limb size is 55 bits each limb, each NonNativeFieldElement
/// translates to 5 FpVar (although not packed).
#[derive(Clone,Debug)]
pub struct CyclePairInputVar<F:PrimeField>{
	/// corresponding to the x in CyclePairInput
	/// for BN254, its length will be 32 (packing every 5 into one)
	pub x: Vec<NonNativeUintVar<F>>,
	/// the bits of Fq (base prime field) modulus
	pub fq_bits: usize,
}

impl <F:PrimeField> CyclePairInputVar<F>{
	/// from the cycle pair input generate its Var version in constraints.
	pub fn from(cs: ConstraintSystemRef<F>, ci: &CyclePairInput<F>)->Self{
		let chunks = 32;
		let ratio = ci.x.len().div_ceil(chunks);
		let nvars = ci.x.chunks(ratio)
			.map(|chunk| {
				let chunk_var = Vec::<FpVar::<F>>
					::new_witness(cs.clone(), || Ok(chunk)).unwrap();
				let res = pack_fp_nonnative(&chunk_var);

				res
			})
			.collect::<Vec<NonNativeUintVar<F>>>();
		assert!(nvars.len()==chunks);		
		Self{x: nvars, fq_bits: ci.fq_bits}
	}

	/// converting a FpVar (keeping the ratio at 55-bits each - e.g.,
	/// 5 FpVars for Bn254/Grumpkin.)
	/// for easier implementation (although can only pack further 
	/// to 2 FpVars.  Total size: 160 FpVar (for BN254).
	/// This incurs about  160 x 250 = 40k R1CS when folding,
	/// acceptable as it's only used for generating succinct
	/// stage 2 proofs for SuperNova.
	///
	/// NOTE: bit ops slow. But should not be a big concern
	/// as it's only used in the 2nd stage.
	pub fn to_vec(&self) -> Vec<FpVar<F>>{
		let bits_per_limb = NonNativeUintVar::<F>::bits_per_limb();
		let limbs = self.x[0].to_bits_le().unwrap().chunks(bits_per_limb).len();
		let res = self.x.iter().map( |u|{ //each u is a NonNativeUintVar
			let vec_frs = u.0.iter().map(|limbvar|
					limbvar.v.clone() ).collect::<Vec<FpVar<F>>>();
			assert!(vec_frs.len()==limbs, "vec_fr.len() != {}", limbs);
			vec_frs
		}).collect::<Vec<Vec<FpVar<F>>>>().into_iter()
		.flatten().collect::<Vec<FpVar<F>>>();
		//note that res would be 64 (2 elements needed actually)
		assert!(res.len()==limbs * self.x.len());
		res
	}

	/// From (e.g., for BN254) 160 FpVar -> 32 NonNativeUintVar.
	pub fn from_vec(v: &Vec<FpVar<F>>, fq_bits: usize)->Self{
		let cs = v[0].cs();
		let limb_size = NonNativeUintVar::<F>::bits_per_limb() as usize;
		let ratio = fq_bits.div_ceil(limb_size);
		let chunks = 32;
		assert!(chunks * ratio == v.len());

		let nvars = v.chunks(ratio)
			.map(|chunk| {
				let chunk_var = chunk.into_iter().map(|x|
				  FpVar::<F>::new_witness(cs.clone(),
				  	|| Ok(x.value().unwrap())).unwrap()
				).collect::<Vec<FpVar<F>>>();
				let res = pack_fp_nonnative(&chunk_var);

				res
			})
			.collect::<Vec<NonNativeUintVar<F>>>();
		
		Self{x: nvars, fq_bits: fq_bits}

	}
}


#[derive(Clone,Debug)]
pub struct ZiPartTwoInstVar<F:PrimeField>{
	/// random nonce for computing sum of input and output
	/// it should be equal to ro(hashchain(fixed segment))
	pub ch: FpVar<F>,
	/// random combination factor for combined kzg
	pub rc: FpVar<F>,
	/// sum from i to n of `r^(n-i) inp_i` across chain,
	/// computed using Holmer method.
	pub sum_inp: FpVar<F>,
	/// Homer's method computed weighted sum of `r^(n-i)  oup_i`
	pub sum_oup: FpVar<F>,

	/// alpha and beta used for Hab'22 lookup scheme.
	/// left: 1/(alpha +col1val*beta + col2val) of query table.
	/// right: m_i/(alpha + col1val*beta + cal2val) of lookup table.
	/// then sum up m_i and the 1's for the lookup table
	pub alpha: FpVar<F>,
	/// beta used for lookup
	pub beta: FpVar<F>,
	/// the sum of Hab'22 equation for query table
	pub sum_hab22_left: FpVar<F>,
	/// the sum of Hab'22 equation for lookup table
	pub sum_hab22_right: FpVar<F>,

	/// sum of the randombly combined evaluation of kzg for
	/// [lkup1, lkup2, all_words, all_len, vec_r, vec_v]
	/// All vectors are REVERSED, as we use Homer's method for computing
	/// because we compute it as: ((a_0 * r) + a_1)*r ...) + a_n,
	/// (See BatchProof in batch_proc.rs). Part is the
	/// accumulation of lkup1 and lkup2
	pub sum_kzg_eval_lk: FpVar<F>,
	/// Part 2 is the sum of concatenated words
	pub sum_kzg_eval_word: FpVar<F>,
	/// Part 3 is the sum of all_len, vec_r, vec_v as they were
	/// accumulated only once per word
	pub sum_kzg_eval_others: FpVar<F>,
	/// current value of vec_v_i, for computing vec_v[i] for each word,
	/// when a word has multiple segments
	pub sum_vec_v_i: FpVar<F>,

	/// the total length of word
	pub total_word_len: FpVar<F>,
	/// the current accumulated length of word
	pub accumulated_word_len: FpVar<F>,

	/// word_id starting from 1
	pub word_id: FpVar<F>,
	/// subseg_id starting from 1 
	pub subseg_id: FpVar<F>,
	/// total number of segs in the current word
	pub total_word_segs: FpVar<F>,
	/// total number of words
	pub total_words: FpVar<F>,

	/// the logical result of the F function.
	pub f_result: FpVar<F>,

	/// optional when it's in full mode
	pub cyclepair_input: Option<CyclePairInputVar<F>>,
}

impl <F:PrimeField + Absorb> ZiPartTwoInst<F>{
	/// serialize to vec
	pub fn to_vec(&self)->Vec<F>{
		let mut res = vec![self.ch, self.rc, self.sum_inp, self.sum_oup, 
			self.alpha,
			self.beta, self.sum_hab22_left, self.sum_hab22_right,
			self.sum_kzg_eval_lk, self.sum_kzg_eval_word, 
			self.sum_kzg_eval_others, self.sum_vec_v_i,
			self.total_word_len, 
			self.accumulated_word_len,
			self.word_id, self.subseg_id, self.total_word_segs, 
			self.total_words, self.f_result];
		let mut cp = self.cyclepair_input.as_ref().map_or(vec![], |cp_i| 
			cp_i.x.clone());
		res.append(&mut cp);

		res
	}

	/// deserialize
	pub fn from_vec(vec: &Vec<F>, fq_bits: usize) ->Self{
		//1. length check
		let fixed_part = 19;
		if vec.len()!=fixed_part{ 
			assert!(vec.len() == 
				fixed_part+CyclePairInput::<F>::total_size(fq_bits));
		}
		let cp_input = if vec.len()>fixed_part {
			Some(CyclePairInput{x: vec[fixed_part..]
				.to_vec(), fq_bits: fq_bits})
		} else {None};
		Self{
			ch: vec[0].clone(),
			rc: vec[1].clone(),
			sum_inp: vec[2].clone(),
			sum_oup: vec[3].clone(),

			alpha: vec[4].clone(),
			beta: vec[5].clone(),
			sum_hab22_left: vec[6].clone(),
			sum_hab22_right: vec[7].clone(),

			sum_kzg_eval_lk: vec[8].clone(),
			sum_kzg_eval_word: vec[9].clone(),
			sum_kzg_eval_others: vec[10].clone(),
			sum_vec_v_i: vec[11].clone(),


			total_word_len: vec[12].clone(),
			accumulated_word_len: vec[13].clone(),

			word_id: vec[14].clone(),
			subseg_id: vec[15].clone(),
			total_word_segs: vec[16].clone(),
			total_words: vec[17].clone(),

			f_result: vec[18].clone(),

			cyclepair_input:  cp_input,
		}
	}

	/// create dummy object
	pub fn dummy(b_full: bool, fq_bits: usize)->Self{
        let poseidon_config = poseidon_canonical_config::<F>();
		Self::new(F::zero(), F::zero(), &poseidon_config, b_full, fq_bits, 0)
	}

	/// return the ZiPartTwoInst size
	pub fn size(b_full: bool, fq_bits: usize)->usize{
		Self::dummy(b_full, fq_bits).to_vec().len()
	}

	/// use hash(hc_cmF, kzg_lookup, kzg_word) as random nonce seed.
	pub fn new(ch: F, rc: F, ps_cfg: &PoseidonConfig<F>, b_full: bool, 
		fq_bits: usize, num_words: usize)->Self{
		let zero = F::zero();
        let mut sponge_alpha = PoseidonSponge::<F>::new(&ps_cfg);
		sponge_alpha.absorb(&rc);
		let alpha = sponge_alpha.squeeze_field_elements(1)[0];
		sponge_alpha.absorb(&alpha);
		let beta = sponge_alpha.squeeze_field_elements(1)[0];
		let cp_inp = if b_full {
			Some(CyclePairInput::<F>::dummy(fq_bits))
		} else {None};
		Self{ch: ch, rc: rc, 
			sum_inp: zero, sum_oup:zero,
			alpha: alpha, beta: beta,
			sum_hab22_left: zero, sum_hab22_right: zero,
			sum_kzg_eval_lk: zero, 
			sum_kzg_eval_word: zero, 
			sum_kzg_eval_others: zero, 
			sum_vec_v_i: zero, 
			total_word_len: zero, 
			accumulated_word_len: zero,
			word_id: zero, subseg_id: zero, total_word_segs: zero, 
			total_words: F::from(num_words as u32),
			f_result: F::zero(),
			cyclepair_input: cp_inp,
			}
	}

	/// hash to one element to use as zi.1
	pub fn hash(&self, ps_cfg: &PoseidonConfig<F>)->F{
        let mut sponge = PoseidonSponge::<F>::new(ps_cfg);
		let vec = self.to_vec();
		sponge.absorb(&vec);
		let res = sponge.squeeze_field_elements(1)[0];

		res
	}
}

impl <F:PrimeField + Absorb> ZiPartTwoInstVar<F>{
	/// serialize to vec
	pub fn to_vec(&self)->Vec<FpVar<F>>{
		let mut res = vec![
			self.ch.clone(), self.rc.clone(),
			self.sum_inp.clone(), self.sum_oup.clone(),
			self.alpha.clone(), self.beta.clone(),
			self.sum_hab22_left.clone(), self.sum_hab22_right.clone(),
			self.sum_kzg_eval_lk.clone(), self.sum_kzg_eval_word.clone(), 
			self.sum_kzg_eval_others.clone(), self.sum_vec_v_i.clone(),
			self.total_word_len.clone(), self.accumulated_word_len.clone(),
			self.word_id.clone(), self.subseg_id.clone(),
			self.total_word_segs.clone(), self.total_words.clone(),
			self.f_result.clone()];
		if self.cyclepair_input.is_some(){
			let mut v1 = self.cyclepair_input.as_ref().expect("cp null")
				.to_vec();
			res.append(&mut v1);
		}
		res
	}

	/// deserialize
	pub fn from_vec(vec: &Vec<FpVar<F>>, fq_bits: usize) ->Self{
		let fixed_part = 19;
		if vec.len()!=fixed_part{ 
			assert!(vec.len() == fixed_part
				+CyclePairInput::<F>::total_size(fq_bits));
		}
		let cp_input = if vec.len()>fixed_part {
			let vec_fp = vec[fixed_part..].to_vec();
			Some(CyclePairInputVar::from_vec(&vec_fp, fq_bits))
		} else {None};
		Self{
			ch: vec[0].clone(),
			rc: vec[1].clone(),
			sum_inp: vec[2].clone(),
			sum_oup: vec[3].clone(),

			alpha: vec[4].clone(),
			beta: vec[5].clone(),
			sum_hab22_left: vec[6].clone(),
			sum_hab22_right: vec[7].clone(),

			sum_kzg_eval_lk: vec[8].clone(),
			sum_kzg_eval_word: vec[9].clone(),
			sum_kzg_eval_others: vec[10].clone(),
			sum_vec_v_i: vec[11].clone(),

			total_word_len: vec[12].clone(),
			accumulated_word_len: vec[13].clone(),

			word_id: vec[14].clone(),
			subseg_id: vec[15].clone(),
			total_word_segs: vec[16].clone(),
			total_words: vec[17].clone(),

			f_result: vec[18].clone(),

			cyclepair_input: cp_input,
		}
	}

	/// convert from real instance
	pub fn from<C:CurveGroup<ScalarField=F>>(
		inst: &ZiPartTwoInst<F>, cs: ConstraintSystemRef<F>)->Self{
		let vec_zi:Vec<F> = inst.to_vec();
		let vec_zi_var = vec_zi.iter().map(|f| 
			FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<F>>>();
		let fq_bits = <<C as CurveGroup>::BaseField as Field>
			::BasePrimeField::MODULUS_BIT_SIZE as usize;
		ZiPartTwoInstVar::from_vec(&vec_zi_var, fq_bits)
	}

	/// hash to one element to use as zi.1
	pub fn hash(&self, ps_cfg: &PoseidonConfig<F>, cs: ConstraintSystemRef<F>)->FpVar<F>{
        let mut sponge = PoseidonSpongeVar::<F>::new(cs, ps_cfg);
		let vec = self.to_vec();
		sponge.absorb(&vec).expect("absort err");
		let res=sponge.squeeze_field_elements(1).expect("hash err")[0].clone();

		res
	}
}

/// The structure information of the WitnessSigmaIR1CS
#[derive(Clone,Debug)]
pub struct WitnessSigmaIR1CSConfig{
	/// size of cmF converted to field elemnets (will be constant 4)
	pub cmF_size: usize,
	/// extra var size before statement
	pub extra_var_size: usize,
	/// size of the statement
	pub statement_size: usize,
	/// size of msg1
	pub msg1_size: usize,
	/// size of msg2
	pub msg2_size: usize, 
	/// size of msg3
	pub msg3_size: usize,
	/// size of zi_part2
	pub zi_part2_size: usize,
	/// statement mapping: for each gadget there is a vector of
	/// RANGES of indices into the statement (combined)
	pub stmt_map: Vec<Vec<(usize,usize)>>,
	/// for each gadget 4 element tuple indicates the size of
	/// statement, msg1, msg2, msg3 for each component
	pub vec_msg_sizes: Vec<(usize, usize, usize, usize)>,
	/// should be equal to: size of cmF, extra vars before statement,
	/// statement, and msg1 (i.e., 6 + subtbl_id.size of ProblemInst)
	pub inv_hab22_left_size: usize,
	/// should be equal to the m_share (max) size
	pub inv_hab22_right_size: usize,

	/// statement config
	pub stmt_cfg: StatementConfig,
}
 
impl WitnessSigmaIR1CSConfig{
	/// compute the size_F, mainly compute the statement_size + msg1_size
	/// minus the contents in the statement, because we only count
	/// witness variables.
	pub fn get_size_f(&self)->usize{
		let raw_size_F = self.statement_size + self.msg1_size;

		let si_data_info = &self.stmt_cfg.si_data_info;
		let si_inp_info = &self.stmt_cfg.si_inp_info;
		let si_oup_info = &self.stmt_cfg.si_oup_info;
		let all_info = [&si_data_info[..], 
			&si_inp_info[..], &si_oup_info[..]].concat();
		let total_const = all_info.iter().filter(|(_,b)| *b)
			.map(|(size,_)| size).sum::<usize>();

		raw_size_F - total_const
	}

	/// length of the cmF-committed vector (stmt + msg1) as actually
	/// committed in gen_witness; includes constant statement entries,
	/// unlike get_size_f which counts only witness variables.
	pub fn get_cmf_len(&self) -> usize {
		self.statement_size + self.msg1_size
	}

	/// return the stmt_idx for statement, then the starting
	/// idx for msg1, msg2, msg3 in the combined message segments.
	pub fn get_gadget_indices(&self, i: usize) 
		-> (Vec<(usize,usize)>, usize, usize, usize){
		let mut msg_idx = vec![0, 0, 0];
		for idx in 0..i{
			msg_idx[0] += self.vec_msg_sizes[idx].1;
			msg_idx[1] += self.vec_msg_sizes[idx].2;
			msg_idx[2] += self.vec_msg_sizes[idx].3;
		}
		(self.stmt_map[i].clone(), msg_idx[0], msg_idx[1], msg_idx[2])
	}

	/// get the total size if serialized into vector
	pub fn get_total_size(&self)->usize{
		let log_level = LOG7;
		log(0, log_level, &format!(" ### WITNESS structure: stmt_size: {}, msg1: {}, msg2: {}, msg3: {}, zi_part2: {}, inv_hab22_left: {} inv_hab22_right: {}", self.statement_size, self.msg1_size, self.msg2_size, self.msg3_size, self.zi_part2_size, self.inv_hab22_left_size, self.inv_hab22_right_size));
		self.cmF_size + self.extra_var_size + self.statement_size + 
		self.msg1_size + self.msg2_size + self.msg3_size + 
		self.zi_part2_size + 
		self.inv_hab22_left_size + self.inv_hab22_right_size
	}
}

/// Witness for the IR1CS. It contains multiple components
/// for supporting I/O of non-uniform, and batch of words (see paper)
/// by instantiating the Commit-and-Fold scheme as proposed in the
/// Mangrove paper
pub struct WitnessSigmaIR1CS<F:PrimeField>{
	/// commitment of statement + msg1
	pub cmF: Vec<F>, //will always be a vector of 4
	/// unused_input_size, unused_output_size all belong to
	/// extra_var_size
	pub unused_input_size: F,
	/// unused output (max_output_size - actual_output_size)
	pub unused_output_size: F,
	/// the concatenated statement from all subprotocols
	pub statement: Vec<F>,
	/// the concatenated msg1 from all subprotocols (gadgets)
	pub msg1: Vec<F>,
	/// the concatenated msg2 from all subprotocols
	pub msg2: Vec<F>,
	/// the concatenated msg3 from all subprotocols
	pub msg3: Vec<F>,
	/// the ZiPartTwoInst (which hashes to z_i.1). 
	pub zi_part2: Vec<F>,
	/// 1/(alpha + col1*beta + col2) for the query table (query table is
	///  cmF + extra vars + statement + msg1)
	pub inv_hab22_left: Vec<F>,
	/// m_i/(alpha + col1 + col2*col2) for the col1/col2 share
	pub inv_hab22_right: Vec<F>,
}

impl <F:PrimeField> WitnessSigmaIR1CS<F>{
	/// convert the witness instance to a vector of FpVar (may consists of
	/// constants + witness vars)
	pub fn to_vec_fp_var(&self, cs: ConstraintSystemRef<F>, cfg: &WitnessSigmaIR1CSConfig) ->Vec<FpVar<F>>{
		//0. define an assisting function to build col considering
		// the constants
		let init_vars = cs.num_witness_variables();
		let build_col = |si_info: &Vec<(usize,bool)>, vals: &[F]|
		->Vec<FpVar<F>>{
			let mut idx_start = 0;
			let mut vec_starts = vec![];
			for (ulen, _) in si_info{
				vec_starts.push(idx_start);
				idx_start += ulen;
			}
			assert!(vec_starts.len()==si_info.len());
			let fp_part2 = (0..vec_starts.len()).into_iter().map(|i|{
				let (ulen, b_const) = si_info[i];
				let start = vec_starts[i];
				let frag = &vals[start..start+ulen];
				if b_const{
					if B_DEBUG {
						let ele1 = frag[0];
						for i in 0..frag.len(){
							assert!(frag[i]==ele1);
						}
					}
					//frag.iter().map(|f|
					//	FpVar::<F>::new_constant(cs.clone(), f.clone()).unwrap()
					//).collect::<Vec<FpVar<F>>>()
					if frag.len()==0 {vec![]} else{
						let var = FpVar::<F>::new_constant(cs.clone(), frag[0].clone()) .unwrap();
						vec![var; frag.len()]
					}
				}else{
					frag.iter().map(|f|
						FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
					).collect::<Vec<FpVar<F>>>()
				}
			}).flatten().collect::<Vec<FpVar<F>>>();

			fp_part2
		};

		//1. build the part1: cmF, extra_vars before the statement
		let vec1 = self.cmF.iter()
			.chain(vec![self.unused_input_size, self.unused_output_size].iter())
			.map(|f| f.clone())
			.collect::<Vec<F>>();
		let z_i1 = vec1.iter().map(|f| 
			FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<F>>>();
		let size_F = cfg.get_size_f();

		//2. build the special stmt var (FIXED M part) - including
		// the statement and msg1. (excluding msg2, msg3 ...)
		// NOTE: constants are handled for si_data/inp/oup
		//2.1 set up the indexes and sizes for segments
		let stmt_cfg = &cfg.stmt_cfg;
		let si_data_info = &stmt_cfg.si_data_info;
		let si_inp_info = &stmt_cfg.si_inp_info;
		let si_oup_info = &stmt_cfg.si_oup_info;
		let data_len2 = si_data_info.iter().map(|(s,_)| s).sum::<usize>();
		let inp_len2 = si_inp_info.iter().map(|(s,_)| s).sum::<usize>();
		let oup_len2 = si_oup_info.iter().map(|(s,_)| s).sum::<usize>();
		let si_data_len = stmt_cfg.data_size;
		let si_inp_len = stmt_cfg.input_size;
		let si_oup_len = stmt_cfg.output_size;
		assert!(data_len2==si_data_len);
		assert!(inp_len2==si_inp_len);
		assert!(oup_len2==si_oup_len);
		assert!(self.statement.len()==stmt_cfg.total_size(), 
			"stmt.len: {} != cfg.total_size: {}", self.statement.len(),
			stmt_cfg.total_size());

		let idx_si_data = stmt_cfg.idx_subtable_id + stmt_cfg.input_size
			+stmt_cfg.output_size;
		let idx_si_inp= stmt_cfg.idx_subtable_id;
		let idx_si_oup= stmt_cfg.idx_subtable_id + stmt_cfg.input_size;

		let st_part1 = &self.statement[0..idx_si_inp];
		let st_inp= &self.statement[idx_si_inp..idx_si_oup];
		let st_oup= &self.statement[idx_si_oup..idx_si_data];
		let st_data= &self.statement[idx_si_data..idx_si_data+si_data_len];
		let st_part3 = &self.statement[idx_si_data+si_data_len..];

		//2.2 build the parts following their structure in witness
		let fp_part1 = st_part1.iter().map(|f|
			FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<F>>>();

		let new_st_inp = build_col(&si_inp_info, st_inp); //addressing consts
		let new_st_oup = build_col(&si_oup_info, st_oup);
		let new_st_data = build_col(&si_data_info, st_data);

		let fp_part3 = st_part3.iter().map(|f|
			FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<F>>>();

		let fp_m1 = self.msg1.iter().map(|f| 
			FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<F>>>();
		let _m1_len = self.msg1.len();

		let z_i2= [fp_part1, new_st_inp, new_st_oup, new_st_data, 
			fp_part3, fp_m1].concat();
		assert!(z_i2.len()==self.statement.len() + _m1_len);
		assert!(init_vars==0 || init_vars==6);
		assert!(size_F == cs.num_witness_variables() - init_vars - 6); //because
			//there are 12 vars before the start of F (fixed segment)
			// which is statement + msg1
			// see where 12 vars in mod.rs::PreprocessorParamFoldPot::new
			// NOTE that when the function is in "normal" workflow
			// the pp_hash, i, z_0 (2 ele), z_i (2 ele) is already
			// encoded into the constraint system by 
			// circuit_super.generate_constraints before calling
			// to_vec_fp_var(). So init_vars will have 6.
			// for gadgets unit testing function test_adv() it
			// does not do this, and the init_var is 0

		//2. assemble the the other parts
		let vec3 = self.msg2.iter().
			chain(self.msg3.iter()).
			chain(self.zi_part2.iter()).
			chain(self.inv_hab22_left.iter()).
			chain(self.inv_hab22_right.iter())
			.map(|f| f.clone())
			.collect::<Vec<F>>();

		let z_i3 = vec3.iter().map(|f| 
			FpVar::<F>::new_witness(cs.clone(), || Ok(f)).unwrap()
		).collect::<Vec<FpVar<F>>>();
		let res = [z_i1, z_i2, z_i3].concat();

		assert!(res.len()==cfg.get_total_size());
		res
	}

	/// return cmF
	pub fn gen_cmF<C:CurveGroup<ScalarField=F>,CS: CommitmentScheme<C,H>,const H:bool>(&self, params: &CS::ProverParams) -> Result<C, Error>
	{
		// note that r_F is in statement. No need for extra blinding factor
		let vec = vec![
			self.statement.clone(),
			self.msg1.clone()
		].concat();
		let zero = F::zero();
		let res = CS::commit(params, &vec, &zero);

		res
	}
}

/// Witness for the IR1CS. It contains multiple components
/// for supporting I/O of non-uniform, and batch of words (see paper)
/// by instantiating the Commit-and-Fold scheme as proposed in the
/// Mangrove paper
pub struct WitnessSigmaIR1CSVar<F:PrimeField> {
	/// the cmF
	pub cmF: Vec<FpVar<F>>,
	/// max_input_size - actual_input_size
	pub unused_input_size: FpVar<F>,
	/// max_output_size - actual_output_size
	pub unused_output_size: FpVar<F>,
	/// the concatenated statement from all subprotocols
	pub statement: Vec<FpVar<F>>,
	/// the concatenated msg1 from all subprotocols (gadgets)
	pub msg1: Vec<FpVar<F>>,
	/// the concatenated msg2 from all subprotocols
	pub msg2: Vec<FpVar<F>>,
	/// the concatenated msg3 from all subprotocols
	pub msg3: Vec<FpVar<F>>,
	/// the zi_part2
	pub zi_part2: Vec<FpVar<F>>,
	/// 1/(alpha + col1*beta + col2) for the query table (query table is
	///  cmF + extra vars + statement + msg1)
	pub inv_hab22_left: Vec<FpVar<F>>,
	/// m_i/(alpha + col1 + col2*col2) for the col1/col2 share
	pub inv_hab22_right: Vec<FpVar<F>>,
}

impl <F:PrimeField> WitnessSigmaIR1CSVar<F>{
	/// reconstruct the Witness structure from vec of F.
	pub fn from_vec(config: &WitnessSigmaIR1CSConfig, vec: &Vec<FpVar<F>>)
		-> Self{
		let mut start = 0;
		let cmF= vec[0..config.cmF_size].to_vec();
		start += config.cmF_size;

		let unused_input_size = vec[start].clone();
		start +=1;

		let unused_output_size = vec[start].clone();
		start +=1;

		let statement = vec[start..start+config.statement_size].to_vec();
		start += config.statement_size;

		let msg1 = vec[start..start+config.msg1_size].to_vec(); 
		start += config.msg1_size;

		let msg2 = vec[start..start+config.msg2_size].to_vec(); 
		start += config.msg2_size;

		let msg3 = vec[start..start+config.msg3_size].to_vec();
		start += config.msg3_size;

		let zi_part2= vec[start..start+config.zi_part2_size].to_vec();
		start += config.zi_part2_size;

		let inv_hab22_left = vec[start..
			start+config.inv_hab22_left_size].to_vec();
		start += config.inv_hab22_left_size;

		let inv_hab22_right = vec[start..
			start+config.inv_hab22_right_size].to_vec();
		start += config.inv_hab22_right_size;
		assert!(start>10); //will update 10 later.


		Self{
			cmF: cmF,
			unused_input_size: unused_input_size,
			unused_output_size: unused_output_size,
			statement: statement,
			msg1: msg1,
			msg2: msg2,
			msg3: msg3,
			zi_part2: zi_part2,
			inv_hab22_left: inv_hab22_left,
			inv_hab22_right: inv_hab22_right
		}
	}
}

/// the real implementation of SigmaIR1CS.
/// All ZkregPlus related circuits are instance of
/// SigmaIR1CS, which are composed of joinable gadgets.
pub struct SigmaIR1CS_Inst<F, C, CS, LK, GM, const H: bool = false>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb + ColEle,
		LK: LookupTableTwoCol<F>,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync,
{
	_lk: PhantomData<LK>,

	/// if full mode (supporting cyclepair). When supporting it,
	/// the ZiPartTwoInst has an extra component of 32-field eleents
	/// as cyclepair input.
	pub b_full_mode: bool,

	/// by default it should be true. Use false value
	/// when debug (a small lkup share which does not check the
	/// the entire lookup table).
	pub b_check_lkup: bool,

	/// if the instance is cyclepair, we will tag sid differently
	pub b_cyclepair: bool,

	/// name of the instance
	pub name: String,

	/// used for Fiat-Shamir random oracle
    pub poseidon_config: PoseidonConfig<F>,

	/// relation mapper: this is prototocol specific.
	/// It manages all sub-components and perform the
	/// check of their ``join relation" among the statements
	/// of each sigma-protcol gadgets. 
	pub gadget_mapper: Arc<Mutex<GM>>,

	/// All the witnesses (sturctured), generate by gadget_mapper
	/// Only set up when calling set_native.
	pub witness: Option<Arc<WitnessSigmaIR1CS<F>>>,

	/// Config of WitnessSigmaIR1CS for deseirliazation 
	pub witness_config: WitnessSigmaIR1CSConfig,

	/// Statement config
	pub stmt_config: StatementConfig,

	/// the list of gadgets
	pub gadgets: Vec<Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>>>,

	/// parameters of the commitment scheme
	pub params: CS::ProverParams,

	/// the bits of Fq
	pub fq_bits: usize,

	/// the value for dummy stmt
	pub dummy_stmt: Option<Vec<F>>,

	pub job_id: usize,
}

impl <F,C,CS,LK, GM, const H: bool> Debug for SigmaIR1CS_Inst<F,C,CS,LK,GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb + ColEle,
		LK: LookupTableTwoCol<F>,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync,
{
	fn fmt(&self, f: &mut Formatter<'_>)-> fmt::Result{
		f.debug_struct("SigmaRICS_Inst")
			.field("name", &self.name)
			.finish()
	}

}

impl <F,C,CS,LK, GM, const H: bool> SigmaIR1CS_Inst<F,C,CS,LK, GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb + ColEle,
		LK: LookupTableTwoCol<F>,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync
			+ GadgetMapperDeepClone,
{
	/// Build an independent copy of this circuit instance for a
	/// single job: the `gadget_mapper` and `gadgets` are rebuilt
	/// with fresh `Arc<Mutex<>>` wrappers so no locking is shared
	/// with the original. Heavy immutable data inside the mapper
	/// (ClamavDB, etc.) remains shared via `Arc::clone`.
	///
	/// 2026-05-14: also re-wrap each gadget through
	/// `clone_arc_sigma_gadget()` so the per-job clone gets fresh
	/// `Arc<Mutex<dyn SigmaGadget>>` shells. Without this, the
	/// gadget Mutexes are Arc-shared across jobs and `assert_msg3`
	/// serializes all jobs in the gen_step_cs hot loop (see
	/// stall_fix_2026-05-13 + manual_stall analysis 2026-05-14).
	pub fn clone_deep(&self) -> Self {
		let new_mapper_val: GM = self.gadget_mapper.lock().unwrap()
			.clone_deep_mapper();
		let new_mapper_arc = Arc::new(Mutex::new(new_mapper_val));
		let raw_gadgets = lock_unwrap!(new_mapper_arc).get_gadgets();
		// Per-job lock independence: rebuild each gadget's
		// Arc<Mutex<>> via the SigmaGadgetCloneBox blanket impl
		// (sigma_ir1cs.rs:380-392) which does
		// `Arc::new(Mutex::new(self.clone()))`. Gadget structs are
		// tiny (~150 B); heavy state is behind Arcs and stays
		// shared via the inner `.clone()`.
		let new_gadgets: Vec<Arc<Mutex<dyn SigmaGadget<F>
			+ Send + Sync>>> = raw_gadgets.iter()
			.map(|g| lock_unwrap!(g).clone_arc_sigma_gadget())
			.collect();
		Self{
			name: self.name.clone(),
			poseidon_config: self.poseidon_config.clone(),
			gadget_mapper: new_mapper_arc,
			witness: self.witness.clone(),
			witness_config: self.witness_config.clone(),
			gadgets: new_gadgets,
			stmt_config: self.stmt_config.clone(),
			params: self.params.clone(),
			b_full_mode: self.b_full_mode,
			fq_bits: self.fq_bits,
			dummy_stmt: self.dummy_stmt.clone(),
			_lk: PhantomData,
			b_cyclepair: self.b_cyclepair,
			b_check_lkup: self.b_check_lkup,
			job_id: self.job_id,
		}
	}
}

impl <F,C,CS,LK, GM, const H: bool> CloneDeep
	for SigmaIR1CS_Inst<F,C,CS,LK, GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb + ColEle,
		LK: LookupTableTwoCol<F>,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync
			+ GadgetMapperDeepClone,
{
	fn clone_deep_self(&self) -> Self { self.clone_deep() }
}

impl <F,C,CS,LK, GM, const H: bool> Clone for SigmaIR1CS_Inst<F,C,CS,LK, GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb + ColEle,
		LK: LookupTableTwoCol<F>,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync,
{
	fn clone(&self) -> Self{
		Self{
			name: self.name.clone(),
			poseidon_config: self.poseidon_config.clone(),
			gadget_mapper: self.gadget_mapper.clone(),
			witness: self.witness.clone(),
			witness_config: self.witness_config.clone(),
			gadgets: self.gadgets.clone(),
			stmt_config: self.stmt_config.clone(),
			params: self.params.clone(),
			b_full_mode: self.b_full_mode,
			fq_bits: self.fq_bits,
			dummy_stmt: self.dummy_stmt.clone(),
			_lk: PhantomData,
			b_cyclepair: self.b_cyclepair,
			b_check_lkup: self.b_check_lkup,
			job_id: self.job_id,
		}
	}
}

impl <F,C,CS,LK, GM, const H: bool> SigmaIR1CS_Inst<F,C,CS,LK, GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		LK: LookupTableTwoCol<F>,
		F: PrimeField + Absorb + ColEle,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync,
{
	/// Convert the witness to a vector of fp_var (call
	/// step_native_mut first
	pub fn witness_to_vec_fp_var(&self, cs: ConstraintSystemRef<F>)
	->Vec<FpVar<F>>{
		let wit = self.witness.as_ref();
		wit.expect("wit is null").to_vec_fp_var(cs, &self.witness_config)
	}

	pub fn get_mapper(&self) -> Arc<Mutex<GM>>{
		self.gadget_mapper.clone()
	}

	/// provide the information of poseidon config, mapper,
	/// whether full mode (supporting cyclepair), and
	/// bits of Fq (base prime field)
	pub fn gen_configs(g_mapper: Arc<Mutex<GM>>, b_full_mode: bool, lkup_share_size: usize)
		-> Result<(WitnessSigmaIR1CSConfig,StatementConfig),Error>{
		let gadgets = lock_unwrap!(g_mapper).get_gadgets();
		let (stmt_len, stmt_cfg, v_idx, _extra_joins, _ci_inp) = lock_unwrap!(g_mapper).gen_statement_structure(lkup_share_size);
		let vec_msg_sizes = gadgets.iter().map(|g| lock_unwrap!(g).get_msg_size())
			.collect::<Vec<(usize, usize, usize, usize)>>();
		let mut m1_len = 0usize;
		let mut m2_len = 0usize;
		let mut m3_len = 0usize;
		for (i,_g) in gadgets.iter().enumerate(){
			m1_len += vec_msg_sizes[i].1;
			m2_len += vec_msg_sizes[i].2;
			m3_len += vec_msg_sizes[i].3;
		}

		let cmF_size = 4usize;
		let extra_var_size = 2usize;
		let si = StatementInst::<F,LK>::from_vec(&stmt_cfg, &vec![F::zero(); stmt_len]);
		let inv_hab22_left_size = si.subtable_id.len() + extra_var_size;
		// right side is the lookup table share

		let fq_bits = <<C as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let inv_hab22_right_size = si.col1_share.len();
		let wtns_cfg = WitnessSigmaIR1CSConfig{
			cmF_size: cmF_size, //4 field elements for cmF
			extra_var_size: extra_var_size, 
				//unused_input_size, unused_output_size
			statement_size: stmt_len,
			stmt_map: v_idx,
			msg1_size: m1_len,
			msg2_size: m2_len,
			msg3_size: m3_len,
			vec_msg_sizes: vec_msg_sizes,
			zi_part2_size: ZiPartTwoInst::<F>::size(b_full_mode, fq_bits),
			inv_hab22_left_size: inv_hab22_left_size,
			inv_hab22_right_size: inv_hab22_right_size,
			stmt_cfg: stmt_cfg.clone(),
		};

		Ok( (wtns_cfg, stmt_cfg) )
	}


	/// generate the witness structure
	pub fn gen_witness_structure(&self, lkup_share_size: usize) 
		-> WitnessSigmaIR1CSConfig{
		let gadgets = lock_unwrap!(self.gadget_mapper).get_gadgets();
		//generate witness config, no need of info such as
		//extra join constraints and map to cyclepair
		let (stmt_len, stmt_cfg, v_idx, _, _) = lock_unwrap!(self.gadget_mapper).gen_statement_structure(lkup_share_size);
		let vec_msg_sizes = gadgets.iter().map(|g| lock_unwrap!(g).get_msg_size())
			.collect::<Vec<(usize, usize, usize, usize)>>();
		let mut m1_len = 0usize;
		let mut m2_len = 0usize;
		let mut m3_len = 0usize;
		for (i,_g) in gadgets.iter().enumerate(){
			m1_len += vec_msg_sizes[i].1;
			m2_len += vec_msg_sizes[i].2;
			m3_len += vec_msg_sizes[i].3;
		}

		let cmF_size = 4usize;
		let extra_var_size = 2usize;
		let si = StatementInst::<F,LK>::from_vec(&stmt_cfg, 
			&vec![F::zero(); stmt_len]);
		// right side is the lookup table share
		let inv_hab22_right_size = si.col1_share.len();
		let inv_hab22_left_size = si.subtable_id.len() + extra_var_size;
		let wtns_cfg = WitnessSigmaIR1CSConfig{
			cmF_size: cmF_size, //4 field elements for cmF
			extra_var_size: extra_var_size, 
				//unused_input_size, unused_output_size
			statement_size: stmt_len,
			stmt_map: v_idx,
			msg1_size: m1_len,
			msg2_size: m2_len,
			msg3_size: m3_len,
			vec_msg_sizes: vec_msg_sizes,
			zi_part2_size: ZiPartTwoInst::<F>::size(self.b_full_mode, self.fq_bits),
			inv_hab22_left_size: inv_hab22_left_size,
			inv_hab22_right_size: inv_hab22_right_size,
			stmt_cfg: stmt_cfg,
		};
		wtns_cfg
	}
}


impl <F,C,CS,LK, GM,const H: bool> SigmaIR1CS<H,F,LK,GM> 
for SigmaIR1CS_Inst<F,C,CS,LK, GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb + ColEle,
		LK: LookupTableTwoCol<F>,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync,
{
	type C = C;
	type CS = CS;

	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, advice: &Arc<dyn NdAdvice + Send + Sync>){ 
		lock_unwrap!(self.gadget_mapper).set_container_config(advice);
		assert!(self.stmt_config== self.witness_config.stmt_cfg);
		let (wtns_cfg, stmt_cfg) = Self::gen_configs(self.gadget_mapper.clone(),
			self.b_full_mode, self.witness_config.stmt_cfg.lookup_share_size)
			.expect("set_container_cfg err");	
		self.witness_config = wtns_cfg;
		self.stmt_config = stmt_cfg;
	}

	fn is_cyclepair(&self)->bool{
		self.b_cyclepair
	}

	fn is_check_lkup(&self)->bool{
		self.b_check_lkup
	}


	/// return the estimated cost in terms of number of constraints.
	/// This is mainly used to apply heurstics to pick the applicable
	/// circuit with minimal cost for a given word
	fn est_cost(&self)->usize{
		//1. get config data
		let (scfg,wcfg) = (&self.stmt_config, &self.witness_config);
		let (ilen,olen,wlen,dlen,lklen) =  (scfg.input_size, scfg.output_size, scfg.word_subseg_size, scfg.data_size, scfg.lookup_share_size);
		let (_m1len, m2len, _m3len) = (wcfg.msg1_size, wcfg.msg2_size, wcfg.msg3_size);
		//2. compute gadgets and step cost for each step
		let gadgets = lock_unwrap!(self.get_mapper()).get_gadgets();
		let gadgets_cost:usize = gadgets.iter().map(|g| lock_unwrap!(g).est_cost()).sum();

		let subtbl_id_len = ilen + olen + wlen + dlen; 
		let (llen,rlen) = (subtbl_id_len+14, lklen); //inv_hab_left and right

		let vec_costs = vec![
			("step 1", 0),
			("step 2", m2len*598), //each hash costs almost 600 R1CS!
			("step 3: gadgets cost", gadgets_cost),
			("step 4: gadgets cost", 12*(ilen+olen)),
			("step 5: logup", 7*llen + 13*rlen ),
			("step 6: word_id", 18 ),
			("step 7: kzg ", if self.b_full_mode {0} else {
				12 + lklen*7  + 11*wlen +  24   
			}),
			("step 8: extra join (assumption constant size)", 1),
			("step 9: cycle_inp", if self.b_full_mode {32 * 5 + 2} else {2}),
			("step 10: hash cmf fixed cost", 2094),
		];
		let total_size =  vec_costs.iter().map(|(_,s)| s).sum::<usize>();


		total_size
	}

	/// return the statement config
	fn get_stmt_config(&self)->StatementConfig{
		self.stmt_config.clone()
	}

	fn get_lkup_share_size(&self)->usize{
		self.stmt_config.lookup_share_size
	}


	/// whether it's supporting cycle pair
	fn is_full_mode(&self) -> bool {self.b_full_mode}

	/// return the name	
	fn get_name(&self) -> String {lock_unwrap!(self.gadget_mapper).get_name()}

	/// return the max word length it can process
	fn max_word_len(&self)-> usize{
		lock_unwrap!(self.gadget_mapper).max_word_len()
	}

	/// return the clone of Rc pointer
	fn get_mapper(&self)->Arc<Mutex<GM>>{
		self.gadget_mapper.clone()
	}

	/// generate the commitment to the fixed memory segment
	/// it actually has the same first part of gen_witness
	fn gen_cmF(&self, stmt: &Vec<F>, _zi_part2: &ZiPartTwoInst<F>) -> Result<Self::C, Error>{
		//0. check input, will not need the extra constraints
		// will be enforced somewhere else, but need
		// the cyclepair input
		let lkup_share_size = self.stmt_config.lookup_share_size;
		let (stmt_len, _stmt_cfg, v_idx, _, _cp_inp) = lock_unwrap!(self.gadget_mapper).gen_statement_structure(lkup_share_size); 
		assert!(stmt_len==stmt.len(), "stmt.len(): {} != stmt_len: {}",
			stmt.len(), stmt_len);
		let v_stmt = stmt.clone();
		assert!(v_idx.len()==self.gadgets.len(), "v_idx.len(): {} != gadgets.len: {}", v_idx.len(), self.gadgets.len());
		let vec_msg_sizes = self.gadgets.iter().map(|g| lock_unwrap!(g)
			.get_msg_size())
			.collect::<Vec<(usize, usize, usize, usize)>>();
		let mut v_msg1:Vec<F> = vec![];

		//1. generate message1
		for (i,g) in self.gadgets.iter().enumerate(){
			let mut msg1 = lock_unwrap!(g).gen_msg1(&v_stmt, &v_idx[i]) ;
			assert!(vec_msg_sizes[i].1==msg1.len(), 
				"ERROR: mistaching msg1 size for i: {}", i);
			v_msg1.append(&mut msg1); 
		}
		//2. generate cmF
		// note that r_F is in statement. No need for extra blinding factor
		let vec = vec![
			stmt.clone(),
			v_msg1.clone()
		].concat();
		let (zero,_one) = (F::zero(),F::one());
		let grp_cmF = Self::CS::commit(&self.params, 
			&vec, &zero).expect("commit fails");

		Ok( grp_cmF )
	}

	/// Given the problem statement, and the part 2 contents
	/// of z_i, generate a witness and its config.
	/// Input ZiPartTwoInst is the raw input
	/// which hashes to z_i.1 (note that z_i.0 is the hashchain of F), 
	/// and returns
	/// (Witness, WitnessSig, ZiPartTwoInst). 
	/// The 3rd element of the return is the part 2 of
	/// the `z_{i+1}` part 2), that is the contents of `z_{i+1}`
	/// for the next global state of the circ.
	fn gen_witness(&self, stmt: &Vec<F>, zi_part2: &ZiPartTwoInst<F>, precomputed_group_cmF: Option<Self::C>) -> (WitnessSigmaIR1CS<F>, WitnessSigmaIR1CSConfig, ZiPartTwoInst<F>)
	{
		//0. check input, will not need the extra constraints
		// will be enforced somewhere else, but need
		// the cyclepair input
		let log_level = LOG7;
		let b_debug = B_DEBUG;

		let mut gt1 = GTimer::new();
		let lkup_share_size = self.stmt_config.lookup_share_size;
		let (stmt_len, stmt_cfg, v_idx, _, cp_inp) = lock_unwrap!(self.gadget_mapper)
			.gen_statement_structure(lkup_share_size);
		assert!(stmt_len==stmt.len(), "stmt.len(): {} != stmt_len: {}",
			stmt.len(), stmt_len);
		let v_stmt = stmt.clone();
		// 2026-05-16: probe 77317.5 — at gen_witness entry, the
		// F-valued stmt vector is what will be wrapped as witness.
		// We slice out the failed/discharged/mtbl regions per
		// stmt_cfg indices and dump them. Used to discriminate
		// upstream (build_statement) vs downstream (to_vec_fp_var /
		// from_vec) corruption.
		if crate::folding::foldpot::utils::probe_77317_enabled() {
			use crate::folding::foldpot::utils::{
				probe_77317_dump_f_vec,
				probe_77317_multiset_diff};
			let if_ = stmt_cfg.idx_failed_sigs;
			let nf  = stmt_cfg.failed_sigs_size;
			let id_ = stmt_cfg.idx_discharged_sigs;
			let nd  = stmt_cfg.discharged_sigs_size;
			let im_ = stmt_cfg.idx_mtbl_sigs;
			let nm  = stmt_cfg.mtbl_sigs_size;
			emit_stdout(format!(
				"DEBUG USE 77317.5: gen_witness ENTRY job={} \
				 stmt.len={} idx_failed={} fail_sz={} \
				 idx_discharged={} disch_sz={} \
				 idx_mtbl={} mtbl_sz={}",
				self.job_id, stmt.len(),
				if_, nf, id_, nd, im_, nm));
			if if_ + nf <= stmt.len()
				&& id_ + nd <= stmt.len()
				&& im_ + nm <= stmt.len() {
				let f_slice = &stmt[if_..if_ + nf];
				let d_slice = &stmt[id_..id_ + nd];
				let m_slice = &stmt[im_..im_ + nm];
				probe_77317_dump_f_vec("5.failed",
					"stmt[failed]", f_slice);
				probe_77317_dump_f_vec("5.discharged",
					"stmt[discharged]", d_slice);
				probe_77317_dump_f_vec("5.mtbl",
					"stmt[mtbl]", m_slice);
				probe_77317_multiset_diff("5",
					f_slice, d_slice, m_slice);
			} else {
				emit_stdout(format!(
					"DEBUG USE 77317.5.OOB: stmt_cfg \
					 indices exceed stmt.len, cannot slice"));
			}
		}

		assert!(v_idx.len()==self.gadgets.len(), "v_idx.len(): {} != gadgets.len: {}", v_idx.len(), self.gadgets.len());
		let vec_msg_sizes = self.gadgets.iter().map(|g| 
			lock_unwrap!(g).get_msg_size())
			.collect::<Vec<(usize, usize, usize, usize)>>();
		let mut v_msg1:Vec<F> = vec![];
		let mut v_msg2:Vec<F> = vec![];
		let mut v_msg3:Vec<F> = vec![];
		log_perf(self.job_id, log_level, &format!("gen_witness step 1: gen stmt structure"),
			&mut gt1);


		//1. generate message1
		for (i,g) in self.gadgets.iter().enumerate(){
			let mut msg1 = lock_unwrap!(g).gen_msg1(&v_stmt, &v_idx[i]) ;
			assert!(vec_msg_sizes[i].1==msg1.len(),
				"ERROR: mistaching msg1 size for i: {}", i);
			v_msg1.append(&mut msg1);
		}
		log_perf(self.job_id, log_level, &format!("gen_witness step 2: gen msg1"),
			&mut gt1);
		//2. generate cmF
		// note that r_F is in statement. No need for extra blinding factor
		let vec = vec![
			stmt.clone(),
			v_msg1.clone()
		].concat();
		{
			use std::sync::atomic::{AtomicUsize, Ordering};
			static N_PROBE_60931: AtomicUsize = AtomicUsize::new(0);
			if N_PROBE_60931.fetch_add(1, Ordering::Relaxed) < 20{
				println!("DEBUG USE 60931.3: gen_witness commit '{}' \
					vec.len={} (stmt {} + msg1 {})", self.name,
					vec.len(), stmt.len(), v_msg1.len());
			}
		}
		let (zero,one) = (F::zero(),F::one());
		let grp_cmF = if precomputed_group_cmF.is_some(){
			let res = precomputed_group_cmF.unwrap();
			if b_debug{
		    	let res2 = CS::commit(&self.params, 
					&vec, &zero).expect("commit fails");
				assert!(res==res2);
			}
			res
		}else{
		    let res = CS::commit(&self.params, 
				&vec, &zero).expect("commit fails");
			res
		};
		// 2026-05-15: was log_perf(0,..) — routed every job's
		// gen_witness step 3.x-11 logs into log_job_0.txt. Fixed
		// here and at sibling sites below.
		log_perf(self.job_id, log_level, &format!("gen_witness step 3.1: gen cmF, for vec.len: {}", vec.len()), &mut gt1);
		let mut cmF = vec![];
		grp_cmF.to_native_sponge_field_elements_as_vec()
			.to_sponge_field_elements(&mut cmF);
		log_perf(self.job_id, log_level, &format!("gen_witness step 3.2: cmF to native field, "), &mut gt1);

		//3. generate message2
		let mut gi = 0;
		while gi<self.gadgets.len() && vec_msg_sizes[gi].2==0 {gi+=1;}
        let mut transcript= PoseidonSponge::<F>::new(&self.poseidon_config);
		transcript.absorb(&cmF);
		while gi<self.gadgets.len(){
			for _i in 0..vec_msg_sizes[gi].2{
				let ch = transcript.get_challenge();
				v_msg2.push(ch);
				transcript.absorb(&ch); 
			}
			gi += 1;
		}
		log_perf(self.job_id, log_level, &format!("gen_witness step 4: gen msg2"),
			&mut gt1);

		//4. generate message3
		let mut msg1_start = 0;
		let mut msg2_start = 0;
		for (i,g) in self.gadgets.iter().enumerate(){
			let mut msg3 = lock_unwrap!(g).gen_msg3(&v_stmt, &v_idx[i], 
				&v_msg1, msg1_start, vec_msg_sizes[i].1, 
				&v_msg2, msg2_start, vec_msg_sizes[i].2);
			assert!(msg3.len()==vec_msg_sizes[i].3, 
				"ERROR on msg3 for i: {}", i);
			msg1_start += vec_msg_sizes[i].1;
			msg2_start += vec_msg_sizes[i].2;
			v_msg3.append(&mut msg3); 

		}
		log_perf(self.job_id, log_level, &format!("gen_witness step 5: gen msg3"),
			&mut gt1);

		//5. build the Lookup related witnesses:
		// (1) inverse for inverse of Hab22 equations
		// (2) compute the sum of Hab22 equations
		let ch = zi_part2.ch.clone();
		let si = StatementInst::<F,LK>::from_vec(&self.stmt_config, &stmt);
		//this corresponds to query table: which consists of
		// extra vars (unused_inp_size, unused_oup_size) 
		//    + subtable_ids in statement (inp,oup,word_sub,data)
		let extra_var_size = 2usize;
		let cmF_size = 4usize;
		let inv_hab22_left_size = si.subtable_id.len() + extra_var_size;
		// right side is the lookup table share
		let inv_hab22_right_size = si.col1_share.len();
		let (alpha, beta) = (zi_part2.alpha, zi_part2.beta);
		let unused_input_size = F::from(self.stmt_config.input_size as u32)
			- si.act_input_size;
		let unused_output_size = F::from(self.stmt_config.output_size as u32)
			- si.act_output_size;
		let qry_tbl2 = vec![
			vec![unused_input_size, unused_output_size],
			si.inp_buf.clone(), si.oup_buf.clone(),
		//	si.word_subseg.clone(),  removed because si_word is not constructed
		//  word has no range restriction, it can be anything because
		// it's packed.
			si.data.clone()
		].concat();
		let qry_tbl1 = vec![ vec![zero,zero], si.subtable_id.clone()].concat();
		assert!(qry_tbl2.len()==inv_hab22_left_size);
		assert!(qry_tbl1.len()==inv_hab22_left_size);

		let _b_last = si.word_id==si.total_words
			&& si.subseg_id==si.total_word_segs;
		log_perf(self.job_id, log_level, &format!("gen_witness step 6: gen qry tbl"),
			&mut gt1);

		let inv_hab22_left = (0..inv_hab22_left_size).into_par_iter().map(|i|{
			let v2 = qry_tbl2[i];
			let v = alpha + qry_tbl1[i]*beta + v2 ;
			v.inverse().expect("inv failed")
		}).collect::<Vec<F>>();
		log_perf(self.job_id, log_level, &format!("gen_witness step 7.1: hab22 inverse, hab2 len: {}", inv_hab22_left.len()),
			&mut gt1);
		let sum_hab22_left = qry_tbl1.par_iter().zip(inv_hab22_left.par_iter())
		.map(|(&a,&b)|{
				if a.is_zero() {zero}
				else {b}
		}).sum::<F>() + zi_part2.sum_hab22_left;
		log_perf(self.job_id, log_level, &format!("gen_witness step 7.2: gen hab22 left, hab2 len: {}", inv_hab22_left.len()),
			&mut gt1);

		let right_size = inv_hab22_right_size;
		let inv_hab22_right = (0..right_size).into_par_iter().map(|i|{
			let v = alpha + si.col1_share[i]*beta + si.col2_share[i];
			v.inverse().unwrap()
		}).collect::<Vec<F>>();
		// Dummies have m=0, so inv*m = 0 either way -- no need to
		// branch on col1.is_zero(). Mirrors the constraint side.
		let sum_hab22_right = (0..right_size).into_par_iter().map(|i|{
			inv_hab22_right[i] * si.m_share[i]
		}).sum::<F>() + zi_part2.sum_hab22_right;

		// this is disabled because fill_lkup is not called during
		// preprocess mode
		// assert!(!final_step || sum_hab22_left==sum_hab22_right);

		assert!(4==cmF.len(), "cmF size not 4!");
		assert!(2==extra_var_size, "extra_var_size is not 2!");
		let cfg =WitnessSigmaIR1CSConfig{
			cmF_size: cmF_size,
			extra_var_size: extra_var_size,
			statement_size: v_stmt.len(),
			stmt_map: v_idx,
			msg1_size: v_msg1.len(),
			msg2_size: v_msg2.len(),
			msg3_size: v_msg3.len(),
			vec_msg_sizes: vec_msg_sizes,
			zi_part2_size: ZiPartTwoInst::<F>::size(self.b_full_mode, self.fq_bits),
			inv_hab22_left_size: inv_hab22_left_size,
			inv_hab22_right_size: inv_hab22_right_size,
			stmt_cfg: stmt_cfg,
		};
		log_perf(self.job_id, log_level, &format!("gen_witness step 8: gen hab22 right"),
			&mut gt1);

		//6. compute the KZG evaluation of :
		// [lookup col1, col2, words, vec_r, vec_v]
		// using Homer's method and combined using rc.
		// This pretty much follow the structure of genenerate_step_constraints
		let si = StatementInst::<F,LK>::from_vec(&self.stmt_config, &stmt);
		let mut sum_kzg_eval_lk= zi_part2.sum_kzg_eval_lk;
		let mut sum_kzg_eval_word= zi_part2.sum_kzg_eval_word;
		let mut sum_kzg_eval_others= zi_part2.sum_kzg_eval_others;
		let mut sum_vec_v_i= zi_part2.sum_vec_v_i;
		if !self.b_full_mode{//only do it for the first stage
			//println!("\nDEBUG USE 500.0: word_id: {}, subseg_id: {},  ch: {}, rc: {}, sum_vec_v_i: {}", si.word_id, si.subseg_id, zi_part2.ch, zi_part2.rc, sum_vec_v_i);
			//6.1 compute rands and assisting vars
			let b_last = si.word_id==si.total_words &&
				si.subseg_id==si.total_word_segs;
			let b_first_seg = si.subseg_id.is_one();
			let b_last_seg = si.subseg_id==si.total_word_segs;
			let ch = zi_part2.ch;
			let rc = zi_part2.rc;
			let mut rcs = vec![one];
			for _i in 0..5{rcs.push(rcs[rcs.len()-1] * rc)};

			//6.2 update sum_kzg_eval_lk
			let old_sum_kzg_eval_lk = sum_kzg_eval_lk.clone();
			let mut lookup_share_size_left = si.act_lookup_share_size;
			for i in 0..self.stmt_config.lookup_share_size{
				let b_lk_left_zero = lookup_share_size_left.is_zero();
				sum_kzg_eval_lk= if b_lk_left_zero{sum_kzg_eval_lk}
					else {
						sum_kzg_eval_lk* ch + 
						si.col1_share[i] * rcs[0] +
						si.col2_share[i] * rcs[1]
					};

				let val2_lk = lookup_share_size_left - one;
				lookup_share_size_left= if b_lk_left_zero {zero} else {val2_lk};
			}
			sum_kzg_eval_lk = if si.act_lookup_share_size.is_zero()
				{old_sum_kzg_eval_lk} else {sum_kzg_eval_lk};


			//6.3 update sum_kzg_eval_word and also sum_vec_v_i
			let old_sum_kzg_eval_word = sum_kzg_eval_word.clone();
			let old_sum_vec_v_i = sum_vec_v_i.clone();
			sum_vec_v_i = if b_first_seg {zero} else {sum_vec_v_i};
			let mut word_size_left = si.act_word_subseg_size;
			for i in 0..self.stmt_config.word_subseg_size{
				let b_wd_left_zero = word_size_left.is_zero();
				let word_to_add=si.word_subseg[i] * rcs[2];
				sum_kzg_eval_word = if b_wd_left_zero 
					{sum_kzg_eval_word} else
					{sum_kzg_eval_word*ch + word_to_add};

				sum_vec_v_i = if b_wd_left_zero 
					{sum_vec_v_i} else
					{sum_vec_v_i * si.batch_r + si.word_subseg[i]} ;
				//println!("DEBUG USE 888.1: word_id: {}, subseg: {}, word: {}, act_word_subseg_size: {}, word: {}, batch_r: {}, sum_vec_v: {}, word_size_left: {}, b_wd_left_zero: {}", si.word_id, si.subseg_id, si.word_subseg[i], si.act_word_subseg_size, si.word_subseg[i], si.batch_r, sum_vec_v_i, word_size_left, b_wd_left_zero);

				let val2_wd = word_size_left- one;
				word_size_left= if b_wd_left_zero {zero} else {val2_wd};
			}
			sum_kzg_eval_word= if si.act_word_subseg_size.is_zero()
				{old_sum_kzg_eval_word} else {sum_kzg_eval_word};
			sum_kzg_eval_word = if b_last 
				{sum_kzg_eval_word*ch + si.r_all_words*rcs[2]} 
				else {sum_kzg_eval_word};
			sum_vec_v_i= if si.act_word_subseg_size.is_zero()
				{old_sum_vec_v_i} else {sum_vec_v_i};
			sum_vec_v_i = if b_last_seg
				{sum_vec_v_i*si.batch_r + si.r_word_i} else {sum_vec_v_i};
			if B_DEBUG {
				if b_last_seg {
				//	println!("DEBUG USE 500.0.1: sum_vec_v_i: {}, batch_v: {}, act_word_sub_size: {}, batch_r: {}", sum_vec_v_i, si.batch_v, si.act_word_subseg_size, si.batch_r);
					assert!(sum_vec_v_i == si.batch_v);
				}
			}

			//6.4 update the sum_kzg_eval_others
			sum_kzg_eval_others = if b_first_seg {
				sum_kzg_eval_others * ch +  
				si.total_word_len*rcs[3] +
				si.batch_r * rcs[4] + 
				si.batch_v * rcs[5]} else {sum_kzg_eval_others};
			sum_kzg_eval_others = if b_last {
				sum_kzg_eval_others * ch + 
				si.r_kzg_len * rcs[3] +
				si.r_vec_r * rcs[4] +
				si.r_vec_v * rcs[5]} else {sum_kzg_eval_others};

			//6.5 total
			let _sum_kzg_eval = sum_kzg_eval_lk + 
				sum_kzg_eval_word + sum_kzg_eval_others;
				//println!("DEBUG USE 500.9: sum_kzg_eval: {}, sum_vec_v_i: {}", sum_kzg_eval, sum_vec_v_i);
			log_perf(self.job_id, log_level, &format!("gen_witness step 9: gen kzg sum"),
			&mut gt1);
		}

		//6. compute the zi_vec
		//6.1 enforce the input/output buffer, compute
		// weighted sum of poly using Holm's approach 
		let (zero, one) = (F::zero(), F::one());
		//let b_first =  si.word_id==one && si.subseg_id==one;
		//let b_last = si.word_id==si.total_words 
		//	&& si.subseg_id==si.total_word_segs;
		let b_first_seg = si.subseg_id==one;
		let b_last_seg = si.subseg_id==si.total_word_segs;
		let mut sum_inp = if b_first_seg {zero} else {zi_part2.sum_inp};
		let mut sum_oup = if b_first_seg {zero} else {zi_part2.sum_oup};

		assert!(si.act_input_size<=F::from(self.stmt_config.input_size as u32),
			"si.act_input_size: {} > stmt_config.input_size: {}",
			si.act_input_size, self.stmt_config.input_size);
		assert!(si.act_output_size<=
			F::from(self.stmt_config.output_size as u32),
			"si.act_output_size: {}> stmt_config.input_size: {}",
			si.act_output_size, self.stmt_config.output_size);
		let mut inp_left = si.act_input_size.clone();
		let mut oup_left = si.act_output_size.clone();
		for i in 0..self.stmt_config.input_size{
			sum_inp = if b_first_seg || inp_left.is_zero() {sum_inp}
			else{ sum_inp * ch + si.inp_buf[i] };
			inp_left = if inp_left.is_zero() {zero} else {inp_left - one};
		}
		for i in 0..self.stmt_config.output_size{
			sum_oup = if b_last_seg || oup_left.is_zero() {sum_oup}
			else{ sum_oup * ch + si.oup_buf[i] };
			oup_left = if oup_left.is_zero() {zero} else {oup_left - one};
		}
		log_perf(self.job_id, log_level, &format!("gen_witness step 10: gen inp/oup"),
			&mut gt1);

		let fq_bits = <<C as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let cp = if self.b_full_mode {
			let cp_vec = cp_inp.into_iter().map(|idx|
				v_stmt[idx]).collect::<Vec<F>>();	
			Some(CyclePairInput{x: cp_vec, fq_bits: fq_bits})
		} else {None};

		//println!("DEBUG USE 500.0.2. BEFORE building zi1_part2: sum_vec_v_i: {}", sum_vec_v_i);
		let zi1_part2 = ZiPartTwoInst::<F>{
			ch: zi_part2.ch.clone(),
			rc: zi_part2.rc.clone(),
			sum_inp: sum_inp,
			sum_oup: sum_oup,

			alpha: zi_part2.alpha.clone(),
			beta: zi_part2.beta.clone(),
			sum_hab22_left: sum_hab22_left,
			sum_hab22_right: sum_hab22_right,

			sum_kzg_eval_lk: sum_kzg_eval_lk,
			sum_kzg_eval_word: sum_kzg_eval_word,
			sum_kzg_eval_others: sum_kzg_eval_others,
			sum_vec_v_i: sum_vec_v_i,

			total_word_len: si.total_word_len,
			accumulated_word_len: si.accumulated_word_len,

			word_id: si.word_id,
			subseg_id: si.subseg_id,
			total_word_segs: si.total_word_segs,
			total_words: si.total_words,
			f_result: si.f_result,
			
			cyclepair_input: cp,
		};
		log_perf(self.job_id, log_level, &format!("gen_witness step 11: assemble ret"),
			&mut gt1);

		(WitnessSigmaIR1CS::<F>{
			cmF: cmF,
			unused_input_size: unused_input_size,
			unused_output_size: unused_output_size,
			statement: v_stmt,
			msg1: v_msg1, 
			msg2: v_msg2,
			msg3: v_msg3,
			zi_part2: zi_part2.to_vec(),
			inv_hab22_left: inv_hab22_left,
			inv_hab22_right: inv_hab22_right,
			},
		 cfg,
		 zi1_part2.clone(), 
		)
	}

	/// provide the information of poseidon config, mapper,
	/// whether full mode (supporting cyclepair), and
	/// bits of Fq (base prime field)
	fn new_adv(name: String, poseidon_config: PoseidonConfig<F>, 
		g_mapper: Arc<Mutex<GM>>, b_full_mode: bool, lkup_share_size: usize,
		b_cyclepair: bool, b_check_lkup: bool)
		-> Result<Self,Error>{
		let gadgets = lock_unwrap!(g_mapper).get_gadgets().clone();
		let (wtns_cfg, stmt_cfg) = Self::gen_configs(g_mapper.clone(), 
			b_full_mode, lkup_share_size)?;
		let stmt_len = wtns_cfg.statement_size;
		let m1_len = wtns_cfg.msg1_size;

		println!("DEBUG USE 60931.2: new_adv '{}' initial cmF key -> {} \
			(stmt {} + msg1 {})", name, stmt_len + m1_len + 1,
			stmt_len, m1_len);
		let mut rng = ark_std::test_rng();
		let (cs_pp, _cs_vp) = CS::setup(&mut rng, stmt_len + m1_len +1)
			.expect("setup error");
		let fq_bits = <<C as CurveGroup>::BaseField as Field>::BasePrimeField
			::MODULUS_BIT_SIZE as usize;
		Ok(Self{name: name, 
			gadget_mapper: g_mapper, 
			witness: None, 
			witness_config: wtns_cfg,
			gadgets: gadgets, poseidon_config: poseidon_config,
			stmt_config: stmt_cfg,
			params: cs_pp, b_full_mode: b_full_mode, fq_bits: fq_bits,
			dummy_stmt: None,
			_lk: PhantomData, b_cyclepair,
			b_check_lkup,
			job_id: 0})
	}

	fn step_native_mut(
		&mut self,
		_i: usize,
		z_i: &ZiPartTwoInst<F>,
		external_inputs: Vec<F>,
	) -> Result<ZiPartTwoInst<F>, Error> {
		//1. generate the real witness out of the problem statement
		//here since step_native_mut is not called by other parts
		//we do not optimize to provide precomputed cmF
		let res = self.gen_witness(&external_inputs, &z_i, None);
		self.witness = Some(Arc::new(res.0));
		self.witness_config = res.1;
		//2. return the next global state (part 2)
		let z_i1 = res.2;

		Ok(z_i1)
	}

	/// delegate to the gadget mapper's per-component spans.
	fn component_spans(&self) -> Vec<(String, usize)>{
		lock_unwrap!(self.gadget_mapper).component_spans()
	}

	/// set its dummy stmt
	//fn set_dummy_stmt(&mut self, vec: Vec<F>){
	fn set_dummy_stmt(&mut self, stmt: StatementInst<F,LK>){
		let vec = stmt.to_vec();
		self.dummy_stmt = Some(vec);
		// cmF key is sized in new_adv from the capacity-default msg1;
		// set_container_config can grow msg1 (fsm_adv::get_msg_size
		// reads the container cfg), so resize here to the dummy
		// (capacity-max) commit length before R1CS extraction.
		let cmf_len = self.witness_config.get_cmf_len();
		println!("DEBUG USE 60931.1: set_dummy_stmt resize cmF key \
			-> {} (stmt {} + msg1 {})", cmf_len + 1,
			self.witness_config.statement_size,
			self.witness_config.msg1_size);
		let mut rng = ark_std::test_rng();
		let (cs_pp, _cs_vp) = CS::setup(&mut rng, cmf_len + 1)
			.expect("resize cmF params");
		self.params = cs_pp;
	}

	// 2026-05-15: propagate job_id to ALL per-job state, not just
	// `self.job_id`. Setting only the inst's own field (previous
	// behaviour) left:
	//   (a) the inner `gadget_mapper` Mutex carrying job_id=0
	//       (inherited from the template through `clone_deep`),
	//       which routed mapper-side `log_perf(self.job_id,..)`
	//       calls into log_job_0.txt for every job, and
	//   (b) the inst's own `self.gadgets` vec (independent
	//       Arcs produced by Option A in `clone_deep`) carrying
	//       job_id=0, which routed every `assert_msg3` /
	//       `gen_step_cs` per-gadget log line into log_job_0.txt.
	// As a result the per-job logs of stalled jobs looked frozen
	// while their gen_step_cs traces were actually being written
	// into log_job_0.txt. See stall analysis 2026-05-15.
	fn set_job_id(&mut self, job_id: usize){
		self.job_id = job_id;
		lock_unwrap!(self.gadget_mapper).set_job_id(job_id);
		for g in self.gadgets.iter() {
			lock_unwrap!(g).set_job_id(job_id);
		}
	}

	fn get_job_id(&self) -> usize{
		self.job_id
	}

	/// generate a dummy statement that could pass the check of
	/// sigma_ir1cs
	fn gen_dummy_stmt(&self) -> Vec<F>{
		let total_size = self.witness_config.statement_size;
		let res = if self.dummy_stmt.is_some(){
			let stmt = self.dummy_stmt.as_ref().unwrap().clone();
			assert!(stmt.len()==total_size, "{} != {}", stmt.len(), total_size);
			stmt
		}else{
			let vec = vec![F::zero(); total_size];
			let mut stmt = StatementInst::<F,LK>::from_vec(&self.stmt_config, &vec);
			stmt.word_id = F::one();
			stmt.total_words = F::one();
			stmt.total_word_segs = F::one();
			stmt.subseg_id = F::one();
			stmt.to_vec()
		};

		res
	}

	/// return the size of F (problem statement + msg1)
	fn get_size_f(&self) -> usize{
		self.witness_config.get_size_f()
	}

	fn get_cmf_len(&self) -> usize{
		self.witness_config.get_cmf_len()
	}
}

impl <F,C,CS,LK, GM, const H: bool> FCircuit<F> for SigmaIR1CS_Inst<F,C,CS,LK,GM, H>
where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		LK: LookupTableTwoCol<F>,
		F: PrimeField + Absorb + ColEle,
		GM: GadgetMapper<F,LK> + std::clone::Clone + Debug + Send + Sync,
{
	type Params = ();

	/// create a new instance
	fn new(_params: Self::Params) -> Result<Self, Error> {
		Err(Error::Other(format!("do not call new(), call new_adv")))
	}

	/// length of z_i between step circuits
	fn state_len(&self) -> usize {
		2
	}

	/// length of secret witness vector (
	fn external_inputs_len(&self) -> usize {
		//return the total len of problem statement
		lock_unwrap!(self.gadget_mapper).gen_statement_structure(
			self.stmt_config.lookup_share_size).0
	}

	/// logical step (logically) perform selfcheck for the step
	/// compute the next output z_i+1. (Here z_i and z_i1 are
	/// used as IVC inputs, e.g., passing finterprinting params)
	/// Use external_inputs to pass the real problem statement
	fn step_native(
		&self,
		_i: usize,
		_z_i: Vec<F>,
		_external_inputs: Vec<F>,
	) -> Result<Vec<F>, Error> {
		Err(Error::Other(format!("call step_native_mut instead")))
	}

	/// generate all constraints by calling sigma-protocol components.
	/// Return a vector of FpVar modeling z_i+1 (two elements).
	fn generate_step_constraints(
		&self,
		cs: ConstraintSystemRef<F>,
		_i: usize,
		z_i: Vec<FpVar<F>>,
		external_inputs: Vec<FpVar<F>>,
	) -> Result<Vec<FpVar<F>>, SynthesisError> {
		let b_debug = B_DEBUG; //set to false in production mode
		let b_show_sigs = false; //set to false in production mode
		let log_level = LOG6;
		//NOTE: cs.is_satisfied() can cause * stack overflow *
		//if constraints are not constructed carefully.
		//sometimes if a constraint has lc (linear combinations) too deep,
		//it will penetrate the stack.
		//when b_debug is set, we call cs.is_satisfied() for debugging
		//and print the stack use
		//1. converts witness from extrenal_inputs to structured version
		let (mut nc, mut nv) = (cs.num_constraints(), cs.num_witness_variables());
		cost_capture_set_entry(cs.num_constraints());
		let mut gt = GTimer::new();
		// 2026-05-16: probe 77317.7 — entry of
		// generate_step_constraints. word_id/subseg_id are not yet
		// extracted at this point (si is built below), so we emit
		// just the entry marker; correlation with 77317.4 below
		// fills in word/seg.
		if crate::folding::foldpot::utils::probe_77317_enabled() {
			emit_stdout(format!(
				"DEBUG USE 77317.7: ENTER generate_step_constraints \
				 job={} cs={} vars={}",
				self.job_id, cs.num_constraints(),
				cs.num_witness_variables()));
		}
		log_perf(self.job_id, log_level, &format!("### gen_step_cs START: cs: {}, vars: {}",
			cs.num_constraints(),
			cs.num_witness_variables()
		), &mut gt);
		assert!(z_i.len()==2);
		let configs = self.gadgets.iter().map(|g| lock_unwrap!(g).get_msg_size())
			.collect::<Vec<(usize, usize, usize, usize)>>();
		let cfg = &self.witness_config;
		assert!(cfg.get_total_size()==external_inputs.len(), "external_inputs.len: {} != cfg.total_size: {}", external_inputs.len(), cfg.get_total_size());
		let wtns_var =  WitnessSigmaIR1CSVar::from_vec(&cfg, &external_inputs);
		//println!("DEBUG USE 101: AFTER msg1: constraints: {}", cs.num_constraints());
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 1: cs: {}, vars: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv), &mut gt);
			nc = cs.num_constraints();
			nv = cs.num_witness_variables();
		log(self.job_id, log_level, &format!("-- witness: stmt: {}, msg1: {}, msg2: {}, msg3: {}", wtns_var.statement.len(), wtns_var.msg1.len(), wtns_var.msg2.len(), wtns_var.msg3.len()));

		//2. check message2 (ro over stmt and msg1)
		let mut gi = 0;
		while gi<self.gadgets.len() && configs[gi].2==0 {gi+=1;}
        let mut transcript= PoseidonSpongeVar::<F>::new(
			cs.clone(), &self.poseidon_config);
		transcript.absorb(&wtns_var.cmF)?; //this is equiv to statement + msg1
		let v_msg2 = &wtns_var.msg2;
		let mut idx = 0;
		while gi<self.gadgets.len(){
			for _i in 0..configs[gi].2{
				let ch = transcript.get_challenge()?;
				if B_DEBUG {
					assert!(ch.value().unwrap()==v_msg2[idx].value().unwrap(),
						"ERROR ch does not match v_msg2");
				}
				ch.enforce_equal(&v_msg2[idx])?;
				transcript.absorb(&ch)?; 
				idx +=1;
			}
			gi += 1;
		}
		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 1");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 1. ",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level,&format!("gen_step_cs step 2: cs: {}, vars: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv), &mut gt);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		let mut nl = cs.num_lc();


		//3. add all constraints by components
		let mut gt3 = GTimer::new();
		let si = StatementInstVar::<F>::from_vec(&self.stmt_config, &wtns_var.statement);
		// 2026-05-16: probe 77317.4 — just after StatementInstVar
		// from_vec slices wtns_var.statement into si.{failed,
		// discharged,mtbl}_sigs. Lets us check the indices are sane
		// and the FpVar values match what gen_witness handed in.
		if crate::folding::foldpot::utils::probe_77317_enabled() {
			use crate::folding::foldpot::utils
				::probe_77317_dump_fpvar_vec;
			let cfg = &self.stmt_config;
			emit_stdout(format!(
				"DEBUG USE 77317.4: AFTER from_vec job={} \
				 stmt.len={} idx_failed={} failed_size={} \
				 idx_discharged={} discharged_size={} \
				 idx_mtbl={} mtbl_size={}",
				self.job_id,
				wtns_var.statement.len(),
				cfg.idx_failed_sigs, cfg.failed_sigs_size,
				cfg.idx_discharged_sigs, cfg.discharged_sigs_size,
				cfg.idx_mtbl_sigs, cfg.mtbl_sigs_size));
			probe_77317_dump_fpvar_vec("4.failed",
				"si.failed_sigs", &si.failed_sigs);
			probe_77317_dump_fpvar_vec("4.discharged",
				"si.discharged_sigs", &si.discharged_sigs);
			probe_77317_dump_fpvar_vec("4.mtbl",
				"si.mtbl_sigs", &si.mtbl_sigs);
		}
		for (i,g) in self.gadgets.iter().enumerate(){
			let (nc, ni, nv) = (cs.num_constraints(), cs.num_instance_variables(), cs.num_witness_variables());
			lock_unwrap!(g).assert_msg3(i, cs.clone(), &wtns_var, &cfg,
				si.word_id.clone(), si.subseg_id.clone())?;
			if B_DEBUG3{
				check_cs(&cs, &format!("After gadget: {}", lock_unwrap!(g).get_name()));
			}
			let stmt_len = lock_unwrap!(g).get_msg_size().0;
			log_perf(self.job_id, log_level, &format!("-- -- after msg3 of module {}: {}:\n\tINCREASED: constraints: {}, const vars: {}, wit vars: {} \n\t==> NOW: CS:{}, const: {}, witness: {}\n\t ==> stmt_size: {}. ", i, lock_unwrap!(g).get_name(), cs.num_constraints()-nc, cs.num_instance_variables()-ni, cs.num_witness_variables()-nv, cs.num_constraints(), cs.num_instance_variables(), cs.num_witness_variables(), stmt_len), &mut gt3);
			// DEBUG USE 64900.1 (ZKR_PROBE_CSBREAK / ZKR_PROBE_SIZES):
			// per-gadget cs delta + running total, labeled by circ name so the
			// 4 circuits' gadget rows are distinguishable. Fires once per circ
			// during preprocess get_r1cs_super.
			if std::env::var("ZKR_PROBE_CSBREAK").is_ok()
				|| std::env::var("ZKR_PROBE_SIZES").is_ok() {
				emit_stdout(format!("DEBUG USE 64900.1: circ={} gadget[{}] {} \
					cs_delta: {} running_total: {}",
					self.name, i, lock_unwrap!(g).get_name(),
					cs.num_constraints() - nc, cs.num_constraints()));
			}
			cost_capture_push(lock_unwrap!(g).get_name(),
				cs.num_constraints() - nc);
		}
		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 3");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 3. ",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 3: cs: {}, vars: {}, lc: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl,
			), &mut gt);
			nc = cs.num_constraints();
			nv = cs.num_witness_variables();
			nl = cs.num_lc();

		//4. enforce the input and output buffer equivalence
		let (zero, one) = (F::zero(), F::one());
		let (zero_var, one_var) =  (
			FpVar::<F>::new_constant(cs.clone(), zero)?, 
			FpVar::<F>::new_constant(cs.clone(), one)?);
		let b_first = si.word_id.is_eq(&one_var)?
			.and(&si.subseg_id.is_eq(&one_var)?)?;
		let b_first_seg = si.subseg_id.is_eq(&one_var)?;
		let b_last_seg = si.subseg_id.is_eq(&si.total_word_segs)?;
		let b_last = si.word_id.is_eq(&si.total_words)?
			.and(&si.subseg_id.is_eq(&si.total_word_segs)?)?;
		//NOTE: later needs to set sub-table id for unused_input_size
		let cfg_input_size = FpVar::<F>::new_constant(cs.clone(),
			F::from(self.stmt_config.input_size as u32))?;
		let diff1 = cfg_input_size - &si.act_input_size;
 		diff1.enforce_equal(&wtns_var.unused_input_size)?;

		let cfg_output_size = FpVar::<F>::new_constant(cs.clone(),
			F::from(self.stmt_config.output_size as u32))?;
		let diff2 = cfg_output_size - &si.act_output_size;
 		diff2.enforce_equal(&wtns_var.unused_output_size)?;
		if B_DEBUG {
			assert!(diff1.value().unwrap()
				==wtns_var.unused_input_size.value().unwrap());
			assert!(diff2.value().unwrap()
				==wtns_var.unused_output_size.value().unwrap());
		}

		let fq_bits = <<C as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let zi_part2 = ZiPartTwoInstVar::from_vec(&wtns_var.zi_part2, fq_bits); 
		let ch = zi_part2.ch.clone();
		let rc = zi_part2.rc.clone();
		let mut sum_inp = b_first_seg.select(&zero_var, 
			&zi_part2.sum_inp)?;
		let mut sum_oup = b_first_seg.select(&zero_var,
			&zi_part2.sum_oup)?;
		let mut inp_left = si.act_input_size.clone();
		let mut oup_left = si.act_output_size.clone();

		let val_lkup_left = inp_left.value()?;
		let vec_left = (0..self.stmt_config.input_size).collect::<Vec<_>>().
			into_par_iter().map(|i|{
				let u_left = field_to_usize(&val_lkup_left);
				if u_left>=i {val_lkup_left-F::from(i as u64)}else{F::zero()}
			}).collect::<Vec<F>>();
		let v_inv_lzero = gen_vec_inverse(&vec_left);
		assert!(v_inv_lzero.len()==self.stmt_config.input_size);
		for i in 0..self.stmt_config.input_size{
			//simulate the gen_witness:
			//sum_inp = if b_first || inp_left.is_zero() {sum_inp}
			//else{ sum_inp * r + si.inp_buf[i] };
			// inp_left = if inp_left.is_zero() {zero} else {inp_left - one};
			let is_inp_left_zero = inp_left.is_zero_adv(&v_inv_lzero[i])?;
			let cond = b_first_seg.or(&is_inp_left_zero)?;
			let new_val = sum_inp.clone() * ch.clone() + si.inp_buf[i].clone();
			sum_inp = cond.select(&sum_inp, &new_val)?;
			let new_inp_left  = inp_left.clone() - &one_var;
			inp_left = is_inp_left_zero.select(&zero_var, &new_inp_left)?;
		}

		let val_lkup_left = oup_left.value()?;
		let vec_left = (0..self.stmt_config.output_size).collect::<Vec<_>>().
			into_par_iter().map(|i|{
				let u_left = field_to_usize(&val_lkup_left);
				if u_left>=i {val_lkup_left-F::from(i as u64)}else{F::zero()}
			}).collect::<Vec<F>>();
		let v_inv_lzero = gen_vec_inverse(&vec_left);
		assert!(v_inv_lzero.len()==self.stmt_config.output_size);
		for i in 0..self.stmt_config.output_size{
			//sum_oup = if b_last || oup_left.is_zero() {sum_oup}
			//else{ sum_oup * r + si.oup_buf[i] };
			//oup_left = if oup_left.is_zero() {zero} else {oup_left - one};
			let is_oup_left_zero = oup_left.is_zero_adv(&v_inv_lzero[i])?;
			let cond = b_last_seg.or(&is_oup_left_zero)?;
			let new_val = sum_oup.clone()*ch.clone() + si.oup_buf[i].clone();
			sum_oup = cond.select(&sum_oup, &new_val)?;
			let new_oup_left  = oup_left.clone() - &one_var;
			oup_left = is_oup_left_zero.select(&zero_var, &new_oup_left)?;
		}

		let eq_inp_oup = sum_inp.is_eq(&sum_oup)?;
		let final_step = b_last.and(&si.word_id.is_eq(&zero_var)?.not())?;
		let not_final_step = final_step.not();
		let io_res = not_final_step.or(&eq_inp_oup)?;
		//println!("DEBUG USE 201: b_last: {}, not_final_step: {}, word_id: {}, total_words: {}, eq_inp_oup: {}, sum_inp: {}, sum_oup: {}", b_last.value()?, not_final_step.value()?, si.word_id.value()?, si.total_words.value()?, eq_inp_oup.value()?, sum_inp.value()?, sum_oup.value()?);
		if B_DEBUG {
			assert!(io_res.value()?, "io not match at final step!");
		}
		io_res.enforce_equal(&Boolean::TRUE)?;
		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 4");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 4. ",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 4: cs: {}, vars: {}, lc: {}, output_size: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl,
			self.stmt_config.output_size
			), &mut gt
		);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();


		//5. verify the Lookup related witnesses:
		// (0) extract the b_req_lkup array
		// (1) verify inverse for inverse of Hab22 equations
		// (2) compute the sum of Hab22 equations
		//NOTE: however, they all have to be UPDATED because
		//the m_vec has to be updated
		// NOTE sometimes there is NO lookup involved at all,
		// then skip this check!!!

		//5.0 setup
		let inv_hab22_left_size = self.witness_config.inv_hab22_left_size;
		let inv_hab22_right_size = self.witness_config.inv_hab22_right_size;
		//right_size is indicator of whether lookup is used
		let b_has_lookup = inv_hab22_right_size>0;
		let mut sum_hab22_left = zi_part2.sum_hab22_left;
		let mut sum_hab22_right = zi_part2.sum_hab22_right;
		
		let _stmt_cfg = &self.stmt_config;
		let (alpha, beta) = (zi_part2.alpha.clone(), zi_part2.beta.clone());
		let unused_input_size = wtns_var.unused_input_size;
		let unused_output_size = wtns_var.unused_output_size;
		let qry_tbl2 = vec![
			vec![unused_input_size, unused_output_size],
			si.inp_buf.clone(), si.oup_buf.clone(),
			//si.word_subseg.clone(),  REMOVE no need to tag word seg
			//as it's arbitrary
			si.data.clone()
		].concat();
		let qry_tbl1 = vec![ 
			vec![zero_var.clone(),zero_var.clone()], 
			si.subtable_id.clone()].concat();
		assert!(qry_tbl2.len()==qry_tbl1.len());

		//NOTE: b_check_lkup should be regarded as a FIXED circuit specific
		//array. To save implementation cost (avoiding large cascading
		//structure change of code), we here build it from the qry_tbl1 value.
		//when the value is 0 (mean's don't care), 
		//b_check_lkup is set to FALSE; othersise TRUE.
		//This array is gauranteed to be the SAME regardless of witness.
		//Ideally, we should hard encode it in all gadget building functions
		//and assemble the array, but here, we do it from var value for
		//conveneince.
		let b_check_lkup = qry_tbl1.iter().map(|x| {
			!x.value().unwrap().is_zero()
		}).collect::<Vec<bool>>();

		//here to break very long linear combination sequence
		//of the fum sum_i=1^n v[i]
		//we periodically multiply the item v[i] with var with value 1
		//this allows to break the chain thus avoid expensive inlining
		//of transform_lc() which is called by cs.finalize() later.
		//NOTE that we need it to be a witness var so that
		// one_wit_var * v[i] will be interpreted as a constraint
		// instead of a linear combination (i.e., one_wit_var is treated
		//   as a var, instead of constant)
		let one_wit_var = FpVar::<F>::new_witness(cs.clone(), ||Ok(F::one())).unwrap();
		one_wit_var.enforce_equal(&one_var)?; 


		//5.1 verify the correct of inverse and compute sum_hab22_left
		assert!(b_check_lkup.len()==inv_hab22_left_size,
			"b_check_up.len(): {} != inv_hab22_left: {}",
			b_check_lkup.len(), inv_hab22_left_size
		);
		/* OLD TO REMOVE 4 R1CS each
		for i in 0..inv_hab22_left_size{
			//note: b_check_lkup is CIRCUIT specific const array
			//if b_check_lkup[i]==false {continue;}
			let v2 = &qry_tbl2[i];
			let v = &alpha + &qry_tbl1[i] + &(v2 * &beta);
			let prod = &v * &wtns_var.inv_hab22_left[i];
			prod.enforce_equal(&one_var)?;
			//use 0 to disable add
			sum_hab22_left += &(&qry_tbl1[i] * &wtns_var.inv_hab22_left[i]);
			if i%ADD_CHAIN_SIZE==0{//avoid building too long linear combinations
				//cs.is_satisfied() -> eval_lc() -> assigned_value(*var)
				//  when var is symbolic it's calling eval_lc() recursively
				//  so here retrieve the value periodically to make recursive
				//  chain shorter.
				//sum_hab22_left = &sum_hab22_left + &zero_var;
				//COMMENT OUT LATER IF DOES NOT HELP
				let _v1 = sum_hab22_left.value()?;
				sum_hab22_left = &sum_hab22_left * &one_wit_var;

			}
		}
		*/
		//IDEA: when qry1[i] is a CONSTANT it means that this is
		// circuit specifc const (not dynamically assigned).
		// case 1: it's a 0. so simply ignore it. As regardless of
		//    witness, this is part of a circuit, it's safe to do so.
		//    cost: 0 constraint.
		// case 2: it's a non-zero. So it IS a "static" lookup for
		//    qry2[i] (tbl_id is qry1[i]). So this is going to
		//    cost: 1 constraint (because multiplication with const
		//    does not cost.
		// --- qry1[i] is a NON-CONSTANT (dynamically assigned tbl ID)
		// case 3: 3 constraints: 1 for weighted sum; 1 for 
		//    verify inverse; 1 for multiplying with qry1[i] before
		//    summing it up.
		//let cv_zero = FpVar::<F>::new_constant(cs.clone(), F::zero());
		let lb_one = LinearCombination::from((F::one(),Variable::One));
		let (mut n_case1, mut n_case2, mut n_case3) = (0,0,0);
		for i in 0..inv_hab22_left_size{
			let tb_id = qry_tbl1[i].value()?;
			if qry_tbl1[i].is_constant(){ 
				if tb_id.is_zero(){//case 1 do nothing, 0 r1cs
					n_case1 += 1;
				}else{//case 2. only 1 constraint coz qry[i] is CONSTANT
					//let v = &alpha + &(&qry_tbl1[i]*&beta) + &qry_tbl2[i];
					//let lb_v = var_to_lb(&v, F::one());
					let lb_v = LinearCombination::<F>(
						vec![
							var_to_tuple(&alpha),
							var_to_tuple_adv(&beta, tb_id),
							var_to_tuple(&qry_tbl2[i])
						]
					);
					let lb_wit= var_to_lb(&wtns_var.inv_hab22_left[i], F::one());
					
					cs.enforce_constraint(
						lb_v,
						lb_wit,
						lb_one.clone(),
					)?;
					sum_hab22_left += &wtns_var.inv_hab22_left[i]; //this one does not cost really it's just a pure add (0 r1cs)

					n_case2 += 1;
				}
			}else{//3 r1cs . We have made sure all qry_tb1[i] (tbl_id is NON
				//zero) if optimized - 2 r1cs because if we can guarantee
				//that qry_tbl1[i] is NOT Nill
				if b_debug{
					assert!(!qry_tbl1[i].value().unwrap().is_zero(), 
						"ERROR: qry_tbl[{}] is zero for case 3", i);
				}
				//let v = &alpha + &(&qry_tbl1[i]*&beta) + &qry_tbl2[i];
				//let lb_v = var_to_lb(&v, F::one());
				//let v1 = &qry_tbl1[i]*&beta;
				let v1 = alloc_fpvar_mul(&qry_tbl1[i], &beta);
				let lb_v = LinearCombination::<F>(
					vec![
						var_to_tuple(&alpha),
						var_to_tuple(&v1),
						var_to_tuple(&qry_tbl2[i])
					]
				);
				let lb_wit= var_to_lb(&wtns_var.inv_hab22_left[i], F::one());
				cs.enforce_constraint(
					lb_v,
					lb_wit,
					lb_one.clone(),
				)?;
				sum_hab22_left += &wtns_var.inv_hab22_left[i];
				n_case3 += 1;
			};

			if i%ADD_CHAIN_SIZE==0{//avoid building too long linear combinations
				//cs.is_satisfied() -> eval_lc() -> assigned_value(*var)
				//  when var is symbolic it's calling eval_lc() recursively
				//  so here retrieve the value periodically to make recursive
				//  chain shorter.
				//sum_hab22_left = &sum_hab22_left + &zero_var;
				//COMMENT OUT LATER IF DOES NOT HELP
				sum_hab22_left = &sum_hab22_left * &one_wit_var;

			}
	}
		//log(job_id, log_level, &format!("gen_step_cs step 5: BEFORE inv_hab22: {}, cs.lc_size: {}, cons: {}", inv_hab22_left_size, cs.inner().lc_map.len(), cs.num_constraints()));
		let n_total = n_case1 + n_case2 + n_case3;
		log_perf(self.job_id, log_level, &format!("gen_step_cs step 5: AFTER inv_hab22: {}, INCREASED cs.lc_size: {}, cons: {}, vars: {} -- Breakdown of logup cases: n_case1: ({}, {:.2}%), n_case2: ({}, {:.2}%), n_case3: ({}, {:.2}%)"
		, inv_hab22_left_size, cs.inner().unwrap().borrow().lc_map.len() - nl, cs.num_constraints()-nc, cs.num_witness_variables()-nv, n_case1, 100.0*(n_case1 as f64)/(n_total as f64), n_case2, 100.0*(n_case2 as f64)/(n_total as f64), n_case3, 100.0*(n_case3 as f64)/(n_total as f64)
		), &mut gt);
		//log(job_id, log_level, &format!("-- Breakdown of logup cases: n_case1: ({}, {:.2}%), n_case2: ({}, {:.2}%), n_case3: ({}, {:.2}%)", 
		//n_case1, 100.0*(n_case1 as f64)/(n_total as f64), n_case2, 100.0*(n_case2 as f64)/(n_total as f64), n_case3, 100.0*(n_case3 as f64)/(n_total as f64)
		//));
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();

		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 5.1");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 5.1 ",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));

		}
		//log(job_id, log_level, &format!("-- lkup_size: {}, inv_hab22_right_size: {}", si.act_lookup_share_size.value()?, inv_hab22_right_size));
		log_perf(self.job_id, log_level, &format!(
				"-- -- gen_step_cs step 5.1: cs: {}, vars: {}: lc: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv,
				cs.num_lc() - nl
				), &mut gt
			);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();

		//5.2 check the right side
		if b_debug{
			emit_stdout(format!(
				"DEBUG USE 6651.RIGHT: i: {}, alpha: {}, beta: {}, \
				inv_hab22_right_size: {}",
				_i, alpha.value()?, beta.value()?,
				inv_hab22_right_size));
		}
		//5.2.2 now process the inv_hab22_right
		for i in 0usize..inv_hab22_right_size{
			//let v_temp = &beta * &si.col1_share[i]; //cost 271ns
			let v_temp = alloc_fpvar_mul(&beta, &si.col1_share[i]); //231ns
			//let v = &alpha + &v_temp + &si.col2_share[i]; //255ns
			let v = sum3(&alpha,&v_temp,&si.col2_share[i]); //160ns
			let m_i = &si.m_share[i];
			//let prod = &v * &wtns_var.inv_hab22_right[i];
			let prod = alloc_fpvar_mul(&v,  &wtns_var.inv_hab22_right[i]);
			prod.enforce_equal(&one_var)?;

			// Dummies (i >= act_lookup_share_size) have col1=col2=m=0
			// per update_lookup() at sigma_ir1cs.rs:1304-1316, so their
			// contribution to sum_hab22_right is (1/alpha)*0 = 0.
			let to_add = &wtns_var.inv_hab22_right[i] * m_i;
			if b_debug{
				if si.col1_share[i].value()?.is_zero(){
					assert!(m_i.value()?.is_zero());
				}
			}
			sum_hab22_right = &sum_hab22_right + &to_add;

			if i%ADD_CHAIN_SIZE==0{//avoid too long chain in later
				sum_hab22_right = &sum_hab22_right * &one_wit_var;
			}
		}


		let b_hab_res1 = sum_hab22_right.is_eq(&sum_hab22_left)?;
		let b_hab_res = not_final_step.or(&b_hab_res1)?.or(&sum_hab22_right.is_zero()?)?; //when sum_hab22_right is zero, we regard it as dummy

		if b_has_lookup && self.b_check_lkup{ 
			//NOTE self.b_check_lkup is ONLY for testing purpose
			//when we pass a large lookup table but set small lkup_share_size
			//in circ.
			if b_hab_res.value().is_ok(){
				assert!(b_hab_res.value()?, "failed checking hab22 equation");
			}
			b_hab_res.enforce_equal(&Boolean::TRUE)?;
		}
		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 5.2");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 5.2",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
				"-- -- gen_step_cs step 5.2: cs: {}, vars: {}: lc: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv,
				cs.num_lc() - nl
				), &mut gt
			);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();




		//6. Check the validity of word_id and subseg_id
		// NOTE: the first and the last zi_part2 will be checked
		// in the decider_circuit. Here's we are just checking
		// the connection points between words
		let b_last_full = zi_part2.accumulated_word_len.is_eq(
			&zi_part2.total_word_len)?; //last subseg is full
		//println!("DEBUG USE 201: b_last_full: {}, zi.word_id: {}, now.word_id: {}, subseg_id: {}, total_segs: {}", b_last_full.value()?, zi_part2.word_id.value()?, si.word_id.value()?, zi_part2.subseg_id.value()?, zi_part2.total_word_segs.value()?);
		assert_imply(&b_last_full, &si.word_id.is_eq(
			&(&zi_part2.word_id+&one_var))?).expect("is eq err");
		assert_imply(&b_last_full, &zi_part2.subseg_id.is_eq(
			&zi_part2.total_word_segs)?).expect("is eq err");
		assert_imply(&b_last_full, &si.subseg_id.is_eq(&one_var)?).expect("eq");

		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 6");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 6",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 6: cs: {}, vars: {}, lc: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl
			), &mut gt
		);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();



		//7. compute the KZG evaluation of :
		// [lookup col1, col2, words, vec_r, vec_v]
		// using Homer's method and combined using rc.
		let mut sum_kzg_eval_lk= zi_part2.sum_kzg_eval_lk.clone();
		let mut sum_kzg_eval_word= zi_part2.sum_kzg_eval_word.clone();
		let mut sum_kzg_eval_others= zi_part2.sum_kzg_eval_others.clone();
		let mut sum_vec_v_i= zi_part2.sum_vec_v_i.clone();
		if !self.b_full_mode{//only do it for the first stage
			//println!("DEBUG USE 501.0: word_id: {}, subseg_id: {},  ch: {}, rc: {}", si.word_id.value()?, si.subseg_id.value()?, zi_part2.ch.value()?, zi_part2.rc.value()?);
			//6.1 compute rands and assisting vars
			let ch = zi_part2.ch.clone();
			let rc = zi_part2.rc.clone();
			let _b_first = si.word_id.is_one()?.and(&si.subseg_id.is_one()?);
			let b_last = si.word_id.is_eq(&si.total_words)?.and(& 
				si.subseg_id.is_eq(&si.total_word_segs)?)?;
			let b_first_seg = si.subseg_id.is_one()?;
			let b_last_seg = si.subseg_id.is_eq(&si.total_word_segs)?;
			let mut rcs = vec![one_var.clone()];
			for _i in 0..5{rcs.push(&rcs[rcs.len()-1] * &rc)};

			//6.2 update sum_kzg_eval_lk
			let old_sum_kzg_eval_lk = sum_kzg_eval_lk.clone();
			let cfg_lk = self.stmt_config.lookup_share_size;

			// ASSUMPTION: cfg_lk < 2^POW_LE_BITS  (= 2^32).
			assert!(
				(cfg_lk as u64) < (1u64 << POW_LE_BITS),
				"step 6.2: lookup_share_size {} exceeds 2^{} bound",
				cfg_lk, POW_LE_BITS
			);


			// (a) UNCONDITIONAL Horner over all cfg slots.  
			//   NOTE: Dummies
			//     (i >= act_lookup_share_size) have col1=col2=0 (see
			//     update_lookup at sigma_ir1cs.rs:~1304-1316), so they
			//     only push *ch through.  We compensate for the extra
			//     ch^(cfg-act) factor in step (c).
			let mut sum_padded = sum_kzg_eval_lk.clone();
			for i in 0..cfg_lk {
				sum_padded = &(&sum_padded * &ch)
					+ &(&si.col1_share[i] * &rcs[0])
					+ &(&si.col2_share[i] * &rcs[1]);
			}

			// (b) ch_pow = ch^(cfg - act) via existing pow_le.
			let cfg_const = FpVar::<F>::new_constant(
				cs.clone(), F::from(cfg_lk as u64))?;
			let n_dummy = &cfg_const - &si.act_lookup_share_size;
			let nd_bits = alloc_le_bits(cs.clone(), &n_dummy)?;
			let ch_pow = ch.pow_le(&nd_bits)?;

			// (c) recover sum_target by enforcing
			//     sum_target * ch_pow == sum_padded.
			let sum_target = FpVar::<F>::new_witness(cs.clone(), || {
				let pad = sum_padded.value()?;
				let pow = ch_pow.value()?;
				// In setup-mode placeholder (ch=0, n_dummy>0), ch_pow=0
				// and inverse is undefined.  Default to zero; the
				// resulting unsat is benign (matrices are still correct
				// for the real-witness path).
				Ok(pad * pow.inverse().unwrap_or(F::zero()))
			})?;
			cs.enforce_constraint(
				var_to_lb(&sum_target, F::one()),
				var_to_lb(&ch_pow,     F::one()),
				var_to_lb(&sum_padded, F::one()),
			)?;

			// (d) preserve original act=0 gate (redundant under (c)
			//     but kept for parity with the previous code).
			sum_kzg_eval_lk = si.act_lookup_share_size.is_zero()?
				.select(&old_sum_kzg_eval_lk, &sum_target)?;

			//6.3 update sum_kzg_eval_word and also sum_vec_v_i
			let old_sum_kzg_eval_word = sum_kzg_eval_word.clone();
			let old_sum_vec_v_i = sum_vec_v_i.clone();
			sum_vec_v_i = b_first_seg.select(&zero_var, &sum_vec_v_i)?;
			let mut word_size_left = si.act_word_subseg_size.clone();
			let val_lkup_left = word_size_left.value()?;
			let vec_left = (0..self.stmt_config.word_subseg_size)
			.collect::<Vec<_>>(). into_par_iter().map(|i|{
					let u_left = field_to_usize(&val_lkup_left);
					if u_left>=i { val_lkup_left - F::from(i as u64) }
						else{ F::zero()}
				}).collect::<Vec<F>>();
			let v_inv_lzero = gen_vec_inverse(&vec_left);
			assert!(v_inv_lzero.len()==self.stmt_config.word_subseg_size);
			for i in 0..self.stmt_config.word_subseg_size{
				//let b_wd_left_zero = word_size_left.is_zero()?;
				let b_wd_left_zero = word_size_left.is_zero_adv(&v_inv_lzero[i])?;
				let word_to_add=&si.word_subseg[i] * &rcs[2];
				sum_kzg_eval_word = b_wd_left_zero.select(
					&sum_kzg_eval_word,
					&(&(&sum_kzg_eval_word*&ch) + &word_to_add) 
				)?;

				sum_vec_v_i = b_wd_left_zero.select(
					&sum_vec_v_i,
					&(&(sum_vec_v_i.clone() * &si.batch_r)+&si.word_subseg[i])
				)?;

				let val2_wd = &word_size_left- &one_var;
				word_size_left= b_wd_left_zero.select(&zero_var, 
					&val2_wd)?;
			}
			sum_kzg_eval_word= si.act_word_subseg_size.is_zero()?.select(
				&old_sum_kzg_eval_word, &sum_kzg_eval_word)?;
			sum_kzg_eval_word = b_last.select(
				&(&sum_kzg_eval_word*&ch + &(&si.r_all_words*&rcs[2])),
				&sum_kzg_eval_word)?;
			sum_vec_v_i= si.act_word_subseg_size.is_zero()?.select(
				&old_sum_vec_v_i, &sum_vec_v_i)?;
			sum_vec_v_i = b_last_seg.select(
				&(&(&sum_vec_v_i*&si.batch_r) + &si.r_word_i), 
				&sum_vec_v_i)?;
			if B_DEBUG {
				if b_last_seg.value()? {assert!(sum_vec_v_i.value()?
					== si.batch_v.value()?);}
			}

			//6.4 update the sum_kzg_eval_others
			sum_kzg_eval_others = b_first_seg.select(&( 
				&(&sum_kzg_eval_others * &ch) +  
				&(&si.total_word_len * &rcs[3])+
				&(&si.batch_r * &rcs[4]) + 
				&(&si.batch_v * &rcs[5])
				),&sum_kzg_eval_others)?;
			sum_kzg_eval_others = b_last.select(&(
				&(&sum_kzg_eval_others * &ch) + 
				&(&si.r_kzg_len * &rcs[3]) +
				&(&si.r_vec_r * &rcs[4]) +
				&(&si.r_vec_v * &rcs[5])
				), &sum_kzg_eval_others)?;

			//6.5 total
			let _sum_kzg_eval = &sum_kzg_eval_lk + 
				&sum_kzg_eval_word + &sum_kzg_eval_others;
			//println!("DEBUG USE 501.9: sum_kzg_eval: {}, sum_vec_v_i: {}", sum_kzg_eval.value()?, sum_vec_v_i.value()?);
		}
		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 7");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 7",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!("gen_step_cs step 7: cs: {}, vars: {}, lc: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl
			), &mut gt
		);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();


		//8. VERIFY join constraints
		let (_stmt_len, _stmt_cfg, _v_idx, extra_join_constraints, vec_idx_cpi) 
			= lock_unwrap!(self.gadget_mapper).gen_statement_structure(self.stmt_config.lookup_share_size);
		let v_stmt = wtns_var.statement;
		if extra_join_constraints.len()>0{
			for (rg1,rg2) in extra_join_constraints{
				let (a,b) = rg1;
				let (c,d) = rg2;
				assert!(b-a == d-c);
				for j in a..b+1{
					v_stmt[j].enforce_equal(&v_stmt[c+j-a])?;
					if B_DEBUG {
						assert!(v_stmt[j].value()==v_stmt[c+j-a].value());
					}
				}
			}
		}

		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 8");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 8",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 8: cs: {}, vars: {}, lc: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl
			), &mut gt
		);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();

		//9. build the new zi_part's cycle input.
		let cp_inp = if self.b_full_mode{
			let cp_vec = vec_idx_cpi.into_iter().map(|x|
				v_stmt[x].clone()).collect::<Vec<FpVar<F>>>();
			Some(CyclePairInputVar::from_vec(&cp_vec, fq_bits))
		} else {None};


		//total_words: treat it like almost a constant along the way
		// if very first, take it from non-determnistic advice and then
		//stick to it (copy from past zi_part2) -
		let total_words=b_first.select(&si.total_words,&zi_part2.total_words)?;
		//acc_word_len: update from previous or for a new word
		let accumulated_word_len = b_last_full.select(&si.act_word_subseg_size,
			&(&zi_part2.accumulated_word_len + &si.act_word_subseg_size))?;

		let zi1_part2 = ZiPartTwoInstVar::<F>{
			ch: ch.clone(),
			rc: rc.clone(),
			sum_inp: sum_inp.clone(),
			sum_oup: sum_oup.clone(),

			alpha: zi_part2.alpha.clone(),
			beta: zi_part2.beta.clone(),
			sum_hab22_left: sum_hab22_left,
			sum_hab22_right: sum_hab22_right,

			sum_kzg_eval_lk: sum_kzg_eval_lk,
			sum_kzg_eval_word: sum_kzg_eval_word,
			sum_kzg_eval_others: sum_kzg_eval_others,
			sum_vec_v_i: sum_vec_v_i,

			total_word_len: si.total_word_len.clone(),
			accumulated_word_len: accumulated_word_len,

			//as we have performed check 6, copy from non-determinic advice si
			word_id: si.word_id.clone(),
			subseg_id: si.subseg_id.clone(),
			total_word_segs: si.total_word_segs.clone(),
			total_words: total_words,
			f_result: si.f_result.clone(),

			cyclepair_input: cp_inp,
		};

		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 9");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 9",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 9: cs: {}, vars: {}, lc: {}, TOTAL: cs: {}, vars: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl,
			cs.num_constraints(),
			cs.num_witness_variables()
			), &mut gt
		);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();
		nl = cs.num_lc();


		//10. now enforce and build `z_{i+1}`
		let cur_hc_cmF = z_i[0].clone();
		let cur_cmF = wtns_var.cmF.clone(); //4 elements
		let to_hash = vec![ vec![cur_hc_cmF], cur_cmF].concat();
        let mut sponge = PoseidonSpongeVar::<F>::new(
			cs.clone(), &self.poseidon_config);
		sponge.absorb(&to_hash)?;
		// 4 poseidon hashes for 7 elements = 1200 
		let new_cur_hc_cmF = sponge.squeeze_field_elements(1)
			.unwrap()[0].clone();

		let hash_zi_part2= zi1_part2.hash(&self.poseidon_config, cs.clone());

		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 9.1");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 9.1",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}

		//10.5 check the failed_sigs are covered by discharged sigs
		let rc2 = &rc + &FpVar::<F>::new_constant(cs.clone(),
			F::from(237177234918187u64))?;
		//rc2 is used to prevent the initial dummy case rc0 causing
		//inverse err. In the real mode, rc will be the real Fiat-Shamir
		// 2026-05-16: probe 77317.3 — caller-side, just before
		// check_logup. Prints the three FpVar vectors' values and
		// computes the host-side multiset diff against mtbl weights.
		// If MULTISET_MISMATCH fires here, the bug is upstream of
		// the circuit (in build_statement / gen_witness / from_vec).
		if crate::folding::foldpot::utils::probe_77317_enabled() {
			use crate::folding::foldpot::utils::{
				probe_77317_dump_fpvar_vec,
				probe_77317_multiset_diff_fpvar};
			let rc2_v = rc2.value().unwrap_or(F::zero());
			emit_stdout(format!(
				"DEBUG USE 77317.3: CALL_SITE sigs_check \
				 job={} failed.len={} discharged.len={} \
				 mtbl.len={} rc2_u64={}",
				self.job_id,
				si.failed_sigs.len(),
				si.discharged_sigs.len(),
				si.mtbl_sigs.len(),
				crate::folding::foldpot::utils
					::probe_77317_f_as_u64_lossy(&rc2_v)));
			probe_77317_dump_fpvar_vec("3.failed",
				"si.failed_sigs", &si.failed_sigs);
			probe_77317_dump_fpvar_vec("3.discharged",
				"si.discharged_sigs", &si.discharged_sigs);
			probe_77317_dump_fpvar_vec("3.mtbl",
				"si.mtbl_sigs", &si.mtbl_sigs);
			probe_77317_multiset_diff_fpvar("3",
				&si.failed_sigs, &si.discharged_sigs,
				&si.mtbl_sigs);
		}
		let b_sigs = check_logup(cs.clone(),
			&si.failed_sigs,
			&si.discharged_sigs,
			&si.mtbl_sigs,
			&rc2,
		)?;
		//Aggressive locality enforces failed-subset-of-discharged per
		//chunk (b_sigs every step); else final-step-only relaxation.
		//Flag-off path is the original expression, byte-identical.
		let b_correct = if utils::consts::read_global_config()
			.clamav_cfg.b_aggressive_sde_for_rep {
			b_sigs.clone()
		} else {
			not_final_step.or(&b_sigs)?
		};

		if B_DEBUG3{
			check_cs(&cs, "gen_step_cs 9.2");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 9.2",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}

		if b_show_sigs{
			print_vec_var("DEBUG USE 7801: sigma_ir1cs: failed_sigs", &si.failed_sigs);
			print_vec_var("DEBUG USE 7802: sigma_ir1cs: : discharged_sigs",
				&si.discharged_sigs);
			emit_stdout(format!(
				"DEBUG USE 7803 sigma_ir1cs: b_correct: {}",
				b_correct.value()?));
		}

		b_correct.enforce_equal(&Boolean::TRUE)?;
		if b_correct.value().is_ok(){
			assert!(b_correct.value()?, "failed b_correct");
		}

		if B_DEBUG2{
			check_cs(&cs, "gen_step_cs FINAL");
			emit_stdout(format!(concat!(
				"--- DEBUG USE 7601: gen_step_constraints step 10. RETURN!",
				"cs: {}, stack  =======, stack: {}"),
				cs.num_constraints(), get_stack_space()
			));
		}
		log_perf(self.job_id, log_level, &format!(
			"gen_step_cs step 10: cs: {}, vars: {}, lc: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			cs.num_lc() - nl
			), &mut gt
		);


		//M0 fingerprint: per-circuit synthesized dims + IO arity (inert
		//unless fp_sink set). Re-emitted each step; sink keeps last.
		utils::consts::fp_emit(
			&format!("{}.nc", self.name), cs.num_constraints() as u64);
		utils::consts::fp_emit(
			&format!("{}.nv", self.name),
			cs.num_witness_variables() as u64);
		utils::consts::fp_emit(
			&format!("{}.ext_in", self.name), external_inputs.len() as u64);

		cost_capture_set_end(cs.num_constraints());
		Ok(vec![new_cur_hc_cmF, hash_zi_part2])
	}
}

#[cfg(test)]
pub mod tests_sigma_ir1cs{
	use core::marker::PhantomData;
	use ark_ff::{PrimeField,ToConstraintField,BigInteger};
	use ark_relations::r1cs::{ConstraintSystem,
		ConstraintSystemRef, SynthesisError};
	use ark_crypto_primitives::sponge::{Absorb};
	use crate::{
		Error,
		folding::foldpot::{
			sigma_ir1cs::{GadgetMapper,SigmaIR1CS,SigmaIR1CS_Inst,WitnessSigmaIR1CSVar,SigmaGadget,StatementInst, StatementConfig,LookupTableTwoCol_Inst,ZiPartTwoInst,LookupTableTwoCol,StatementExtraInfo,CyclePairInput,CyclePairInputVar, WitnessSigmaIR1CSConfig,DummyNdAdvice, DummyCapacity,NdAdvice,Capacity,WordInfo},
			circuits_super::{field_to_usize},
			utils::{f1_to_f2_limbs, f1_limbs_to_f2,expand2},
			container_config::{ContainerConfig,ColEle},
		}
	};

	use ark_std::{One,Zero,UniformRand};
	use ark_r1cs_std::{
		R1CSVar,
		fields::{fp::FpVar,FieldVar},
		alloc::AllocVar, 
		eq::EqGadget, ToBitsGadget,
	};
    use ark_bn254::{Bn254, Fr, G1Projective as Projective, G2Projective as Projective2, Fq};
	use crate::{
		transcript::poseidon::poseidon_canonical_config,
		frontend::{FCircuit},
	};
	use std::collections::HashMap;
	use ark_ec::{CurveGroup,pairing::Pairing};
	use ark_std::sync::Arc;
	use crate::commitment::{
		CommitmentScheme,
		kzg::KZG,
	};
	use std::{sync::Mutex};

	/// a gadget verifies an input number has a cubic root. 
	/// Statement (x;w): where x is the number to verify and w is
	/// its cubic root.
	/// The gadget works by sending a dummy msg1, 
	/// receiving a dummy msg2, and then
	/// copying w as msg3.
	#[derive(Clone,Debug)]
	pub struct VerCubicGadget<F:PrimeField>{ 
		_f: PhantomData<F>
	}

	impl <F:PrimeField> SigmaGadget<F> for VerCubicGadget<F>{
		fn set_job_id(&mut self, _job_id: usize){}
		fn get_job_id(&self)->usize{0}
		fn get_container_config(&self)->ContainerConfig{
			unimplemented!("not needed. legacy code")
		}
		fn get_name(&self)->&str{
			"VerCubicGadget"
		}

		/// set the container cfg. This is only needed for those gadgets
		/// in SED approach
		fn set_container_cfg(&mut self, _cfgs_context: Arc<Vec<ContainerConfig>>, _idx: usize){
			unimplemented!("not needed. handled by legacy code");
		}

		/// Get the instructions for build its statement.
		/// NOTE: this is only needed for those used in SedGadgetMapper.
		/// Others are handled by legacy code in their gadget mapper.
		fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
			unimplemented!("no need to implement. legacy of caller handles it");
		}


		/// return the sizes of inp/oup/data to append to the
		/// buffer of GadgetMapper.
		fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the estimated cost in number of constraints
		fn est_cost(&self)->usize{
			4
		}



		/// statment `(x;w)` where w is the cubic root of x
		fn get_msg_size(&self) -> (usize, usize, usize, usize){
			(2, 1, 1, 1)
		}

		fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) -> Vec<F>{
			vec![F::one()]	// dummy
		}

		fn gen_msg3(&self, stmt_vec: &Vec<F>, stmt_idx: 
			&Vec<(usize,usize)>, 
			_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
			_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
			let w = stmt_vec[stmt_idx[1].0]; //second element of statment
			vec![w]
		}

		fn assert_msg3(&self, i: usize, _cs: ConstraintSystemRef<F>, 
			wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig,
			_word_id: FpVar<F>, _subsig_id: FpVar<F>) 
			-> Result<(), SynthesisError>{
			let (stmt_idx, _m1_idx, _m2_idx, m3_idx) = cfg.get_gadget_indices(i);
			let msg3 = &wtns.msg3[m3_idx];
			let x = &wtns.statement[stmt_idx[0].0];
			let cube = msg3 * msg3 * msg3;
			#[cfg(test)]{
				assert!(cube.value().unwrap()==x.value().unwrap(),"fails assert_msg3 of VerCubicGadget");
			}
			x.enforce_equal(&cube)?;

			Ok(())
		}
	}

	/// a gadget verifies an input number has a quadratic root. 
	/// Statement (x;w): where x is the number to verify and w is
	/// its square root.
	/// The gadget works by sending a dummy msg1, 
	/// receiving a dummy msg2, and then
	/// copying w as msg3.
	#[derive(Clone,Debug)]
	pub struct VerSquareGadget<F:PrimeField>{ 
		_f: PhantomData<F>
	}

	impl <F:PrimeField> SigmaGadget<F> for VerSquareGadget<F>{
		fn set_job_id(&mut self, _job_id: usize){}
		fn get_job_id(&self)->usize{0}
		fn get_container_config(&self)->ContainerConfig{
			unimplemented!("not needed. legacy code")
		}
		fn get_name(&self)->&str{
			"VerSquareGadget"
		}

		/// set the container cfg. This is only needed for those gadgets
		/// in SED approach
		fn set_container_cfg(&mut self, _cfgs_context: Arc<Vec<ContainerConfig>>, _idx: usize){
			unimplemented!("not needed. handled by legacy code");
		}

		/// Get the instructions for build its statement.
		/// NOTE: this is only needed for those used in SedGadgetMapper.
		/// Others are handled by legacy code in their gadget mapper.
		fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the sizes of inp/oup/data to append to the
		/// buffer of GadgetMapper.
		fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the estimated cost in number of constraints
		fn est_cost(&self)->usize{
			3
		}

		/// statment `(x;w)` where w is the square root of x
		fn get_msg_size(&self) -> (usize, usize, usize, usize){
			(2, 1, 1, 1)
		}

		fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) 
			-> Vec<F>{
			vec![F::one()]	// dummy
		}

		fn gen_msg3(&self, stmt_vec: &Vec<F>, stmt_idx: 
			&Vec<(usize,usize)>,
			_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
			_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
			let w = stmt_vec[stmt_idx[1].0]; //second element of statment
			vec![w]
		}

		fn assert_msg3(&self, i: usize, _cs: ConstraintSystemRef<F>, 
			wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig,
			_word_id: FpVar<F>, _subsig_id: FpVar<F>) 
			-> Result<(), SynthesisError>{
			let (stmt_idx, _m1_idx, _m2_idx, m3_idx) = cfg.get_gadget_indices(i);
			let msg3 = &wtns.msg3[m3_idx];
			let x = &wtns.statement[stmt_idx[0].0];
			let sq = msg3 * msg3;
			#[cfg(test)]{
				assert!(sq.value().unwrap()==x.value().unwrap(),"fails assert_msg3 of VerSquareGadget");
			}
			x.enforce_equal(&sq)?;

			Ok(())
		}
	}

	/// A gadget verifies the relation of counter
	/// (c1, tbl_id, c2) it verifies that
	/// when tbl_id is not 0, c2 = c1 + 1 otherwise
	/// c2 is c1.
	#[derive(Clone,Debug)]
	pub struct CounterIOGadget<F:PrimeField>{ 
		_f: PhantomData<F>
	}

	impl <F:PrimeField> SigmaGadget<F> for CounterIOGadget<F>{
		fn set_job_id(&mut self, _job_id: usize){}
		fn get_job_id(&self)->usize{0}

		fn get_container_config(&self)->ContainerConfig{
			unimplemented!("not needed. legacy code")
		}

		fn get_name(&self)->&str{
			"CounterIOGadget"
		}

		/// set the container cfg. This is only needed for those gadgets
		/// in SED approach
		fn set_container_cfg(&mut self, _cfgs_context: Arc<Vec<ContainerConfig>>, _idx: usize){
			unimplemented!("not needed. handled by legacy code");
		}

		/// Get the instructions for build its statement.
		/// NOTE: this is only needed for those used in SedGadgetMapper.
		/// Others are handled by legacy code in their gadget mapper.
		fn get_stmt_map_instructions(&self)->Vec<(i32, usize, usize, usize)>{
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the sizes of inp/oup/data to append to the
		/// buffer of GadgetMapper.
		fn get_to_add_size(&self)->(usize, usize, usize, usize, usize){
			unimplemented!("no need to implement. legacy of caller handles it");
		}

		/// return the estimated cost in number of constraints
		fn est_cost(&self)->usize{
			5
		}

		/// statement (c1, tbl_id, c2). all three messages length 0
		fn get_msg_size(&self) -> (usize, usize, usize, usize){
			(3, 0, 0, 0)
		}

		fn gen_msg1(&self, _stmt_vec: &Vec<F>, _v_idx: &Vec<(usize,usize)>) 
			-> Vec<F>{
			vec![] // dummy
		}

		fn gen_msg3(&self, _stmt_vec: &Vec<F>, _stmt_idx: 
			&Vec<(usize,usize)>, 
			_msg1_vec: &Vec<F>, _idx_msg1: usize, _len_msg1: usize,
			_msg2_vec: &Vec<F>, _idx_msg2: usize, _len_msg2: usize) -> Vec<F>{
			vec![]
		}

		fn assert_msg3(&self, i: usize, cs: ConstraintSystemRef<F>, 
			wtns: &WitnessSigmaIR1CSVar<F>, cfg: &WitnessSigmaIR1CSConfig,
			_word_id: FpVar<F>, _subsig_id: FpVar<F>) 
			-> Result<(), SynthesisError>{
			let (stmt_idx, _, _, _) = cfg.get_gadget_indices(i);
			let c1 = &wtns.statement[stmt_idx[0].0];
			let tbl_id = &wtns.statement[stmt_idx[1].0];
			let c2 = &wtns.statement[stmt_idx[2].0];

			let zero = FpVar::<F>::new_constant(cs.clone(), F::zero())?;
			let one= FpVar::<F>::new_constant(cs.clone(), F::one())?;
			let b_add = tbl_id.is_zero()?;
			let to_add =b_add.select(&zero, &one)?;
			let res = c1 + to_add.clone();
			#[cfg(test)]{
				assert!(c2.value().unwrap()==res.value().unwrap(),"fails assert_msg3 of Counter");
			}
			c2.enforce_equal(&res)?;

			Ok(())
		}
	}

	/// SixRoot relation consists of three gadgets:
	/// (1) verify cubic root, (2) verify square root, 
	/// (3) update_counter gadget which based on if
	/// n is tagged with sub-tableID i, increase the input counter
	#[derive(Clone,Debug)]
	pub struct SixRootMapper<F:PrimeField, LK: LookupTableTwoCol<F>>{
		pub _f: PhantomData<F>,
		pub _lk: PhantomData<LK>,
		pub job_id: usize,
	}

	/// get the cubic root of v (assuming its cubic root is
	/// less than 10. If no cubic root, return 0. Assuming v
	/// is a natural number between 1 and 1000.
	fn get_cubic_root(v: usize)->usize{
		for i in 1..v+1{ if i*i*i == v {return i;} }
		0
	}

	/// assume v is between 1 and 100, return its square root.
	/// if not found, return 0
	fn get_sq_root(v: usize) -> usize{
		for i in 1..v+1{ if i*i == v {return i;} }
		0
	}

	impl <F:PrimeField, LK: LookupTableTwoCol<F>> 
	GadgetMapper<F,LK> for SixRootMapper<F, LK>{
		fn set_job_id(&mut self, job_id: usize){
			self.job_id = job_id;
		}
		fn get_job_id(&self)->usize{
			self.job_id
		}

		/// use advice to generate container config and set it for
		/// each gadget (if gadgetes support container config for
		/// deseiralization). This is only needed for those gadgets in SED
		/// approach.
		fn set_container_config(&mut self, _advice: &Arc<dyn NdAdvice + Send + Sync>){ 
			//not needed, handled by legacy code
		}

		/// the capacity is the word length that can be handled by
		/// the circuit
		fn get_capacity(&self)->Arc<dyn Capacity + Send + Sync>{
			let word_seg_len = self.max_word_len();
			Arc::new( DummyCapacity{word_seg_len} )
		}


		fn gen_nd_advice(&self, word: &Vec<F>, _wi: &WordInfo,
			_prv_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, _seg_id: usize, _job_id: usize) 
		-> Result<Arc<dyn NdAdvice + Send + Sync>, Error>{
			if word.len()<=self.max_word_len(){
				Ok( Arc::new(DummyNdAdvice{}))
			}else{
				Err(
					Error::CapErr(vec![(format!("max_word_len"), word.len())])
				)
			}
		}

		fn get_name(&self) -> String { "SixRootMapper".to_string() }

		fn max_word_len(&self)->usize{ 1 }

		fn get_gadgets(&self) -> Vec<Arc<Mutex<dyn SigmaGadget<F> + Send + Sync>>>{ 
			let cubic = VerCubicGadget::<F>{_f:PhantomData};
			let sq = VerSquareGadget::<F>{_f:PhantomData};
			let counter = CounterIOGadget::<F>{_f:PhantomData};
			vec![
				Arc::new(Mutex::new(cubic)), 
				Arc::new(Mutex::new(sq)), 
				Arc::new(Mutex::new(counter))
			]
		}

		/// expecting [n], and build the rest of problem statement instance.
		fn build_statement(&self, word: &Vec<F>, prev_stmt: &Option<StatementInst<F,LK>>, lkup: Arc<LK>, ea: &StatementExtraInfo<F>, _advice: Arc<dyn NdAdvice + Send + Sync>, _lkup_size: usize, _b_dummy: bool, _job_id: usize) -> Result<StatementInst<F,LK>, Error>{
			//1. compute the cube_root, sq_root, tbl_id
			assert!(word.len()==1);
			let n = word[0]; 
			let n_val = field_to_usize(&n);
			let croot_val = get_cubic_root(n_val);
			let sroot_val = get_sq_root(n_val);
			//println!("DEBUG USE 201: n: {}, croot_val: {}, sroot_val: {}", n, croot_val, sroot_val);

			let croot = F::from(croot_val as u32);
			let sroot = F::from(sroot_val as u32);
			let _f_word_id = ea.word_id;
			let _f_total_words = ea.total_words;
			let (zero, one,two) = (F::zero(), F::one(),F::from(2u32));
			let find_res = lkup.find(two, F::from(n));
			let tbl_id = match find_res{
				Ok(_id) => two,
				Err(_id) =>  F::zero(), //null entry
			};

			//2. retrieve the previous counter from previous witness
			let ctr= prev_stmt.as_ref().map_or(zero, |stmt| {
				stmt.oup_buf[0] 
			});
			//println!("DEBUG USE 203: prev_counter: {}", ctr);
			let to_add = if croot_val>0 && tbl_id==zero {zero} else {one};
			let new_ctr = to_add + ctr;
			//println!("DEBUG USE 204: new_counter: {}", ctr);
			let pc_i = zero; //current circ
			let pc_i1 = zero; //will be RESET later
			let f_n_circ = ea.n_circ;
			let ncirc_minus_pci = f_n_circ-pc_i;

			let failed_sigs = vec![zero];
			let discharged_sigs = vec![zero];
			let mtbl_sigs = vec![one]; //as zero appeared once failed_sigs
			let stmt = StatementInst{
				pc_i: pc_i,
				pc_i1: pc_i1, //will be reset later
				n_circ: f_n_circ,
				n_circ_minus_pc: ncirc_minus_pci,
				act_input_size: one,
				act_output_size: one,
				act_lookup_share_size: F::from(4u32),
				act_word_subseg_size: one,
				word_id: ea.word_id,
				subseg_id: ea.subseg_id,
				total_word_len: ea.total_word_len,
				total_word_segs: ea.total_word_segs,
				total_words: ea.total_words,
				r_F: two, //for debug

				batch_r: ea.batch_r,
				batch_v: ea.batch_v,
				r_all_words: ea.r_all_words,
				r_kzg_len: ea.r_kzg_len,
				r_vec_r: ea.r_vec_r,
				r_vec_v: ea.r_vec_v,
				r_word_i: ea.r_word_i,
				accumulated_word_len: ea.accumulated_word_len,
				f_result: zero, //we didn't take advantage of it.

				inp_buf: vec![ctr,zero], //input counter
				oup_buf: vec![new_ctr,zero],  //output counter
				word_subseg: vec![n, zero], //claim n has six'6h root
				data: vec![croot, sroot, zero, zero], //cubic and sq root as wit
				// subtbl_id zero means do not look it up
				// will eventually generate (0,0) entry
				subtable_id: vec![
					zero, zero,  //inp_buf
					zero, zero, //oup_buf
			//		tbl_id, zero, //word_sug (legacy) - not checked.
					zero, zero, zero, zero //data
				],
				col1_share: vec![zero; 4], //to be updated, capcity 4
				col2_share: vec![zero; 4], //to be updated
				m_share: vec![zero; 4],//to be updated

				failed_sigs,
				discharged_sigs,
				mtbl_sigs,

				_lk: PhantomData,
			};
			let _stmt_vec = stmt.to_vec();
				
			Ok(stmt)
		}

		fn gen_statement_structure(&self, _lookup_share_size: usize) -> 
			(usize, StatementConfig, Vec<Vec<(usize,usize)>>, 
				Vec<((usize,usize),(usize,usize))>,
				Vec<usize>){
			//1. a sample statemnet structure
			let input_size = 2;
			let output_size = 2;
			let word_subseg_size = 2;
			let data_size = 4;
			let lookup_share_size = 4;//overwrite it to keep legacy code logic
			let failed_sig_size = 1;
			let discharged_sig_size = 1;
			let b_cyclepair = false;
			let cfg = StatementConfig::new(
				input_size, output_size, word_subseg_size,
				data_size, lookup_share_size,
				failed_sig_size, discharged_sig_size,
				b_cyclepair
			);

			//2. generate the result to return
			let cb_map = vec![cfg.idx_word_subseg, cfg.idx_data];
			let sq_map = vec![cfg.idx_word_subseg, cfg.idx_data+1];
			let ct_map = vec![cfg.idx_inp, cfg.idx_subtable_id+cfg.idx_word_subseg-cfg.idx_inp, cfg.idx_oup];

			//3. return. Note: no extra join constraints and cyclepair inp
			let opt_joins = vec![];
			let cyclepair_map = vec![]; 
			(cfg.total_size(), cfg, 
				vec![expand2(&cb_map), expand2(&sq_map), expand2(&ct_map)], 
				opt_joins, cyclepair_map)
		}


	}


	/// Generate the data pack: lookups, six_root IR1CS instance,
	/// and a number of step (statements) for unit testing.
	///
	/// SixRoot circuit statement has the following structure:
	/// (n, cubic_root, sq_root, input_counter, output_counter)
	/// it verifies that if cubic_root and sq_root given are really
	/// the cubic and sq root of n, and it also verifies that
	/// n is contained in lookup subtable 1. If all these conditions
	/// are satisfied, it increases input_counter by 1.
	/// NOTE that it DOES NOT decide if n has a six-th root, it only
	/// verify the validity of the supplied witness.
	///
	/// This data pack generation algorithm generates steps alternating
	/// between 64 and 729, where 729 is not contained in subtable 1
	/// Thus, only even tries will increasing the input counter.
	/// SixRoot example does NOT demonstrate the word batch processing
	/// functions. Use SumWord example for demonstrating word batch processing.
	/// return (a lookup table, SixRoot instance, and 
	/// the corresponding statements with lookup shares set)
	pub fn gen_six_root<F,C,CS,LK,const H:bool>(n_steps: usize)->
		(Arc<LK>, SigmaIR1CS_Inst<F,C,CS,LK,SixRootMapper<F,LK>,H>, Vec<StatementInst<F,LK>>)
	where 	C: CurveGroup<ScalarField=F>,
		CS: CommitmentScheme<C, H>,
		F: PrimeField + Absorb +ColEle,
		LK: LookupTableTwoCol<F> + 'static,
	{
		//1. create the lookup, and relation object
		let lk = LK::new(vec![
			(F::from(0u32), F::from(0u32)), //0, null entry
			(F::from(1u32), F::from(0u32)), //First, we have 5 entries [0,4]
			(F::from(1u32), F::from(1u32)), 
			(F::from(1u32), F::from(2u32)), 
			(F::from(1u32), F::from(3u32)), 
			(F::from(1u32), F::from(4u32)), 
			(F::from(2u32), F::from(5u32)), //subtable 2 for filtering sixpow 
			(F::from(2u32), F::from(7u32)), //only allow 64 
			(F::from(2u32), F::from(64u32)), //3 --> valid entry (8th entry)
			(F::from(2u32), F::from(200u32)), 
			(F::from(2u32), F::from(300u32)), 
			(F::from(2u32), F::from(400u32)),
		]);
		let mapper_raw = SixRootMapper::<F,LK>{_f: PhantomData, 
			_lk: PhantomData, job_id: 0};
		let mapper = Arc::new(Mutex::new(mapper_raw));
		let lk_len = lk.get_size();
		let share_size = lock_unwrap!(mapper).gen_statement_structure(lk_len/n_steps)
			.1.lookup_share_size;
		assert!(share_size * n_steps >= lk_len, "ERROR: share_size * n_step < lookup table size, increase number of steps!");
        let poseidon_config = poseidon_canonical_config::<F>();
		let b_check_lkup = true;
		let six_ir1cs = 
			SigmaIR1CS_Inst::<F,C,CS,LK,SixRootMapper<F,LK>,H>
			::new_adv(format!("six_ir1cs"), 
			poseidon_config, mapper.clone(), false, share_size, false, 
				b_check_lkup).expect("creating ir1cs failed");

		//2. create the inputs and then statements
		//let mut counter = 0;
		let mut vec_stmt = vec![];
		let (_, _stmt_cfg,_, _, _) = lock_unwrap!(mapper)
			.gen_statement_structure(share_size);
		let _wtns_cfg = six_ir1cs.gen_witness_structure(share_size);
		let lkup = Arc::new(lk);
		for i in 0..n_steps{
			//inp: [n, cubic_root, square_root, subtable_id, inp_counter, step_id starting from 0, n_steps]
			let word_id = i+1;
			let total_words = n_steps;
			let u_root = (i+1) as u32;
			let sq_root = u_root * u_root * u_root;
			let _cb_root = u_root * u_root;
			let n = sq_root*sq_root;
			let find_res = lkup.find(F::from(2u32), F::from(n));
			let _tbl_id = match find_res{
				Ok(_id) => F::from(2u32),
				Err(_id) =>  F::zero(), //null entry
			};
			let inp = vec![F::from(n)];
			let subseg_id = 1usize;
			let total_word_len = n_steps;
			let total_word_segs = 1;
			let n_circ = 1;
			let ea = StatementExtraInfo::<F>{
				total_words: F::from(total_words as u32),
				word_id: F::from(word_id as u32),
				subseg_id: F::from(subseg_id as u32),
				total_word_len: F::from(total_word_len as u32),
				total_word_segs: F::from(total_word_segs as u32),
				n_circ: F::from(n_circ as u32),
				pc_i: F::one(),
				pc_i1: F::one(),
				act_word_subseg_size: F::one(),

				batch_r: F::zero(),
				batch_v: F::zero(),
				r_all_words: F::zero(),
				r_kzg_len: F::zero(),
				r_vec_r: F::zero(),
				r_vec_v: F::zero(),
				r_word_i: F::zero(),
				accumulated_word_len: F::one(),
			};
			let dummy_adv = Arc::new(DummyNdAdvice{});
			let stmt = lock_unwrap!(mapper)
				.build_statement(&inp, &None, lkup.clone(), 
					&ea, dummy_adv, 4, false, 0).expect("build stmt fails"); 
			//if tbl_id!=F::zero() {counter += 1;}
			vec_stmt.push(stmt);
		}

		//3. build the m_vec hash based on existing statements 
		// and update the shares
		StatementInst::<F,LK>::update_with_lkup(&lkup, &mut vec_stmt);

		//6. return
		(lkup, six_ir1cs, vec_stmt)
	}

	#[test]
	pub fn test_create_ir1cs(){
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let (_lk, mut six_ir1cs, vec_stmt) = gen_six_root::<Fr,Projective,KZG<'static,Bn254>,LookupTableTwoCol_Inst<Fr>, false>(5);
		let cm_F = Fr::from(10);
		let ch = Fr::from(2);
		let rc = Fr::from(3);
		let fq_bits = Fq::MODULUS_BIT_SIZE as usize;
		let num_words = 1;
		let z_i_part2 = ZiPartTwoInst::new(ch, rc, &poseidon_config, false, fq_bits, num_words);
		six_ir1cs.step_native_mut(0, &z_i_part2, vec_stmt[0].to_vec()).expect("step native mut err");

        let cs = ConstraintSystem::<Fr>::new_ref();
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let zi_part2_hash = z_i_part2.hash(&poseidon_config);
		let z_i = vec![
			FpVar::<Fr>::new_witness(cs.clone(), || Ok(cm_F)).unwrap(),
			FpVar::<Fr>::new_input(cs.clone(), || Ok(zi_part2_hash)).unwrap()
		];
		let external_inputs = six_ir1cs.witness_to_vec_fp_var(cs.clone());
		let _vec_fr = six_ir1cs.generate_step_constraints(cs.clone(), 0,
			z_i, external_inputs);
		//4+1 poseidon hash for msg2 --> 
		//step3 costs 3 to 5 constraints only
		//then genereate hash_cmF (15 elements in zi_part2 to hash)->
		//needs 23 hashes*200 => 4k (actual 3.5k)
		let expected_cs = 3600;
		let act_cs = cs.num_constraints();
		assert!(act_cs>=expected_cs-100 && act_cs<expected_cs+100,
			"number of constraints: {} too far away fro est: {}",
			act_cs, expected_cs);
	}	

	#[test]
	pub fn test_stmt_serialize(){
		let failed_sigs = vec![Fr::zero()];
		let discharged_sigs = vec![Fr::zero()];
		let mtbl_sigs= vec![Fr::one()]; //coz 0 appeared once in failed sigs
		let stmt = StatementInst::<Fr,LookupTableTwoCol_Inst<Fr>>{
			pc_i: Fr::from(2),
			pc_i1: Fr::from(3),
			n_circ: Fr::from(9),
			n_circ_minus_pc: Fr::from(7),
			act_input_size: Fr::from(1),
			act_output_size: Fr::from(1),
			act_lookup_share_size: Fr::from(1),
			act_word_subseg_size: Fr::from(1),
			word_id: Fr::from(2),
			subseg_id: Fr::from(1),
			total_word_len: Fr::from(500),
			total_word_segs: Fr::from(400),
			total_words: Fr::from(1),
			r_F: Fr::from(2),
				batch_r: Fr::zero(),
				batch_v: Fr::zero(),
				r_all_words: Fr::zero(),
				r_kzg_len: Fr::zero(),
				r_vec_r: Fr::zero(),
				r_vec_v: Fr::zero(),
				r_word_i: Fr::zero(),
				accumulated_word_len: Fr::one(),
				f_result: Fr::zero(),

			inp_buf: vec![Fr::from(11), Fr::from(12)],
			oup_buf: vec![Fr::from(21), Fr::from(22)],
			word_subseg: vec![Fr::from(1001), Fr::from(1002)],
			data: vec![Fr::from(31), Fr::from(32)],
			subtable_id: vec![Fr::from(0), Fr::from(0), Fr::from(1),
					Fr::from(1), Fr::from(2), Fr::from(2), Fr::from(3),
					Fr::from(3)],
			col1_share: vec![Fr::from(101), Fr::from(102)],
			col2_share: vec![Fr::from(201), Fr::from(202)],
			m_share: vec![Fr::from(301), Fr::from(302)],

			failed_sigs,
			discharged_sigs,
			mtbl_sigs,

			_lk: PhantomData,
		};
		let b_cyclepair = false;
		let cfg = stmt.gen_config(b_cyclepair);
		let v1 = stmt.to_vec();
		let stmt2 = StatementInst::<Fr,LookupTableTwoCol_Inst<Fr>>
			::from_vec(&cfg, &v1);
		let v2 = stmt2.to_vec();
		for i in 0..v1.len(){
			if v1[i]!=v2[i]{
				println!("DIFFERENCE at i: {}, v1[i]: {:?}, v2[i]: {:?}",
					i, v1[i], v2[i]);
			}
		}
		assert!(cfg.total_size() == v1.len(), "ERROR in cfg size");
		assert!(v1==v2, "ERROR in stmt serialize");
	}

	#[test]
	pub fn test_lookup(){
		//1. make a double check of self_check
		let lk1 = LookupTableTwoCol_Inst::new(vec![(Fr::from(0), Fr::from(100)), (Fr::from(1), Fr::from(2))]);
		let lk2 = LookupTableTwoCol_Inst::new(vec![(Fr::from(0), Fr::from(100)), (Fr::from(1), Fr::from(2)), (Fr::from(1), Fr::from(1))]);
		assert!(lk1.self_check().is_ok());
		assert!(!lk2.self_check().is_ok());

		//2. test find
		let lk2 = LookupTableTwoCol_Inst::new(vec![
			(Fr::from(0), Fr::from(1)), //0
			(Fr::from(0), Fr::from(5)), //1
			(Fr::from(0), Fr::from(7)), //2
			(Fr::from(1), Fr::from(100)), //3
			(Fr::from(1), Fr::from(200)), //4
			(Fr::from(1), Fr::from(300)), //5
			(Fr::from(1), Fr::from(400)), //6
		]);
		assert!(lk2.find(Fr::from(0), Fr::from(5))==Ok(1));
		assert!(lk2.find(Fr::from(1), Fr::from(100))==Ok(3));
		//should be inserted at 5
		assert!(lk2.find(Fr::from(1), Fr::from(250))==Err(5)); 

		//3. test update_hash
		let mut map = HashMap::<usize, usize>::new();
		lk2.fill_mvec(&vec![Fr::from(0), Fr::from(1)], 
				   &vec![Fr::from(1), Fr::from(100)], &mut map);
		lk2.fill_mvec(&vec![Fr::from(0), Fr::from(1)], 
				   &vec![Fr::from(1), Fr::from(200)], &mut map);
		lk2.fill_mvec(&vec![Fr::from(0), Fr::from(1)], 
				   &vec![Fr::from(1), Fr::from(100)], &mut map);
		lk2.fill_mvec(&vec![Fr::from(0), Fr::from(1)], 
				   &vec![Fr::from(1), Fr::from(400)], &mut map);
		let vec = LookupTableTwoCol_Inst::<Fr>::gen_m_share(0, 4, &map);
		let v2 = vec![4, 0, 0, 2].iter().map(|x| Fr::from(*x as u32))
			.collect::<Vec<Fr>>();
		assert!(vec==v2, "fill_mvec fails");
	}

	#[test]
	pub fn test_zi_inst(){
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let vb = vec![true, false];
		let fq_bits = Fq::MODULUS_BIT_SIZE as usize;
		let num_words = 2;
		for b in vb{
			let zi_inst= ZiPartTwoInst::new(Fr::from(3u32), Fr::from(2u32), &poseidon_config,b,fq_bits, num_words);
			let v1 = zi_inst.to_vec();
			let zi2 = ZiPartTwoInst::from_vec(&v1, fq_bits);
			let v2 = zi2.to_vec();
			assert!(v1==v2, "ERROR in stmt serialize");
		}
	}

	#[test]
	pub fn test_cyclepair_input(){
		//1. test fr to fq conversion
		//let mut rng = ark_std::test_rng();
		let mut rng = rand::rngs::OsRng;
		let fq1 = Fq::rand(&mut rng);
		let vec_fr1 = f1_to_f2_limbs::<Fq,Fr>(&fq1);
		let fq2 = f1_limbs_to_f2::<Fr,Fq>(&vec_fr1);
		assert!(fq1==fq2);

		//2. test cyclepair from and to
		let a = Projective::rand(&mut rng);
		let b = Projective2::rand(&mut rng);
		let c = Projective::rand(&mut rng);
		let d = Projective2::rand(&mut rng);
		let gt1 = Bn254::pairing(&c, &d).0;
		let gt2 = gt1 * Bn254::pairing(&a, &b).0; //note + is * here for Gt
		let vec_fq1 = vec![
			gt1.to_field_elements().unwrap(), a.to_field_elements().unwrap(), 
			b.to_field_elements().unwrap(),gt2.to_field_elements().unwrap()]
			.concat();
		let cp1 = CyclePairInput::from::<Bn254,Projective,Fq>(&gt1,&a,&b,&gt2);
		let fq_bits = Fq::MODULUS_BIT_SIZE as usize;
		let total_size = CyclePairInput::<Fr>::total_size(fq_bits);
		assert_eq!(total_size, cp1.x.len());

		//3. check pack_non_native
		let cs = ConstraintSystem::<Fr>::new_ref();
		let cpi = CyclePairInputVar::<Fr>::from(cs, &cp1);
		let vec_fq2 = cpi.x.iter().map(|x| {
			let vb = x.to_bits_le().unwrap();
			let bits:Vec<bool> = vb.value().unwrap();
			Fq::from_bigint(<Fq as PrimeField>::BigInt
				::from_bits_le(&bits)).unwrap()
		}).collect::<Vec<Fq>>();
		assert!(vec_fq1==vec_fq2);

		//4. test to_vec() and from_vec
		let vec_fr = cpi.to_vec();
		let fq_bits = Fq::MODULUS_BIT_SIZE as usize;
		let cpi2 = CyclePairInputVar::<Fr>::from_vec(&vec_fr, fq_bits);
		for i in 0..cpi.x.len(){
			assert!(cpi.x[i].value().unwrap() == cpi2.x[i].value().unwrap());
		}
	}

}
