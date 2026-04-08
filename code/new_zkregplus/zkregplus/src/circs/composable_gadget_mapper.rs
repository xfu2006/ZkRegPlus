use std::sync::Arc;
/* Created 02/12/2025

Composite gadget mapper: that can be consisting of
atomic mappers (mainly has a starting address) and allocate
their own spaces.
For this ZkReg: composite gadget mapper consists of the 
following:
  CPGadgetMapper: which is a component gadget mapper
  SEDGadgetMapper: component mapper
  DFAGadgetMapper (optional): component mapper
*/

use folding_schemes::folding::foldpot::container_config::{ColEle, ContainerConfig};
use utils::{logger::{log_perf, LOG1 }, timer::Timer};
use std::any::{Any};
use folding_schemes::{
	Error,
	folding::foldpot::{
		sigma_ir1cs::{LookupTableTwoCol,GadgetMapper,SigmaGadget,StatementConfig,StatementInst,StatementExtraInfo,NdAdvice,Capacity,WordInfo} 	}
};
use ark_ff::{PrimeField};
use std::{
	marker::PhantomData,
	
	fmt::{Debug},
};
use crate::gadgets::{
	commons::{gen_m_table},
	traits::{
		IDX_WORD, IDX_INP, IDX_OUP, IDX_DATA, 
		IDX_SI_INP, IDX_SI_OUP, IDX_SI_DATA,
		IDX_FAILED_SIGS, IDX_DISCHARGED_SIGS,
	},
};
use crate::circs::{
	sed_mapper::SedAdvice,
	dfa_mapper::DfaAdvice,
};

/// Compononent of a CompositeGadgetMapper.
/// In general, a component mapper should be regarded as a self-contained
/// mapper that manages a FIXED set of gadgets.
/// Given its region in input/data/output, its
/// statement is always [word; inp; output; data; subtable_id]
/// where the subtable_id size is the sum of inp/oup/data
/// If there are needs to correlate its data with others, it's
/// done through extra join constraints.
#[allow(non_camel_case_types)]
pub trait ComponentMapper<F:PrimeField + ColEle, LK: LookupTableTwoCol<F>>: Debug + Send + Sync{
	/// get its own name
	fn get_name(&self)->String;

	/// return an Rc dyn object of capacity
	fn get_capacity(&self)->Arc<dyn Capacity + Send + Sync>;

	/// create a vector of gadgets
	fn create_gadgets(&self) -> Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>>;  

	/// return the number of gadgets
	fn num_gadgets(&self) -> usize;

	/// return the max len of the word that can be processed.
	fn max_word_len(&self) -> usize;

	/// return the sizes of input/output/data/failed_sigs/discharged_sigs
	/// expecting 5 elements.
	fn get_sizes(&self)->Vec<usize>;

	/// Given its own gadget stmt_map: 8 range entries for
	///   [inp,oup,data, subtbl_inp, subtbl_oup, subtbl_data,
	///        failed_sigs, discharged_sigs]
	/// return the 8 range entry for each of its compoments.
	/// In addition, it returns 3 Vec<(usize, bool)> about the
	/// chunk info of si_data (bool indicates if it is constant or not)
	/// and similarly si_inp and si_oup. Where each element indicates
	/// a chunk of (column_size, if_const)
	fn get_gadgets_stmt_map(&self, vec_alloc: &Vec<(usize,usize)>)
	->(Vec<Vec<(usize,usize)>>, Vec<(usize,bool)>, Vec<(usize, bool)>,
		Vec<(usize,bool)>);

	/// return the ``global" join constraints, so that
	/// it can generate constraints to bind its own statement elements
	/// with others. the comp_cfgs has the following structure,
	/// (inp_start_idx, oup_start_idx, data_start_idx) for each component
	/// in the upper level statement.
	/// The join statement are ``global" in the sense that
	/// they refer to the global position.
	/// i - informs the component that it is the i'th component
	/// stmg_cfg provides statement structure info.
	/// cmp_cfgs: each tuple is (idx_inp, idx_oup, idx_data) for each component.
	fn get_joins(&self, i: usize, stmt_cfg: &StatementConfig, comp_cfgs: &Vec<Vec<usize>>)->Vec<( (usize,usize), (usize,usize) )>;

	/// Also responsible for generating nd_advice with its own capacity.
	/// seg_id is for debugging purpose only.
	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, seg_id: usize, job_id: usize)
		->Result<Arc<dyn NdAdvice + Send + Sync>, Error>;


	/// return the inp, oup, data and 3 subtable segments,
	/// and then failed_sigs, discharged_sigs. (8 vecs)
	/// the id, cfg, and comp_mapping helps it to locate the information
	/// it needs in prev_stmt which has the same structure as specified
	/// in StatementConfig. Note we pass the max len word, padded.
	/// the actual_word_len indicates the actual word seg in the word_seg.
	///
	/// NOTE: comp_id refers to the component, stmt_map_id refers
	/// to the starting index of FIRST of its gadget in the stma_mapping.
	/// e.g., let's say there are two components with 2 and 3 gadgets,
	/// the the comp_id for the 2nd is 1, and its stmt_map_id is 2. (idx
	/// starting from 0). For conveneince, we sometimes use
	/// the prev_stmt or the vector of its prev_stmt.
	///
	/// NOTE: we dropped stmt and stmt_vec from the parameters, so at this
	/// moment stmt_map_id and comp_id are actually not useful anymore 
	/// (deprecated). 
	fn build_statement_comp(&self, comp_id: usize, stmt_map_id: usize, word_seg: &Vec<F>, actual_word_len: usize, lkup: &Arc<LK>, extra_info: &StatementExtraInfo<F>, _advice: &Arc<dyn NdAdvice + Send + Sync>, cfg: &StatementConfig, comp_mapping: &Vec<Vec<(usize,usize)>>) -> Result<Vec<Vec<F>>, Error>;

	/// This is not required for those non-SED gadgets, they are handled
	/// by legacy gode.
	fn set_container_config(&mut self, _advice: &Arc<dyn NdAdvice + Send + Sync>); 


}


/// Composite list of advices (the internal ND_ADVICE for CompositeGadgetMapper)
#[derive(Debug)]
pub struct CompositeAdvice{
	pub vec_adv: Vec<Arc<dyn NdAdvice + Send + Sync>>,
}

impl NdAdvice for CompositeAdvice{
	fn as_any(&self) -> &dyn Any{ self }
}

/// A vector of dynamic capcity objects.
#[derive(Debug)]
pub struct CompositeCapacity{
	pub vec_cap: Vec<Arc<dyn Capacity + Send + Sync>>,
}

impl Capacity for CompositeCapacity{
	/// requires the r_other also be a CompositeCapacity
	/// of the same size.
	fn can_satisfy(&self, r_other: &Arc<dyn Capacity + Send + Sync>)->bool{
		let other = r_other.as_any().downcast_ref::<CompositeCapacity>()
			.expect("downcast err!");
		assert!(self.vec_cap.len()==other.vec_cap.len());
		self.vec_cap.iter().zip(other.vec_cap.iter()).map(|(x,y)|
			x.can_satisfy(&y)
		).fold(true, |acc, res| acc && res)
	}

	fn clone(&self) -> Arc<dyn Capacity + Send + Sync>{
		let vec_cap = self.vec_cap.iter().map(|x|
			x.clone()).collect::<Vec<Arc<dyn Capacity + Send + Sync>>>();
        Arc::new(CompositeCapacity{vec_cap})
    }

	fn as_any(&self)->&dyn Any{ self }
}

/// A composable gadget mapper means that it can have a flexible
/// combination of atomic gadget mappers. (e.g., allowing
/// free compbination of CP, SED, DFA discharging gadgets)
#[derive(Clone,Debug)]
pub struct CompositeGadgetMapper<F:PrimeField + ColEle, LK:LookupTableTwoCol<F>>{
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub vec_components: Vec<std::sync::Arc<std::sync::Mutex<dyn ComponentMapper<F,LK> + Send + Sync + Send + Sync>>>,
	pub name: String,
}

impl <F:PrimeField + ColEle,LK:LookupTableTwoCol<F>> CompositeGadgetMapper<F,LK>{
	pub fn new(name: &str, vec_components: Vec<std::sync::Arc<std::sync::Mutex<dyn ComponentMapper<F,LK> + Send + Sync + Send + Sync>>>)->Self{
		Self{
			_f: PhantomData,
			_lk: PhantomData,
			vec_components,
			name: format!("{}", name)
		}
	}
	pub fn set_name(&mut self, name: &str){ self.name = format!("{}", name); }

	/// Given a subtbl_idx, find out its corresponding vec_component
	/// ID and the column path (of the data, not SI column)
	/// NOTE: slow, for debugging only
	pub fn find_idx(
		&self, 
		subtbl_idx: usize,  //this is also the offset in
			//StmtInst::inp || oup || data if b_report_data is true
			//NOTE that it is NOT the global offset in StatementInst.to_vec()
			//NOTE this index does NOT account for the word_subseg elements.
		lkup_share_size: usize, 
		b_report_data: bool, //true for report col in inp/oup/data
			//false for report si_inp/si_oup/si_data
	) -> Option<(usize, String)> {
		// 1. Recreate the statement structure to get segment sizes
		let (_, cfg, _, _, _) = self.gen_statement_structure(lkup_share_size);

		// 2. Estimate the segemnet (one of inp/oup/data/si_inp/si_oup/si_data)
		// and convert subtbl_idx to offset in StmtInst::to_vec()
		let seg_id = if subtbl_idx<cfg.input_size{
			IDX_INP
		} else if subtbl_idx< cfg.input_size + cfg.output_size{
			IDX_OUP
		} else if subtbl_idx < cfg.input_size + cfg.output_size + cfg.data_size{
			IDX_DATA
		} else{
			panic!("cannot handle subtbl_idx: {}", subtbl_idx)
		};
		let seg_id = if b_report_data {seg_id} else {seg_id + 3};
		let offset_in_stmt = if b_report_data { subtbl_idx +cfg.idx_inp }
		else { subtbl_idx + cfg.idx_subtable_id };
		let offset_in_stmt = if b_report_data && 
			subtbl_idx>=cfg.input_size + cfg.output_size{
			offset_in_stmt + cfg.word_subseg_size //need to accomodate
				// the to wordsubseg which is included in between the
				// oup and data section in StatementInstance.
		}else{ offset_in_stmt };

		// 3. Find which component owns this offset. 
		//note: seg_id starts from 1 (INP)
		// and SI_INP (4)
		let size_idx = if b_report_data{seg_id-1} else
			{seg_id- 4}; // Map 4->0, 5->1, 6->2
		let mut current_comp_base = if b_report_data {
			match seg_id{
				IDX_INP=> cfg.idx_inp,
				IDX_OUP=> cfg.idx_oup,
				IDX_DATA=> cfg.idx_data,
				_ => panic!("cannot handle seg_id: {}", seg_id)
			}
		} else {
			match seg_id{
				IDX_SI_INP=> cfg.idx_subtable_id,
				IDX_SI_OUP=> cfg.idx_subtable_id + cfg.input_size,
				IDX_SI_DATA=> cfg.idx_subtable_id + cfg.input_size
					+ cfg.output_size,
				_ => panic!("cannot handle seg_id: {}", seg_id)
			}
		}; //when the seg is fixed
			//it stands for the base for the corresponding inp/si
			//for the component (two cases one for inp/oup/data
			// and the 2nd case is for si_inp/si_oup/si_data
			// this variable is only used for CP components only.
			// the others just directly use the offset_in_stmt to search.

		for (i, comp_rc) in self.vec_components.iter().enumerate() {
			let comp = comp_rc.lock().unwrap();
			let comp_sizes = comp.get_sizes();
			let comp_seg_size = comp_sizes[size_idx];
			if offset_in_stmt >= current_comp_base && 
			   offset_in_stmt < current_comp_base + comp_seg_size {
				
				if comp_rc.lock().unwrap().get_name().contains("Cp"){
					let name = match seg_id {
						IDX_INP => "cp_inp",
						IDX_OUP => "cp_oup",
						IDX_DATA => "cp_data",
						IDX_SI_INP => "cp_si_inp",
						IDX_SI_OUP => "cp_si_oup",
						IDX_SI_DATA => "cp_si_data",
						_ => "unknown",
					};
					return Some((i, name.to_string()));
				}

				for gadget_rc in comp.create_gadgets() {
					let g_cfg = gadget_rc.lock().unwrap().get_container_config();
					if let Some(path) = self.search_by_dest(
						&g_cfg, seg_id, offset_in_stmt - current_comp_base
					) {
						return Some((i, path));
					}
				}
			}
			current_comp_base += comp_seg_size;
		}
		None
	}

	/// Enumerate all column paths in all components and their gadgets.
	/// This is for debugging purposes to trace the global statement order.
	/// Returns a list of (component_idx, column_path).
	/// NOTE: slow for debugging only
	pub fn enumerate_col_paths(&self) -> Vec<(usize, String)> {
		let mut res = Vec::new();
		for (i, comp_rc) in self.vec_components.iter().enumerate() {
			let comp = comp_rc.lock().unwrap();

			// Special handling for component 0 (cp_mapper)
			if comp.get_name().contains("Cp") {
				res.push((i, "cp_inp".to_string()));
				res.push((i, "cp_si_inp".to_string()));
				res.push((i, "cp_oup".to_string()));
				res.push((i, "cp_si_oup".to_string()));
				res.push((i, "cp_data".to_string()));
				res.push((i, "cp_si_data".to_string()));
			}else{
				for gadget_rc in comp.create_gadgets() {
					let g_cfg = gadget_rc.lock().unwrap().get_container_config();
					self.collect_paths_recursive(&g_cfg, i, &mut res);
				}
			}
		}
		res
	}

	/// Retrieve the destination location and size of a column.
	/// Return (segment_id, global_offset, length).
	/// - segment_id: e.g., IDX_INP, IDX_SI_DATA.
	/// - global_offset: Absolute index in the StatementInst vector. 
	///   It correctly accounts for the accumulated sizes of all 
	///   prior segments (e.g., word segment size).
	pub fn get_col_info(&self, component_id: usize, path: &str,
		lkup_share_size: usize) -> Option<(usize, usize, usize)> {
		if component_id >= self.vec_components.len() { return None; }

		// 1. Recreate structure to get segment sizes and bases
		let (_, cfg, _, _, _) = self.gen_statement_structure(lkup_share_size);

		// 2. Calculate the accumulated offset for this component
		let mut my_offset = vec![0, 0, 0, 0, 0]; // [inp, oup, data, failed, discharged]
		for i in 0..component_id {
			let sizes = self.vec_components[i].lock().unwrap().get_sizes();
			for j in 0..5 { my_offset[j] += sizes[j]; }
		}

		let comp = self.vec_components[component_id].lock().unwrap();

		// Case 1: cp_mapper (component 0)
		if comp.get_name().contains("Cp") {
			let (seg_id, size_idx) = match path {
				"cp_inp" => (IDX_INP, 0),
				"cp_si_inp" => (IDX_SI_INP, 0),
				"cp_oup" => (IDX_OUP, 1),
				"cp_si_oup" => (IDX_SI_OUP, 1),
				"cp_data" => (IDX_DATA, 2),
				"cp_si_data" => (IDX_SI_DATA, 2),
				_ => return None,
			};
			let len = self.vec_components[component_id]
				.lock().unwrap().get_sizes()[size_idx];

			let start = match seg_id {
				IDX_INP => cfg.idx_inp + my_offset[0],
				IDX_OUP => cfg.idx_oup + my_offset[1],
				IDX_DATA => cfg.idx_data + my_offset[2],
				IDX_SI_INP => cfg.idx_subtable_id + my_offset[0],
				IDX_SI_OUP => cfg.idx_subtable_id + cfg.input_size 
					+ my_offset[1],
				IDX_SI_DATA => cfg.idx_subtable_id + cfg.input_size + 
					cfg.output_size + my_offset[2],
				IDX_WORD  => cfg.idx_word_subseg,
				_ => panic!("can't handle seg_id: {}", seg_id),
			};
			return Some((seg_id, start, len));
		}

		// Case 2: Other mappers
		for gadget_rc in comp.create_gadgets() {
			let g_cfg = gadget_rc.lock().unwrap().get_container_config();
			if let Some((seg_id, r_start, len)) = self.find_info_recursive(
				&g_cfg, path
			) {
				let start = match seg_id {
					IDX_INP => cfg.idx_inp + my_offset[0] + r_start,
					IDX_OUP => cfg.idx_oup + my_offset[1] + r_start,
					IDX_DATA => cfg.idx_data + my_offset[2] + r_start,
					IDX_SI_INP => cfg.idx_subtable_id + my_offset[0] + r_start,
					IDX_SI_OUP => cfg.idx_subtable_id + cfg.input_size + my_offset[1] + r_start,
					IDX_SI_DATA => cfg.idx_subtable_id + cfg.input_size + 
						cfg.output_size + my_offset[2] + r_start,
					IDX_FAILED_SIGS => cfg.idx_failed_sigs + my_offset[3] + r_start,
						//will be skipped in self check
					IDX_DISCHARGED_SIGS => cfg.idx_discharged_sigs + my_offset[4] + r_start,
						//will be skipped in self check
					IDX_WORD => cfg.idx_word_subseg + r_start, //will be skipped
						//in self_check()
					_ => panic!("can't handle seg_id: {}", seg_id),
				};
				return Some((seg_id, start, len));
			}
		}
		None
	}

	/// Recursive helper for get_col_info to search ContainerConfig for a path.
	fn find_info_recursive(&self, cfg: &ContainerConfig, target_path: &str) 
	-> Option<(usize, usize, usize)> {
		match cfg {
			ContainerConfig::Column(loc, _name, path, _b_const) => {
				if path == target_path { 
					if let Some(dest) = loc.dest {
						return Some(dest);
					} else {
						// It's a foreign column. Return info from src.
						// src is (i32, usize, usize, usize, String, bool)
						// (rel_idx, seg_id, start, len, qry_str, resolved)
						return Some((loc.src.1, loc.src.2, loc.src.3));
					}
				}
				None
			}
			ContainerConfig::Complex(children, _name, _path) => {
				for child in children {
					if let Some(res) = self.find_info_recursive(child, 
						target_path) { return Some(res); }
				}
				None
			}
		}
	}

	/// Recursive helper for enumerate_paths to traverse the 
	/// ContainerConfig tree and collect column paths.
	fn collect_paths_recursive(&self, cfg: &ContainerConfig, 
		comp_idx: usize, res: &mut Vec<(usize, String)>) {
		match cfg {
			ContainerConfig::Column(_loc, _name, path, _b_const) => {
				res.push((comp_idx, path.clone()));
			}
			ContainerConfig::Complex(children, _name, _path) => {
				for child in children {
					self.collect_paths_recursive(child, comp_idx, res);
				}
			}
		}
	}

	/// Helper function to find a Column path by matching the 'dest' field
	/// NOTE: slow. for debugging only.
	fn search_by_dest(&self, cfg: &ContainerConfig, target_seg: usize, 
		target_off: usize) -> Option<String> {
		match cfg {
			ContainerConfig::Column(loc, _name, path, _b_const) => {
				// Use the pre-calculated 'dest' from adjust_locations
				if let Some((d_seg, d_start, d_len)) = loc.dest {
					if d_seg == target_seg && target_off >= d_start && 
						target_off < d_start + d_len {
						return Some(path.clone());
					}
				}
				None
			}
			ContainerConfig::Complex(children, _name, _path) => {
				for child in children {
					if let Some(path) = self.search_by_dest(
						child, target_seg, target_off
					) {
						return Some(path);
					}
				}
				None
			}
		}
	}

	/// Retrieve the value of a column at a specific row from the advice.
	/// - word: The word input.
	/// - lkup: The lookup table.
	/// - ea: The statement extra info.
	/// - advice: The global CompositeAdvice object.
	/// - lkup_share_size: Required for statement reconstruction.
	/// - comp_idx: The index of the component (0 for cp_mapper).
	/// - path: The column path (as returned by enumerate_col_paths).
	/// - row: The row index within the column. (which element to retrieve
	pub fn get_value(&self, 
		word: &Vec<F>, 
		lkup: Arc<LK>, 
		ea: &StatementExtraInfo<F>, 
		advice: &Arc<dyn NdAdvice + Send + Sync>, 
		lkup_share_size: usize,
		comp_idx: usize, 
		path: &str, 
		row: usize) -> F {
		let advices = advice.as_any().downcast_ref::<CompositeAdvice>()
			.expect("downcast CompositeAdvice err!");
		let inner_adv = &advices.vec_adv[comp_idx];
		let comp = self.vec_components[comp_idx].lock().unwrap();

		if comp.get_name().contains("Cp"){
			// Case 1: cp_mapper (Component 0 or maybe 1)
			let (_, cfg, stmt_map, _, _) = 
				self.gen_statement_structure(lkup_share_size);
			let mut rem_word = vec![F::zero(); 
				self.max_word_len() - word.len()];
			let mut word_seg = word.clone();
			word_seg.append(&mut rem_word);
			let actual_word_len = word.len();

			let vecs = comp.build_statement_comp(
				0, 0, &word_seg, actual_word_len, &lkup,
				ea, inner_adv, &cfg, &stmt_map
			).expect("build_statement_comp err for CP");

			// 2. Map path to segment index (0-7)
			let seg_idx = match path {
				"cp_inp" => 0, "cp_oup" => 1, "cp_data" => 2,
				"cp_si_inp" => 3, "cp_si_oup" => 4, "cp_si_data" => 5,
				"cp_failed_sigs" => 6, "cp_discharged_sigs" => 7,
				_ => panic!("unknown cp path: {}", path),
			};
			let res = vecs[seg_idx][row].clone();

			res
		} else {
			// Case 2: SED/DFA mappers (Component > 0)
			// Both SedAdvice and DfaAdvice provide vec_advices

			let vec_comp_adv = if let Some(sed_adv) = inner_adv.as_any()
				.downcast_ref::<SedAdvice<F>>() {
				&sed_adv.vec_advices
			} else if let Some(dfa_adv) = inner_adv.as_any()
				.downcast_ref::<DfaAdvice<F>>() {
				&dfa_adv.vec_advices
			} else {
				panic!("unknown component advice type")
			};
			let gadgets = comp.create_gadgets();
			for (i, gadget_rc) in gadgets.iter().enumerate() {
				let g_cfg = gadget_rc.lock().unwrap().get_container_config();
				if self.find_info_recursive(&g_cfg, path).is_some() {
					let container = vec_comp_adv[i].get_container();
					let g_name = container.lock().unwrap().get_name();
					let words: Vec<&str> = path.split_whitespace().collect();
					let pos = words.iter().position(|&w| w == g_name)
						.expect("gadget name not found in path");
					let rel_path = words[pos..].join(" ");

					let col_cont = container.lock().unwrap()
						.search_container(&rel_path)
						.expect("search_container err");
					let res = col_cont.lock().unwrap().to_vec();
					assert!(res.len() > row);
					return res[row].clone();
				}
			}
			panic!("path {} not found in component {}", path, comp_idx);
		}
	}

	/// Used for debugging. Slow. 
	/// most of parameters are the same as build_statement(), because
	/// this function is used in build_statement() to debug.
	pub fn self_check(&self, 
		word: &Vec<F>, 
		_prev_stmt: &Option<StatementInst<F,LK>>, 
		lkup: Arc<LK>, 
		ea: &StatementExtraInfo<F>, 
		r_advice: Arc<dyn NdAdvice + Send + Sync>, 
		lkup_share_size: usize, 
		_b_dummy: bool, 
		num_extra_sample_points: usize, //extra index to sample for testing
		inp_oup_wd_data: &Vec<F>, //the concat of inp/oup/wd_seg/data
		subtbl_id: &Vec<F>, //the subtbl_id of StatementInstance.
	) {
		let mut timer = Timer::new();
		//1. enumerate all col paths of Vec<(comp_id, col_path)
		let (_, cfg, _ , _, _) = 
			self.gen_statement_structure(lkup_share_size);
		let paths = self.enumerate_col_paths();

		//2. for each <comp_id, col_path>
		for (comp_idx, path) in paths {
			//2.1 get its information such as start and length
			let info = self.get_col_info(
				comp_idx, &path, lkup_share_size
			);
			if info.is_none() {
				panic!("Cannot find col info for comp: {}, col: {}", 
					comp_idx, path);
			}
			let (seg_id, global_off, len) = info.unwrap();
			if seg_id == 0 || seg_id>6{
				println!("DEBUG USE 7102.5: SKIP word seg: seg_id: {}, global_off: {}, len: {}", seg_id, global_off, len);
				continue;
			}

			//2.2. construct list of sample points
			let mut sample_points = vec![0];
			assert!(len>=1);
			sample_points.push(len - 1);
			for i in 1..num_extra_sample_points + 1 {
				let new_pt = i*(len-1)/(num_extra_sample_points+1);
				assert!(new_pt + 1 <= len);
				sample_points.push(new_pt);
			}
			sample_points.sort();
			sample_points.dedup();

			//2.3 for each sample index in the list constructed above:
			for rel_idx in sample_points {
				//2.3.2 its index is start_idx + itself
				let abs_idx = global_off + rel_idx;

				//2.3.2 call find_idx(index) twice
				let b_data_col = !path.contains("si_") && 
					!path.contains("sid_");
				let offset= if b_data_col {
					//NOTE that abs_pos in word, has an additional component
					// of word_seg, but inp_oup_data does not have word
					// it should be adjusted.
					if abs_idx>=cfg.idx_data{
						abs_idx - cfg.idx_inp - cfg.word_subseg_size
					}else{//if it's in inp/oup it's fine
						abs_idx - cfg.idx_inp
					}
				} else {abs_idx-cfg.idx_subtable_id};
				let info_data = self.find_idx(offset, lkup_share_size, true);
				let info_si = self.find_idx(offset, lkup_share_size, false);
				
				let (cid1, path_data) = info_data
					.expect(&format!(
						"info_data none for comp: {}, col_path: {} ", 
						comp_idx, path));
				let (cid2, path_si) = info_si
					.expect(&format!(
						"info_sid none for comp: {}, col_path: {} ", 
						comp_idx, path));
				assert!(cid1 == comp_idx && cid2 == comp_idx,
					"cid mismatch: {} vs cid1: {} vs cid2: {}, path: {}", 
					comp_idx, cid1, cid2, path);

				let org_name = path.split_whitespace().last().unwrap()
					.split("_").last().unwrap();
                let datacol_name = path_data.split_whitespace().last()
					.unwrap().split("_").last().unwrap();
                let sicol_name = path_si.split_whitespace().last()
					.unwrap().split("_").last().unwrap();
                assert!(sicol_name.contains(&datacol_name) && 
					sicol_name.contains(&org_name), "ERROR: for path: {} we LOCATE that the data and sid columns MISMATCH! org_name: {}, datacol_name: {}, sicol_name: {}", path, org_name, datacol_name, sicol_name);

				//2.3.3 now retrieve the (si_idx, value) by calling
				//get_value() using the sample index and the col path
				let val = self.get_value(
					word, lkup.clone(), ea, &r_advice, lkup_share_size,
					comp_idx, &path_data, rel_idx
				);
				let sid = self.get_value(
					word, lkup.clone(), ea, &r_advice, lkup_share_size,
					comp_idx, &path_si, rel_idx
				);

				//2.3.4 retrieve the comparion pair (si_idx2, value2)
				//from inp_oup_data, subtbl_id
				let sid2 = subtbl_id[offset];
				let val2 = inp_oup_wd_data[offset];
				assert!(sid2==sid && val2==val, 
					"ERROR in self check: comp_id: {}, path: {}, \
					rel_idx: {}, (sid: {}, val: {}), \
					(sid2: {}, val2: {}), seg_id: {}", 
					comp_idx, path, rel_idx, sid, val, sid2, val2, seg_id);
				println!("DEBUG USE 6801: self-checked comp_idx: {}, path: {}", 
					comp_idx, path);
			}
		}
		log_perf(0, LOG1, "DEBUG USE 9999: CompositeGadgetMapper: self_check", &mut timer);
	}

}

impl <F:PrimeField+ColEle,LK:LookupTableTwoCol<F>> GadgetMapper<F,LK> for CompositeGadgetMapper<F,LK>{
	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, r_advice: &Arc<dyn NdAdvice + Send + Sync>){ 
		let advices = r_advice.as_any().downcast_ref::<CompositeAdvice>()
			.expect("downcast err!");
		assert!(advices.vec_adv.len()==self.vec_components.len());
		for i in 0..self.vec_components.len(){
			let adv = &advices.vec_adv[i];
			self.vec_components[i].lock().unwrap().set_container_config(adv);
		}
	}

	/// return the capacity of this circuit
	fn get_capacity(&self) -> Arc<dyn Capacity + Send + Sync>{
		let vec_cap = self.vec_components.iter().map(|x|
			x.lock().unwrap().get_capacity()).collect::<Vec<Arc<dyn Capacity + Send + Sync>>>();
		Arc::new(CompositeCapacity{vec_cap})
	}

	/// return the name
	fn get_name(&self) -> String{ self.name.clone() }

	/// Create the components. The config is contained
	/// in the relation mapper object, and should be passed
	/// by the corresonding constructor.
	fn get_gadgets(&self) -> Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>>{  
		self.vec_components.iter().map(|x|
			x.lock().unwrap().create_gadgets()
		).flatten().collect::<Vec<std::sync::Arc<std::sync::Mutex<dyn SigmaGadget<F> + Send + Sync>>>>()
	}

	/// Build the statement structure form all components.
	/// We assume that components are "independent", if there are 
	/// relations, specify them using join constraints
	///
	/// As this is for main circuit, we do not have cycle_pair_input.
	fn gen_statement_structure(&self, lkup_share_size: usize) 
		-> (usize, StatementConfig, 
		Vec<Vec<(usize,usize)>>,  //component stmt map
		Vec<((usize,usize), (usize,usize))>,  //optional extra join constraints
		Vec<usize> //optional map of CyclePairInput
	){
		//1. collect and prep the starting positions
		//vec_size is 5 elements for size of
		//[inp, oup, data, failed_sigs, discharged_sigs]
		let vec_sizes = self.vec_components.iter().map(|c|
			c.lock().unwrap().get_sizes()).collect::<Vec<Vec<usize>>>();
		let mut vec_starts:Vec<Vec<usize>> = vec![vec![0,0,0,0,0]];
		for i in 0..vec_sizes.len(){
			let cur_size = &vec_sizes[i];
			assert!(cur_size[0]==cur_size[1], 
				"inp!=oup size for component: {}", i);
			assert!(cur_size.len()==5, "expecting 5 elements");
			let cur_start = &vec_starts[vec_starts.len()-1];
			let new_start = cur_size.iter().zip(cur_start.iter()).map(|(x,y)|
				x+y).collect::<Vec<usize>>();
			assert!(new_start.len()==cur_size.len());
			vec_starts.push(new_start);
		}
		let mut sum_sizes = vec![0,0,0,0,0];
		for vs in &vec_sizes{ for j in 0..vs.len(){sum_sizes[j] += vs[j] } }
		//2. generate the config of statement. Note we assume
		// all components process the same max word len
		let (input_size, output_size, data_size, failed_sigs_size,
			discharged_sigs_size) = (sum_sizes[0], sum_sizes[1], 
				sum_sizes[2], sum_sizes[3], sum_sizes[4]);
		assert!(input_size == output_size);
		let word_subseg_size = self.max_word_len(); 
		let b_cyclepair = false;
		let mut cfg = StatementConfig::new(
			input_size, output_size, word_subseg_size,
			data_size, lkup_share_size, failed_sigs_size, discharged_sigs_size,
			b_cyclepair
		); //will have si_data_info reset later

		//3. generate the map for each component. Each component's statement
		// is structured as
		// [word, inp, output, data, subtable_id,failed_sigs,discharged_sigs] 
		// which are mapped 
		// correspondingly, note that subtble_id itself has 3 chunks
		// for inp/oup/data
		let mut vec_maps = vec![];
		let idx_inp_in_subtbl_id = cfg.idx_subtable_id + 0;
		let idx_oup_in_subtbl_id = cfg.idx_subtable_id + cfg.input_size;
		let idx_data_in_subtbl_id = cfg.idx_subtable_id + cfg.input_size + cfg.output_size;
		let mut si_data_info = vec![];
		let mut si_inp_info = vec![];
		let mut si_oup_info = vec![];
		for i in 0..self.vec_components.len(){
			//NOTE: ranges are including both ends
			// e.g., (1,1) has one element, (2, 3) has 2 elements
			// for empty sections, it looks like (2, 1)
			let rg_word = (cfg.idx_word_subseg, 
				cfg.idx_word_subseg+word_subseg_size-1);
			let rg_inp = (cfg.idx_inp + vec_starts[i][0],
				cfg.idx_inp + vec_starts[i][0] + vec_sizes[i][0]-1);
			let rg_oup = (cfg.idx_oup + vec_starts[i][1],
				cfg.idx_oup + vec_starts[i][1] + vec_sizes[i][1]-1);
			let rg_data = (cfg.idx_data + vec_starts[i][2],
				cfg.idx_data + vec_starts[i][2] + vec_sizes[i][2]-1);
			let rg_failed_sigs= (cfg.idx_failed_sigs+ vec_starts[i][3],
				cfg.idx_failed_sigs + vec_starts[i][3] + vec_sizes[i][3]-1);
			let rg_discharged_sigs= (cfg.idx_discharged_sigs+ vec_starts[i][4],
				cfg.idx_discharged_sigs+ vec_starts[i][4] + vec_sizes[i][4]-1);

			let rg_subtbl_id_inp = (idx_inp_in_subtbl_id +  vec_starts[i][0],
				idx_inp_in_subtbl_id + vec_starts[i][0] + vec_sizes[i][0]-1);
			let rg_subtbl_id_oup = (idx_oup_in_subtbl_id +  vec_starts[i][1],
				idx_oup_in_subtbl_id + vec_starts[i][1] + vec_sizes[i][1]-1);
			let rg_subtbl_id_data = (idx_data_in_subtbl_id +  vec_starts[i][2],
				idx_data_in_subtbl_id + vec_starts[i][2] + vec_sizes[i][2]-1);

			let cur_alloc= vec![
				rg_word, rg_inp, rg_oup, rg_data,
				rg_subtbl_id_inp, rg_subtbl_id_oup, rg_subtbl_id_data,
				rg_failed_sigs, rg_discharged_sigs,
			];
			let (mut comp_maps, mut new_si_data_info, mut new_si_inp_info,
				mut new_si_oup_info) = self.vec_components[i].lock().unwrap()
				.get_gadgets_stmt_map(&cur_alloc);
			assert!(comp_maps.len()==self.vec_components[i].lock().unwrap().num_gadgets());
			vec_maps.append(&mut comp_maps);
			si_data_info.append(&mut new_si_data_info);
			si_inp_info.append(&mut new_si_inp_info);
			si_oup_info.append(&mut new_si_oup_info);
		}
		let num_gadgets = self.vec_components.iter().map(|x| 
			x.lock().unwrap().num_gadgets())
			.sum::<usize>();
		assert!(vec_maps.len()==num_gadgets);
		cfg.reset_si_info(si_data_info, si_inp_info, si_oup_info);
		

		//4. collect the joins
		let opt_joins = self.vec_components.iter().enumerate().map(|(i,c)|
			c.lock().unwrap().get_joins(i, &cfg, &vec_starts)
		).flatten().collect::<Vec<((usize,usize),(usize,usize))>>();
		let cyclepair_map = vec![]; 


		(cfg.total_size(), cfg, vec_maps, opt_joins, cyclepair_map)
	}


	/// given word input, previous witness, try to construct
	/// the full problem statement (including non-deterministic witness). 
	/// NOTE that the real i/o has only two elements in z_i array.
	fn build_statement(&self, word: &Vec<F>, _prev_stmt: &Option<StatementInst<F,LK>>, lkup: Arc<LK>, ea: &StatementExtraInfo<F>, r_advice: Arc<dyn NdAdvice + Send + Sync>, lkup_share_size: usize, b_dummy: bool, _job_id: usize) -> Result<StatementInst<F,LK>, Error>{
		//1. expand word_seg to max capacity.
		let b_debug = false;
		let mut rem_word = vec![F::zero(); self.max_word_len() - word.len()];
		let mut word_seg = word.clone();
		word_seg.append(&mut rem_word); //always guarnatee max len
		let actual_word_len = word.len();

		//2. collect inp/oup/data/subtbl_id/failed_sig/discharged_sig
		// from components
		let mut vec_inp = vec![];
		let mut vec_oup = vec![];
		let mut vec_data = vec![];
		let mut vec_failed_sigs = vec![]; //no sid
		let mut vec_discharged_sigs = vec![]; //no sid

		let mut vec_st_inp = vec![]; //subtable_id inp part
		let mut vec_st_oup = vec![]; //subtable_id oup part
		let mut vec_st_data = vec![];

		let advices = r_advice.as_any().downcast_ref::<CompositeAdvice>()
			.expect("downcast err!");
		let (_, cfg, stmt_map, _, _) = 
			self.gen_statement_structure(lkup_share_size);
		let mut stmt_map_id = 0;
		for i in 0..self.vec_components.len(){
			let comp = &self.vec_components[i];
			let vecs = comp.lock().unwrap()
				.build_statement_comp(i, stmt_map_id, 
					&word_seg, actual_word_len, &lkup,
					ea, &advices.vec_adv[i], &cfg, &stmt_map
				)?;
			//REMOVE LATER -----------
			if i==0{
				println!("DEBUG USE 7500: data[0]: {}, data[1]: {}, si_data[0]: {}, si_data[1]: {}", vecs[2][0], vecs[2][1], vecs[5][0], vecs[5][1]);
			}
			//REMOVE LATER ----------- LATER
			#[cfg(test)]{
				let sizes = comp.lock().unwrap().get_sizes();
				for i in 0..3{
					assert!(sizes[i]==vecs[i].len());
					assert!(sizes[i]==vecs[i+3].len());
				}
			}
			vec_inp.push(vecs[0].clone());
			vec_oup.push(vecs[1].clone());
			vec_data.push(vecs[2].clone());

			vec_st_inp.push(vecs[3].clone());
			vec_st_oup.push(vecs[4].clone());
			vec_st_data.push(vecs[5].clone());
			vec_failed_sigs.push(vecs[6].clone()); //no sid
			vec_discharged_sigs.push(vecs[7].clone()); //no sid
			stmt_map_id += comp.lock().unwrap().num_gadgets();
		}
		assert!(stmt_map_id == stmt_map.len());
		let inp = vec_inp.concat();
		let oup = vec_oup.concat();
		assert!(inp.len()==oup.len());
		let data = vec_data.concat();
		println!("DEBUG USE 7500: inp.len: {}, oup.len: {}, data.len: {}", inp.len(), oup.len(), data.len());
		let failed_sigs = vec_failed_sigs.concat();
		let failed_sigs = if b_dummy {vec![F::zero(); failed_sigs.len()]}
			else {failed_sigs};
		let discharged_sigs = vec_discharged_sigs.concat();

		//subtbl_word is not needed any more because
		//it doesnot need to be checked anyway.
		//let subtbl_word = vec![F::zero(); self.max_word_len()];
		let subtbl_inp = vec_st_inp.concat();
		let subtbl_oup = vec_st_oup.concat();
		let subtbl_data = vec_st_data.concat();
		let subtbl_id = vec![subtbl_inp, subtbl_oup, subtbl_data]
			.concat();
		#[cfg(test)]{
			assert!(inp.len()==cfg.input_size);
			assert!(oup.len()==cfg.output_size);
			assert!(word_seg.len()==cfg.word_subseg_size);
			assert!(data.len()==cfg.data_size);
			assert!(lkup_share_size==cfg.lookup_share_size);
			assert!(failed_sigs.len()==cfg.failed_sigs_size);
			assert!(discharged_sigs.len()==cfg.discharged_sigs_size);
		}

		//3. assemble the statement instance by setting its inp/oup/data/subtbl
		let ncirc_minus_pci = ea.n_circ - ea.pc_i;
		let zero = F::zero();
		if !discharged_sigs.contains(&F::zero()){
			return Err(Error::CapErr(
				vec![(format!("build_stmt::dis_charged_sigs (adjust cap::sigs)"), 
				discharged_sigs.len())])); //no need to +1, as this value
					//is already the capacity.sigs + 1
		}
		assert!(discharged_sigs.contains(&F::zero()),
			"Increase discharged sig buf. needs at least one 0 dummy entry");
		if !failed_sigs.contains(&F::zero()){
			return Err(Error::CapErr(
				vec![(format!("build_stmt::failed_sigs (adjust cap::sigs)"), 
				failed_sigs.len())])); //no need to +1, as this value
					//is already the capacity.sigs + 1
		}
		assert!(failed_sigs.contains(&F::zero()),
			"Increase failed sig buf. needs at least one 0 dummy entry");

		let mtbl_sigs = gen_m_table(&failed_sigs, &discharged_sigs);
		let stmt = StatementInst{
			pc_i: ea.pc_i,
			pc_i1: ea.pc_i1, //will be reset later
			n_circ: ea.n_circ,
			n_circ_minus_pc: ncirc_minus_pci,
			act_input_size: F::from(inp.len() as u32),
			act_output_size: F::from(oup.len() as u32),
			act_lookup_share_size: F::from(lkup_share_size as u32),
			act_word_subseg_size: F::from(word.len() as u32),
			word_id: ea.word_id,
			subseg_id: ea.subseg_id,
			total_word_len: ea.total_word_len,
			total_word_segs: ea.total_word_segs,
			total_words: ea.total_words,
			r_F: F::from(2u32), //temp for debug

			batch_r: ea.batch_r,
			batch_v: ea.batch_v,
			r_all_words: ea.r_all_words,
			r_kzg_len: ea.r_kzg_len,
			r_vec_r: ea.r_vec_r,
			r_vec_v: ea.r_vec_v,
			r_word_i: ea.r_word_i,
			accumulated_word_len: ea.accumulated_word_len,
			f_result: if oup.len()>0 {oup[oup.len()-1]}
				else {zero}, //by convention, we make it the
										//LAST element of oup.

			inp_buf: inp,
			oup_buf: oup,
			word_subseg: word_seg,
			data: data,
			subtable_id: subtbl_id,
			col1_share: vec![zero; lkup_share_size], //will be filled 
			col2_share: vec![zero; lkup_share_size], //to be updated
			m_share: vec![zero; lkup_share_size],//will be filled

			failed_sigs: failed_sigs,
			discharged_sigs: discharged_sigs,
			mtbl_sigs: mtbl_sigs,

			_lk: PhantomData,
		};

		if b_debug{
			let inp_oup_data = [
				stmt.inp_buf.clone(),
				stmt.oup_buf.clone(),
				stmt.data.clone(),
			].concat();
			assert!(inp_oup_data.len()==stmt.subtable_id.len());

			self.self_check(
				word,
				_prev_stmt,
				lkup.clone(),
				ea,
				r_advice.clone(),
				lkup_share_size,
				b_dummy,
				5, // num_extra_sample_points
				&inp_oup_data,
				&stmt.subtable_id
			);
		}

		#[cfg(test)]{
			let stmt_vec = stmt.to_vec();
			assert!(stmt_vec.len()==cfg.total_size());
		}
		
		Ok(stmt)
	}
	/// return the max word length that can be processed, we require
	/// that all component gadget mapper handle the same length of word.
	fn max_word_len(&self) -> usize{
		let max_len = self.vec_components[0].lock().unwrap().max_word_len();
		#[cfg(test)]{
			for i in 0..self.vec_components.len(){
				assert!(self.vec_components[i].lock().unwrap().max_word_len()==max_len);
			}
		}
		max_len
	}

	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		r_prev_adv: Option<Arc<dyn NdAdvice + Send + Sync>>, seg_id: usize, job_id: usize)
		->Result<Arc<dyn NdAdvice + Send + Sync>, Error>{
		let b_perf = true;
		let mut t1 = Timer::new();
		if seg_id==0 {assert!(r_prev_adv.is_none());}

		let vec_prev_adv = if r_prev_adv.is_some(){
			r_prev_adv.unwrap().as_any().downcast_ref
				::<CompositeAdvice>().expect("downcast err")
				.vec_adv.iter().map(|x| 
					Some(x.clone())
				).collect::<Vec<Option<Arc<dyn NdAdvice + Send + Sync>>>>()

		}else{vec![None; self.vec_components.len()]};

		let res= self.vec_components.iter().zip(vec_prev_adv.into_iter()).
			map(|(c,a)|{
				c.lock().unwrap().gen_nd_advice(&word, &word_info, a, seg_id, job_id)
			}
		).collect::<Vec<Result<Arc<dyn NdAdvice + Send + Sync>, Error>>>();

		let vec_errs = res.iter().map(|r|
			match r{
				Ok(_) => vec![],
				Err(Error::CapErr(vec)) => vec.to_vec(),
				_ => panic!("unable to handle r: {:?}", r),
			}
		).collect::<Vec<Vec<(String,usize)>>>().concat();

		let vec_adv= res.iter().map(|r|
			match r{
				Ok(adv) => vec![adv.clone()],
				_ => vec![],
			}
		).collect::<Vec<Vec<Arc<dyn NdAdvice + Send + Sync>>>>().concat();
		assert!(vec_errs.len() + vec_adv.len() == res.len());

		if b_perf{ log_perf(0, LOG1, "Generate Advice", &mut t1); }
	
		if vec_errs.len()>0{ Err(Error::CapErr(vec_errs)) } else{
			Ok(Arc::new(CompositeAdvice{vec_adv}))
		}
	}
}
