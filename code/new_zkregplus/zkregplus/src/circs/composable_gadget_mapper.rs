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
	rc::{Rc},cell::{RefCell},
	fmt::{Debug},
};
use crate::gadgets::commons::{gen_m_table};

/// Compononent of a CompositeGadgetMapper.
/// In general, a component mapper should be regarded as a self-contained
/// mapper that manages a FIXED set of gadgets.
/// Given its region in input/data/output, its
/// statement is always [word; inp; output; data; subtable_id]
/// where the subtable_id size is the sum of inp/oup/data
/// If there are needs to correlate its data with others, it's
/// done through extra join constraints.
#[allow(non_camel_case_types)]
pub trait ComponentMapper<F:PrimeField, LK: LookupTableTwoCol<F>>: Debug{
	/// return an Rc dyn object of capacity
	fn get_capacity(&self)->Rc<dyn Capacity>;

	/// create a vector of gadgets
	fn create_gadgets(&self) -> Vec<Rc<RefCell<dyn SigmaGadget<F>>>>;  

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

	/// Also responsible for generating nd_advice with its own capacity
	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		prev_adv: Option<Rc<dyn NdAdvice>>)
		->Result<Rc<dyn NdAdvice>, Error>;


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
	fn build_statement_comp(&self, comp_id: usize, stmt_map_id: usize, word_seg: &Vec<F>, actual_word_len: usize, lkup: &Rc<RefCell<LK>>, extra_info: &StatementExtraInfo<F>, _advice: &Rc<dyn NdAdvice>, cfg: &StatementConfig, comp_mapping: &Vec<Vec<(usize,usize)>>) -> Result<Vec<Vec<F>>, Error>;

	/// This is not required for those non-SED gadgets, they are handled
	/// by legacy gode.
	fn set_container_config(&mut self, _advice: &Rc<dyn NdAdvice>); 


}


/// Composite list of advices (the internal ND_ADVICE for CompositeGadgetMapper)
#[derive(Debug)]
pub struct CompositeAdvice{
	pub vec_adv: Vec<Rc<dyn NdAdvice>>,
}

impl NdAdvice for CompositeAdvice{
	fn as_any(&self) -> &dyn Any{ self }
}

/// A vector of dynamic capcity objects.
#[derive(Debug)]
pub struct CompositeCapacity{
	pub vec_cap: Vec<Rc<dyn Capacity>>,
}

impl Capacity for CompositeCapacity{
	/// requires the r_other also be a CompositeCapacity
	/// of the same size.
	fn can_satisfy(&self, r_other: &Rc<dyn Capacity>)->bool{
		let other = r_other.as_any().downcast_ref::<CompositeCapacity>()
			.expect("downcast err!");
		assert!(self.vec_cap.len()==other.vec_cap.len());
		self.vec_cap.iter().zip(other.vec_cap.iter()).map(|(x,y)|
			x.can_satisfy(&y)
		).fold(true, |acc, res| acc && res)
	}

	fn clone(&self) -> Rc<dyn Capacity>{
		let vec_cap = self.vec_cap.iter().map(|x|
			x.clone()).collect::<Vec<Rc<dyn Capacity>>>();
        Rc::new(CompositeCapacity{vec_cap})
    }

	fn as_any(&self)->&dyn Any{ self }
}

/// A composable gadget mapper means that it can have a flexible
/// combination of atomic gadget mappers. (e.g., allowing
/// free compbination of CP, SED, DFA discharging gadgets)
#[derive(Clone,Debug)]
pub struct CompositeGadgetMapper<F:PrimeField, LK:LookupTableTwoCol<F>>{
	pub _f: PhantomData<F>,
	pub _lk: PhantomData<LK>,
	pub vec_components: Vec<Rc<RefCell<dyn ComponentMapper<F,LK>>>>,
	pub name: String,
}

impl <F:PrimeField,LK:LookupTableTwoCol<F>> CompositeGadgetMapper<F,LK>{
	pub fn new(name: &str, vec_components: Vec<Rc<RefCell<dyn ComponentMapper<F,LK>>>>)->Self{
		Self{
			_f: PhantomData,
			_lk: PhantomData,
			vec_components,
			name: format!("{}", name)
		}
	}
	pub fn set_name(&mut self, name: &str){ self.name = format!("{}", name); }

}

impl <F:PrimeField,LK:LookupTableTwoCol<F>> GadgetMapper<F,LK> for CompositeGadgetMapper<F,LK>{
	/// use advice to generate container config and set it for
	/// each gadget (if gadgetes support container config for
	/// deseiralization). This is only needed for those gadgets in SED
	/// approach.
	fn set_container_config(&mut self, r_advice: &Rc<dyn NdAdvice>){ 
		let advices = r_advice.as_any().downcast_ref::<CompositeAdvice>()
			.expect("downcast err!");
		assert!(advices.vec_adv.len()==self.vec_components.len());
		for i in 0..self.vec_components.len(){
			let adv = &advices.vec_adv[i];
			self.vec_components[i].borrow_mut().set_container_config(adv);
		}
	}

	/// return the capacity of this circuit
	fn get_capacity(&self) -> Rc<dyn Capacity>{
		let vec_cap = self.vec_components.iter().map(|x|
			x.borrow().get_capacity()).collect::<Vec<Rc<dyn Capacity>>>();
		Rc::new(CompositeCapacity{vec_cap})
	}

	/// return the name
	fn get_name(&self) -> String{ self.name.clone() }

	/// Create the components. The config is contained
	/// in the relation mapper object, and should be passed
	/// by the corresonding constructor.
	fn get_gadgets(&self) -> Vec<Rc<RefCell<dyn SigmaGadget<F>>>>{  
		self.vec_components.iter().map(|x|
			x.borrow().create_gadgets()
		).flatten().collect::<Vec<Rc<RefCell<dyn SigmaGadget<F>>>>>()
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
			c.borrow().get_sizes()).collect::<Vec<Vec<usize>>>();
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
				mut new_si_oup_info) = self.vec_components[i].borrow()
				.get_gadgets_stmt_map(&cur_alloc);
			assert!(comp_maps.len()==self.vec_components[i].borrow().num_gadgets());
			vec_maps.append(&mut comp_maps);
			si_data_info.append(&mut new_si_data_info);
			si_inp_info.append(&mut new_si_inp_info);
			si_oup_info.append(&mut new_si_oup_info);
		}
		let num_gadgets = self.vec_components.iter().map(|x| 
			x.borrow().num_gadgets())
			.sum::<usize>();
		assert!(vec_maps.len()==num_gadgets);
		cfg.reset_si_info(si_data_info, si_inp_info, si_oup_info);
		

		//4. collect the joins
		let opt_joins = self.vec_components.iter().enumerate().map(|(i,c)|
			c.borrow().get_joins(i, &cfg, &vec_starts)
		).flatten().collect::<Vec<((usize,usize),(usize,usize))>>();
		let cyclepair_map = vec![]; 


		(cfg.total_size(), cfg, vec_maps, opt_joins, cyclepair_map)
	}

	/// given word input, previous witness, try to construct
	/// the full problem statement (including non-deterministic witness). 
	/// NOTE that the real i/o has only two elements in z_i array.
	fn build_statement(&self, word: &Vec<F>, _prev_stmt: &Option<StatementInst<F,LK>>, lkup: Rc<RefCell<LK>>, ea: &StatementExtraInfo<F>, r_advice: Rc<dyn NdAdvice>, lkup_share_size: usize, b_dummy: bool) 
	-> Result<StatementInst<F,LK>, Error>{
		//1. expand word_seg to max capacity.
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
			let vecs = comp.borrow()
				.build_statement_comp(i, stmt_map_id, 
					&word_seg, actual_word_len, &lkup,
					ea, &advices.vec_adv[i], &cfg, &stmt_map
				)?;
			#[cfg(test)]{
				let sizes = comp.borrow().get_sizes();
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
			stmt_map_id += comp.borrow().num_gadgets();
		}
		assert!(stmt_map_id == stmt_map.len());
		let inp = vec_inp.concat();
		let oup = vec_oup.concat();
		assert!(inp.len()==oup.len());
		let data = vec_data.concat();
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

		#[cfg(test)]{
			let stmt_vec = stmt.to_vec();
			assert!(stmt_vec.len()==cfg.total_size());
		}
		
		Ok(stmt)
	}
	/// return the max word length that can be processed, we require
	/// that all component gadget mapper handle the same length of word.
	fn max_word_len(&self) -> usize{
		let max_len = self.vec_components[0].borrow().max_word_len();
		#[cfg(test)]{
			for i in 0..self.vec_components.len(){
				assert!(self.vec_components[i].borrow().max_word_len()==max_len);
			}
		}
		max_len
	}

	fn gen_nd_advice(&self, word: &Vec<F>, word_info: &WordInfo,
		r_prev_adv: Option<Rc<dyn NdAdvice>>)
		->Result<Rc<dyn NdAdvice>, Error>{
		let b_perf = true;
		let mut t1 = Timer::new();
		let vec_prev_adv = if r_prev_adv.is_some(){
			r_prev_adv.unwrap().as_any().downcast_ref
				::<CompositeAdvice>().expect("downcast err")
				.vec_adv.iter().map(|x| 
					Some(x.clone())
				).collect::<Vec<Option<Rc<dyn NdAdvice>>>>()

		}else{vec![None; self.vec_components.len()]};

		let res= self.vec_components.iter().zip(vec_prev_adv.into_iter()).
			map(|(c,a)|{
				c.borrow().gen_nd_advice(&word, &word_info, a)
			}
		).collect::<Vec<Result<Rc<dyn NdAdvice>, Error>>>();

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
		).collect::<Vec<Vec<Rc<dyn NdAdvice>>>>().concat();
		assert!(vec_errs.len() + vec_adv.len() == res.len());

		if b_perf{ log_perf(LOG1, "Generate Advice", &mut t1); }
	
		if vec_errs.len()>0{ Err(Error::CapErr(vec_errs)) } else{
			Ok(Rc::new(CompositeAdvice{vec_adv}))
		}
	}
}
