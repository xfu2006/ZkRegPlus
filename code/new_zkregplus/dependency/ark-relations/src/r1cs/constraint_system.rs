#[cfg(feature = "std")]
use crate::r1cs::ConstraintTrace;
use crate::r1cs::{LcIndex, LinearCombination, Matrix, SynthesisError, Variable};
use ark_ff::Field;
use ark_std::{
    //any::{Any, TypeId},
    //boxed::Box,
    cell::{Ref, RefCell, RefMut},
    collections::{
//		BTreeMap,
		VecDeque
	},
    format,
    rc::Rc,
    string::String,
    vec,
    vec::Vec,
	sync::{Condvar,Arc,Mutex},
	time::Instant,
};
use rayon::iter::{ParallelIterator,IntoParallelRefIterator,IntoParallelIterator};

const B_DEBUG: bool = false;

/// Computations are expressed in terms of rank-1 constraint systems (R1CS).
/// The `generate_constraints` method is called to generate constraints for
/// both CRS generation and for proving.
// TODO: Think: should we replace this with just a closure?
pub trait ConstraintSynthesizer<F: Field> {
    /// Drives generation of new constraints inside `cs`.
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> crate::r1cs::Result<()>;
}

/// An Rank-One `ConstraintSystem`. Enforces constraints of the form
/// `⟨a_i, z⟩ ⋅ ⟨b_i, z⟩ = ⟨c_i, z⟩`, where `a_i`, `b_i`, and `c_i` are linear
/// combinations over variables, and `z` is the concrete assignment to these
/// variables.
#[derive(Debug, Clone)]
pub struct ConstraintSystem<F: Field> {
    /// The mode in which the constraint system is operating. `self` can either
    /// be in setup mode (i.e., `self.mode == SynthesisMode::Setup`) or in
    /// proving mode (i.e., `self.mode == SynthesisMode::Prove`). If we are
    /// in proving mode, then we have the additional option of whether or
    /// not to construct the A, B, and C matrices of the constraint system
    /// (see below).
    pub mode: SynthesisMode,
    /// The number of variables that are "public inputs" to the constraint
    /// system.
    pub num_instance_variables: usize,
    /// The number of variables that are "private inputs" to the constraint
    /// system.
    pub num_witness_variables: usize,
    /// The number of constraints in the constraint system.
    pub num_constraints: usize,
    /// The number of linear combinations
    pub num_linear_combinations: usize,

    /// The parameter we aim to minimize in this constraint system (either the
    /// number of constraints or their total weight).
    pub optimization_goal: OptimizationGoal,

    /// Assignments to the public input variables. This is empty if `self.mode
    /// == SynthesisMode::Setup`.
    pub instance_assignment: Vec<F>,
    /// Assignments to the private input variables. This is empty if `self.mode
    /// == SynthesisMode::Setup`.
    pub witness_assignment: Vec<F>,

    // Map for gadgets to cache computation results.
    //pub cache_map: Rc<RefCell<BTreeMap<TypeId, Box<dyn Any>>>>,

	/// the map from index to linear combination
    //pub lc_map: BTreeMap<LcIndex, LinearCombination<F>>,
    //pub lc_map: HashMap<LcIndex, LinearCombination<F>>,
	pub lc_map: Vec<Option<LinearCombination<F>>>,

    #[cfg(feature = "std")]
    constraint_traces: Vec<Option<ConstraintTrace>>,

    a_constraints: Vec<LcIndex>,
    b_constraints: Vec<LcIndex>,
    c_constraints: Vec<LcIndex>,

    //lc_assignment_cache: Rc<RefCell<BTreeMap<LcIndex, F>>>,
    lc_assignment_cache: Rc<RefCell<Vec<Option<F>>>>,
}

impl<F: Field> Default for ConstraintSystem<F> {
    fn default() -> Self {
        Self::new()
    }
}

/// Defines the mode of operation of a `ConstraintSystem`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum SynthesisMode {
    /// Indicate to the `ConstraintSystem` that it should only generate
    /// constraint matrices and not populate the variable assignments.
    Setup,
    /// Indicate to the `ConstraintSystem` that it populate the variable
    /// assignments. If additionally `construct_matrices == true`, then generate
    /// the matrices as in the `Setup` case.
    Prove {
        /// If `construct_matrices == true`, then generate
        /// the matrices as in the `Setup` case.
        construct_matrices: bool,
    },
}

/// Defines the parameter to optimize for a `ConstraintSystem`.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub enum OptimizationGoal {
    /// Make no attempt to optimize.
    None,
    /// Minimize the number of constraints.
    Constraints,
    /// Minimize the total weight of the constraints (the number of nonzero
    /// entries across all constraints).
    Weight,
}

impl<F: Field> ConstraintSystem<F> {
    #[inline]
    fn make_row(&self, l: &LinearCombination<F>) -> Vec<(F, usize)> {
        let num_input = self.num_instance_variables;
        l.0.iter()
            .filter_map(|(coeff, var)| {
                if coeff.is_zero() {
                    None
                } else {
                    Some((
                        *coeff,
                        var.get_index_unchecked(num_input).expect("no symbolic LCs"),
                    ))
                }
            })
            .collect()
    }

    /// Construct an empty `ConstraintSystem`.
    pub fn new() -> Self {
        Self {
            num_instance_variables: 1,
            num_witness_variables: 0,
            num_constraints: 0,
            num_linear_combinations: 0,
            a_constraints: Vec::new(),
            b_constraints: Vec::new(),
            c_constraints: Vec::new(),
            instance_assignment: vec![F::one()],
            witness_assignment: Vec::new(),
            //cache_map: Rc::new(RefCell::new(BTreeMap::new())),
            #[cfg(feature = "std")]
            constraint_traces: Vec::new(),

            lc_map: Vec::new(),
            lc_assignment_cache: Rc::new(RefCell::new(Vec::new())),

            mode: SynthesisMode::Prove {
                construct_matrices: true,
            },

            optimization_goal: OptimizationGoal::Constraints,
        }
    }

    /// Create a new `ConstraintSystemRef<F>`.
    pub fn new_ref() -> ConstraintSystemRef<F> {
        ConstraintSystemRef::new(Self::new())
    }

    /// Set `self.mode` to `mode`.
    pub fn set_mode(&mut self, mode: SynthesisMode) {
        self.mode = mode;
    }

    /// Check whether `self.mode == SynthesisMode::Setup`.
    pub fn is_in_setup_mode(&self) -> bool {
        self.mode == SynthesisMode::Setup
    }

    /// Check whether this constraint system aims to optimize weight,
    /// number of constraints, or neither.
    pub fn optimization_goal(&self) -> OptimizationGoal {
        self.optimization_goal
    }

    /// Specify whether this constraint system should aim to optimize weight,
    /// number of constraints, or neither.
    pub fn set_optimization_goal(&mut self, goal: OptimizationGoal) {
        // `set_optimization_goal` should only be executed before any constraint or value is created.
        assert_eq!(self.num_instance_variables, 1);
        assert_eq!(self.num_witness_variables, 0);
        assert_eq!(self.num_constraints, 0);
        assert_eq!(self.num_linear_combinations, 0);

        self.optimization_goal = goal;
    }

    /// Check whether or not `self` will construct matrices.
    #[inline(always)]
    pub fn should_construct_matrices(&self) -> bool {
        match self.mode {
            SynthesisMode::Setup => true,
            SynthesisMode::Prove { construct_matrices } => construct_matrices,
        }
    }

    /// Return a variable representing the constant "zero" inside the constraint
    /// system.
    #[inline]
    pub fn zero() -> Variable {
        Variable::Zero
    }

    /// Return a variable representing the constant "one" inside the constraint
    /// system.
    #[inline]
    pub fn one() -> Variable {
        Variable::One
    }

    /// Obtain a variable representing a new public instance input.
    #[inline]
    pub fn new_input_variable<Func>(&mut self, f: Func) -> crate::r1cs::Result<Variable>
    where
        Func: FnOnce() -> crate::r1cs::Result<F>,
    {
        let index = self.num_instance_variables;
        self.num_instance_variables += 1;

        if !self.is_in_setup_mode() {
            self.instance_assignment.push(f()?);
        }
        Ok(Variable::Instance(index))
    }

    /// Obtain a variable representing a new private witness input.
    #[inline]
    pub fn new_witness_variable<Func>(&mut self, f: Func) -> crate::r1cs::Result<Variable>
    where
        Func: FnOnce() -> crate::r1cs::Result<F>,
    {
        let index = self.num_witness_variables;
        self.num_witness_variables += 1;

        if !self.is_in_setup_mode() {
            self.witness_assignment.push(f()?);
        }
        Ok(Variable::Witness(index))
    }

    /// Obtain a variable representing a linear combination.
    #[inline]
    pub fn new_lc(&mut self, lc: LinearCombination<F>) -> crate::r1cs::Result<Variable> {
		//1. create the lc
        let index = LcIndex(self.num_linear_combinations);
        let var = Variable::SymbolicLc(index);
		if B_DEBUG {
			assert!(index.0==self.lc_map.len());
		}
		self.lc_map.push(Some(lc));
        self.num_linear_combinations += 1;
        Ok(var)
    }

    /// Enforce a R1CS constraint with the name `name`.
    #[inline(always)]
    pub fn enforce_constraint(
        &mut self,
        a: LinearCombination<F>,
        b: LinearCombination<F>,
        c: LinearCombination<F>,
    ) -> crate::r1cs::Result<()> {
        if self.should_construct_matrices() {
            let a_index = self.new_lc(a)?.get_lc_index().unwrap();
            let b_index = self.new_lc(b)?.get_lc_index().unwrap();
            let c_index = self.new_lc(c)?.get_lc_index().unwrap();
            self.a_constraints.push(a_index);
            self.b_constraints.push(b_index);
            self.c_constraints.push(c_index);
        }
        self.num_constraints += 1;
		/* LOOKS LIKE simply set default-features = false
		on ark-r1cs-std crate does not disalbe it.
		so temporary solution commitent it here. Xiang Fu.
        #[cfg(feature = "std")]
        {
           let trace = ConstraintTrace::capture();
            self.constraint_traces.push(trace);
        }
		*/
        Ok(())
    }

    /// Count the number of times each LC is used within other LCs in the
    /// constraint system
    fn lc_num_times_used(&self, count_sinks: bool) -> Vec<usize> {
        let mut num_times_used = vec![0; self.lc_map.len()];

        // Iterate over every lc in constraint system
        for index in 0..self.lc_map.len() {
			let lc = &self.lc_map[index];
			if !lc.is_some(){continue;}
			let lc = &lc.as_ref().unwrap();
            num_times_used[index] += count_sinks as usize;

            // Increment the counter for each lc that this lc has a direct dependency on.
            for &(_, var) in lc.iter() {
                if var.is_lc() {
                    let lc_index = var.get_lc_index().expect("should be lc");
                    num_times_used[lc_index.0] += 1;
                }
            }
        }
        num_times_used
    }

	/// Used for debugging purpose, this reports the maximum
	/// lc_len() for each existing linear combination
	/// VERY SLOW (because it calls transform_lc_map)! Call at caution
	pub fn report_max_lc_len(&self)->usize{
		let lc_map = self.transform_lc_map_old_worker(	&mut |_,_,_| (0,None));
		if lc_map.len()==0{return 0;}
		let res:usize = lc_map.par_iter().map(|v| 
			if v.is_some() {v.as_ref().unwrap().len()} else {0}
		).max().unwrap();

		res
	}

    /// Transform the map of linear combinations.
    /// Specifically, allow the creation of additional witness assignments.
    ///
    /// This method is used as a subroutine of `inline_all_lcs` and `outline_lcs`.
    ///
    /// The transformer function is given a references of this constraint system (&self),
    /// number of times used, and a mutable reference of the linear combination to be transformed.
    ///     (&ConstraintSystem<F>, usize, &mut LinearCombination<F>)
    ///
    /// The transformer function returns the number of new witness variables needed
    /// and a vector of new witness assignments (if not in the setup mode).
    ///     (usize, Option<Vec<F>>)
    pub fn transform_lc_map(
        &mut self,
        transformer: &mut dyn FnMut(
            &ConstraintSystem<F>,
            usize,
            &mut LinearCombination<F>,
        ) -> (usize, Option<Vec<F>>),
    ) {
		let b_new = false; //strangely 1-thread is faster.
		let b_perf = false;
		let timer = Instant::now();
		let size = self.lc_map.len();
		if !b_new{
			self.transform_lc_map_old(transformer)
		}else{
			self.transform_lc_map_new_1(transformer)
			//self.transform_lc_map_new_2()
		}
		if b_perf{
			println!(" --- transform_lc: time: {:?} for size: {} --> {}", timer.elapsed(), size, self.lc_map.len());
			//let total_len: usize = self.lc_map.par_iter().map(|(_k,v)|
			//	v.len()).sum();
			//let avg_len = (total_len as f64)/(self.lc_map.len() as f64);
			//let max_len = self.lc_map.par_iter().map(|(_,v)|
			//	v.len()).max().unwrap();
		}
	}

	/// transform lc_map old (but modified to skip transformer)
    pub fn transform_lc_map_old(&mut self,
        transformer: &mut dyn FnMut(
            &ConstraintSystem<F>,
            usize,
            &mut LinearCombination<F>,
        ) -> (usize, Option<Vec<F>>),
	){
		self.lc_map = self.transform_lc_map_old_worker(transformer);
	}

	/// the old version
    pub fn transform_lc_map_old_worker(
        &self,
        transformer: &mut dyn FnMut(
            &ConstraintSystem<F>,
            usize,
            &mut LinearCombination<F>,
        ) -> (usize, Option<Vec<F>>),
	//)-> BTreeMap<LcIndex, LinearCombination<F>>{
	//)-> HashMap<LcIndex, LinearCombination<F>>{
	)-> Vec<Option<LinearCombination<F>>>{
        // `transformed_lc_map` stores the transformed linear combinations.
        //let mut transformed_lc_map = BTreeMap::<_, LinearCombination<F>>::new();
        //let mut transformed_lc_map = HashMap::<_, LinearCombination<F>>::new();
        let mut transformed_lc_map = Vec::<Option<LinearCombination<F>>>::new();
        let mut num_times_used = self.lc_num_times_used(false);
		let max_idx = self.lc_map.len()-1;


        // This loop goes through all the LCs in the map, starting from
        // the early ones. The transformer function is applied to the
        // inlined LC, where new witness variables can be created.
		// ** BY XIANG FU **
		// SINCE the BTreeMap is replaced by the hashmap
		// index is no longer sorted in self.lc_map
		// we need to retrieve the index from 0 to max val (luckily
		// it is consecutive
		// ******************
        //for (&index, lc) in &self.lc_map {
		for idx in 0..max_idx+1{
			let index = LcIndex(idx);
			let lc = &self.lc_map[idx];
			if !lc.is_some() {continue;} //this is for removed entry
										//no need to process it
			let lc = &self.lc_map[idx].as_ref().unwrap();
            let mut transformed_lc = LinearCombination::new();

            // Inline the LC, unwrapping symbolic LCs that may constitute it,
            // and updating them according to transformations in prior iterations.

            for &(coeff, var) in lc.iter() {
                if var.is_lc() {
                    let lc_index = var.get_lc_index().expect("should be lc");

                    // If `var` is a `SymbolicLc`, fetch the corresponding
                    // inlined LC, and substitute it in.
                    //
                    // We have the guarantee that `lc_index` must exist in
                    // `new_lc_map` since a LC can only depend on other
                    // LCs with lower indices, which we have transformed.
                    //
                    let lc = transformed_lc_map[lc_index.0].as_ref().unwrap();
                    transformed_lc.extend((lc * coeff).0.into_iter());

                    // Delete linear combinations that are no longer used.
                    //
                    // Deletion is safe for both outlining and inlining:
                    // * Inlining: the LC is substituted directly into all use sites, and so once it
                    //   is fully inlined, it is redundant.
                    //
                    // * Outlining: the LC is associated with a new variable `w`, and a new
                    //   constraint of the form `lc_data * 1 = w`, where `lc_data` is the actual
                    //   data in the linear combination. Furthermore, we replace its entry in
                    //   `new_lc_map` with `(1, w)`. Once `w` is fully inlined, then we can delete
                    //   the entry from `new_lc_map`
                    //
                    num_times_used[lc_index.0] -= 1;
                    if num_times_used[lc_index.0] == 0 {
                        // This lc is not used any more, so remove it.
						// but here since it's changed to Vec
						// just leave it there as unused
                        //transformed_lc_map.remove(&lc_index);
						transformed_lc_map[lc_index.0] = None;
                    }
                } else {
                    // Otherwise, it's a concrete variable and so we
                    // substitute it in directly.
                    transformed_lc.push((coeff, var));
                }
            }

            transformed_lc.compactify();

            // Call the transformer function.
            let (num_new_witness_variables, _new_witness_assignments) =
                transformer(&self, num_times_used[index.0], &mut transformed_lc);
			assert!(num_new_witness_variables == 0);
			//NOTE: here we assume that transformer passed is EMPTY.
			//WE EXPECT THAT THIS FUNCTION IS ONLY CALLED FROM
			//INLINE (optimization goal is for constraints)

            // Insert the transformed LC. (COMMENTED OUT BASED 
			//ON ASSUMPTION ON INLINE - NO NEW WITNESS ADDED
            //transformed_lc_map.insert(index, transformed_lc);
			assert!(transformed_lc_map.len()==index.0);
            transformed_lc_map.push(Some(transformed_lc));

            // Update the witness counter.
			//BASED ON ASSUMPTION INLINE - NO NEW WITNESS ADDED
            //self.num_witness_variables += num_new_witness_variables;

            // Supply additional witness assignments if not in the
            // setup mode and if new witness variables are created.
			assert!(num_new_witness_variables ==0); //again assumpton on INLINE
			/* COMMENTED OUT
            if !self.is_in_setup_mode() && num_new_witness_variables > 0 {
				if 1>0 {panic!("STOP HERE 201");}
                assert!(new_witness_assignments.is_some());
                if let Some(new_witness_assignments) = new_witness_assignments {
                    assert_eq!(new_witness_assignments.len(), num_new_witness_variables);
                    self.witness_assignment
                        .extend_from_slice(&new_witness_assignments);
                }
            }
			*/
        }
        	
		transformed_lc_map
    }

	/// the new version which leverages rayon parallel processing
	/// We use condvar for dependency of tasks 
	#[allow(dead_code)]
    pub fn transform_lc_map_new_1(
        &mut self,
        _transformer: &mut dyn FnMut(
            &ConstraintSystem<F>,
            usize,
            &mut LinearCombination<F>,
        ) -> (usize, Option<Vec<F>>),
    ) {
        //1. init data structures
		// `transformed_lc_map` stores the transformed linear combinations.
		let t1 = Arc::new(Mutex::new(Instant::now()));
        //let transformed_lc_map = 
		//	Arc::new(Mutex::new(
		//		//BTreeMap::<LcIndex, LinearCombination<F>>::new()
		//		HashMap::<LcIndex, LinearCombination<F>>::new()
		//	));
        let transformed_lc_map = 
			Arc::new(Mutex::new(
				//BTreeMap::<LcIndex, LinearCombination<F>>::new()
				//HashMap::<LcIndex, LinearCombination<F>>::new()
				Vec::<Option<LinearCombination<F>>>::new()
			));
        let num_times_used = Arc::new(Mutex::new(
			self.lc_num_times_used(false) ));

		//2. create one conditional variable for each lc_idx
		/*
		let map_cond = self.lc_map.par_iter().map(|(ldx, _)|{
			let cond_var = Condvar::new();
			(ldx.0, Arc::new( (Mutex::new(1), cond_var) ))
		}).collect::<HashMap<usize, Arc<(Mutex<_>,Condvar)>>>();
		*/
		//let max_idx = self.lc_map.par_iter().map(|(ldx, _)| ldx.0).max().unwrap();
		let max_idx = self.lc_map.len()-1; //
		let locks = Arc::new((0..max_idx+1).into_par_iter().map(|_|
			Mutex::new(false) ).collect::<Vec<Mutex<_>>>());
		let conds = Arc::new((0..max_idx+1).into_par_iter().map(|_|
			Condvar::new() ).collect::<Vec<Condvar>>());
		let bmap = Arc::new(self.lc_map.clone());
		let counter = Arc::new(Mutex::new(0));
		let threads = rayon::current_num_threads();

		rayon::scope(|scope|{
		  for thread_id in 0..threads{
		  	let chunk_size = (max_idx+1)/threads;
		  	let idx_begin = thread_id * chunk_size;
			let idx_end = if thread_id==threads-1{
				max_idx + 1 
			}else{
				idx_begin + chunk_size
			};//atually not included, idx_end is the real last idx
			let bmap = bmap.clone(); //low cost clone, to move vals into
					//threads.
			let locks = locks.clone(); //low cost (for the rest clones)
			let conds = conds.clone(); //low cost
			let num_times_used = num_times_used.clone();
			let transformed_lc_map = transformed_lc_map.clone(); 
			let t1 = t1.clone();
			let counter = counter.clone();
			scope.spawn(move |_|{
			  	for idx in idx_begin..idx_end{//process all idx
					//let lc = bmap.get(&lc_idx).unwrap();
					let lc = &bmap[idx];
					if !lc.is_some(){continue;}
					let lc = lc.as_ref().unwrap();
            		let mut transformed_lc = LinearCombination::new();
            		for &(coeff, var) in lc.iter() {
                		if var.is_lc() {
                    		let d_index= var.get_lc_index()
								.expect("should be lc");
							let mut done = locks[d_index.0].lock().unwrap();
							while !*done{
								done = conds[d_index.0].wait(done).unwrap();
							}
							let lc = 
							{
								let tmap= transformed_lc_map
									.lock().unwrap();
								//let lc = tmap.get(&d_index)
								//	.expect(&format!("expect val at idx: {}",
								//		d_index.0));
								let lc = &tmap[d_index.0];
								lc.clone()
							}; //make tmap out of scope

                    		transformed_lc.extend((lc.unwrap() * coeff)
								.0.into_iter());
							let mut num_times = num_times_used.lock().unwrap();
                    		num_times[d_index.0] -= 1;
                    		if num_times[d_index.0] == 0 {
								let mut tmap= transformed_lc_map
									.lock().unwrap();
								tmap[d_index.0] = None;
							}
						}else{
                    		transformed_lc.push((coeff, var));
						}
					}
					
            		transformed_lc.compactify();
					//let index = LcIndex(idx);
					{
            			//transformed_lc_map.lock().unwrap()
						//	.insert(index, transformed_lc);
						transformed_lc_map.lock().unwrap()[idx] 
							= Some(transformed_lc); //update
					}
					//no check of is_in_setupmode and new_witness_vars
					//as we don't call transfer and don't generate
					//new witness vars
		
					let mut cnt = counter.lock().unwrap();
					*cnt += 1;
					if *cnt%(1000*1000)==0{
						let mut timer = t1.lock().unwrap();
						*timer = Instant::now();
					}
					//wait up everybody waiting on me
					let mut done = locks[idx].lock().unwrap();
					*done = true;
					conds[idx].notify_all();
				}//end of for loop
			});//end of spawn
		  }//for each thread
		}); //end of rayon scope
        self.lc_map = std::mem::take(&mut transformed_lc_map.lock().unwrap());

    }

	/// the new version2 which leverages rayon parallel processing
	/// We collect the DAG of dependency first and use the
	/// producer/consumer model to let threads handle tasks of
	///   inlining linear combinations
	/// LCs with only concrete variables (no symbolic ones) are
	///   those which are ready to process first.
	/// When an LC has a child LC which forms a single-thread dependnecy,
	///   the child can be processed within thread (without checking
	///    the dependee info as it has only one parent).
	/// Here we assume transformer is an EMPTY one, we do not call it
	/// at all (so no new witness vars are added). 
	#[allow(dead_code)]
    pub fn transform_lc_map_new_2(
        &mut self,
    ) {
        //1. init data structures
		//1.1 num times
		let mut timer = Instant::now();
		let b_debug = B_DEBUG;
		let t1 = Arc::new(Mutex::new(Instant::now()));
        let transformed_lc_map = 
			Arc::new(Mutex::new(
				//BTreeMap::<LcIndex, LinearCombination<F>>::new()
				//HashMap::<LcIndex, LinearCombination<F>>::new()
				Vec::<Option<LinearCombination<F>>>::new()
			));
        let num_times_used = Arc::new(Mutex::new(
			self.lc_num_times_used(false) ));
		if b_debug{
			println!("DEUG USE 2101.1: init num_time_used: {:?}, size: {}", 
				timer.elapsed(), self.lc_map.len());
			timer = Instant::now();
		}

		//1.2 build the children info [for each lc_idx, who's its
		//children (for dependency)
		let n_total = self.lc_map.len();
		//let max_idx = n_total-1;
        let mut child_list = vec![vec![]; n_total]; //symbolic only
		let mut par_list = vec![vec![]; n_total]; //symbolic only
		let mut task_queue = VecDeque::<usize>::new();
		let mut singles_dep = 0;
		let mut two_dep = 0;
		let mut three_dep = 0;
		let mut more_dep = 0;
		let mut starting = 0;
        //for (index, lc) in self.lc_map.iter() {
        for idx in 0..self.lc_map.len() {
			let lc = &self.lc_map[idx];
			if !lc.is_some(){ continue; }
			let lc = lc.as_ref().unwrap();
			let mut cnt = 0;
            for &(_, var) in lc.iter() {
                if var.is_lc() {
                    let lc_index = var.get_lc_index().expect("should be lc");
                    child_list[lc_index.0].push(idx);
					par_list[idx].push(lc_index.0);
					cnt += 1;
                }
            }
			if cnt==0 {
				starting += 1;
				task_queue.push_back(idx); //no dependees, can handle now 
			};
			if cnt==1 {singles_dep += 1};
			if cnt==2 {two_dep += 1};
			if cnt==3 {three_dep += 1};
			if cnt>3 {more_dep+=1;}
        }
		assert!(task_queue.len()==starting);
		if b_debug{
			println!("DEUG USE 2101.2: build dependency time: {:?}", 
				timer.elapsed());
			timer = Instant::now();
		}

		//2. start all threads to process the available tasks.
		let threads = rayon::current_num_threads();
		let task_queue = Arc::new(Mutex::new(task_queue));
		let cond_queue = Arc::new(Condvar::new());
		let processed = Arc::new(Mutex::new(0)); //alread processed
		let bmap = Arc::new(std::mem::take(&mut self.lc_map)); //transfer
			//self.lc_map is empty now
		let child_list = Arc::new(child_list);
		let par_list= Arc::new(par_list);
		let unresolved_par_count_list = par_list.par_iter().map(|v|
			v.len()).collect::<Vec<usize>>();
		let unresolved_par_count_list = Arc::new(
			Mutex::new(unresolved_par_count_list)
		);

		//3. start threads and process until processed == n_total
		rayon::scope(|scope|{
		  for _thread_id in 0..threads{
		    //3.1 clone vars needed for sharing local vars
			// all are low cost clone of Arc
			let task_queue = task_queue.clone(); 
			let cond_queue = cond_queue.clone();
			let processed = processed.clone(); 
			let bmap = bmap.clone();
			let transformed_lc_map = transformed_lc_map.clone();
			let num_times_used = num_times_used.clone();
			let unresolved_par_count_list = unresolved_par_count_list.clone();
			let par_list = par_list.clone();
			let child_list = child_list.clone();
			let t1 = t1.clone();
			//3.2 start the threads
			scope.spawn(move |_|{//continue as long as there are unprocessed
				let mut cur_proc = 0; 
				while cur_proc < n_total{
					//3.3.1 retrieve one task
					//when all tasks processed task is None
					//task is the LcIdx of the linear combination to process
					let mut task:Option<usize> = {
						//3.3.1 retrieve one task (if all processed do not wait)
						let mut q = task_queue.lock().unwrap();
						while q.is_empty() && cur_proc<n_total{
							q = cond_queue.wait(q).unwrap();
							//if we're waiting but cur_proc reaches max (all done)
							//break out
							cur_proc = *processed.lock().unwrap(); //just read
										//release lock using scope
						}
						let task = if cur_proc==n_total {
							//if all processed, q MUST BE empty
							assert!(q.is_empty()); 
							//we need to notify the waiting threads in
							//cond_queue again as we are going to unlock it.
							//this is needed if there are multi-threads waiting
							cond_queue.notify_all();
							None
						} else {
							Some(q.pop_front().expect("queue pop err"))
						};

						task
					};
					if task.is_none() {break;} //task is actually the LcIdx
						
					//3.3.2 process this task and all of its single-thread
					//dependent (note: they DO NOT need locking as we know
					//these single-thread dpeendent has ONLY ONE dependee)
					while task.is_some(){
						//3.3.2.1 for the current task resolve and build
						//its transformed_linear combination
						//basically for each symbolic var, retrieve
						//its LC, and materialize the LC of the task
						let idx:usize = task.unwrap();
						let lc_idx =LcIndex(idx);
						//let lc = bmap.get(&lc_idx).unwrap();
						let lc = &bmap[lc_idx.0];
						if !lc.is_some() {continue;}
						let lc = lc.as_ref().unwrap();
            			let mut transformed_lc = LinearCombination::<F>::new();
						for &(coeff, var) in lc.iter() {//retrieve each var
							if var.is_lc() {//they are already there
								let d_index= var.get_lc_index()
									.expect("should be lc");
								let lc = 
								{
									let tmap= transformed_lc_map
										.lock().unwrap();
									//let lc = tmap.get(&d_index).expect(
									//	&format!("expect val at idx: {}",
									//		d_index.0)
									//);
									let lc = &tmap[d_index.0];
									lc.clone()
								}; //make tmap out of scope

								transformed_lc.extend((lc.unwrap()*coeff).0.into_iter());
								{//block to unlock the lock immediately
									let mut num_times = num_times_used
										.lock().unwrap();
									num_times[d_index.0] -= 1;
									if num_times[d_index.0] == 0 {
										let mut tmap= transformed_lc_map
											.lock().unwrap();
										tmap[d_index.0] = None;
									}
								}//remove unused entries
							}else{//if it's var directly
								transformed_lc.push((coeff, var));
							}
						}
					
						//3.3.2.2 update global state about the
						//processed LC (of task).
						transformed_lc.compactify();
						let index = LcIndex(idx);
						{//single block to release lock immediately
							//transformed_lc_map.lock().unwrap()
							//	.insert(index, transformed_lc);
							transformed_lc_map.lock().unwrap()[index.0]
								= Some(transformed_lc);
						}

						//3.3.2.3 update the dependee info of 
						//each of its children
						//pick one single-thread child
						//to the rest and push the rest (ready) to the queue.
						let mut next_task = None;
						let mut vec_to_add_to_queue = vec![];
						{
						 let mut unresolved_counts = unresolved_par_count_list
						 	.lock().unwrap();
						 for ptr_child_id in &child_list[idx]{
						    let child_id = *ptr_child_id;
							unresolved_counts[child_id] -= 1;
							//if all dependees removed, should
							//either be processed directly if it's 
							//single-thread, or add to queue
							if unresolved_counts[child_id]==0{
							   if par_list[child_id].len()==1 && 
							   	next_task.is_none(){
									next_task = Some(child_id);
							   }else{
							     vec_to_add_to_queue.push(child_id);
							   }
							}
						 }
						}

						{//put in block to release lock
							let mut q = task_queue.lock().unwrap(); 
							for cid in &vec_to_add_to_queue{
								assert!(*cid > idx); //must be larger
								q.push_back(*cid);
							}
						}


						//3.3.2.4 update the processed count.
						task = next_task;
						{
						 let mut cnt = processed.lock().unwrap();
						 if b_debug{
							if *cnt%(1000*1000)==0{
								let mut timer = t1.lock().unwrap();
								*timer = Instant::now();
							}
						 }
						 *cnt+= 1;
						 cond_queue.notify_all();
						}//block of update processed count
					}//while task is some
				}//while cur_processed < n_total
			});//end of for spawn thread
		  }//for each thread
		}); //end of rayon::scope

		if b_debug{
			println!("DEUG USE 2101.LAST: build dependency time: {:?} for size: {}", timer.elapsed(), n_total);
		}

        self.lc_map = std::mem::take(&mut transformed_lc_map.lock().unwrap());
    }


    /// Naively inlines symbolic linear combinations into the linear
    /// combinations that use them.
    ///
    /// Useful for standard pairing-based SNARKs where addition gates are cheap.
    /// For example, in the SNARKs such as [\[Groth16\]](https://eprint.iacr.org/2016/260) and
    /// [\[Groth-Maller17\]](https://eprint.iacr.org/2017/540), addition gates
    /// do not contribute to the size of the multi-scalar multiplication, which
    /// is the dominating cost.
    pub fn inline_all_lcs(&mut self) {
        // Only inline when a matrix representing R1CS is needed.
        if !self.should_construct_matrices() {
            return;
        }

        // A dummy closure is used, which means that
        // - it does not modify the inlined LC.
        // - it does not add new witness variables.
        self.transform_lc_map(&mut |_, _, _| (0, None));
    }

    /// If a `SymbolicLc` is used in more than one location and has sufficient
    /// length, this method makes a new variable for that `SymbolicLc`, adds
    /// a constraint ensuring the equality of the variable and the linear
    /// combination, and then uses that variable in every location the
    /// `SymbolicLc` is used.
    ///
    /// Useful for SNARKs like [\[Marlin\]](https://eprint.iacr.org/2019/1047) or
    /// [\[Fractal\]](https://eprint.iacr.org/2019/1076), where addition gates
    /// are not cheap.
    fn outline_lcs(&mut self) {
        // Only inline when a matrix representing R1CS is needed.
        if !self.should_construct_matrices() {
            return;
        }

        // Store information about new witness variables created
        // for outlining. New constraints will be added after the
        // transformation of the LC map.
        let mut new_witness_linear_combinations = Vec::new();
        let mut new_witness_indices = Vec::new();

        // It goes through all the LCs in the map, starting from
        // the early ones, and decides whether or not to dedicate a witness
        // variable for this LC.
        //
        // If true, the LC is replaced with 1 * this witness variable.
        // Otherwise, the LC is inlined.
        //
        // Each iteration first updates the LC according to outlinings in prior
        // iterations, and then sees if it should be outlined, and if so adds
        // the outlining to the map.
        //
        self.transform_lc_map(&mut |cs, num_times_used, inlined_lc| {
            let mut should_dedicate_a_witness_variable = false;
            let mut new_witness_index = None;
            let mut new_witness_assignment = Vec::new();

            // Check if it is worthwhile to dedicate a witness variable.
            let this_used_times = num_times_used + 1;
            let this_len = inlined_lc.len();

            // Cost with no outlining = `lc_len * number of usages`
            // Cost with outlining is one constraint for `(lc_len) * 1 = {new variable}` and
            // using that single new variable in each of the prior usages.
            // This has total cost `number_of_usages + lc_len + 2`
            if this_used_times * this_len > this_used_times + 2 + this_len {
                should_dedicate_a_witness_variable = true;
            }

            // If it is worthwhile to dedicate a witness variable,
            if should_dedicate_a_witness_variable {
                // Add a new witness (the value of the linear combination).
                // This part follows the same logic of `new_witness_variable`.
                let witness_index = cs.num_witness_variables;
                new_witness_index = Some(witness_index);

                // Compute the witness assignment.
                if !cs.is_in_setup_mode() {
                    let mut acc = F::zero();
                    for (coeff, var) in inlined_lc.iter() {
                        acc += *coeff * &cs.assigned_value(*var).unwrap();
                    }
                    new_witness_assignment.push(acc);
                }

                // Add a new constraint for this new witness.
                new_witness_linear_combinations.push(inlined_lc.clone());
                new_witness_indices.push(witness_index);

                // Replace the linear combination with (1 * this new witness).
                *inlined_lc = LinearCombination::from(Variable::Witness(witness_index));
            }
            // Otherwise, the LC remains unchanged.

            // Return information about new witness variables.
            if new_witness_index.is_some() {
                (1, Some(new_witness_assignment))
            } else {
                (0, None)
            }
        });

        // Add the constraints for the newly added witness variables.
        for (new_witness_linear_combination, new_witness_variable) in
            new_witness_linear_combinations
                .iter()
                .zip(new_witness_indices.iter())
        {
            // Add a new constraint
            self.enforce_constraint(
                new_witness_linear_combination.clone(),
                LinearCombination::from(Self::one()),
                LinearCombination::from(Variable::Witness(*new_witness_variable)),
            )
            .unwrap();
        }
    }

    /// Finalize the constraint system (either by outlining or inlining,
    /// if an optimization goal is set).
    pub fn finalize(&mut self) {
        match self.optimization_goal {
            OptimizationGoal::None => self.inline_all_lcs(),
            OptimizationGoal::Constraints => self.inline_all_lcs(),
            OptimizationGoal::Weight => self.outline_lcs(),
        };
    }

    /// This step must be called after constraint generation has completed, and
    /// after all symbolic LCs have been inlined into the places that they
    /// are used.
    pub fn to_matrices(&self) -> Option<ConstraintMatrices<F>> {
        if let SynthesisMode::Prove {
            construct_matrices: false,
        } = self.mode
        {
            None
        } else {
            let a: Vec<_> = self
                .a_constraints
                .iter()
                .map(|index| self.make_row(self.lc_map[index.0].as_ref().unwrap()))
                .collect();
            let b: Vec<_> = self
                .b_constraints
                .iter()
                //.map(|index| self.make_row(self.lc_map.get(index).unwrap()))
                .map(|index| self.make_row(self.lc_map[index.0].as_ref().unwrap()))
                .collect();
            let c: Vec<_> = self
                .c_constraints
                .iter()
                .map(|index| self.make_row(self.lc_map[index.0].as_ref().unwrap()))
                .collect();

            let a_num_non_zero: usize = a.iter().map(|lc| lc.len()).sum();
            let b_num_non_zero: usize = b.iter().map(|lc| lc.len()).sum();
            let c_num_non_zero: usize = c.iter().map(|lc| lc.len()).sum();
            let matrices = ConstraintMatrices {
                num_instance_variables: self.num_instance_variables,
                num_witness_variables: self.num_witness_variables,
                num_constraints: self.num_constraints,

                a_num_non_zero,
                b_num_non_zero,
                c_num_non_zero,

                a,
                b,
                c,
            };
            Some(matrices)
        }
    }

	#[inline(always)]
    fn eval_lc(&self, lc: LcIndex) -> Option<F> {
        let lc = &self.lc_map[lc.0].as_ref().unwrap();
        let mut acc = F::zero();
        for (coeff, var) in lc.iter() {
			let v1 = self.assigned_value(*var);
			if v1.is_none(){ return None; }
			let v1 = v1.unwrap();
            acc += *coeff * v1;
        }
        Some(acc)
    }

    /// If `self` is satisfied, outputs `Ok(true)`.
    /// If `self` is unsatisfied, outputs `Ok(false)`.
    /// If `self.is_in_setup_mode()`, outputs `Err(())`.
    pub fn is_satisfied(&self) -> crate::r1cs::Result<bool> {
        self.which_is_unsatisfied().map(|s| s.is_none())
    }

    /// If `self` is satisfied, outputs `Ok(None)`.
    /// If `self` is unsatisfied, outputs `Some(i)`, where `i` is the index of
    /// the first unsatisfied constraint. If `self.is_in_setup_mode()`, outputs
    /// `Err(())`.
    pub fn which_is_unsatisfied(&self) -> crate::r1cs::Result<Option<String>> {
        if self.is_in_setup_mode() {
            Err(SynthesisError::AssignmentMissing)
        } else {
            for i in 0..self.num_constraints {
                let a = self
                    .eval_lc(self.a_constraints[i])
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let b = self
                    .eval_lc(self.b_constraints[i])
                    .ok_or(SynthesisError::AssignmentMissing)?;
                let c = self
                    .eval_lc(self.c_constraints[i])
                    .ok_or(SynthesisError::AssignmentMissing)?;
                if a * b != c {
                    let trace;
                    #[cfg(feature = "std")]
                    {
                        trace = if self.constraint_traces.len() > i {
                            self.constraint_traces[i].as_ref().map_or_else(
                                || {
                                    eprintln!("Constraint trace requires enabling `ConstraintLayer` (or it was disabled by Xiang Fu)");
                                    format!("{}", i)
                                },
                                |t| format!("{}", t),
                            )
                        } else {
                            format!("{}", i)
                        };
                    }
                    #[cfg(not(feature = "std"))]
                    {
                        trace = format!("{}", i);
                    }
                    return Ok(Some(trace));
                }
            }
            Ok(None)
        }
    }

    /// Obtain the assignment corresponding to the `Variable` `v`.
    pub fn assigned_value(&self, v: Variable) -> Option<F> {
        let res = match v {
            Variable::One => Some(F::one()),
            Variable::Zero => Some(F::zero()),
            Variable::Witness(idx) => self.witness_assignment.get(idx).copied(),
            Variable::Instance(idx) => self.instance_assignment.get(idx).copied(),
            Variable::SymbolicLc(idx) => {
				let value = if self.lc_assignment_cache
					.borrow_mut().len()>idx.0{
					self.lc_assignment_cache.borrow_mut()[idx.0]
				}else{
					None
				};

                let ret = if value.is_some() {
                    value
                } else {
                    let value = self.eval_lc(idx)?;
					if self.lc_assignment_cache.borrow_mut().len()<idx.0+1{
						let resize_len = self.lc_assignment_cache.borrow_mut().len()*2;
						let resize_len = if resize_len<1024*512 {1024*512} else {resize_len};
						let resize_len = if resize_len<idx.0+1 {idx.0*2} else {resize_len};
						self.lc_assignment_cache.borrow_mut()
							.resize_with(resize_len, || None);
					}
                    self.lc_assignment_cache.borrow_mut()[idx.0] = Some(value);
                    Some(value)
                };
				ret
            },
        };
		res

    }
}
/// The A, B and C matrices of a Rank-One `ConstraintSystem`.
/// Also contains metadata on the structure of the constraint system
/// and the matrices.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintMatrices<F: Field> {
    /// The number of variables that are "public instances" to the constraint
    /// system.
    pub num_instance_variables: usize,
    /// The number of variables that are "private witnesses" to the constraint
    /// system.
    pub num_witness_variables: usize,
    /// The number of constraints in the constraint system.
    pub num_constraints: usize,
    /// The number of non_zero entries in the A matrix.
    pub a_num_non_zero: usize,
    /// The number of non_zero entries in the B matrix.
    pub b_num_non_zero: usize,
    /// The number of non_zero entries in the C matrix.
    pub c_num_non_zero: usize,

    /// The A constraint matrix. This is empty when
    /// `self.mode == SynthesisMode::Prove { construct_matrices = false }`.
    pub a: Matrix<F>,
    /// The B constraint matrix. This is empty when
    /// `self.mode == SynthesisMode::Prove { construct_matrices = false }`.
    pub b: Matrix<F>,
    /// The C constraint matrix. This is empty when
    /// `self.mode == SynthesisMode::Prove { construct_matrices = false }`.
    pub c: Matrix<F>,
}

/// A shared reference to a constraint system that can be stored in high level
/// variables.
#[derive(Debug, Clone)]
pub enum ConstraintSystemRef<F: Field> {
    /// Represents the case where we *don't* need to allocate variables or
    /// enforce constraints. Encountered when operating over constant
    /// values.
    None,
    /// Represents the case where we *do* allocate variables or enforce
    /// constraints.
    CS(Rc<RefCell<ConstraintSystem<F>>>),
}

impl<F: Field> PartialEq for ConstraintSystemRef<F> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::None, Self::None) => true,
            (..) => false,
        }
    }
}

impl<F: Field> Eq for ConstraintSystemRef<F> {}

/// A namespaced `ConstraintSystemRef`.
#[derive(Debug, Clone)]
pub struct Namespace<F: Field> {
    inner: ConstraintSystemRef<F>,
    id: Option<tracing::Id>,
}

impl<F: Field> From<ConstraintSystemRef<F>> for Namespace<F> {
    fn from(other: ConstraintSystemRef<F>) -> Self {
        Self {
            inner: other,
            id: None,
        }
    }
}

impl<F: Field> Namespace<F> {
    /// Construct a new `Namespace`.
    pub fn new(inner: ConstraintSystemRef<F>, id: Option<tracing::Id>) -> Self {
        Self { inner, id }
    }

    /// Obtain the inner `ConstraintSystemRef<F>`.
    pub fn cs(&self) -> ConstraintSystemRef<F> {
        self.inner.clone()
    }

    /// Manually leave the namespace.
    pub fn leave_namespace(self) {
        drop(self)
    }
}

impl<F: Field> Drop for Namespace<F> {
    fn drop(&mut self) {
        if let Some(id) = self.id.as_ref() {
            tracing::dispatcher::get_default(|dispatch| dispatch.exit(id))
        }
        //drop(&mut self.inner)
    }
}

impl<F: Field> ConstraintSystemRef<F> {
    /// Returns `self` if `!self.is_none()`, otherwise returns `other`.
    pub fn or(self, other: Self) -> Self {
        match self {
            ConstraintSystemRef::None => other,
            _ => self,
        }
    }

    /// Returns `true` is `self == ConstraintSystemRef::None`.
    pub fn is_none(&self) -> bool {
        matches!(self, ConstraintSystemRef::None)
    }

    /// Construct a `ConstraintSystemRef` from a `ConstraintSystem`.
    #[inline]
    pub fn new(inner: ConstraintSystem<F>) -> Self {
        Self::CS(Rc::new(RefCell::new(inner)))
    }

	/// made it public to access the instance
    pub fn inner(&self) -> Option<&Rc<RefCell<ConstraintSystem<F>>>> {
        match self {
            Self::CS(a) => Some(a),
            Self::None => None,
        }
    }

    /// Consumes self to return the inner `ConstraintSystem<F>`. Returns
    /// `None` if `Self::CS` is `None` or if any other references to
    /// `Self::CS` exist.  
    pub fn into_inner(self) -> Option<ConstraintSystem<F>> {
        match self {
            Self::CS(a) => Rc::try_unwrap(a).ok().map(|s| s.into_inner()),
            Self::None => None,
        }
    }

    /// Obtain an immutable reference to the underlying `ConstraintSystem`.
    ///
    /// # Panics
    /// This method panics if `self` is already mutably borrowed.
    #[inline]
    pub fn borrow(&self) -> Option<Ref<'_, ConstraintSystem<F>>> {
        self.inner().map(|cs| cs.borrow())
    }

    /// Obtain a mutable reference to the underlying `ConstraintSystem`.
    ///
    /// # Panics
    /// This method panics if `self` is already mutably borrowed.
    #[inline]
    pub fn borrow_mut(&self) -> Option<RefMut<'_, ConstraintSystem<F>>> {
        self.inner().map(|cs| cs.borrow_mut())
    }

    /// Set `self.mode` to `mode`.
    pub fn set_mode(&self, mode: SynthesisMode) {
        self.inner().map_or((), |cs| cs.borrow_mut().set_mode(mode))
    }

    /// Check whether `self.mode == SynthesisMode::Setup`.
    #[inline]
    pub fn is_in_setup_mode(&self) -> bool {
        self.inner()
            .map_or(false, |cs| cs.borrow().is_in_setup_mode())
    }

    /// Returns the number of constraints.
    #[inline]
    pub fn num_constraints(&self) -> usize {
        self.inner().map_or(0, |cs| cs.borrow().num_constraints)
    }

	/// return the number of linear combinations
	#[inline]
	pub fn num_lc(&self) -> usize{
		self.inner().map_or(0, |cs| cs.borrow().num_linear_combinations)
	}

	/// report the max lc_chain length of all linear combinations
	pub fn report_max_lc_len(&self)->usize{
		self.inner().map_or(0, |cs| cs.borrow().report_max_lc_len())
	}

    /// Returns the number of instance variables.
    #[inline]
    pub fn num_instance_variables(&self) -> usize {
        self.inner()
            .map_or(0, |cs| cs.borrow().num_instance_variables)
    }

    /// Returns the number of witness variables.
    #[inline]
    pub fn num_witness_variables(&self) -> usize {
        self.inner()
            .map_or(0, |cs| cs.borrow().num_witness_variables)
    }

    /// Check whether this constraint system aims to optimize weight,
    /// number of constraints, or neither.
    #[inline]
    pub fn optimization_goal(&self) -> OptimizationGoal {
        self.inner().map_or(OptimizationGoal::Constraints, |cs| {
            cs.borrow().optimization_goal()
        })
    }

    /// Specify whether this constraint system should aim to optimize weight,
    /// number of constraints, or neither.
    #[inline]
    pub fn set_optimization_goal(&self, goal: OptimizationGoal) {
        self.inner()
            .map_or((), |cs| cs.borrow_mut().set_optimization_goal(goal))
    }

    /// Check whether or not `self` will construct matrices.
    #[inline]
    pub fn should_construct_matrices(&self) -> bool {
        self.inner()
            .map_or(false, |cs| cs.borrow().should_construct_matrices())
    }

    /// Obtain a variable representing a new public instance input.
    #[inline]
    pub fn new_input_variable<Func>(&self, f: Func) -> crate::r1cs::Result<Variable>
    where
        Func: FnOnce() -> crate::r1cs::Result<F>,
    {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| {
                if !self.is_in_setup_mode() {
                    // This is needed to avoid double-borrows, because `f`
                    // might itself mutably borrow `cs` (eg: `f = || g.value()`).
                    let value = f();
                    cs.borrow_mut().new_input_variable(|| value)
                } else {
                    cs.borrow_mut().new_input_variable(f)
                }
            })
    }

    /// Obtain a variable representing a new private witness input.
    #[inline]
    pub fn new_witness_variable<Func>(&self, f: Func) -> crate::r1cs::Result<Variable>
    where
        Func: FnOnce() -> crate::r1cs::Result<F>,
    {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| {
                if !self.is_in_setup_mode() {
                    // This is needed to avoid double-borrows, because `f`
                    // might itself mutably borrow `cs` (eg: `f = || g.value()`).
                    let value = f();
                    cs.borrow_mut().new_witness_variable(|| value)
                } else {
                    cs.borrow_mut().new_witness_variable(f)
                }
            })
    }

    /// Obtain a variable representing a linear combination.
    #[inline]
    pub fn new_lc(&self, lc: LinearCombination<F>) -> crate::r1cs::Result<Variable> {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| cs.borrow_mut().new_lc(lc))
    }

    /// Enforce a R1CS constraint with the name `name`.
    #[inline(always)]
    pub fn enforce_constraint(
        &self,
        a: LinearCombination<F>,
        b: LinearCombination<F>,
        c: LinearCombination<F>,
    ) -> crate::r1cs::Result<()> {
        self.inner()
            .ok_or(SynthesisError::MissingCS)
            .and_then(|cs| cs.borrow_mut().enforce_constraint(a, b, c))
    }

    /// Naively inlines symbolic linear combinations into the linear
    /// combinations that use them.
    ///
    /// Useful for standard pairing-based SNARKs where addition gates are cheap.
    /// For example, in the SNARKs such as [\[Groth16\]](https://eprint.iacr.org/2016/260) and
    /// [\[Groth-Maller17\]](https://eprint.iacr.org/2017/540), addition gates
    /// do not contribute to the size of the multi-scalar multiplication, which
    /// is the dominating cost.
    pub fn inline_all_lcs(&self) {
        if let Some(cs) = self.inner() {
            cs.borrow_mut().inline_all_lcs()
        }
    }

    /// Finalize the constraint system (either by outlining or inlining,
    /// if an optimization goal is set).
    pub fn finalize(&self) {
        if let Some(cs) = self.inner() {
            cs.borrow_mut().finalize()
        }
    }

    /// This step must be called after constraint generation has completed, and
    /// after all symbolic LCs have been inlined into the places that they
    /// are used.
    #[inline]
    pub fn to_matrices(&self) -> Option<ConstraintMatrices<F>> {
        self.inner().and_then(|cs| cs.borrow().to_matrices())
    }

    /// If `self` is satisfied, outputs `Ok(true)`.
    /// If `self` is unsatisfied, outputs `Ok(false)`.
    /// If `self.is_in_setup_mode()` or if `self == None`, outputs `Err(())`.
    pub fn is_satisfied(&self) -> crate::r1cs::Result<bool> {
        self.inner()
            .map_or(Err(SynthesisError::AssignmentMissing), |cs| {
                cs.borrow().is_satisfied()
            })
    }

    /// If `self` is satisfied, outputs `Ok(None)`.
    /// If `self` is unsatisfied, outputs `Some(i)`, where `i` is the index of
    /// the first unsatisfied constraint.
    /// If `self.is_in_setup_mode()` or `self == None`, outputs `Err(())`.
    pub fn which_is_unsatisfied(&self) -> crate::r1cs::Result<Option<String>> {
        self.inner()
            .map_or(Err(SynthesisError::AssignmentMissing), |cs| {
                cs.borrow().which_is_unsatisfied()
            })
    }

    /// Obtain the assignment corresponding to the `Variable` `v`.
    pub fn assigned_value(&self, v: Variable) -> Option<F> {
        self.inner().and_then(|cs| cs.borrow().assigned_value(v))
    }

    /// Get trace information about all constraints in the system
    pub fn constraint_names(&self) -> Option<Vec<String>> {
        #[cfg(feature = "std")]
        {
            self.inner().and_then(|cs| {
                cs.borrow()
                    .constraint_traces
                    .iter()
                    .map(|trace| {
                        let mut constraint_path = String::new();
                        let mut prev_module_path = "";
                        let mut prefixes = ark_std::collections::BTreeSet::new();
                        for step in trace.as_ref()?.path() {
                            let module_path = if prev_module_path == step.module_path {
                                prefixes.insert(step.module_path.to_string());
                                String::new()
                            } else {
                                let mut parts = step
                                    .module_path
                                    .split("::")
                                    .filter(|&part| part != "r1cs_std" && part != "constraints");
                                let mut path_so_far = String::new();
                                for part in parts.by_ref() {
                                    if path_so_far.is_empty() {
                                        path_so_far += part;
                                    } else {
                                        path_so_far += &["::", part].join("");
                                    }
                                    if prefixes.contains(&path_so_far) {
                                        continue;
                                    } else {
                                        prefixes.insert(path_so_far.clone());
                                        break;
                                    }
                                }
                                parts.collect::<Vec<_>>().join("::") + "::"
                            };
                            prev_module_path = step.module_path;
                            constraint_path += &["/", &module_path, step.name].join("");
                        }
                        Some(constraint_path)
                    })
                    .collect::<Option<Vec<_>>>()
            })
        }
        #[cfg(not(feature = "std"))]
        {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::r1cs::*;
    use ark_ff::One;
    use ark_test_curves::bls12_381::Fr;

    #[test]
    fn matrix_generation() -> crate::r1cs::Result<()> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let two = Fr::one() + Fr::one();
        let a = cs.new_input_variable(|| Ok(Fr::one()))?;
        let b = cs.new_witness_variable(|| Ok(Fr::one()))?;
        let c = cs.new_witness_variable(|| Ok(two))?;
        cs.enforce_constraint(lc!() + a, lc!() + (two, b), lc!() + c)?;
        let d = cs.new_lc(lc!() + a + b)?;
        cs.enforce_constraint(lc!() + a, lc!() + d, lc!() + d)?;
        let e = cs.new_lc(lc!() + d + d)?;
        cs.enforce_constraint(lc!() + Variable::One, lc!() + e, lc!() + e)?;
        cs.inline_all_lcs();
        let matrices = cs.to_matrices().unwrap();
        assert_eq!(matrices.a[0], vec![(Fr::one(), 1)]);
        assert_eq!(matrices.b[0], vec![(two, 2)]);
        assert_eq!(matrices.c[0], vec![(Fr::one(), 3)]);

        assert_eq!(matrices.a[1], vec![(Fr::one(), 1)]);
        assert_eq!(matrices.b[1], vec![(Fr::one(), 1), (Fr::one(), 2)]);
        assert_eq!(matrices.c[1], vec![(Fr::one(), 1), (Fr::one(), 2)]);

        assert_eq!(matrices.a[2], vec![(Fr::one(), 0)]);
        assert_eq!(matrices.b[2], vec![(two, 1), (two, 2)]);
        assert_eq!(matrices.c[2], vec![(two, 1), (two, 2)]);
        Ok(())
    }

    #[test]
    fn matrix_generation_outlined() -> crate::r1cs::Result<()> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Weight);
        let two = Fr::one() + Fr::one();
        let a = cs.new_input_variable(|| Ok(Fr::one()))?;
        let b = cs.new_witness_variable(|| Ok(Fr::one()))?;
        let c = cs.new_witness_variable(|| Ok(two))?;
        cs.enforce_constraint(lc!() + a, lc!() + (two, b), lc!() + c)?;

        let d = cs.new_lc(lc!() + a + b)?;
        cs.enforce_constraint(lc!() + a, lc!() + d, lc!() + d)?;

        let e = cs.new_lc(lc!() + d + d)?;
        cs.enforce_constraint(lc!() + Variable::One, lc!() + e, lc!() + e)?;

        cs.finalize();
        assert!(cs.is_satisfied().unwrap());
        let matrices = cs.to_matrices().unwrap();
        assert_eq!(matrices.a[0], vec![(Fr::one(), 1)]);
        assert_eq!(matrices.b[0], vec![(two, 2)]);
        assert_eq!(matrices.c[0], vec![(Fr::one(), 3)]);

        assert_eq!(matrices.a[1], vec![(Fr::one(), 1)]);
        // Notice here how the variable allocated for d is outlined
        // compared to the example in previous test case.
        // We are optimising for weight: there are less non-zero elements.
        assert_eq!(matrices.b[1], vec![(Fr::one(), 4)]);
        assert_eq!(matrices.c[1], vec![(Fr::one(), 4)]);

        assert_eq!(matrices.a[2], vec![(Fr::one(), 0)]);
        assert_eq!(matrices.b[2], vec![(two, 4)]);
        assert_eq!(matrices.c[2], vec![(two, 4)]);
        Ok(())
    }

    /// Example meant to follow as closely as possible the excellent R1CS
    /// write-up by [Vitalik Buterin](https://vitalik.ca/general/2016/12/10/qap.html)
    /// and demonstrate how to construct such matrices in arkworks.
    #[test]
    fn matrix_generation_example() -> crate::r1cs::Result<()> {
        let cs = ConstraintSystem::<Fr>::new_ref();
        // helper definitions
        let three = Fr::from(3u8);
        let five = Fr::from(5u8);
        let nine = Fr::from(9u8);
        // There will be six variables in the system, in the order governed by adding
        // them to the constraint system (Note that the CS is initialised with
        // `Variable::One` in the first position implicitly).
        // Note also that the all public variables will always be placed before all witnesses
        //
        // Variable::One
        // Variable::Instance(35)
        // Variable::Witness(3) ( == x )
        // Variable::Witness(9) ( == sym_1 )
        // Variable::Witness(27) ( == y )
        // Variable::Witness(30) ( == sym_2 )

        // let one = Variable::One; // public input, implicitly defined
        let out = cs.new_input_variable(|| Ok(nine * three + three + five))?; // public input
        let x = cs.new_witness_variable(|| Ok(three))?; // explicit witness
        let sym_1 = cs.new_witness_variable(|| Ok(nine))?; // intermediate witness variable
        let y = cs.new_witness_variable(|| Ok(nine * three))?; // intermediate witness variable
        let sym_2 = cs.new_witness_variable(|| Ok(nine * three + three))?; // intermediate witness variable

        cs.enforce_constraint(lc!() + x, lc!() + x, lc!() + sym_1)?;
        cs.enforce_constraint(lc!() + sym_1, lc!() + x, lc!() + y)?;
        cs.enforce_constraint(lc!() + y + x, lc!() + Variable::One, lc!() + sym_2)?;
        cs.enforce_constraint(
            lc!() + sym_2 + (five, Variable::One),
            lc!() + Variable::One,
            lc!() + out,
        )?;

        cs.finalize();
        assert!(cs.is_satisfied().unwrap());
        let matrices = cs.to_matrices().unwrap();
        // There are four gates(constraints), each generating a row.
        // Resulting matrices:
        // (Note how 2nd & 3rd columns are swapped compared to the online example.
        // This results from an implementation detail of placing all Variable::Instances(_) first.
        //
        // A
        // [0, 0, 1, 0, 0, 0]
        // [0, 0, 0, 1, 0, 0]
        // [0, 0, 1, 0, 1, 0]
        // [5, 0, 0, 0, 0, 1]
        // B
        // [0, 0, 1, 0, 0, 0]
        // [0, 0, 1, 0, 0, 0]
        // [1, 0, 0, 0, 0, 0]
        // [1, 0, 0, 0, 0, 0]
        // C
        // [0, 0, 0, 1, 0, 0]
        // [0, 0, 0, 0, 1, 0]
        // [0, 0, 0, 0, 0, 1]
        // [0, 1, 0, 0, 0, 0]
        assert_eq!(matrices.a[0], vec![(Fr::one(), 2)]);
        assert_eq!(matrices.b[0], vec![(Fr::one(), 2)]);
        assert_eq!(matrices.c[0], vec![(Fr::one(), 3)]);

        assert_eq!(matrices.a[1], vec![(Fr::one(), 3)]);
        assert_eq!(matrices.b[1], vec![(Fr::one(), 2)]);
        assert_eq!(matrices.c[1], vec![(Fr::one(), 4)]);

        assert_eq!(matrices.a[2], vec![(Fr::one(), 2), (Fr::one(), 4)]);
        assert_eq!(matrices.b[2], vec![(Fr::one(), 0)]);
        assert_eq!(matrices.c[2], vec![(Fr::one(), 5)]);

        assert_eq!(matrices.a[3], vec![(five, 0), (Fr::one(), 5)]);
        assert_eq!(matrices.b[3], vec![(Fr::one(), 0)]);
        assert_eq!(matrices.c[3], vec![(Fr::one(), 1)]);
        Ok(())
    }
}
