/* 
	Created 08/30/2024. SuperNova version compared with circuit.rs
	Revised 10/07/2024. Added the cyclepair instance.
	Revised 10/12/2024. Added optional b_full_mode to allow dual mode.
*/

/// contains [Nova](https://eprint.iacr.org/2021/370.pdf) related circuits
use utils::{logger::{log_perf, emit_stdout, LOG5}, timer::Timer as GTimer};
use ark_crypto_primitives::sponge::{
    constraints::{AbsorbGadget, CryptographicSpongeVar},
    poseidon::{constraints::PoseidonSpongeVar, PoseidonConfig},
    Absorb, CryptographicSponge,
};
use ark_ec::{CurveGroup, Group};
use ark_ff::{Field,PrimeField,BigInteger};
//use crate::transcript::AbsorbNonNative;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    groups::GroupOpsBounds,
    prelude::CurveVar,
    uint8::UInt8,
    R1CSVar, ToConstraintFieldGadget,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::{fmt::Debug, One, Zero};
use core::{borrow::Borrow, marker::PhantomData};

use crate::folding::foldpot::{
	CommittedInstance, 
	circuits::{CommittedInstanceVarFoldPot, 
//		ChallengeGadgetFoldPot
	},
	sigma_ir1cs::{SigmaIR1CS,ZiPartTwoInst,LookupTableTwoCol,CyclePairInput,CyclePairInputVar,GadgetMapper},
	mod_super::{CommittedInstanceFoldPotSuper},
	cyclepair::{CyclePairCommittedInstanceVar,CyclePairChallengeGadget, NIFSFullGadgetCyclePair,cp_io_len},
	utils::{B_DEBUG},
	
};
use super::{CommittedInstanceFoldPot, FOLDPOT_CF_N_POINTS};
use crate::constants::N_BITS_RO;
use crate::folding::circuits::{
    cyclefold::{
        cf_io_len, CycleFoldChallengeGadget, CycleFoldCommittedInstanceVar, NIFSFullGadget,
    },
    nonnative::{affine::NonNativeAffineVar, uint::NonNativeUintVar},
    CF1, CF2,
};
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNativeGadget, Transcript, TranscriptVar};


/// convert a field element to usize (at best effort) - 32-bit
pub fn field_to_usize<F:PrimeField>(v: &F)->usize{
	let bytes = v.into_bigint().to_bytes_le();
	let b4 = [bytes[0], bytes[1], bytes[2], bytes[3]];
	let uvalue = u32::from_le_bytes(b4);
	let res = uvalue as usize;
	let v2 = F::from(uvalue);
	assert!(*v==v2);

	res
}

/// convert a field element to usize (at best effort)
pub fn field_to_u64<F:PrimeField>(v: &F)->u64{
	let bytes = v.into_bigint().to_bytes_le();
	let b8 = [bytes[0], bytes[1], bytes[2], bytes[3], 
		bytes[4], bytes[5], bytes[6], bytes[7]];
	let uvalue = u64::from_le_bytes(b8);
	let v2 = F::from(uvalue);
	assert!(*v==v2);

	uvalue	
}


/// Corresponds to CommittedInstanceFoldPotSuper
#[derive(Debug, Clone)]
pub struct CommittedInstanceVarFoldPotSuper<C: CurveGroup>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
	/// the vector of CommittedInstance, one for each circuit
	pub vec_inst: Vec<CommittedInstanceVarFoldPot<C>>,
	/// global x_1 value for Hash(cycle_fold_U)
	/// NOTE: for all committed instances, only its x[0] will be checked,
	/// their x[1] is moved out as global x_1 because we keep only one copy
	/// of cyclefold gadget.
	pub x_1: FpVar<C::ScalarField>,
	/// Hash of (cycle_pair_U) - Added
	pub x_2: Option<FpVar<C::ScalarField>>,
	/// the circuit ID to USE when fold with incoming instance.
	pub pc_i: FpVar<C::ScalarField>,
}

impl <C:CurveGroup> CommittedInstanceVarFoldPotSuper<C>
where <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField{
	pub fn dump(&self, msg: &str){
		for i in 0..self.vec_inst.len(){
			let inst = &self.vec_inst[i];
			emit_stdout(format!(
				"{}:   {}: cmE: ({}, {}), u: ({:?}), \
				cmW: ({},{}), x: ({:?},{:?}), cmF: ({}, {})",
				msg, i,
				inst.cmE.x.value().unwrap(),
				inst.cmE.y.value().unwrap(),
				inst.u.value().unwrap(),
				inst.cmW.x.value().unwrap(),
				inst.cmW.y.value().unwrap(),
				inst.x[0].value().unwrap(),
				inst.x[1].value().unwrap(),
				inst.cmF.x.value().unwrap(),
				inst.cmF.y.value().unwrap()));
		}
		emit_stdout(format!(
			"{}:  x_1: {:?}, x_2: {:?}, pc_i: {:?}",
			msg, self.x_1, self.x_2, self.pc_i));
	}
}

impl<C> AllocVar<CommittedInstanceFoldPotSuper<C>, CF1<C>> for 
CommittedInstanceVarFoldPotSuper<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: PrimeField,
{
    fn new_variable<T: Borrow<CommittedInstanceFoldPotSuper<C>>>(
        cs: impl Into<Namespace<CF1<C>>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|cis| { 
			//cis is an instance of CommittedInstanceFoldPotSuper
			let cs = cs.into();
			let mut vec_inst = vec![];
			let _x_1 = cis.borrow().x_1.clone();
			let _x_2 = cis.borrow().x_2.clone();
			for val in &cis.borrow().vec_inst{
				let new_inst = CommittedInstanceVarFoldPot
					::new_variable(cs.clone(), || Ok(val), mode)?;
				vec_inst.push(new_inst);
			}
			let _zero = C::ScalarField::zero();
            let x_1 = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(cis.borrow().x_1.clone()), mode)?;
			let b_full = cis.borrow().x_2.is_some();
            let x_2 = if b_full {Some(FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(cis.borrow().x_2.clone().unwrap()), mode).unwrap())} else {None};
			let pc_i = FpVar::<C::ScalarField>::new_variable(cs.clone(), || Ok(cis.borrow().pc_i.clone()), mode)?;
            Ok(Self {vec_inst, x_1: x_1, x_2: x_2, pc_i: pc_i})
        })
    }
}

impl<C> AbsorbGadget<C::ScalarField> for CommittedInstanceVarFoldPotSuper<C>
where
    C: CurveGroup,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    fn to_sponge_bytes(&self) -> Result<Vec<UInt8<C::ScalarField>>, SynthesisError> {
        unimplemented!()
    }

    fn to_sponge_field_elements(&self) -> Result<Vec<FpVar<C::ScalarField>>, SynthesisError> {
		let mut vec_res = vec![];
		for x in &self.vec_inst{
			let mut res = x.to_sponge_field_elements()?;
			vec_res.append(&mut res);
		}
		let mut res1 = self.x_1.to_sponge_field_elements()?;
		vec_res.append(&mut res1);
		if self.x_2.is_some(){
			let mut resx2 = self.x_2.to_sponge_field_elements()?;
			vec_res.append(&mut resx2);
		}
		let mut res2 = self.pc_i.to_sponge_field_elements()?;
		vec_res.append(&mut res2);

		Ok( vec_res )
    }
}

impl<C> CommittedInstanceVarFoldPotSuper<C>
where
    C: CurveGroup,
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
	/// hash() corresponds to CommittedInstanceFoldPotSuper in mods_super.rs
    #[allow(clippy::type_complexity)]
    pub fn hash<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        self,
        sponge: &T,
        pp_hash: FpVar<CF1<C>>,
        i: FpVar<CF1<C>>,
        pc_i: FpVar<CF1<C>>,
        z_0: Vec<FpVar<CF1<C>>>,
        z_i: Vec<FpVar<CF1<C>>>,
    ) -> Result<(FpVar<CF1<C>>, Vec<FpVar<CF1<C>>>), SynthesisError> {
        let mut sponge = sponge.clone();
        let U_vec = self.to_sponge_field_elements()?;


        sponge.absorb(&pp_hash)?;
        sponge.absorb(&i)?;
        sponge.absorb(&pc_i)?;
        sponge.absorb(&z_0)?;
        sponge.absorb(&z_i)?;
        sponge.absorb(&U_vec)?;

        let res =  
			Ok((sponge.squeeze_field_elements(1)?.pop().unwrap(), U_vec));
	
		res
    }
}


/// ChallengeGadget computes the RO challenge used for the Nova instances NIFS, it contains a
/// rust-native and a in-circuit compatible versions.
/// NOTE: only very syntax change for taking CommitedInstanceFoldPot (one
/// more cmF element)
pub struct ChallengeGadgetFoldPotSuper<C: CurveGroup> {
    _c: PhantomData<C>,
}
impl<C: CurveGroup> ChallengeGadgetFoldPotSuper<C>
where
    C: CurveGroup,
    <C as CurveGroup>::BaseField: PrimeField,
    <C as Group>::ScalarField: Absorb,
{
    pub fn get_challenge_native<T: Transcript<C::ScalarField>>(
        transcript: &mut T,
        pp_hash: C::ScalarField, // public params hash
        U_i: CommittedInstanceFoldPotSuper<C>,
        u_i: CommittedInstanceFoldPot<C>,
        cmT: C,
    ) -> Vec<bool> {
        transcript.absorb(&pp_hash);
        transcript.absorb(&U_i);
        transcript.absorb(&u_i);
        transcript.absorb_nonnative(&cmT);
        transcript.squeeze_bits(N_BITS_RO)
    }

    // compatible with the native get_challenge_native
    pub fn get_challenge_gadget<S: CryptographicSponge, T: TranscriptVar<CF1<C>, S>>(
        transcript: &mut T,
        pp_hash: FpVar<CF1<C>>,      // public params hash
        U_i_vec: Vec<FpVar<CF1<C>>>, // apready processed input, so we don't have to recompute these values
        u_i: CommittedInstanceVarFoldPot<C>,
        cmT: NonNativeAffineVar<C>,
    ) -> Result<Vec<Boolean<C::ScalarField>>, SynthesisError> {

        transcript.absorb(&pp_hash)?;
        transcript.absorb(&U_i_vec)?;
        transcript.absorb(&u_i)?;
        transcript.absorb_nonnative(&cmT)?;
        transcript.squeeze_bits(N_BITS_RO)
    }
}

/// Compared with the AgumentedF Circuit in circuits.rs,
/// make the change to accommodate the array of committed instances
/// NOTE specifically we do NOT model the phi function in supernova,
/// which generates the next `pc_i+1`. The value of `pc_i+1` is
/// embedded as a nondeterministic advice in the StatementInstance.
/// The phi function simply checks its validity (in range).
/// The reason is that for the word-batch processing problem,
/// any circuit in the collection of non-uniform circuits is valid,
/// the difference is their efficiency. We just pick the best fit,
/// and the best fit `pc_i+1` is determined outside of the circuit by
/// FoldPot driver.
///
/// When the b_full_mode is set, it checks cyclepair constraints,
/// and require the F circuits to be full mode
#[derive(Debug, Clone)]
pub struct AugmentedFCircuitFoldPotSuper<
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    FC: FCircuit<CF1<C1>> + SigmaIR1CS<H, CF1<C1>,LK, GM>,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
	const H: bool,
> where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
	pub _gm: PhantomData<GM>,
	pub _lk: PhantomData<LK>,
    pub _gc2: PhantomData<GC2>,
    pub poseidon_config: PoseidonConfig<CF1<C1>>,
    pub pp_hash: Option<CF1<C1>>,
    pub i: Option<CF1<C1>>,
    pub i_usize: Option<usize>,
    pub z_0: Option<Vec<C1::ScalarField>>,
	pub z0_part2_inst: Option<ZiPartTwoInst<C1::ScalarField>>, //Added
    pub z_i: Option<Vec<C1::ScalarField>>,
	pub zi_part2_inst: Option<ZiPartTwoInst<C1::ScalarField>>, //Added
    pub external_inputs: Option<Vec<C1::ScalarField>>,
    pub u_i_cmW: Option<C1>,
    pub u_i_cmF: Option<C1>, //new element compared with Nova
    pub U_i: Option<CommittedInstanceFoldPotSuper<C1>>,
    pub U_i1_cmE: Option<C1>,
    pub U_i1_cmW: Option<C1>,
    pub U_i1_cmF: Option<C1>, //new elemeent compared with Nova
    pub cmT: Option<C1>,
    pub F: FC,              // F circuit
    pub x: Option<CF1<C1>>, // public input (u_{i+1}.x[0])

    // cyclefold verifier on C1
    // Here 'cf1, cf2, cf3' are for each of the CycleFold circuits, corresponding to the fold of cmW,cmE, cmF respectively
    pub cf1_u_i_cmW: Option<C2>,               // input
    pub cf2_u_i_cmW: Option<C2>,               // input
    pub cf3_u_i_cmW: Option<C2>,               // input, ADDED
    pub cf_U_i: Option<CommittedInstance<C2>>, // input, normal NOVA ins
    pub cf1_cmT: Option<C2>,
    pub cf2_cmT: Option<C2>,
    pub cf3_cmT: Option<C2>, //ADDED
    pub cf_x: Option<CF1<C1>>, // public input (u_{i+1}.x[1])

	// cyclepair verifier on C1
    pub cp_u_i_cmW: Option<C2>,    // the cmW (committed witness of cyclepair).
    pub cp_U_i: Option<CommittedInstance<C2>>, // committed inst of cyclepair 
    pub cp_x: Option<CF1<C1>>, // public input (u_{i+1}.x[2]) (hash of next)
	pub cp_cm_T: Option<C2>, //commitment of cmT in committed instance
	pub b_full_mode: bool, //full mode means checking cyclepair logic

	// Added for super_nova
	/// the number of circuits in supernova (regard it as hard coded)
	pub n_circ: usize,
	/// j, the Fj to compute `z_{i+1}` = Fj(z_i), regard it as hard coded
	pub j: C1::ScalarField,

	/// precomputed commitment to the Fixed segment (if its available)
	pub precomputed_cmF: Option<C1>,

	pub job_id: usize,
}


impl<C1: CurveGroup, C2: CurveGroup, GC2: CurveVar<C2, CF2<C2>>, LK, FC: FCircuit<CF1<C1>> + SigmaIR1CS<H, CF1<C1>, LK, GM>, GM, const H: bool>
    AugmentedFCircuitFoldPotSuper<C1, C2, GC2, LK, FC, GM, H>
where
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	LK: LookupTableTwoCol<C1::ScalarField>,
	<C1 as Group>::ScalarField: Absorb,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
{
	/// NOTE that F_circuit's full_mode decides its full mode
    pub fn empty(poseidon_config: &PoseidonConfig<CF1<C1>>, mut F_circuit: FC, n_circ: usize, j: usize, job_id: usize)->Self{
		let mut dummy_external_inputs = F_circuit.gen_dummy_stmt();
		// make pc_i1 part to be consistent with j
		dummy_external_inputs[1] = C1::ScalarField::from(j as u32);
		// this synthesis only feeds extract_r1cs; the dummy stmt has
		// no m_share fill, so quiet the hab22 assert (S109)
		F_circuit.set_keygen_synth(true);
		let zero = C1::ScalarField::zero();
		let b_full = F_circuit.is_full_mode();
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let zi_dummy= ZiPartTwoInst::new(zero, zero, poseidon_config, b_full, fq_bits, job_id);
        Self {
			_gm: PhantomData,
            _lk: PhantomData,
            _gc2: PhantomData,
            poseidon_config: poseidon_config.clone(),
            pp_hash: None,
            i: None,
            i_usize: None,
            z_0: None,
			z0_part2_inst: Some(zi_dummy.clone()),
            z_i: None,
			zi_part2_inst: Some(zi_dummy),
            external_inputs: Some(dummy_external_inputs),
            u_i_cmW: None,
            u_i_cmF: None, //new element
            U_i: None,
            U_i1_cmE: None,
            U_i1_cmW: None,
            U_i1_cmF: None, //new element
            cmT: None,
            F: F_circuit,
            x: None,
            // cyclefold values
            cf1_u_i_cmW: None,
            cf2_u_i_cmW: None,
            cf3_u_i_cmW: None, //Added for FoldPot
            cf_U_i: None,
            cf1_cmT: None,
            cf2_cmT: None,
            cf3_cmT: None, //Added for FoldPot
            cf_x: None,
			// cyclepair values
			cp_u_i_cmW: None,
			cp_U_i: None,
			cp_cm_T: None,
			cp_x: None,
			b_full_mode: b_full,

			n_circ: n_circ, //dummy anway. but make at least one circ
			j: C1::ScalarField::from(j as u32),
			precomputed_cmF: None,
			job_id,
        }
    }
}


impl<C1, C2, GC2, LK, FC, GM, const H: bool> ConstraintSynthesizer<CF1<C1>> 
for AugmentedFCircuitFoldPotSuper<C1, C2, GC2, LK, FC, GM, H >
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    FC: FCircuit<CF1<C1>> + SigmaIR1CS<H, CF1<C1>, LK, GM, C=C1 >,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
{
    fn generate_constraints(self, cs: ConstraintSystemRef<CF1<C1>>) -> Result<(), SynthesisError> {
		let b_debug = B_DEBUG; //should be the same as
			//mod_super.generate_constraints.b_debug
			//as the CS is set up with no matrix mode when not b_debug
		let log_level = LOG5;
		let mut gt1 = GTimer::new();
		let (mut nc, mut nv) = (cs.num_constraints(), cs.num_witness_variables());
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs: START: cs: {}, vars: {}",
				cs.num_constraints(),
				cs.num_witness_variables()), 
		&mut gt1);

		//1. retrieve pp_hash, i, z_0, and z_i as Var (witness)
		let stmt = self.external_inputs.clone().expect("stmt empty"); 
        let pp_hash = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.pp_hash.clone().unwrap_or_else(CF1::<C1>::zero))
        })?;
        let i = FpVar::<CF1<C1>>::new_witness(cs.clone(), || {
            Ok(self.i.unwrap_or_else(CF1::<C1>::zero))
        })?;
        let z_0 = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_0
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
        let z_i = Vec::<FpVar<CF1<C1>>>::new_witness(cs.clone(), || {
            Ok(self
                .z_i
                .unwrap_or(vec![CF1::<C1>::zero(); self.F.state_len()]))
        })?;
		log_perf(self.job_id, log_level, &format!(
				"-- circuit_super gen_cs step 1: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();


		//2. retrieve pc_i and pc_i1 (j) from the statement instance
		// verify the validity of pc_i1. Note that they are ALL
		// field elements.
		let pc_i_val = stmt[0]; //see sigma_ir1cs.rs
		let pc_i1_val = stmt[1]; //see sigma_ir1cs.rs
		let _pc_0_val = C1::ScalarField::zero();
		let _pc_i_usize = field_to_usize(&pc_i_val);
		assert!(pc_i1_val == self.j, "statement.pc_i1: {} != self.j {}",
			pc_i1_val, self.j);

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ assert!(csat.unwrap(), "step 2 of circuitsuper"); }
		}
		log_perf(self.job_id, log_level,&format!(
				"-- circuit_super gen_cs step 2: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		//3. Compute z_{i+1} from the F circuit and use it as Witness to
		// construct Var
		let pre_cmF = self.precomputed_cmF;
        let i_usize = self.i_usize.unwrap_or(0);
 		let (witness, wit_cfg, z_i1_part2) = 
  			self.F.gen_witness(&stmt, &self.zi_part2_inst.clone().unwrap(),
				pre_cmF);
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 3.0 generate wit: cs: {}, vars: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

  		let wtns_vec = witness.to_vec_fp_var(cs.clone(), &wit_cfg);
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 3.1: to_vec_fp_var: cs: {}, vars: {}, wtns_vec: {}",
			cs.num_constraints() - nc,
			cs.num_witness_variables() - nv,
			wtns_vec.len()), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ 
				assert!(csat.unwrap(), "step 2.5 of circuitsuper"); 
			}
		}

		//S105a: at i=0 the step function must run on z_0, not on the
		//free witness z_i -- otherwise the chain that S104 builds
		//bottoms out on a state the prover picked.
		//PLACEMENT IS LOAD-BEARING: is_basecase must be computed
		//strictly AFTER to_vec_fp_var (:498) and before this call.
		//FpVar::is_zero allocates witness variables, and
		//sigma_ir1cs.rs:2468 asserts the witness count on entry to
		//to_vec_fp_var is 0 or 6 because start_F = 12 is hard-coded
		//(mod.rs:452). Hoisting it any higher panics there -- and
		//without that assert it would silently mis-slice the folded
		//cmF window.
		let is_basecase = i.is_zero()?;
		let mut z_in: Vec<FpVar<CF1<C1>>> = vec![];
		for k in 0..z_i.len(){
			z_in.push(is_basecase.select(&z_0[k], &z_i[k])?);
		}
        let z_i1 = self.F
                 .generate_step_constraints(cs.clone(), i_usize, z_in, wtns_vec)?;

		log_perf(self.job_id, log_level,&format!( 
			"-- circuit_super gen_cs step 3.2: gen_step_cs cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ 
				assert!(csat.unwrap(), "step 2.6 of circuitsuper"); 
			}
		}

		if b_debug{
			let zi1_part2_hash = z_i1_part2.hash(&self.poseidon_config);
			assert!(z_i1[1].value()? == zi1_part2_hash);
		}
		//S105a: is_basecase is now computed above, just before the step
		//call, and reused here.

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ 
				assert!(csat.unwrap(), "step 2.7 of circuitsuper"); 
			}
		}

        let u_dummy = if self.b_full_mode {//x has 3 elements for full version
		 CommittedInstanceFoldPotSuper::dummy(3, self.n_circ, self.b_full_mode)
		}else{
		 CommittedInstanceFoldPotSuper::dummy(2, self.n_circ, self.b_full_mode)
		};
        let U_i = CommittedInstanceVarFoldPotSuper::<C1>::new_witness(cs.clone(), || {
            Ok(self.U_i.unwrap_or(u_dummy.clone()))
        })?;

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ 
				assert!(csat.unwrap(), "step 3 of circuitsuper"); 
			}
		}

		log_perf(self.job_id, log_level,&format!( 
			"-- circuit_super gen_cs step 3.4 others: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		//4. Construct U_i1_cmE, cmW, cmF from the hints
		// and cyclefold related variables from hints
		// they will be verified by cyclefold circuit.
        let U_i1_cmE = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmE.unwrap_or_else(C1::zero))
        })?;
        let U_i1_cmW = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmW.unwrap_or_else(C1::zero))
        })?;
		// added cmF logic here for foldpot
        let U_i1_cmF = NonNativeAffineVar::new_witness(cs.clone(), || {
            Ok(self.U_i1_cmF.unwrap_or_else(C1::zero))
        })?;
		//println!(">> step 3");
        let cmT =
            NonNativeAffineVar::new_witness(cs.clone(), || Ok(self.cmT.unwrap_or_else(C1::zero)))?;

        let cf_u_dummy = CommittedInstance::<C2>::dummy(cf_io_len(FOLDPOT_CF_N_POINTS)); 
        let cf_U_i = CycleFoldCommittedInstanceVar::<C2, GC2>::new_witness(cs.clone(), || {
            Ok(self.cf_U_i.unwrap_or(cf_u_dummy.clone()))
        })?;

		
		let cp_u_dummy = CommittedInstance::<C2>::dummy(cp_io_len());

        let cf1_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf1_cmT.unwrap_or_else(C2::zero)))?;
        let cf2_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf2_cmT.unwrap_or_else(C2::zero)))?;
        let cf3_cmT = GC2::new_witness(cs.clone(), || Ok(self.cf3_cmT.unwrap_or_else(C2::zero)))?;


        // `sponge` is for digest computation.
        // `transcript` is for challenge generation.
        let sponge = PoseidonSpongeVar::<C1::ScalarField>::new(cs.clone(), &self.poseidon_config);
        let mut transcript = sponge.clone();

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ 
				assert!(csat.unwrap(), "step 4 of circuitsuper"); 
			}
		}
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 4: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		//5. compute u_i.x as Var
        // u_i.x[0] = H(i, pc_i, z_0, z_i, U_i) (as Supernova)
		// note U_i is already a vector of folded instances
		let pc_i1 = FpVar::<C1::ScalarField>::new_witness(cs.clone(),
			|| Ok(pc_i1_val)).unwrap();
		let pc_i = FpVar::<C1::ScalarField>::new_witness(cs.clone(),
			|| Ok(pc_i_val)).unwrap();
        let (u_i_x, U_i_vec) = U_i.clone().hash(
            &sponge,
            pp_hash.clone(),
            i.clone(),
			pc_i.clone(),
            z_0.clone(),
            z_i.clone(),
        )?;

        // u_i.x[1] = H(cf_U_i)
        let (cf_u_i_x, cf_U_i_vec) = cf_U_i.clone().hash(&sponge, pp_hash.clone())?;
		let (cp_u_i_x, cp_U_i_vec, cp_U_i) = if self.b_full_mode{
			// u_i.x[2] = H(cp_U_i) (if b_full_mode)
			let cp_U_i = CyclePairCommittedInstanceVar::<C2,GC2>
				::new_witness(cs.clone(), || {
					Ok(self.cp_U_i.unwrap_or(cp_u_dummy.clone()))
				})?;
			let (cp_u_i_x, cp_U_i_vec) = 
				cp_U_i.clone().hash(&sponge, pp_hash.clone())?;
			(Some(cp_u_i_x), Some(cp_U_i_vec), Some(cp_U_i))
		}else {(None,None,None)};

		if b_debug{
			let csat = cs.is_satisfied();
			if csat.is_ok(){ 
				assert!(csat.unwrap(), "step 6 of circuitsuper"); 
			}
		}
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 5: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

        //6. Construct u_i Var from hints
        let u_i = CommittedInstanceVarFoldPot {
            // u_i.cmE = cm(0)
            cmE: NonNativeAffineVar::new_constant(cs.clone(), C1::zero())?,
            // u_i.u = 1
            u: FpVar::one(),
            // u_i.cmW is provided by the prover as witness
            cmW: NonNativeAffineVar::new_witness(cs.clone(), || {
                Ok(self.u_i_cmW.unwrap_or(C1::zero()))
            })?,
            // u_i.x is computed in step 1
            x: if self.b_full_mode { vec![u_i_x, cf_u_i_x, cp_u_i_x.unwrap()] 
				}else{ vec![u_i_x, cf_u_i_x] },
            cmF: NonNativeAffineVar::new_witness(cs.clone(), || {
                Ok(self.u_i_cmF.unwrap_or(C1::zero()))
            })?,
        };
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 6: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();


        //7. compute the Fiat-shamir challenge
        // compute r = H(u_i, U_i, cmT)
		// since this is fed to cyclepair, convert to NonNativeUintVar
        let r_bits = ChallengeGadgetFoldPotSuper::<C1>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            U_i_vec,
            u_i.clone(), //note that only pass u_i
            cmT.clone(),
        )?;
        let r = Boolean::le_bits_to_fp_var(&r_bits)?;
        let r_nonnat = {
            let mut bits = r_bits.clone(); //RECOVER LATER drop clone
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 7: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		//8. using the hints/advice (in Augmented structure) construct
		// the Var instance of U_i1[pc_i]. Note that its
		// x and u and directly computed using r nonce in circuit,
		// but the cmE, cmW, and cmF are GIVEN AS ADVICE,
		// which is LATER CHECKED in cyclefold circuit. 
		let mut new_u = FpVar::zero();
		let mut new_x_0 = FpVar::zero(); //hash(U_i..)
		let mut new_x_1 = FpVar::zero(); //for hash(cyclefold_U_i)
		let mut new_x_2 = FpVar::zero(); //for hash(cyclepair_U_i), optional
		for i in 0..self.n_circ{
			//NOTE: have to use select  in a loop.
			//otherwise will result in different R1CS for pc_i value
			let fp_i = FpVar::new_constant(cs.clone(), 
				C1::ScalarField::from(i as u32))?;
			let b_eq = fp_i.is_eq(&pc_i)?;
			new_u = b_eq.select(&U_i.vec_inst[i].u, &new_u)?;
			new_x_0 = b_eq.select(&U_i.vec_inst[i].x[0], &new_x_0)?;
			new_x_1 = b_eq.select(&U_i.vec_inst[i].x[1], &new_x_1)?;
			if self.b_full_mode{
				new_x_2 = b_eq.select(&U_i.vec_inst[i].x[2], &new_x_2)?;
			}
		}
		new_u = &new_u + &r * &u_i.u;
		new_x_0 = &new_x_0 + &r * &u_i.x[0];
		new_x_1 = &new_x_1 + &r * &u_i.x[1];
		if self.b_full_mode{
			new_x_2 = &new_x_2 + &r * &u_i.x[2];
		}
		let Ui1_pci = CommittedInstanceVarFoldPot{
			u: new_u, 
			x: if self.b_full_mode { vec![new_x_0, new_x_1, new_x_2] }
				else{ vec![new_x_0, new_x_1]},
			cmE: U_i1_cmE.clone(), cmW: U_i1_cmW.clone(), cmF: U_i1_cmF.clone()
		};
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 8: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

		//9. build the U_i1 var version. Note that to amke sure that
		// r1cs is generated for all possible pc_i values, we cannot
		// directly set U_i1[pc_i] = Ui1_pci. Instead, we have to do
		// a select statement.
		let mut U_i1 = U_i.clone(); //Var
		let _j_val = field_to_usize(&self.j);


		let global_U_i_x1 = U_i.x_1.clone(); 
		let global_U_i_x2 = U_i.x_2;
		let global_u_i_x1 = u_i.x[1].clone(); 
		let global_u_i_x2 = if self.b_full_mode {Some(u_i.x[2].clone())}
			else {None}; 
		let global_U_i1_x1 = &global_U_i_x1 + &r * &global_u_i_x1; 
		let global_U_i1_x2 = if self.b_full_mode{
			Some(global_U_i_x2.unwrap() + &r * &global_u_i_x2.unwrap())
		}else{None};
		U_i1.x_1 = global_U_i1_x1; //coz we only do one copy of Hash(cf_Ui)
		U_i1.x_2 = global_U_i1_x2; 
		U_i1.pc_i = pc_i1.clone(); //the one to fold U_i1 (to compute u_i1)



		for i in 0..self.n_circ{//use select to determine value
			let fp_i = FpVar::new_constant(cs.clone(), 
				C1::ScalarField::from(i as u32))?;
			let b_eq= pc_i.is_eq(&fp_i)?;
			U_i1.vec_inst[i] = b_eq.select(&Ui1_pci, &U_i1.vec_inst[i])?;
		}

		//10.  compute and check the first output of F'
        // Base case: u_{i+1}.x[0] == H((i+1, pc_i+1, z_0, z_{i+1}, U_{\bot})
        // Non-base case: u_{i+1}.x[0] == H((i+1, pc_i+1, z_0, z_{i+1}, U_{i+1})
        let (u_i1_x, _) = U_i1.clone().hash(
            &sponge,
            pp_hash.clone(),
            i.clone() + FpVar::<CF1<C1>>::one(),
			pc_i1.clone(),
            z_0.clone(),
            z_i1.clone(),
        )?;
		let mut c_ui1_base = CommittedInstanceVarFoldPotSuper::
				new_constant(cs.clone(), u_dummy)?;
		c_ui1_base.pc_i = pc_i1.clone(); //to be consistent with
			//U_i1 in mod_super.rs::U_i1 for the base case
			//and also u_dumm1.pc_i in mod_super.rs
        let (u_i1_x_base, _) = c_ui1_base.hash(
            &sponge,
            pp_hash.clone(),
            FpVar::<CF1<C1>>::one(),
			pc_i1.clone(),
            z_0.clone(),
            z_i1.clone(),
        )?;
        let x = FpVar::new_input(cs.clone(), || Ok(self.x.unwrap_or(u_i1_x_base.value()?)))?;
        x.enforce_equal(&is_basecase.select(&u_i1_x_base, &u_i1_x)?)?;


		//REMOVE LATER ----------- RECOVER BELOW
		//if b_debug{
		//REMOVE LATER ----------- BELOW
		if b_debug{
			let b1 = is_basecase.value()?;
			let x1 = u_i1_x.value()?;
			let x1_base = u_i1_x_base.value()?;
			let expect_x = if b1 {x1_base} else {x1};
			let x_value = x.value()?;
			assert!(expect_x == x_value);
		}
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 9: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();

        //11. CycleFold part
        // C.1. Compute cf1_u_i.x and cf2_u_i.x
		// Note the base value are retrieved from the pc_i's element of U_i
		// Again: have to ues a loop to do a select
		let mut U_i_cmW_x = U_i.vec_inst[0].cmW.x.clone();
		let mut U_i_cmW_y = U_i.vec_inst[0].cmW.y.clone();
		let mut U_i1_cmW_x = U_i1.vec_inst[0].cmW.x.clone();
		let mut U_i1_cmW_y = U_i1.vec_inst[0].cmW.y.clone();

		let mut U_i_cmF_x = U_i.vec_inst[0].cmF.x.clone();
		let mut U_i_cmF_y = U_i.vec_inst[0].cmF.y.clone();
		let mut U_i1_cmF_x = U_i1.vec_inst[0].cmF.x.clone();
		let mut U_i1_cmF_y = U_i1.vec_inst[0].cmF.y.clone();

		let mut U_i_cmE_x = U_i.vec_inst[0].cmE.x.clone();
		let mut U_i_cmE_y = U_i.vec_inst[0].cmE.y.clone();
		let mut U_i1_cmE_x = U_i1.vec_inst[0].cmE.x.clone();
		let mut U_i1_cmE_y = U_i1.vec_inst[0].cmE.y.clone();

		for i in 0..self.n_circ{
			let fp_i = FpVar::new_constant(cs.clone(), 
				C1::ScalarField::from(i as u32))?;
			let b_eq= pc_i.is_eq(&fp_i)?;
			U_i_cmW_x = b_eq.select(&U_i.vec_inst[i].cmW.x, &U_i_cmW_x)?;
			U_i_cmW_y = b_eq.select(&U_i.vec_inst[i].cmW.y, &U_i_cmW_y)?;
			U_i1_cmW_x = b_eq.select(&U_i1.vec_inst[i].cmW.x, &U_i1_cmW_x)?;
			U_i1_cmW_y = b_eq.select(&U_i1.vec_inst[i].cmW.y, &U_i1_cmW_y)?;

			U_i_cmF_x = b_eq.select(&U_i.vec_inst[i].cmF.x, &U_i_cmF_x)?;
			U_i_cmF_y = b_eq.select(&U_i.vec_inst[i].cmF.y, &U_i_cmF_y)?;
			U_i1_cmF_x = b_eq.select(&U_i1.vec_inst[i].cmF.x, &U_i1_cmF_x)?;
			U_i1_cmF_y = b_eq.select(&U_i1.vec_inst[i].cmF.y, &U_i1_cmF_y)?;

			U_i_cmE_x = b_eq.select(&U_i.vec_inst[i].cmE.x, &U_i_cmE_x)?;
			U_i_cmE_y = b_eq.select(&U_i.vec_inst[i].cmE.y, &U_i_cmE_y)?;
			U_i1_cmE_x = b_eq.select(&U_i1.vec_inst[i].cmE.x, &U_i1_cmE_x)?;
			U_i1_cmE_y = b_eq.select(&U_i1.vec_inst[i].cmE.y, &U_i1_cmE_y)?;
		}

        let cfW_x = vec![
            r_nonnat.clone(),
            //U_i.vec_inst[pci_val].cmW.x.clone(),
            //U_i.vec_inst[pci_val].cmW.y.clone(),
			U_i_cmW_x,
			U_i_cmW_y,
            u_i.cmW.x,
            u_i.cmW.y,
            //U_i1.vec_inst[pci_val].cmW.x.clone(),
            //U_i1.vec_inst[pci_val].cmW.y.clone(),
			U_i1_cmW_x,
			U_i1_cmW_y,
        ];
        let cfF_x = vec![
            r_nonnat.clone(),
            //U_i.vec_inst[pci_val].cmF.x.clone(),
            //U_i.vec_inst[pci_val].cmF.y.clone(),
			U_i_cmF_x,
			U_i_cmF_y,
            u_i.cmF.x,
            u_i.cmF.y,
            //U_i1.vec_inst[pci_val].cmF.x.clone(),
            //U_i1.vec_inst[pci_val].cmF.y.clone(),
			U_i1_cmF_x,
			U_i1_cmF_y,
        ];
        let cfE_x = vec![
            r_nonnat, 
			//U_i.vec_inst[pci_val].cmE.x.clone(), 
			//U_i.vec_inst[pci_val].cmE.y.clone(), 
			U_i_cmE_x,
			U_i_cmE_y,
			cmT.x, 
			cmT.y, 
			//U_i1.vec_inst[pci_val].cmE.x.clone(), 
			//U_i1.vec_inst[pci_val].cmE.y.clone(),
			U_i1_cmE_x,
			U_i1_cmE_y,
        ];
        // ensure that cf1_u & cf2_u have as public inputs the cmW & cmE from main instances U_i,
        // u_i, U_i+1 coordinates of the commitments
        // C.2. Construct `cf1_u_i` and `cf2_u_i`
        let cf1_u_i = CycleFoldCommittedInstanceVar {
            // cf1_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf1_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf1_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf1_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf1_u_i.x is computed in step 1
            x: cfW_x,
        };
        let cf2_u_i = CycleFoldCommittedInstanceVar {
            // cf2_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf2_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf2_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf2_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf2_u_i.x is computed in step 1
            x: cfE_x,
        };
		// cf3 is the ADDED cyclefold component for folding cmF
        let cf3_u_i = CycleFoldCommittedInstanceVar {
            // cf3_u_i.cmE = 0
            cmE: GC2::zero(),
            // cf3_u_i.u = 1
            u: NonNativeUintVar::new_constant(cs.clone(), C1::BaseField::one())?,
            // cf3_u_i.cmW is provided by the prover as witness
            cmW: GC2::new_witness(cs.clone(), || Ok(self.cf3_u_i_cmW.unwrap_or(C2::zero())))?,
            // cf3_u_i.x is computed in step 1
            x: cfF_x,
        };


        // C.3. nifs.verify, 
		// obtains cf1_U_{i+1} by folding cf1_u_i & cf_U_i, 
		// and then cf2_U_{i+1} by folding cf2_u_i & cf1_U_{i+1}. - original
		// and then cf3_U{i+1} again by folding cf3_u_i & cf2_U_{i+1}. (added)

        // compute cf1_r = H(cf1_u_i, cf_U_i, cf1_cmT)
        // cf_r_bits is denoted by rho* in the paper.
        let cf1_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf_U_i_vec,
            cf1_u_i.clone(),
            cf1_cmT.clone(),
        )?;
        // Convert cf1_r_bits to a `NonNativeFieldVar`

        let cf1_r_nonnat = {
            let mut bits = cf1_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        // Fold cf1_u_i & cf_U_i into cf1_U_{i+1}
        let cf1_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf1_r_bits,
            cf1_r_nonnat,
            cf1_cmT,
            cf_U_i,
            cf1_u_i,
        )?;


        // same for cf2_r:
        let cf2_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf1_U_i1.to_native_sponge_field_elements()?,
            cf2_u_i.clone(),
            cf2_cmT.clone(),
        )?;
        let cf2_r_nonnat = {
            let mut bits = cf2_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        let cf2_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf2_r_bits,
            cf2_r_nonnat,
            cf2_cmT,
            cf1_U_i1, // the output from NIFS.V(cf1_r, cf_U, cfE_u)
            cf2_u_i,
        )?;

		//ADDED -----
        // same for cf3_r:
        let cf3_r_bits = CycleFoldChallengeGadget::<C2, GC2>::get_challenge_gadget(
            &mut transcript,
            pp_hash.clone(),
            cf2_U_i1.to_native_sponge_field_elements()?,
            cf3_u_i.clone(),
            cf3_cmT.clone(),
        )?;
        let cf3_r_nonnat = {
            let mut bits = cf3_r_bits.clone();
            bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, Boolean::FALSE);
            NonNativeUintVar::from(&bits)
        };
        let cf3_U_i1 = NIFSFullGadget::<C2, GC2>::fold_committed_instance(
            cf3_r_bits,
            cf3_r_nonnat,
            cf3_cmT,
            cf2_U_i1.clone(), // the output from NIFS.V(cf1_r, cf_U, cfE_u)
            cf3_u_i.clone(),
        )?;

        // Back to Primary Part
        // P.4.b compute and check the second output of F'
        // Base case: u_{i+1}.x[1] == H(cf_U_{\bot})
        // Non-base case: u_{i+1}.x[1] == H(cf_U_{i+1})
        let (cf_u_i1_x, _) = cf3_U_i1.clone().hash(&sponge, pp_hash.clone())?;
        let (cf_u_i1_x_base, _) =
            CycleFoldCommittedInstanceVar::new_constant(cs.clone(), cf_u_dummy)?
                .hash(&sponge, pp_hash.clone())?;
        let cf_x = FpVar::new_input(cs.clone(), || {
            Ok(self.cf_x.unwrap_or(cf_u_i1_x_base.value()?))
        })?;
		let exp_cf_x = is_basecase.select(&cf_u_i1_x_base, &cf_u_i1_x)?;
        cf_x.enforce_equal(&exp_cf_x)?;
		if B_DEBUG {
			assert!(exp_cf_x.value()?==cf_x.value()?, "exp_cf_x error");
		}
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 11: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);
		nc = cs.num_constraints();
		nv = cs.num_witness_variables();


		//12. Cyclepair part only if it's full mode
		if self.b_full_mode{
			//1. read the input
			let ci:CyclePairInput<CF1<C1>>=z_i1_part2.cyclepair_input.unwrap();				let cpi= CyclePairInputVar::from(cs.clone(), &ci);
			//NOTE: x should be 32 elements (NonNativeUint essentially
			//captures 32 Fq elements), so that they can be involved in
			//R1CS computation in the decider proof
		
			//2. build the committed instance of cyclepair
			let cp_u_i = CyclePairCommittedInstanceVar{
				cmE: GC2::zero(), //essentally x,y in Fr
				u: NonNativeUintVar::new_constant(cs.clone(), 
					C1::BaseField::one())?, //NonNative for Fq, in Fr
				cmW: GC2::new_witness(cs.clone(),|| 
					Ok(self.cp_u_i_cmW.unwrap_or(C2::zero())))?, //same as cmE
				x: cpi.x, //NonNative for array of Fqs, in Fr.
			};

			//3. create the folding factor r (should be over Fq), as nonnative
        	let cp_cmT = GC2::new_witness(cs.clone(), 
				|| Ok(self.cp_cm_T.unwrap_or_else(C2::zero)))?;
        	let cp_r_bits = CyclePairChallengeGadget::<C2, GC2>
				::get_challenge_gadget(
				&mut transcript,
				pp_hash.clone(),
				cp_U_i_vec.unwrap().clone(),
				cp_u_i.clone(),
				cp_cmT.clone(),
			)?;
        	let cp_r_nonnat = {
            	let mut bits = cp_r_bits.clone();
            	bits.resize(C1::BaseField::MODULUS_BIT_SIZE as usize, 
					Boolean::FALSE);
            	NonNativeUintVar::from(&bits)
			};

			//4. fold cp_U_i and cp_u_i into cp_U_i1
			let cp_U_i1 = NIFSFullGadgetCyclePair
				::<C2,GC2>::fold_committed_instance(
				cp_r_bits,
				cp_r_nonnat,
				cp_cmT,
				cp_U_i.unwrap(),
				cp_u_i
			)?;

			//5. compute and check the u_{i+1}.x[2] = H(cp_U_i1)
        	let (cp_u_i1_x, _) = cp_U_i1.clone().hash(&sponge, 
				pp_hash.clone())?;
			let cp_u_dummy_x_len = cp_u_dummy.x.len();
        	let (cp_u_i1_x_base, _) = CyclePairCommittedInstanceVar::
				new_constant(cs.clone(), cp_u_dummy)?
                .hash(&sponge, pp_hash)?;
			assert!(cp_U_i1.x.len() == cp_u_dummy_x_len);
			if self.b_full_mode && !is_basecase.value()?{
				assert!(self.cp_x.is_some());
			}
        	let cp_x = FpVar::new_input(cs.clone(), || {
            	Ok(self.cp_x.unwrap_or(cp_u_i1_x_base.value()?))
        	})?;
			let exp_cp_x = is_basecase.select(&cp_u_i1_x_base, &cp_u_i1_x)?;
        	cp_x.enforce_equal(&exp_cp_x)?;

			if B_DEBUG {
				assert!(exp_cp_x.value()?==cp_x.value()?, "exp_cp_x error");
			}

        }; //end of cyclepair part


		if b_debug{
			if cs.is_satisfied().is_ok(){ 
				assert!(cs.is_satisfied().unwrap());
			}
		}
		log_perf(self.job_id, log_level, &format!(
			"-- circuit_super gen_cs step 12: cs: {}, vars: {}",
				cs.num_constraints() - nc,
				cs.num_witness_variables() - nv), &mut gt1);

        Ok(())
    }
}

#[cfg(test)]
pub mod tests_circuits_super {
    use super::*;
    use ark_bn254::{Fr, G1Projective as Projective};
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_ff::BigInteger;
    use ark_relations::r1cs::ConstraintSystem;
    use ark_std::UniformRand;
    use crate::transcript::poseidon::poseidon_canonical_config;

    #[test]
    fn test_committed_instance_var_super() {
        let mut rng = ark_std::test_rng();
		let cs = ConstraintSystem::<Fr>::new_ref();

		let n_circ = 5;
		let mut vec_inst = vec![];
		let mut vec_ci = vec![];
		for _i in 0..n_circ{ 
			let ci = CommittedInstanceFoldPot::<Projective> {
				cmE: Projective::rand(&mut rng),
				u: Fr::rand(&mut rng),
				cmW: Projective::rand(&mut rng),
				cmF: Projective::rand(&mut rng), //not even need to ensure a part
												 //W, because the circuit only 
												 //checks random combination
				x: vec![Fr::rand(&mut rng); 1],
			};

			let ciVar =
				CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
			vec_inst.push(ciVar);
			vec_ci.push(ci);
		}
		let x_1_val = Fr::rand(&mut rng);
		let x_2_val = Fr::rand(&mut rng);
		let x_1 = FpVar::<Fr>::new_witness(cs.clone(), || Ok(x_1_val))
			.unwrap();
		let x_2 = FpVar::<Fr>::new_witness(cs.clone(), || Ok(x_2_val))
			.unwrap();
		let pc_i_val = Fr::rand(&mut rng);
		let pc_i= FpVar::<Fr>::new_witness(cs.clone(), || Ok(pc_i_val))
			.unwrap();
		let cis = CommittedInstanceVarFoldPotSuper{vec_inst: vec_inst, 
			x_1: x_1, x_2: Some(x_2), pc_i: pc_i};

		for i in 0..n_circ{
			let ciVar = &cis.vec_inst[i];
			let ci = &vec_ci[i];
			assert_eq!(ciVar.u.value().unwrap(), ci.u);
			assert_eq!(ciVar.x.value().unwrap(), ci.x);
		}
		assert!(cis.x_1.value().unwrap()==x_1_val);
        // the values cmE and cmW are checked in the CycleFold's circuit
        // CommittedInstanceInCycleFoldVar in
        // nova::cyclefold::tests::test_committed_instance_cyclefold_var
    }

    #[test]
    fn test_committed_instance_hash() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let sponge = PoseidonSponge::<Fr>::new(&poseidon_config);
        let pp_hash = Fr::from(42u32); // only for test

        let i = Fr::from(3_u32);
        let z_0 = vec![Fr::from(3_u32)];
        let z_i = vec![Fr::from(3_u32)];
        let cs = ConstraintSystem::<Fr>::new_ref();

		let n_circ = 5;
		let mut vec_inst = vec![];
		let mut vec_ci = vec![];
		for _i in 0..n_circ{ 
			let ci = CommittedInstanceFoldPot::<Projective> {
				cmE: Projective::rand(&mut rng),
				u: Fr::rand(&mut rng),
				cmW: Projective::rand(&mut rng),
				cmF: Projective::rand(&mut rng), //not even need to ensure a part
												 //W, because the circuit only 
												 //checks random combination
				x: vec![Fr::rand(&mut rng); 1],
			};

			let ciVar =
				CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
			vec_inst.push(ciVar);
			vec_ci.push(ci);
		}
		let x_1_val = Fr::rand(&mut rng);
		let x_2_val = Fr::rand(&mut rng);
		let pc_i_val = Fr::rand(&mut rng);
		let _x_1 = FpVar::<Fr>::new_witness(cs.clone(), || Ok(x_1_val))
			.unwrap();
		let _x_2 = FpVar::<Fr>::new_witness(cs.clone(), || Ok(x_2_val))
			.unwrap();
		let cis = CommittedInstanceFoldPotSuper{vec_inst: vec_ci, 
			x_1: x_1_val, x_2: Some(x_2_val), pc_i: pc_i_val};
		let pc_i = Fr::from(2_u32);
		let _pc_i1 = Fr::from(7_u32);

        // compute the CommittedInstance hash natively
        let h = cis.hash(&sponge, pp_hash, i, pc_i, z_0.clone(), z_i.clone());


        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let iVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(i)).unwrap();
		let pciVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pc_i)).unwrap();
        let z_0Var = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_0.clone())).unwrap();
        let z_iVar = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z_i.clone())).unwrap();
        let cisVar =
            CommittedInstanceVarFoldPotSuper::<Projective>::new_witness(cs.clone(), || Ok(cis.clone())).unwrap();

        let sponge = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);
        // compute the CommittedInstance hash in-circuit
        let (hVar, _) = cisVar
            .hash(&sponge, pp_hashVar, iVar, pciVar, z_0Var, z_iVar)
            .unwrap();
        assert!(cs.is_satisfied().unwrap());

        // check that the natively computed and in-circuit computed hashes match
        assert_eq!(hVar.value().unwrap(), h);
    }

    // checks that the gadget and native implementations of the challenge computation match
    #[test]
    fn test_challenge_gadget() {
        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let mut transcript = PoseidonSponge::<Fr>::new(&poseidon_config);

		//1. build u_i
        let u_i = CommittedInstanceFoldPot::<Projective> {
            cmE: Projective::rand(&mut rng),
            u: Fr::rand(&mut rng),
            cmW: Projective::rand(&mut rng),
            x: vec![Fr::rand(&mut rng); 1],
            cmF: Projective::rand(&mut rng),
        };

		//2. build U_i
        let cs = ConstraintSystem::<Fr>::new_ref();
		let n_circ = 5;
		let mut vec_inst = vec![];
		let mut vec_ci = vec![];
		for _i in 0..n_circ{ 
			let ci = CommittedInstanceFoldPot::<Projective> {
				cmE: Projective::rand(&mut rng),
				u: Fr::rand(&mut rng),
				cmW: Projective::rand(&mut rng),
				cmF: Projective::rand(&mut rng), //not even need to ensure a part
												 //W, because the circuit only 
												 //checks random combination
				x: vec![Fr::rand(&mut rng); 1],
			};

			let ciVar =
				CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(ci.clone())).unwrap();
			vec_inst.push(ciVar);
			vec_ci.push(ci);
		}
		let x_1_val = Fr::rand(&mut rng);
		let x_2_val = Fr::rand(&mut rng);
		let pc_i_val = Fr::rand(&mut rng);
		let U_i= CommittedInstanceFoldPotSuper{vec_inst: vec_ci, 
			x_1: x_1_val, x_2: Some(x_2_val), pc_i: pc_i_val};

		//3. pc_i and pc_i1
		let _pc_i = Fr::from(2_u32);
		let _pc_i1 = Fr::from(7_u32);
        let cmT = Projective::rand(&mut rng);
        let pp_hash = Fr::from(42u32); // only for testing

        //4. compute the challenge natively
        let r_bits = ChallengeGadgetFoldPotSuper::<Projective>::get_challenge_native(
            &mut transcript,
            pp_hash,
            U_i.clone(),
            u_i.clone(),
            cmT,
        );
        let r = Fr::from_bigint(BigInteger::from_bits_le(&r_bits)).unwrap();

        let pp_hashVar = FpVar::<Fr>::new_witness(cs.clone(), || Ok(pp_hash)).unwrap();
        let u_iVar =
            CommittedInstanceVarFoldPot::<Projective>::new_witness(cs.clone(), || Ok(u_i.clone()))
                .unwrap();
        let U_iVar =
            CommittedInstanceVarFoldPotSuper::<Projective>::new_witness(cs.clone(), || Ok(U_i.clone()))
                .unwrap();
        let cmTVar = NonNativeAffineVar::<Projective>::new_witness(cs.clone(), || Ok(cmT)).unwrap();
        let mut transcriptVar = PoseidonSpongeVar::<Fr>::new(cs.clone(), &poseidon_config);

        //5. compute the challenge in-circuit
		let U_iVar_vec = U_iVar.to_sponge_field_elements().unwrap();
        let r_bitsVar = ChallengeGadgetFoldPotSuper::<Projective>::get_challenge_gadget(
            &mut transcriptVar,
            pp_hashVar,
            U_iVar_vec,
            u_iVar,
            cmTVar,
        )
        .unwrap();
        assert!(cs.is_satisfied().unwrap());
		//println!("CHALLENGE GADGET SUPER DONE");

        // check that the natively computed and in-circuit computed hashes match
        let rVar = Boolean::le_bits_to_fp_var(&r_bitsVar).unwrap();
        assert_eq!(rVar.value().unwrap(), r);
        assert_eq!(r_bitsVar.value().unwrap(), r_bits);
    }
}
