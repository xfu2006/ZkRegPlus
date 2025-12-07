/// Implements the scheme described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf).
/// Modified from the NOVA scheme: by adding ONE Pedersen commitment to the
/// ``fixed memory" in the witness (those who do not depend on the
/// Fiat-Shamir random challenges).

/* Modified 08/09/2024 */

use std::{rc::Rc, cell::RefCell};
//use crate::folding::foldpot::utils::Timer;
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_ec::{AffineRepr, CurveGroup, Group, short_weierstrass::SWCurveConfig};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::fmt::Debug;
use ark_std::rand::RngCore;
use ark_std::{One, UniformRand, Zero};
use core::marker::PhantomData;

use crate::commitment::CommitmentScheme;
use crate::folding::circuits::cyclefold::{fold_cyclefold_circuit, CycleFoldCircuit};
use crate::folding::circuits::CF2;
use crate::frontend::FCircuit;
use crate::transcript::{AbsorbNonNative, Transcript};
use crate::utils::vec::is_zero_vec;
use crate::Error;
use crate::FoldingScheme;
use crate::{
    arith::r1cs::{extract_r1cs, extract_w_x, R1CS},
    utils::{get_cm_coordinates, pp_hash},
	folding::nova,
	folding::nova::{
		Witness, CommittedInstance,
		traits::NovaR1CS,
		//PreprocessorParam, ProverParams, VerifierParams,
	},
	folding::foldpot::{
		nifs::{NIFSFoldPot},
		circuits::{ChallengeGadgetFoldPot,AugmentedFCircuitFoldPot},
		sigma_ir1cs::{SigmaIR1CS,LookupTableTwoCol,ZiPartTwoInst,
			StatementInst,GadgetMapper},
	}
};

//inherited from nova + cyclefold
pub mod utils;
pub mod sigma_ir1cs;
pub mod nifs;
pub mod circuits;
pub mod nonnative_group;
pub mod from_field;
pub mod batch_proc;
pub mod sigma_cyclepair;
pub mod container_config;


// for super-nova version
pub mod mod_super;
pub mod qa_nizk;
pub mod decider_eth_circuit_super;
pub mod cyclepair;
pub mod circuits_super;


pub mod driver;
pub mod veccom;

//use circuits::{AugmentedFCircuit, ChallengeGadget};
//use traits::NovaR1CS;

/// Number of points to be folded in the CycleFold circuit, same
/// as Nova; difference: we have 3 cyclefold circuits (one additional
/// for folding cmF - fixed memory's commitments)
const FOLDPOT_CF_N_POINTS: usize = 2_usize;

#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct CommittedInstanceFoldPot<C: CurveGroup> {
    pub cmE: C,
    pub u: C::ScalarField,
    pub cmW: C,
    pub x: Vec<C::ScalarField>,
	/// Commitment to the Fixed Memory (it has a fixed structure in cmW)
	/// First |F| elements in W.
    pub cmF: C,
}

impl<C:CurveGroup> Into<CommittedInstance<C>> for CommittedInstanceFoldPot<C>{
	fn into(self)->CommittedInstance<C>{
		CommittedInstance::<C>{
			cmE: self.cmE,
			u: self.u,
			cmW: self.cmW,
			x: self.x
		}
	}
}
impl<C: CurveGroup> CommittedInstanceFoldPot<C> {
    pub fn dummy(io_len: usize) -> Self {
        Self {
            cmE: C::zero(),
            u: C::ScalarField::zero(),
            cmW: C::zero(),
            x: vec![C::ScalarField::zero(); io_len],
			cmF: C::zero(),
        }
    }
}

impl<C: CurveGroup> Absorb for CommittedInstanceFoldPot<C>
where
    C::ScalarField: Absorb,
{
    fn to_sponge_bytes(&self, _dest: &mut Vec<u8>) {
        // This is never called
        unimplemented!()
    }

    fn to_sponge_field_elements<F: PrimeField>(&self, dest: &mut Vec<F>) {
        self.u.to_sponge_field_elements(dest);
        self.x.to_sponge_field_elements(dest);
        // We cannot call `to_native_sponge_field_elements(dest)` directly, as
        // `to_native_sponge_field_elements` needs `F` to be `C::ScalarField`,
        // but here `F` is a generic `PrimeField`.
        self.cmE
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
        self.cmW
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
        self.cmF
            .to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(dest);
    }
}

impl<C: CurveGroup> AbsorbNonNative<C::BaseField> for 
CommittedInstanceFoldPot<C>
where
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField + Absorb,
{
    // Compatible with the in-circuit `CycleFoldCommittedInstanceVar::to_native_sponge_field_elements`
    // in `cyclefold.rs`.
    fn to_native_sponge_field_elements(&self, dest: &mut Vec<C::BaseField>) {
        [self.u].to_native_sponge_field_elements(dest);
        self.x.to_native_sponge_field_elements(dest);
        let (cmE_x, cmE_y) = match self.cmE.into_affine().xy() {
            Some((&x, &y)) => (x, y),
            None => (C::BaseField::zero(), C::BaseField::zero()),
        };
        let (cmW_x, cmW_y) = match self.cmW.into_affine().xy() {
            Some((&x, &y)) => (x, y),
            None => (C::BaseField::zero(), C::BaseField::zero()),
        };
        let (cmF_x, cmF_y) = match self.cmF.into_affine().xy() {
            Some((&x, &y)) => (x, y),
            None => (C::BaseField::zero(), C::BaseField::zero()),
        };
        cmE_x.to_sponge_field_elements(dest);
        cmE_y.to_sponge_field_elements(dest);
        cmW_x.to_sponge_field_elements(dest);
        cmW_y.to_sponge_field_elements(dest);
        cmF_x.to_sponge_field_elements(dest);
        cmF_y.to_sponge_field_elements(dest);

    }
}

impl<C: CurveGroup> CommittedInstanceFoldPot<C>
where
    <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField,
{
    /// hash implements the committed instance hash compatible with the gadget implemented in
    /// nova/circuits.rs::CommittedInstanceVar.hash.
    /// Returns `H(i, z_0, z_i, U_i)`, where `i` can be `i` but also `i+1`, and `U_i` is the
    /// `CommittedInstance`.
    pub fn hash<T: Transcript<C::ScalarField>>(
        &self,
        sponge: &T,
        pp_hash: C::ScalarField, // public params hash
        i: C::ScalarField,
        z_0: Vec<C::ScalarField>,
        z_i: Vec<C::ScalarField>,
    ) -> C::ScalarField {
        let mut sponge = sponge.clone();

        sponge.absorb(&pp_hash);
        sponge.absorb(&i);
        sponge.absorb(&z_0);
        sponge.absorb(&z_i);
        sponge.absorb(&self);
        let res = sponge.squeeze_field_elements(1)[0];

		res
    }
}


#[derive(Debug, Clone, Eq, PartialEq, CanonicalSerialize, CanonicalDeserialize)]
pub struct WitnessFoldPot<C: CurveGroup> {
    pub E: Vec<C::ScalarField>,
    pub rE: C::ScalarField,
    pub W: Vec<C::ScalarField>,
    pub rW: C::ScalarField,
	/// size of F (it is the first size_F elements of W) 
	pub size_F: usize,
	/// index of F in the AugmentedFCircuit (4 + external_inp.len)
	pub start_F: usize,
	/// random for PedCom of F
	pub rF: C::ScalarField,
}

impl<C:CurveGroup> Into<Witness<C>> for WitnessFoldPot<C>
where
    <C as Group>::ScalarField: Absorb{
	fn into(self) -> Witness<C>{
		Witness::<C>{
			E: self.E,
			rE: self.rE,
			W: self.W,
			rW: self.rW
		}
	}
}

impl<C: CurveGroup> WitnessFoldPot<C>
where
    <C as Group>::ScalarField: Absorb,
{
	/// start_F: the starting position of Fixed Mem segment in AugmentedCircuit
	/// witness, size_F: the size of the fixed mem segment
    pub fn new<const H: bool>(w: Vec<C::ScalarField>, e_len: usize, rng: &mut impl RngCore, size_F: usize, start_F: usize) -> Self {
        let (rW, rE, rF) = if H {
            (
                C::ScalarField::rand(rng),
                C::ScalarField::rand(rng),
                C::ScalarField::rand(rng),
            )
        } else {
            (C::ScalarField::zero(), C::ScalarField::zero(), 
				C::ScalarField::zero())
        };

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            rE,
            W: w,
            rW,
			size_F: size_F,
			rF,
			start_F,
        }
    }

    pub fn dummy(w_len: usize, e_len: usize) -> Self {
        let (rW, rE, rF) = (C::ScalarField::zero(), C::ScalarField::zero(),
			C::ScalarField::zero());
        let w = vec![C::ScalarField::zero(); w_len];

        Self {
            E: vec![C::ScalarField::zero(); e_len],
            rE,
            W: w,
            rW,
			size_F: 1, //always guaranteed for const 1 in witness
			rF: rF,
			start_F: 0, //dummy value
        }
    }

    pub fn commit<CS: CommitmentScheme<C, HC>, const HC: bool>(
        &self,
        params: &CS::ProverParams,
        x: Vec<C::ScalarField>,
    ) -> Result<CommittedInstanceFoldPot<C>, Error> {
        let mut cmE = C::zero();
        if !is_zero_vec::<C::ScalarField>(&self.E) {
            cmE = CS::commit(params, &self.E, &self.rE)?;
        }
        let cmW = CS::commit(params, &self.W, &self.rW)?;
		// logically start_F is 0
		let (start_F, _size_F) = (self.start_F, self.size_F);
		let vecF = self.W[start_F .. start_F+self.size_F].to_vec();

        let cmF = CS::commit(params, &vecF, &self.rF)?;
        Ok(CommittedInstanceFoldPot{
            cmE,
            u: C::ScalarField::one(),
            cmW,
            x,
			cmF: cmF
        })
    }
}

#[derive(Debug, Clone)]
pub struct PreprocessorParamFoldPot<C1, C2, FC, CS1, CS2, LK, GM, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H,C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
{
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    pub F: FC,
    // cs params if not provided, will be generated at the preprocess method
    pub cs_pp: Option<CS1::ProverParams>,
    pub cs_vp: Option<CS1::VerifierParams>,
    pub cf_cs_pp: Option<CS2::ProverParams>, //cyclefold
    pub cf_cs_vp: Option<CS2::VerifierParams>,
    pub cp_cs_pp: Option<CS2::ProverParams>, //cyclepair
    pub cp_cs_vp: Option<CS2::VerifierParams>,
	/// lookup table. We require ALL points to the same lookup table
	/// for non-uniform circuits in the supernova system.
	/// shoudl call setup_lookup RIGHT AFTER init
	pub lk_tbl: Rc<RefCell<LK>>,
	pub size_F: usize,
	/// index of F in the AugmentedFCircuit (4 + external_inp.len)
	pub start_F: usize,
	_gm: PhantomData<GM>,
}

impl<C1, C2, FC, CS1, CS2, LK, GM, const H: bool> PreprocessorParamFoldPot<C1, C2, FC, CS1, CS2, LK, GM, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H,C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
{
    pub fn new(poseidon_config: PoseidonConfig<C1::ScalarField>, F: FC, lk: Rc<RefCell<LK>>, size_F: usize) -> Self {
		let start_F = 12;
							//because there are 6 vars (pp_hash, i,z_0 (2 ele), 
							//z_i (2 ele) - see gen_constraints of circuit.rs)
							//before F.witness in AugFCirc.
							//Plus the sum of cmF_size (4)
							// + extra_var_size (2) of Wit
							// that's where statement starts
        Self {
			_gm: PhantomData,
            poseidon_config,
            F,
            cs_pp: None,
            cs_vp: None,
            cf_cs_pp: None,
            cf_cs_vp: None,
            cp_cs_pp: None,
            cp_cs_vp: None,
			lk_tbl: lk, 
			size_F: size_F, 
			start_F: start_F,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ProverParamsFoldPot<C1, C2, CS1, CS2, LK, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    pub cs_pp: CS1::ProverParams,
    pub cf_cs_pp: CS2::ProverParams,
    pub cp_cs_pp: CS2::ProverParams,
	/// size of Fixed Memory segment in Witness
	pub size_F: usize,
	/// index of F in the AugmentedFCircuit (4 + external_inp.len)
	pub start_F: usize,
	/// reference to lookup table
	pub lk_tbl: Rc<RefCell<LK>>,
	/// the size of cs_pp
	pub cs_pp_len: usize,
}

#[derive(Debug, Clone)]
pub struct VerifierParamsFoldPot<C1, C2, CS1, CS2, const H: bool>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    pub r1cs: R1CS<C1::ScalarField>,
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub cs_vp: CS1::VerifierParams,
    pub cf_cs_vp: CS2::VerifierParams,
    pub cp_cs_vp: CS2::VerifierParams,
	// KZG commitment to col1 of lookup, built as the same time cs_pp is
	// constructed -> MOVED to GlobalClaim
	// pub kzg_lk_col1: C1,
	// KZG commitment to col2 of lookup
	// pub kzg_lk_col2: C1,
}

impl<C1, C2, CS1, CS2, const H: bool> VerifierParamsFoldPot<C1, C2, CS1, CS2, H>
where
    C1: CurveGroup,
    C2: CurveGroup,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
{
    /// returns the hash of the public parameters of Nova
    pub fn pp_hash(&self) -> Result<C1::ScalarField, Error> {
        pp_hash::<C1, C2, CS1, CS2, H>(
            &self.r1cs,
            &self.cf_r1cs,
            &self.cs_vp,
            &self.cf_cs_vp,
            &self.poseidon_config,
        )
    }
}


/// Implements Nova+CycleFold's IVC, described in [Nova](https://eprint.iacr.org/2021/370.pdf) and
/// [CycleFold](https://eprint.iacr.org/2023/1192.pdf), following the FoldingScheme trait
/// The `H` const generic specifies whether the homorphic commitment scheme is blinding
/// NOTE: changes compared with Nova: (1) added lookup table 
#[derive(Clone, Debug)]
pub struct FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, 
	const H: bool = false>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
	C1::BaseField: PrimeField,
	C2::BaseField: PrimeField,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,

{
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
	_gm: PhantomData<GM>,
    /// R1CS of the Augmented Function circuit
    pub r1cs: R1CS<C1::ScalarField>,
    /// R1CS of the CycleFold circuit
    pub cf_r1cs: R1CS<C2::ScalarField>,
    pub poseidon_config: PoseidonConfig<C1::ScalarField>,
    /// CommitmentScheme::ProverParams over C1
    pub cs_pp: CS1::ProverParams,
    /// CycleFold CommitmentScheme::ProverParams, over C2
    pub cf_cs_pp: CS2::ProverParams,
    /// F circuit, the circuit that is being folded
    pub F: FC,
	/// the lookup table (not: shared among all circuits) 
	pub lk_tbl: Option<Rc<RefCell<LK>>>,
    /// public params hash
    pub pp_hash: C1::ScalarField,
    pub i: C1::ScalarField,
    /// initial state
    pub z_0: Vec<C1::ScalarField>,
    /// current i-th state
    pub z_i: Vec<C1::ScalarField>,
	/// the the contents that hash to z0.1
	pub z0_part2_inst: ZiPartTwoInst<C1::ScalarField>, //ADDED, ALWAYS same
	/// the contents that hashes to of zi.1
	pub zi_part2_inst: ZiPartTwoInst<C1::ScalarField>, //ADDED
    /// Nova instances (enhanced with fixed MEM)
    pub w_i: WitnessFoldPot<C1>,
    pub u_i: CommittedInstanceFoldPot<C1>,
    pub W_i: WitnessFoldPot<C1>,
    pub U_i: CommittedInstanceFoldPot<C1>,

    /// CycleFold running instance (no fixed mem needed - use Nova Witness)
    pub cf_W_i: Witness<C2>,
    pub cf_U_i: CommittedInstance<C2>,

	// Added
	/// size of F (Fixed Mem) in W
	pub size_F: usize,
	/// index of F in the AugmentedFCircuit (4 + external_inp.len)
	pub start_F: usize,
}

/// This just creates DUMMY instance. 
pub fn dummy_instance_foldpot<C:CurveGroup>(r1cs: &R1CS<C::ScalarField>, size_F: usize, start_F: usize)
-> (WitnessFoldPot<C>, CommittedInstanceFoldPot<C>)
where <C as Group>::ScalarField: Absorb,
    <C as ark_ec::CurveGroup>::BaseField: ark_ff::PrimeField{
        let w_len = r1cs.A.n_cols - 1 - r1cs.l;
        let w_dummy = nova::Witness::<C>::dummy(w_len, r1cs.A.n_rows);
        let u_dummy = nova::CommittedInstance::<C>::dummy(r1cs.l);
		assert!(w_dummy.W.len()>=size_F + start_F);
		let w2 = WitnessFoldPot{
			E: w_dummy.E,
			rE: w_dummy.rE,
			W: w_dummy.W,
			rW: w_dummy.rW,
			size_F: size_F, 
			start_F: start_F, 
			rF: C::ScalarField::zero(), 
		};
		let u2 = CommittedInstanceFoldPot{
			cmE: u_dummy.cmE,
			u: u_dummy.u,
			cmW: u_dummy.cmW,
			x: u_dummy.x,
			cmF: C::zero(), 
		};
        (w2, u2)
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, const H: bool> 
FoldingScheme<C1, C2, FC> for FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H,C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<C1::ScalarField,LK> + Debug + Clone,
{
    type PreprocessorParam = PreprocessorParamFoldPot<C1, C2, FC, CS1, CS2, LK,  GM, H>;
    type ProverParam = ProverParamsFoldPot<C1, C2, CS1, CS2, LK, H>;
    type VerifierParam = VerifierParamsFoldPot<C1, C2, CS1, CS2, H>;
    type RunningInstance = (CommittedInstanceFoldPot<C1>, WitnessFoldPot<C1>);
    type IncomingInstance = (CommittedInstanceFoldPot<C1>, WitnessFoldPot<C1>);
    type MultiCommittedInstanceWithWitness = ();
    type CFInstance = (CommittedInstance<C2>, Witness<C2>);//still nova inst.

    fn preprocess(
        mut rng: impl RngCore,
        prep_param: &Self::PreprocessorParam,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let (r1cs, cf_r1cs, cp_r1cs) =
            get_r1cs::<C1, GC1, C2, GC2, FC, LK, GM, H>(&prep_param.poseidon_config, prep_param.F.clone())?;

        // if cs params exist, use them, if not, generate new ones
		// TODO: add prover param setup for lookups
        let cs_pp: CS1::ProverParams;
        let cs_vp: CS1::VerifierParams;
        let cf_cs_pp: CS2::ProverParams;
        let cf_cs_vp: CS2::VerifierParams;
        let cp_cs_pp: CS2::ProverParams;
        let cp_cs_vp: CS2::VerifierParams;
		let vec_sizes = vec![ r1cs.A.n_cols, prep_param.lk_tbl.borrow().get_size() + 1];
		let max_size:usize = *vec_sizes.iter().max().unwrap();
        if prep_param.cs_pp.is_some()
            && prep_param.cf_cs_pp.is_some()
            && prep_param.cs_vp.is_some()
            && prep_param.cf_cs_vp.is_some()
        {
            cs_pp = prep_param.clone().cs_pp.unwrap();
            cs_vp = prep_param.clone().cs_vp.unwrap();
            cf_cs_pp = prep_param.clone().cf_cs_pp.unwrap();
            cf_cs_vp = prep_param.clone().cf_cs_vp.unwrap();
            cp_cs_pp = prep_param.clone().cp_cs_pp.unwrap();
            cp_cs_vp = prep_param.clone().cp_cs_vp.unwrap();
        } else {
			//UPDATED (now the cs_pp is used to prove r1cs
			//as well as commitment for the Word and Lookup

            (cs_pp, cs_vp) = CS1::setup(&mut rng, max_size)?;
            (cf_cs_pp, cf_cs_vp) = CS2::setup(&mut rng, cf_r1cs.A.n_rows)?;
            (cp_cs_pp, cp_cs_vp) = CS2::setup(&mut rng, cp_r1cs.A.n_rows)?;
        }

		let lookup = prep_param.lk_tbl.borrow();
		let (col1_raw, col2_raw) = lookup.get_cols();
		let (lkup_col1_rev,lkup_col2_rev)
			: (Vec<C1::ScalarField>, Vec<C1::ScalarField>) 
			= (col1_raw.iter().rev().map(|x| *x).collect(), 
				col2_raw.iter().rev().map(|x| *x).collect());
		assert!(lkup_col1_rev.len()==lookup.get_size() &&
			lkup_col2_rev.len()==lookup.get_size());
		//let kzg_lk_col1 = CS1::commit(&cs_pp, &lkup_col1_rev, &zero)?; 
		//let kzg_lk_col2 = CS1::commit(&cs_pp, &lkup_col2_rev, &zero)?; 

        let prover_params = ProverParamsFoldPot::<C1, C2, CS1, CS2, LK, H> {
            poseidon_config: prep_param.poseidon_config.clone(),
            cs_pp: cs_pp.clone(),
            cf_cs_pp: cf_cs_pp.clone(),
            cp_cs_pp: cp_cs_pp.clone(),
			size_F: prep_param.size_F,
			start_F: prep_param.start_F,
			lk_tbl: prep_param.lk_tbl.clone(),
			cs_pp_len: max_size,
        };
        let verifier_params = VerifierParamsFoldPot::<C1, C2, CS1, CS2, H> {
            poseidon_config: prep_param.poseidon_config.clone(),
            r1cs,
            cf_r1cs,
            cs_vp,
            cf_cs_vp,
            cp_cs_vp,
			//kzg_lk_col1,
			//kzg_lk_col2,
        };

        Ok((prover_params, verifier_params))
    }

    /// Initializes the Nova+CycleFold's IVC for the given parameters and initial state `z_0`.
	/// IMPORTANT NOTICE: z_0 and z_i actually consists of the FOLLOWING:
	/// (1) the hashchain of cmF from the previous stage.
	/// (2) the hash of z_0 or z_i_part2
	/// NOTE: for step 0, we will make an exception to pass the information
	/// of ALREADY computed FINAL hashchain of cmF (so that we can
	/// rebuild the z0_part2_inst using it. In this case `z_0[0]`
	/// will be the FINAL hashchain cmF (i.e., the r used for 
	/// z0_part2).  At this moment, because there is no step 1 information,
	/// zi_part2_inst is the same as z0_part2_inst
    fn init(
        params: &(Self::ProverParam, Self::VerifierParam),
        _F: FC,
        z_0: Vec<C1::ScalarField>,
    ) -> Result<Self, Error> {
        let (_pp, _vp) = params;
		assert!(z_0.len()==2, "z_0 length: {} is not 2!", z_0.len());
		panic!("NEEDS HANDLING HERE: need to pass both ch and rc");
		/*
		let (ch, rc) = (hc_cmF, hc_cmF);

		let b_full = F.is_full_mode();
		assert!(b_full==false); //only support dual mode in super
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;

		panic!("CHECK IF IT'S OK TO PASS num_words = 0");
		let num_words = 0;
		let z0_part2_inst=ZiPartTwoInst::new(ch, rc, &params.0.poseidon_config,
			b_full, fq_bits, num_words);
		let z0_part2_hash = z0_part2_inst.hash(&params.0.poseidon_config);
		assert!(z0_part2_hash==z_0[1], "z0_part2_hash: {} != z0[1]: {}",
			z0_part2_hash, z_0[1]);
		let z0_new = vec![hc_cmF, z0_part2_hash]; //rewrite it

        // prepare the circuit to obtain its R1CS
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        let cs2 = ConstraintSystem::<C1::BaseField>::new_ref();

        let augmented_F_circuit =
            AugmentedFCircuitFoldPot::<C1, C2, GC2, LK, FC>::empty(&pp.poseidon_config, F.clone(), b_full);
        let cf_circuit= CycleFoldCircuit::<C1, GC1>::empty(FOLDPOT_CF_N_POINTS);

        augmented_F_circuit.generate_constraints(cs.clone())?;
        cs.finalize();
        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let r1cs = extract_r1cs::<C1::ScalarField>(&cs);

        cf_circuit.generate_constraints(cs2.clone())?;
        cs2.finalize();
        let cs2 = cs2.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let cf_r1cs = extract_r1cs::<C1::BaseField>(&cs2);

        // compute the public params hash
        let pp_hash = vp.pp_hash()?;

        // setup the dummy instances
        let (w_dummy, u_dummy) = dummy_instance_foldpot::<C1>(&r1cs, size_F, start_F);

        let (cf_w_dummy, cf_u_dummy): (nova::Witness<C2>, nova::CommittedInstance<C2>) = cf_r1cs.dummy_instance();

        // W_dummy=W_0 is a 'dummy witness', all zeroes, but with the size corresponding to the
        // R1CS that we're working with.
		let lktbl = LookupTableTwoCol_Inst::<C1::ScalarField>::dummy();
        Ok(Self {
            _gc1: PhantomData,
            _c2: PhantomData,
            _gc2: PhantomData,
            r1cs,
            cf_r1cs,
            poseidon_config: pp.poseidon_config.clone(),
            cs_pp: pp.cs_pp.clone(),
            cf_cs_pp: pp.cf_cs_pp.clone(),
            F,
            pp_hash,
            i: C1::ScalarField::zero(),
            z_0: z0_new.clone(),
            z_i: z0_new, //fake value
			z0_part2_inst: z0_part2_inst.clone(),
			zi_part2_inst: z0_part2_inst,
            w_i: w_dummy.clone(),
            u_i: u_dummy.clone(),
            W_i: w_dummy,
            U_i: u_dummy,
            // cyclefold running instance
            cf_W_i: cf_w_dummy.clone(),
            cf_U_i: cf_u_dummy.clone(),
			lk_tbl: Some(pp.lk_tbl.clone()),
			size_F: pp.size_F,
			start_F: pp.start_F,
        })
		*/
    }

    /// Implements IVC.P of Nova+CycleFold
    fn prove_step(
        &mut self,
        mut rng: impl RngCore,
        external_inputs: Vec<C1::ScalarField>,
        // Nova does not support multi-instances folding
        _other_instances: Option<Self::MultiCommittedInstanceWithWitness>,
    ) -> Result<(), Error> {
        // ensure that commitments are blinding if user has specified so.
        if H && self.i >= C1::ScalarField::one() {
            let blinding_commitments = if self.i == C1::ScalarField::one() {
                // blinding values of the running instances are zero at the first iteration
                vec![self.w_i.rW, self.w_i.rE]
            } else {
                vec![self.w_i.rW, self.w_i.rE, self.W_i.rW, self.W_i.rE]
            };
            if blinding_commitments.contains(&C1::ScalarField::zero()) {
                return Err(Error::IncorrectBlinding(
                    H,
                    format!("{:?}", blinding_commitments),
                ));
            }
        }
        // `sponge` is for digest computation.
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
        // `transcript` is for challenge generation.
        let mut transcript = sponge.clone();

        let augmented_F_circuit: AugmentedFCircuitFoldPot<C1, C2, GC2, LK, FC, GM, H>;

        // Nova does not support (by design) multi-instances folding
        if _other_instances.is_some() {
            return Err(Error::NoMultiInstances);
        }

        if self.z_i.len() != self.F.state_len() {
            return Err(Error::NotSameLength(
                "z_i.len()".to_string(),
                self.z_i.len(),
                "F.state_len()".to_string(),
                self.F.state_len(),
            ));
        }
        if external_inputs.len() != self.F.external_inputs_len() {
            return Err(Error::NotSameLength(
                "F.external_inputs_len()".to_string(),
                self.F.external_inputs_len(),
                "external_inputs.len()".to_string(),
                external_inputs.len(),
            ));
        }

        if self.i > C1::ScalarField::from_le_bytes_mod_order(&usize::MAX.to_le_bytes()) {
            return Err(Error::MaxStep);
        }
        let mut i_bytes: [u8; 8] = [0; 8];
        i_bytes.copy_from_slice(&self.i.into_bigint().to_bytes_le()[..8]);
        let i_usize: usize = usize::from_le_bytes(i_bytes);

		//z_i1_part2 is the part 2 instance of the `z_{i+1}`
		let pre_cmF = None;
		if 1>0 {panic!("this function should NOT be called. call mod_super.rs prove_step() instead");}
        let (wtns, _wtns_config, z_i1_part2) = self
            .F
            .gen_witness(&external_inputs, &self.zi_part2_inst, pre_cmF);
		//ADDED: now rebuild z_i1 (`z_{i+1}`)
		let zi_part2 = self.zi_part2_inst.hash(&self.poseidon_config);
		assert!(self.z_i[1]==zi_part2, "z_i[1] != zi_part2");
		let cur_hc_cmF = self.z_i[0];
		let to_hash = vec![
			vec![cur_hc_cmF],
			wtns.cmF.clone(),
		].concat();
        let mut sponge_cmf = 
			PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);
		sponge_cmf.absorb(&to_hash);
		let new_hc_cmF:C1::ScalarField=sponge_cmf.squeeze_field_elements(1)[0];
		let z_i1 = vec![new_hc_cmF, z_i1_part2.hash(&self.poseidon_config)];

        // compute T and cmT for AugmentedFCircuit
        // r_bits is the r used to the RLC of the F' instances
        let (T, cmT) = self.compute_cmT()?;
        let r_bits = ChallengeGadgetFoldPot::<C1>::get_challenge_native(
            &mut transcript,
            self.pp_hash,
            self.U_i.clone(),
            self.u_i.clone(),
            cmT,
        );
        let r_Fr = C1::ScalarField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;
        let r_Fq = C1::BaseField::from_bigint(BigInteger::from_bits_le(&r_bits))
            .ok_or(Error::OutOfBounds)?;

        // fold Nova instances
        let (W_i1, U_i1): (WitnessFoldPot<C1>, CommittedInstanceFoldPot<C1>) =
            NIFSFoldPot::<C1, CS1, H>::fold_instances(
                r_Fr, &self.W_i, &self.U_i, &self.w_i, &self.u_i, &T, cmT,
            )?;

        // folded instance output (public input, x)
        // u_{i+1}.x[0] = H(i+1, z_0, z_{i+1}, U_{i+1})
        let u_i1_x = U_i1.hash(
            &sponge,
            self.pp_hash,
            self.i + C1::ScalarField::one(),
            self.z_0.clone(),
            z_i1.clone(),
        );

        // u_{i+1}.x[1] = H(cf_U_{i+1})
        let cf_u_i1_x: C1::ScalarField;

        if self.i == C1::ScalarField::zero() {
            cf_u_i1_x = self.cf_U_i.hash_cyclefold(&sponge, self.pp_hash);
            // base case
            augmented_F_circuit = AugmentedFCircuitFoldPot::<C1,C2,GC2,LK,FC,GM,H> {
				_gm: PhantomData,
				_lk: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(C1::ScalarField::zero()), // = i=0
                i_usize: Some(0),
                z_0: Some(self.z_0.clone()), // = z_i
                z_i: Some(self.z_i.clone()),
				z0_part2_inst: Some(self.z0_part2_inst.clone()),
				zi_part2_inst: Some(self.zi_part2_inst.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_cmW: Some(self.u_i.cmW), // = dummy
                u_i_cmF: Some(self.u_i.cmF), // = dummy
                U_i: Some(self.U_i.clone()), // = dummy
                U_i1_cmE: Some(U_i1.cmE),
                U_i1_cmW: Some(U_i1.cmW),
                U_i1_cmF: Some(U_i1.cmF),
                cmT: Some(cmT),
                F: self.F.clone(),
                x: Some(u_i1_x),
                cf1_u_i_cmW: None,
                cf2_u_i_cmW: None,
                cf3_u_i_cmW: None,
                cf_U_i: None,
                cf1_cmT: None,
                cf2_cmT: None,
                cf3_cmT: None,
                cf_x: Some(cf_u_i1_x),
            };

            #[cfg(test)]
            NIFSFoldPot::<C1, CS1, H>::verify_folded_instance(r_Fr, &self.U_i, &self.u_i, &U_i1, &cmT)?;
        } else {
            // CycleFold part:
            // get the vector used as public inputs 'x' in the CycleFold circuit
            // cyclefold circuit for cmW
            let cfW_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.cmW),
                get_cm_coordinates(&self.u_i.cmW),
                get_cm_coordinates(&U_i1.cmW),
            ]
            .concat();
            // cyclefold circuit for cmE
            let cfE_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.cmE),
                get_cm_coordinates(&cmT),
                get_cm_coordinates(&U_i1.cmE),
            ].concat();
            // cyclefold circuit for cmF
            let cfF_u_i_x = [
                vec![r_Fq],
                get_cm_coordinates(&self.U_i.cmF),
                get_cm_coordinates(&self.u_i.cmF),
                get_cm_coordinates(&U_i1.cmF),
            ]
            .concat();

            let cfW_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                n_points: FOLDPOT_CF_N_POINTS,
                r_bits: Some(vec![r_bits.clone()]),
                points: Some(vec![self.U_i.clone().cmW, self.u_i.clone().cmW]),
                x: Some(cfW_u_i_x.clone()),
            };
            let cfE_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                n_points: FOLDPOT_CF_N_POINTS,
                r_bits: Some(vec![r_bits.clone()]),
                points: Some(vec![self.U_i.clone().cmE, cmT]),
                x: Some(cfE_u_i_x.clone()),
            };
            let cfF_circuit = CycleFoldCircuit::<C1, GC1> {
                _gc: PhantomData,
                n_points: FOLDPOT_CF_N_POINTS,
                r_bits: Some(vec![r_bits.clone()]),
                points: Some(vec![self.U_i.clone().cmF, self.u_i.clone().cmF]),
                x: Some(cfF_u_i_x.clone()),
            };

            // fold self.cf_U_i + cfW_U -> folded running with cfW
            let (_cfW_w_i, cfW_u_i, cfW_W_i1, cfW_U_i1, cfW_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                self.cf_W_i.clone(), // CycleFold running instance witness
                self.cf_U_i.clone(), // CycleFold running instance
                cfW_u_i_x,
                cfW_circuit,
                &mut rng,
            )?;


            // fold [the output from folding self.cf_U_i + cfW_U] + cfE_U = folded_running_with_cfW + cfE
            let (_cfE_w_i, cfE_u_i, cfE_W_i1, cfE_U_i1, cfE_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                cfW_W_i1,
                cfW_U_i1.clone(),
                cfE_u_i_x,
                cfE_circuit,
                &mut rng,
            )?;

			// siimilarly fold with cfF (added)
            let (_cfF_w_i, cfF_u_i, cfF_W_i1, cfF_U_i1, cfF_cmT, _) = self.fold_cyclefold_circuit(
                &mut transcript,
                cfE_W_i1,
                cfE_U_i1.clone(),
                cfF_u_i_x.clone(),
                cfF_circuit,
                &mut rng,
            )?;

            cf_u_i1_x = cfF_U_i1.hash_cyclefold(&sponge, self.pp_hash);

            augmented_F_circuit = AugmentedFCircuitFoldPot::<C1,C2,GC2,LK,FC,GM,H> {
				_gm: PhantomData,
				_lk: PhantomData,
                _gc2: PhantomData,
                poseidon_config: self.poseidon_config.clone(),
                pp_hash: Some(self.pp_hash),
                i: Some(self.i),
                i_usize: Some(i_usize),
                z_0: Some(self.z_0.clone()),
                z_i: Some(self.z_i.clone()),
				z0_part2_inst: Some(self.z0_part2_inst.clone()),
				zi_part2_inst: Some(self.zi_part2_inst.clone()),
                external_inputs: Some(external_inputs.clone()),
                u_i_cmW: Some(self.u_i.cmW),
                u_i_cmF: Some(self.u_i.cmF),
                U_i: Some(self.U_i.clone()),
                U_i1_cmE: Some(U_i1.cmE),
                U_i1_cmW: Some(U_i1.cmW),
                U_i1_cmF: Some(U_i1.cmF),
                cmT: Some(cmT),
                F: self.F.clone(),
                x: Some(u_i1_x),
                // cyclefold values
                cf1_u_i_cmW: Some(cfW_u_i.cmW),
                cf2_u_i_cmW: Some(cfE_u_i.cmW),
                cf3_u_i_cmW: Some(cfF_u_i.cmW),
                cf_U_i: Some(self.cf_U_i.clone()),
                cf1_cmT: Some(cfW_cmT),
                cf2_cmT: Some(cfE_cmT),
                cf3_cmT: Some(cfF_cmT),
                cf_x: Some(cf_u_i1_x),
            };

            self.cf_W_i = cfF_W_i1;
            self.cf_U_i = cfF_U_i1;

            #[cfg(test)]
            {
                self.cf_r1cs.check_instance_relation(&_cfW_w_i, &cfW_u_i)?;
                self.cf_r1cs.check_instance_relation(&_cfE_w_i, &cfE_u_i)?;
                self.cf_r1cs
                    .check_relaxed_instance_relation(&self.cf_W_i, &self.cf_U_i)?;
            }
        }


		//println!(">*>*>* prove_step step 1");
        let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        augmented_F_circuit.generate_constraints(cs.clone())?;

		//println!(">*>*>* prove_step step 2");

        #[cfg(test)]
        assert!(cs.is_satisfied().unwrap());

        let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
        let (w_i1, x_i1) = extract_w_x::<C1::ScalarField>(&cs);
        if x_i1[0] != u_i1_x || x_i1[1] != cf_u_i1_x {
            return Err(Error::NotEqual);
        }

		//println!(">*>*>* prove_step step 3");

        #[cfg(test)]
        if x_i1.len() != 2 {
            return Err(Error::NotExpectedLength(x_i1.len(), 2));
        }

        // set values for next iteration
        self.i += C1::ScalarField::one();
        self.z_i = z_i1;
		self.zi_part2_inst = z_i1_part2;
        self.w_i = WitnessFoldPot::<C1>::
			new::<H>(w_i1, self.r1cs.A.n_rows, &mut rng, self.size_F, self.start_F);
        self.u_i = self.w_i.commit::<CS1, H>(&self.cs_pp, x_i1)?;
        self.W_i = W_i1;
        self.U_i = U_i1;


        #[cfg(test)]
        {
            self.r1cs.check_instance_relation(&self.w_i.clone().into(), &self.u_i.clone().into())?;
            self.r1cs
                .check_relaxed_instance_relation(&self.W_i.clone().into(), &self.U_i.clone().into())?;
        }

        Ok(())
    }

    fn state(&self) -> Vec<C1::ScalarField> {
        self.z_i.clone()
    }

    fn instances(
        &self,
    ) -> (
        Self::RunningInstance,
        Self::IncomingInstance,
        Self::CFInstance,
		Option<Self::CFInstance>,
    ) {
        (
            (self.U_i.clone(), self.W_i.clone()),
            (self.u_i.clone(), self.w_i.clone()),
            (self.cf_U_i.clone(), self.cf_W_i.clone()),
			None
        )
    }

    /// Implements IVC.V of Nova+CycleFold. Notice that this method does not include the
    /// commitments verification, which is done in the Decider.
    fn verify(
        vp: Self::VerifierParam,
        z_0: Vec<C1::ScalarField>, // initial state
        z_i: Vec<C1::ScalarField>, // last state
        num_steps: C1::ScalarField,
        running_instance: Self::RunningInstance,
        incoming_instance: Self::IncomingInstance,
        cyclefold_instance: Self::CFInstance,
        _cyclepair_instance: Option<Self::CFInstance>,
    ) -> Result<(), Error> {
        let sponge = PoseidonSponge::<C1::ScalarField>::new(&vp.poseidon_config);

        if num_steps == C1::ScalarField::zero() {
            if z_0 != z_i {
                return Err(Error::IVCVerificationFail);
            }
            return Ok(());
        }

        let (U_i, W_i) = running_instance;
        let (u_i, w_i) = incoming_instance;
        let (cf_U_i, cf_W_i) = cyclefold_instance;

        if u_i.x.len() != 2 || U_i.x.len() != 2 {
			println!("ERROR: u_ix or U_i.x.len()!=2");
            return Err(Error::IVCVerificationFail);
        }
        let pp_hash = vp.pp_hash()?;

        // check that u_i's output points to the running instance
        // u_i.X[0] == H(i, z_0, z_i, U_i)
        let expected_u_i_x = U_i.hash(&sponge, pp_hash, num_steps, z_0.clone(), z_i.clone());
        if expected_u_i_x != u_i.x[0] {
			println!("u_i.x[0] error, u_i.x[0]: {}, expected_u_i_x: {}, U_i: {:?}\nz_0: {:?}\nz_i1:{:?}", u_i.x[0], expected_u_i_x, U_i, z_0, z_i);
            return Err(Error::IVCVerificationFail);
        }

        // u_i.X[1] == H(cf_U_i)
        let expected_cf_u_i_x = cf_U_i.hash_cyclefold(&sponge, pp_hash);
        if expected_cf_u_i_x != u_i.x[1] {
			println!("u_i.X[1] check fails");
            return Err(Error::IVCVerificationFail);
        }

        // check u_i.cmE==0, u_i.u==1 (=u_i is a un-relaxed instance)
        if !u_i.cmE.is_zero() || !u_i.u.is_one() {
			println!("cmE error");
            return Err(Error::IVCVerificationFail);
        }

        // check R1CS satisfiability
        vp.r1cs.check_instance_relation(&w_i.into(), &u_i.into())?;
        // check RelaxedR1CS satisfiability
        vp.r1cs.check_relaxed_instance_relation(&W_i.into(), &U_i.into())?;

        // check CycleFold RelaxedR1CS satisfiability
        vp.cf_r1cs
            .check_relaxed_instance_relation(&cf_W_i, &cf_U_i)?;

        Ok(())
    }
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, const H: bool> FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H,C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
{
    // computes T and cmT for the AugmentedFCircuit
    fn compute_cmT(&self) -> Result<(Vec<C1::ScalarField>, C1), Error> {
        NIFSFoldPot::<C1, CS1, H>::compute_cmT(
            &self.cs_pp,
            &self.r1cs,
            &self.w_i,
            &self.u_i,
            &self.W_i,
            &self.U_i,
        )
    }


	/// given the statement of the current step and the current hashchain
	/// of cmF, compute the cmF.
	pub fn compute_step_hc_cmF(&self, hc_cmF: C1::ScalarField, stmt: &StatementInst<C1::ScalarField, LK>) -> Result<C1::ScalarField, Error>{
		//1. create the sponge
        let mut sponge_cmf = 
			PoseidonSponge::<C1::ScalarField>::new(&self.poseidon_config);

		//2. compute the cmF using witness of F
		let circ = &self.F;
		let fq_bits = <<C1 as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let zi_part2 = ZiPartTwoInst::dummy(circ.is_full_mode(), fq_bits); //does not matter
		let pre_cmF = None;
		if 1>0 {panic!("this function should not be called. Call the one in mod_super.rs instead");}
		let (wit, _wconfig, _zi1_part2) = circ
			.gen_witness(&stmt.to_vec(), &zi_part2, pre_cmF);
		let cmF = wit.gen_cmF::<C1,CS1,H>(&self.cs_pp).expect("gen_cmF error"); 
		let mut vec_cmF = vec![];
		cmF.to_native_sponge_field_elements_as_vec()
            .to_sponge_field_elements(&mut vec_cmF);
		let to_hash = vec![
			vec![hc_cmF],
			vec_cmF,
		].concat();
		sponge_cmf.absorb(&to_hash);

		//3. hash the result
		let new_hc_cmF:C1::ScalarField=sponge_cmf.squeeze_field_elements(1)[0];
		Ok(new_hc_cmF)
	}
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, const H: bool> FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, GM, H>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1: CommitmentScheme<C1, H>,
    CS2: CommitmentScheme<C2, H>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,

{
    // folds the given cyclefold circuit and its instances
    #[allow(clippy::type_complexity)]
    fn fold_cyclefold_circuit<T: Transcript<C1::ScalarField>>(
        &self,
        transcript: &mut T,
        cf_W_i: Witness<C2>,           // witness of the running instance
        cf_U_i: CommittedInstance<C2>, // running instance
        cf_u_i_x: Vec<C2::ScalarField>,
        cf_circuit: CycleFoldCircuit<C1, GC1>,
        rng: &mut impl RngCore,
    ) -> Result<
        (
            Witness<C2>,
            CommittedInstance<C2>, // u_i
            Witness<C2>,           // W_i1
            CommittedInstance<C2>, // U_i1
            C2,                    // cmT
            C2::ScalarField,       // r_Fq
        ),
        Error,
    > {
        fold_cyclefold_circuit::<C1, GC1, C2, GC2, FC, CS1, CS2, H>(
            FOLDPOT_CF_N_POINTS,
            transcript,
            self.cf_r1cs.clone(),
            self.cf_cs_pp.clone(),
            self.pp_hash,
            cf_W_i,
            cf_U_i,
            cf_u_i_x,
            cf_circuit,
            rng,
        )
    }
}

/// helper method to get the r1cs from the ConstraintSynthesizer
pub fn get_r1cs_from_cs<F: PrimeField>(
    circuit: impl ConstraintSynthesizer<F>,
) -> Result<R1CS<F>, Error> {
    let cs = ConstraintSystem::<F>::new_ref();
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();
    let cs = cs.into_inner().ok_or(Error::NoInnerConstraintSystem)?;
    let r1cs = extract_r1cs::<F>(&cs);
    Ok(r1cs)
}

/// helper method to get the R1CS for both the AugmentedFCircuit and the CycleFold circuit
#[allow(clippy::type_complexity)]
pub fn get_r1cs<C1, GC1, C2, GC2, FC, LK, GM, const H: bool>(
    _poseidon_config: &PoseidonConfig<C1::ScalarField>,
    _F_circuit: FC,
) -> Result<(R1CS<C1::ScalarField>, R1CS<C2::ScalarField>, R1CS<C2::ScalarField>), Error>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
	LK: LookupTableTwoCol<C1::ScalarField>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
{
	panic!("THIS FUNCTION is deprecated. Never called");
	/* 
	let b_full = F_circuit.is_full_mode();
    let augmented_F_circuit =
        AugmentedFCircuitFoldPot::<C1,C2,GC2,LK,FC>::empty(poseidon_config, F_circuit, b_full);
    let cf_circuit = CycleFoldCircuit::<C1, GC1>::empty(FOLDPOT_CF_N_POINTS);
    let cp_circuit = CycleFoldCircuit::<C1, GC1>::empty(FOLDPOT_CF_N_POINTS);
    let r1cs = get_r1cs_from_cs::<C1::ScalarField>(augmented_F_circuit)?;
    let cf_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cf_circuit)?;
    let cp_r1cs = get_r1cs_from_cs::<C2::ScalarField>(cp_circuit)?;
    Ok((r1cs, cf_r1cs, cp_r1cs))
	*/
}

/// helper method to get the pedersen params length for both the AugmentedFCircuit and the
/// CycleFold circuit
pub fn get_cs_params_len<C1, GC1, C2, GC2, FC, LK, GM, const H: bool>(
    poseidon_config: &PoseidonConfig<C1::ScalarField>,
    F_circuit: FC,
) -> Result<(usize, usize), Error>
where
    C1: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    C2: CurveGroup,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<H, C1::ScalarField, LK, GM>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'a> &'a GC1: GroupOpsBounds<'a, C1, GC1>,
    for<'a> &'a GC2: GroupOpsBounds<'a, C2, GC2>,
	C1::Config: SWCurveConfig,
	GM: GadgetMapper<C1::ScalarField,LK> + std::clone::Clone + Debug,
{
    let (r1cs, cf_r1cs, _cp_r1cs) = get_r1cs::<C1, GC1, C2, GC2, FC, LK, GM, H>(poseidon_config, F_circuit)?;
    Ok((r1cs.A.n_rows, cf_r1cs.A.n_rows))
}

#[cfg(test)]
pub mod tests_mod_basic {
    use crate::commitment::kzg::KZG;
    use ark_bn254::{constraints::GVar, Bn254, Fr, G1Projective as Projective};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::transcript::poseidon::poseidon_canonical_config;
	use crate::folding::foldpot::{
		sigma_ir1cs::{
			SigmaIR1CS_Inst,StatementInst,LookupTableTwoCol_Inst,
			tests_sigma_ir1cs::{gen_six_root, SixRootMapper},
		}
	};

    /// This test tests the Nova+CycleFold IVC, and by consequence it is also testing the
    /// AugmentedFCircuit
    #[test]
    fn test_ivc() {
		type GM = SixRootMapper<Fr,LookupTableTwoCol_Inst<Fr>>;
        let poseidon_config = poseidon_canonical_config::<Fr>();
        let num_steps: usize = 5;
		let (lk1, F_circuit, _vec_stmt) = gen_six_root(5);
		let (lk2, F_circuit2, _vec_stmt) = gen_six_root(5);
		let (lk3, F_circuit3, vec_stmt) = gen_six_root(5);
        // run the test using Pedersen commitments on both sides of the curve cycle
        test_ivc_opt::<Pedersen<Projective>, Pedersen<Projective2>, LookupTableTwoCol_Inst<Fr>,GM, false>(
            poseidon_config.clone(),
			lk1,
            F_circuit.clone(),
			&vec_stmt,
			num_steps
        );
        test_ivc_opt::<Pedersen<Projective, true>, Pedersen<Projective2, true>, LookupTableTwoCol_Inst<Fr>, GM, true >(
            poseidon_config.clone(),
			lk2,
            F_circuit2.clone(),
			&vec_stmt,
			num_steps
        );

        // run the test using KZG for the commitments on the main curve, and Pedersen for the
        // commitments on the secondary curve
        test_ivc_opt::<KZG<Bn254>, Pedersen<Projective2>, LookupTableTwoCol_Inst<Fr>, GM, false>(
			poseidon_config, lk3, F_circuit3, &vec_stmt, num_steps);
    }

    // test_ivc allowing to choose the CommitmentSchemes
    fn test_ivc_opt<
        CS1: CommitmentScheme<Projective, H>,
        CS2: CommitmentScheme<Projective2, H>,
		LK: LookupTableTwoCol<Fr>,
		GM: GadgetMapper<Fr,LK> + std::clone::Clone + Debug,
        const H: bool,
    >(
        poseidon_config: PoseidonConfig<Fr>,
		lkup_inp: Rc<RefCell<LK>>,
        F_circuit: SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>,
		vec_stmts: &Vec<StatementInst<Fr,LK>>,
		num_steps: usize,
    ) {
        let mut rng = ark_std::test_rng();

        let prep_param =
            PreprocessorParamFoldPot::<Projective, Projective2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM, H>, CS1, CS2, LK, GM, H>
			::new(
				poseidon_config.clone(), 
				F_circuit.clone(), 
				lkup_inp,
				F_circuit.get_size_f()
			);
        let nova_params = FoldPot::<
            Projective,
            GVar,
            Projective2,
            GVar2,
            SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>,
            CS1,
            CS2,
			LK,
			GM,
            H,
        >::preprocess(&mut rng, &prep_param)
        .unwrap();


		//PASS1. generate cm_F first
		let num_words = 1;
		let zero = Fr::zero();
		let fq_bits = <<Projective as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		let z0_part2 = ZiPartTwoInst::<Fr>::new(zero, zero, &poseidon_config, 
			F_circuit.is_full_mode(), fq_bits, num_words);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);
		let z_0 = vec![zero, z0_part2_hash];
        let nova1 =
            FoldPot::<Projective, GVar, Projective2, GVar2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK,GM,H>, CS1, CS2, LK, GM,H>::init(
                &nova_params,
                F_circuit.clone(),
                z_0.clone(),
            )
            .unwrap();
		let mut hash_cmF= Fr::zero();
		for i in 0..num_steps{
			hash_cmF = nova1.compute_step_hc_cmF(hash_cmF, &vec_stmts[i])
				.expect("hash_cmf generation error");
		}
		let _fq_bits = <<Projective as CurveGroup>::BaseField as Field>::BasePrimeField::MODULUS_BIT_SIZE as usize;
		panic!("CHECK if it's ok to pass cmF as rc");
		/*
		let (ch, rc) = (hash_cmF, hash_cmF);
		let z0_part2 = ZiPartTwoInst::<Fr>::new(ch, rc, &poseidon_config,
			F_circuit.is_full_mode(), fq_bits, num_words);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);

		//2. PASS2 real IVC
		// NOTE: for step 0, the z_0[0] will be the FINAL hc_cmF,
		// for other steps, it will be hte hashchain of cmF from
		// the previous step
        let z_0 = vec![hash_cmF, z0_part2_hash]; //[stage hc_cmF, z_0]
        let mut nova =
            FoldPot::<Projective, GVar, Projective2, GVar2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK,H>, CS1, CS2, LK, H>::init(
                &nova_params,
                F_circuit,
                z_0.clone(),
            )
            .unwrap();

        for j in 0..num_steps {
			let v_stmt = vec_stmts[j].to_vec();
            nova.prove_step(&mut rng, v_stmt, None).expect("prove step error");
        }

        assert_eq!(Fr::from(num_steps as u32), nova.i);

        let (running_instance, incoming_instance, cyclefold_instance, cp_instance) = nova.instances();
        FoldPot::<Projective, GVar, Projective2, GVar2, SigmaIR1CS_Inst<Fr,Projective,CS1,LK, H>, CS1, CS2, LK, H>::verify(
            nova_params.1, // Nova's verifier params
            z_0,
            nova.z_i,
            nova.i,
            running_instance,
            incoming_instance,
            cyclefold_instance,
			cp_instance
        )
        .unwrap();
		*/
    }
}
