use std::sync::Arc;
/* Created 09/16/2024 */
// OUTDATED -> will be replaced by driver.
/// This file implements the onchain (Ethereum's EVM) decider. (SuperNova)
/// version
use std::cmp::max;
use ark_relations::r1cs::ConstraintSystem;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_bn254::Bn254;
use crate::transcript::{AbsorbNonNative, Transcript};
use crate::Decider;
use crate::folding::foldpot::from_field::{AffineFromField,curve_from_field_elements};
use ark_crypto_primitives::sponge::{
    poseidon::{PoseidonConfig, PoseidonSponge},
    Absorb, CryptographicSponge,
};
use ark_std::rand::{RngCore,CryptoRng};
use ark_ec::{Group, AffineRepr, CurveGroup,
	pairing::{Pairing,PairingOutput},
};
use ark_ff::{BigInteger, PrimeField, Field,ToConstraintField};
use ark_groth16::Groth16;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar},
    prelude::{CurveVar,PairingVar,FieldOpsBounds,GroupOpsBounds},
	//prelude::*,
    ToConstraintFieldGadget,
};
use ark_snark::SNARK;
use ark_std::{One, Zero};
use core::marker::PhantomData;

//pub use super::decider_eth_circuit::{DeciderEthCircuit, KZGChallengesGadget};
use crate::folding::{
	foldpot::{
		FoldPot,CommittedInstanceFoldPot,NIFSFoldPot,
		mod_super::{FoldPotSuper,ProverParamsFoldPotSuper,VerifierParamsFoldPotSuper,CommittedInstanceFoldPotSuper},
		decider_eth_circuit_super::{DeciderEthCircuitSuper},
		circuits_super::{field_to_usize},
		qa_nizk::{QaNizkProverParams,QaNizkVerifierParams, setup_qa_nizk,SparseMatrix, prove_qa_nizk, verify_qa_nizk},
	},
};
use crate::commitment::{
    kzg::{Proof as KZGProof, KZG},
    pedersen::Params as PedersenParams,
    CommitmentScheme,
};
use crate::folding::circuits::{nonnative::affine::NonNativeAffineVar, CF1, CF2, CF3};
use crate::frontend::FCircuit;
use crate::Error;
use crate::{Decider as DeciderTrait, FoldingScheme};
use crate::folding::{foldpot::
	sigma_ir1cs::{SigmaIR1CS, LookupTableTwoCol,LookupTableTwoCol_Inst}
};

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Proof<C1, CS1, S>
where
    C1: CurveGroup,
    CS1: CommitmentScheme<C1, ProverChallenge = C1::ScalarField, Challenge = C1::ScalarField>,
    S: SNARK<C1::ScalarField>,
{
    snark_proof: S::Proof,
    kzg_proofs: [CS1::Proof; 5], //increased to 3 for kzg_F (added two more for lookup)
    // cmT and r are values for the last fold, U_{i+1}=NIFS.V(r, U_i, u_i, cmT), and they are
    // checked in-circuit
    cmT: C1,
    r: C1::ScalarField,
    // the KZG challenges are provided by the prover, but in-circuit they are checked to match
    // the in-circuit computed computed ones.
    kzg_challenges: [C1::ScalarField; 4], //added two more for looup
}

/// Onchain Decider, for ethereum use cases
#[derive(Clone, Debug)]
pub struct DeciderFoldPotSuper<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK> 
where
//    C1: CurveGroup,
 //   C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<C1::ScalarField, LK>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
	/*
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
	*/
    CS1: CommitmentScheme<C1, false>,
    CS1E: CommitmentScheme<C1, false>, //be kzg
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
  //  C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, false>: From<FS>,
    crate::folding::foldpot::mod_super::ProverParamsFoldPotSuper<E,C1, C2, CS1, CS2, CS1E, LK, false>: From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::foldpot::mod_super::VerifierParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, false>: From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>>,
{
	_e: PhantomData<E>,
	_p: PhantomData<P>,
	_c2g2: PhantomData<C2G2>,
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs1e: PhantomData<CS1E>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
	_lk: PhantomData<LK>,
}



impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK> DeciderTrait<C1, C2, FC, FS> for DeciderFoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK>
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<C1::ScalarField, LK>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
    CS1E: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C2>, ProverChallenge=C1::ScalarField>,
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    //C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, false>: From<FS>,
    crate::folding::foldpot::mod_super::ProverParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, LK, false>: From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::foldpot::mod_super::VerifierParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, false>: From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{
    type PreprocessorParam = (FS::ProverParam, FS::VerifierParam);
    type ProverParam = (S::ProvingKey, CS1::ProverParams, CS1E::ProverParams);
    type Proof = Proof<C1, CS1E, S>;
    /// VerifierParam = (pp_hash, snark::vk, commitment_scheme::vk, kzg_lk_col1, kzg_lk_col2)
    type VerifierParam = (C1::ScalarField, S::VerifyingKey, CS1::VerifierParams, CS1E::VerifierParams, C1, C1); //ADDED two group elements as the KZG commitments to two cols of lkup
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstance = CommittedInstanceFoldPotSuper<C1>;

    fn preprocess(
        mut rng: impl RngCore + CryptoRng,
        prep_param: &Self::PreprocessorParam,
        fs: FS,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let circuit = DeciderEthCircuitSuper::<E,P,C2G2,C1, GC1, C2, GC2, CS1, CS2, CS1E, LK> ::from_nova::<FC>(fs.into()).unwrap();

        // get the Groth16 specific setup for the circuit
        let (g16_pk, g16_vk) = {//to save ram, clone will be freed
        	let (g16_pk, g16_vk) = S::circuit_specific_setup(circuit.clone(), 
				&mut rng).unwrap();
			(g16_pk, g16_vk)
		};


        // get the FoldingScheme prover & verifier params from Nova
        #[allow(clippy::type_complexity)]
        let nova_pp: <FoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::ProverParam = prep_param.0.clone().into();

        #[allow(clippy::type_complexity)]
        let nova_vp: <FoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = prep_param.1.clone().into();
        let pp_hash = nova_vp.pp_hash()?;
	
		let sum_n = nova_pp.vec_pp.iter().map(|p| p.cs_pp_len).sum();
		let max_size = max(sum_n, 
			nova_pp.vec_pp[0].lk_tbl.get_size()+1);

		panic!("CHECK if needs to keep both cs_pp and cs1e_pp");
		let (cs_pp, cs_vp) = CS1::setup(&mut rng, max_size)?;
		let (cs1e_pp, cs1e_vp) = CS1E::setup(&mut rng, max_size)?;
		//let kzg_lk_col1 = nova_vp.vec_vp[0].kzg_lk_col1; //all vec_vp's same
		//let kzg_lk_col2 = nova_vp.vec_vp[0].kzg_lk_col2;

        let vp = (pp_hash, g16_vk, cs_vp,cs1e_vp); //kzg_lk_col1, kzg_lk_col2);
        let pp = (g16_pk, cs_pp, cs1e_pp);
        Ok( (pp, vp) )
    }


    fn prove(
        mut rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
		//1. prepare the keys and circuit
        let (snark_pk, cs_pk, cs1e_pk): (S::ProvingKey, CS1::ProverParams, CS1E::ProverParams) = pp;
        let circuit = DeciderEthCircuitSuper
			::<E, P, C2G2, C1, GC1, C2, GC2, CS1, CS2, CS1E, LK>::from_nova::<FC>(
            folding_scheme.into(),
        )?;
		#[cfg(test)]{
        	let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        	circuit.clone().generate_constraints(cs.clone()).unwrap();
        	assert!(cs.is_satisfied().unwrap());
		}

		//2. generate the SNARK proof
        let snark_proof = S::prove(&snark_pk, circuit.clone(), &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;

		//3. compute the KZG evaluation
        let cmT = circuit.cmT.unwrap();
        let r_Fr = circuit.r.unwrap();
        let W_i1 = circuit.W_i1.unwrap();

        // get the challenges that have been already computed 
		// when preparing the circuit inputs in
        // the above `from_nova` call
        let challenge_W = circuit
            .kzg_c_W
            .ok_or(Error::MissingValue("kzg_c_W".to_string()))?;
        let challenge_E = circuit
            .kzg_c_E
            .ok_or(Error::MissingValue("kzg_c_E".to_string()))?;
        let challenge_F = circuit
            .kzg_c_F
            .ok_or(Error::MissingValue("kzg_c_F".to_string()))?;
		// -- Added for supporting lookup
        let challenge_lkup = circuit
            .kzg_c_lkup
            .ok_or(Error::MissingValue("kzg_c_lkup".to_string()))?;

        let W = W_i1.vec_wit.iter().map(|v| v.W.clone()).
			into_iter().flatten().collect::<Vec<C1::ScalarField>>();
        let E = W_i1.vec_wit.iter().map(|v| v.E.clone()).
			into_iter().flatten().collect::<Vec<C1::ScalarField>>();
		let size_F = W_i1.vec_wit.iter().map(|v| v.size_F)
			.collect::<Vec<usize>>();
		let start_F = W_i1.vec_wit.iter().map(|v| v.start_F)
			.collect::<Vec<usize>>();
        let F = W_i1.vec_wit.iter().map(|v|{
			(&v.W[v.start_F..v.start_F+v.size_F]).to_vec()
		}).into_iter().flatten().collect::<Vec<C1::ScalarField>>();

		panic!("WILL LATER REMOVE U_cmW_proof");
        let U_cmW_proof = CS1E::prove_with_challenge(
            &cs1e_pk,
            challenge_W,
            &W,
            &C1::ScalarField::zero(),
            None,
        )?;
        let U_cmE_proof = CS1E::prove_with_challenge(
            &cs1e_pk,
            challenge_E,
            &E,
            &C1::ScalarField::zero(),
            None,
        )?;
        let U_cmF_proof = CS1E::prove_with_challenge(
            &cs1e_pk,
            challenge_F,
            &F,
            &C1::ScalarField::zero(),
            None,
        )?;

		//Added for lookup
        let kzg_lkup_col1_proof = CS1E::prove_with_challenge(
            &cs1e_pk,
			challenge_lkup,
            &circuit.lkup_col1_rev.expect("col1 rev null!"),
            &C1::ScalarField::zero(),
            None,
        )?;
        let kzg_lkup_col2_proof = CS1E::prove_with_challenge(
            &cs1e_pk,
			challenge_lkup,
            &circuit.lkup_col2_rev.expect("col2 rev null!"),
            &C1::ScalarField::zero(),
            None,
        )?;
		#[cfg(test)]{
			assert!(kzg_lkup_col1_proof.eval==circuit.eval_lkup_col1.unwrap());
			assert!(kzg_lkup_col2_proof.eval==circuit.eval_lkup_col2.unwrap());
		}
		

        Ok(Self::Proof {
            snark_proof,
            kzg_proofs: [U_cmW_proof, U_cmE_proof, U_cmF_proof, kzg_lkup_col1_proof, kzg_lkup_col2_proof],
            cmT,
            r: r_Fr,
            kzg_challenges: [challenge_W, challenge_E, challenge_F, challenge_lkup],
        })
    }

	/// NOTE here incoming_instance_wrapper is a CommittedFoldPotInstanceSuper
	/// wrapper which contains ONE single CommittedFoldPotInstance,
	/// but the running_instance is a completed CommittedInstanceFoldPotSuper
    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        incoming_instance_wrapper: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Error> {
		//1. retrieve params
        if i <= C1::ScalarField::one() { return Err(Error::NotEnoughSteps); }
        let (pp_hash, snark_vk, cs_vk, cs1e_vk
		//, kzg_lk_col1, kzg_lk_col2
		): (C1::ScalarField, S::VerifyingKey, CS1::VerifierParams, CS1E::VerifierParams, C1, C1 ) = vp;

        //2. compute U = U_{d+1}= NIFS.V(U_d, u_d, cmT)
		let pc_i = running_instance.pc_i;
		let pc_i_usize = field_to_usize(&pc_i);
		let incoming_instance = &incoming_instance_wrapper.vec_inst[0];
        let Ui1_pci = NIFSFoldPot::<C1, CS1>::verify(proof.r, &running_instance.vec_inst[pc_i_usize], incoming_instance, &proof.cmT);
		let mut Ui1 = running_instance.clone();
		Ui1.vec_inst[pc_i_usize] = Ui1_pci.clone();
		let mut Ui1_vec = vec![];
		for U in Ui1.vec_inst{
			Ui1_vec.push(U.u);
			let mut U_x = U.x.clone();
			Ui1_vec.append(&mut U_x);
        	let (cmE_x, cmE_y) = NonNativeAffineVar::inputize(U.cmE)?;
        	let (cmW_x, cmW_y) = NonNativeAffineVar::inputize(U.cmW)?;
        	let (cmF_x, cmF_y) = NonNativeAffineVar::inputize(U.cmF)?;
			let mut v1 =  vec![
				cmE_x, cmE_y, cmW_x, cmW_y, cmF_x, cmF_y
			].concat();
			Ui1_vec.append(&mut v1);
		}
		Ui1_vec.push(Ui1.x_1);
		Ui1_vec.push(Ui1.pc_i);

/* REMOVE LATER
		//Ui1.to_sponge_field_elements(&mut Ui1_vec);
        let (cmE_x, cmE_y) = NonNativeAffineVar::inputize(U.cmE)?;
        let (cmW_x, cmW_y) = NonNativeAffineVar::inputize(U.cmW)?;
        let (cmF_x, cmF_y) = NonNativeAffineVar::inputize(U.cmF)?;
		*/
        let (cmT_x, cmT_y) = NonNativeAffineVar::inputize(proof.cmT)?;

		//3. build up the public input the SNARK circuit
        let public_input: Vec<C1::ScalarField> = vec![
            vec![pp_hash, i],
            z_0,
            z_i,
			/* RECOVE LATER
            vec![U.u], //the following u, x, cmE, cmW, cmF belongs to U_i1
            U.x.clone(), //following the order of to_sponge_field_elements
            cmE_x,		//of CommittedInstanceVarFoldPot
            cmE_y,
            cmW_x,
            cmW_y,
            cmF_x,
            cmF_y,
			*/
			Ui1_vec,
            proof.kzg_challenges.to_vec(), //note one more ele added for lkup
            vec![
                proof.kzg_proofs[1].eval, // eval_E
                proof.kzg_proofs[0].eval, // eval_W
                proof.kzg_proofs[2].eval, // eval_F
                proof.kzg_proofs[3].eval, // eval_col1  of lookup
                proof.kzg_proofs[4].eval, // eval_col2  of lookup
            ],
            cmT_x,
            cmT_y,
            vec![proof.r],
        ]
        .concat();

		println!("DEBUG USE 9101: public_input: {}", public_input.len());

		//4. verify the snark proof
        let snark_v = S::verify(&snark_vk, &public_input, &proof.snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        //5. we're at the Ethereum EVM case, so the CS1 is KZG commitments
        CS1E::verify_with_challenge(
            &cs1e_vk,
            proof.kzg_challenges[0],
            &Ui1_pci.cmW,
            &proof.kzg_proofs[0],
        )?;
        CS1E::verify_with_challenge(
            &cs1e_vk,
            proof.kzg_challenges[1],
            &Ui1_pci.cmE,
            &proof.kzg_proofs[1],
        )?;
        CS1E::verify_with_challenge(
            &cs1e_vk,
            proof.kzg_challenges[2],
            &Ui1_pci.cmF,
            &proof.kzg_proofs[2],
        )?;
		/* REMOVE LATER coz kzg_lk_col1 is removed
        CS1E::verify_with_challenge(
            &cs1e_vk,
            proof.kzg_challenges[3],
			&kzg_lk_col1,
            &proof.kzg_proofs[3], //col1 eval passed as public input to circ
        )?;
        CS1E::verify_with_challenge(
            &cs1e_vk,
            proof.kzg_challenges[3], //use the same challenge as col1, later
									 //can batch
			&kzg_lk_col2,
            &proof.kzg_proofs[4], //col2 eval passed as public input to circ
        )?;
		*/

        Ok(true)
    }
}

impl<E: Pairing<G1=C1,G2=C2G2>, P: PairingVar<E,CF3<C2G2>> + std::fmt::Debug + Clone, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK> 
DeciderFoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK>
where
    //C1: CurveGroup,
    //C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<C1::ScalarField, LK>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    CS1E: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS1: CommitmentScheme<C1, ProverParams = PedersenParams<C2>, ProverChallenge=C1::ScalarField>,
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    //C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    FoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, LK, false>: From<FS>,
    crate::folding::foldpot::mod_super::ProverParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, LK, false>: From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::foldpot::mod_super::VerifierParamsFoldPotSuper<E, C1, C2, CS1, CS2, CS1E, false>: From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
	//New for cyclepair
	for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
	for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
	for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	P::G1Var: ToConstraintFieldGadget<CF2<E::G1>>,
	CF2<E::G1>: PrimeField,
	P::G2Var: ToConstraintFieldGadget<CF3<E::G2>>,
	P::GTVar: ToConstraintFieldGadget<CF2<E::G1>>,
	CF3<E::G2>: PrimeField,
    C1: CurveGroup<BaseField = <C2G2::BaseField as Field>::BasePrimeField, ScalarField=C2G2::ScalarField>,
	C2G2: CurveGroup,
	C2: CurveGroup<BaseField = C1::ScalarField, ScalarField=C1::BaseField>,
	E::G1: ToConstraintField<CF2<C1>>,
	E::G2: ToConstraintField<CF2<C1>>,
	E::TargetField: ToConstraintField<CF2<C1>> + Field<BasePrimeField=CF3<C1>>,
	C1::Affine: AffineFromField<CF2<C1>>,
	C2G2::Affine: AffineFromField<CF2<C2G2>>,
{
	/// verifies the EXISTENCE of appropriate z_0, z_k,
	/// and running instance that proves the commitment to word w
	/// satisfies the criteria.
	/// NOTE THAT when we feed to the decider_eth_circuit
	///   we serve the running and incoming instance as witness (instead
	///   of I/O, thus saving cost of proof)
	pub fn verify_adv(
		vp: &<DeciderFoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK> as DeciderTrait<C1,C2,FC,FS>>::VerifierParam,
		prf: &<DeciderFoldPotSuper<E, P, C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, CS1E, S, FS, LK> as DeciderTrait<C1,C2,FC,FS>>::Proof)
		-> Result<bool, Error>{
			unimplemented!()
	}
}
/// Prepares solidity calldata for calling the NovaDecider contract
pub fn prepare_calldata(
    function_signature_check: [u8; 4],
    i: ark_bn254::Fr,
    z_0: Vec<ark_bn254::Fr>,
    z_i: Vec<ark_bn254::Fr>,
    running_instance: &CommittedInstanceFoldPot<ark_bn254::G1Projective>,
    incoming_instance: &CommittedInstanceFoldPot<ark_bn254::G1Projective>,
    proof: Proof<ark_bn254::G1Projective, KZG<'static, Bn254>, Groth16<Bn254>>,
) -> Result<Vec<u8>, Error> {
    Ok(vec![
        function_signature_check.to_vec(),
        i.into_bigint().to_bytes_be(), // i
        z_0.iter()
            .flat_map(|v| v.into_bigint().to_bytes_be())
            .collect::<Vec<u8>>(), // z_0
        z_i.iter()
            .flat_map(|v| v.into_bigint().to_bytes_be())
            .collect::<Vec<u8>>(), // z_i
        point_to_eth_format(running_instance.cmW.into_affine())?, // U_i_cmW
        point_to_eth_format(running_instance.cmE.into_affine())?, // U_i_cmE
        point_to_eth_format(running_instance.cmF.into_affine())?, // U_i_cmF, ADDED
        running_instance.u.into_bigint().to_bytes_be(), // U_i_u
        incoming_instance.u.into_bigint().to_bytes_be(), // u_i_u
        proof.r.into_bigint().to_bytes_be(), // r
        running_instance
            .x
            .iter()
            .flat_map(|v| v.into_bigint().to_bytes_be())
            .collect::<Vec<u8>>(), // U_i_x
        point_to_eth_format(incoming_instance.cmW.into_affine())?, // u_i_cmW
        point_to_eth_format(incoming_instance.cmF.into_affine())?, // u_i_cmF, ADDED
        incoming_instance
            .x
            .iter()
            .flat_map(|v| v.into_bigint().to_bytes_be())
            .collect::<Vec<u8>>(), // u_i_x
        point_to_eth_format(proof.cmT.into_affine())?, // cmT
        point_to_eth_format(proof.snark_proof.a)?, // pA
        point2_to_eth_format(proof.snark_proof.b)?, // pB
        point_to_eth_format(proof.snark_proof.c)?, // pC
        proof.kzg_challenges[0].into_bigint().to_bytes_be(), // challenge_W
        proof.kzg_challenges[1].into_bigint().to_bytes_be(), // challenge_E
        proof.kzg_challenges[2].into_bigint().to_bytes_be(), // challenge_F, ADDED
        proof.kzg_proofs[0].eval.into_bigint().to_bytes_be(), // eval W
        proof.kzg_proofs[1].eval.into_bigint().to_bytes_be(), // eval E
        proof.kzg_proofs[2].eval.into_bigint().to_bytes_be(), // eval F
        point_to_eth_format(proof.kzg_proofs[0].proof.into_affine())?, // W kzg_proof
        point_to_eth_format(proof.kzg_proofs[1].proof.into_affine())?, // E kzg_proof
        point_to_eth_format(proof.kzg_proofs[2].proof.into_affine())?, // F kzg_proof, ADDED
    ]
    .concat())
}

fn point_to_eth_format<C: AffineRepr>(p: C) -> Result<Vec<u8>, Error>
where
    C::BaseField: PrimeField,
{
    // the encoding of the additive identity is [0, 0] on the EVM
    let zero_point = (&C::BaseField::zero(), &C::BaseField::zero());
    let (x, y) = p.xy().unwrap_or(zero_point);

    Ok([x.into_bigint().to_bytes_be(), y.into_bigint().to_bytes_be()].concat())
}
fn point2_to_eth_format(p: ark_bn254::G2Affine) -> Result<Vec<u8>, Error> {
    let zero_point = (&ark_bn254::Fq2::zero(), &ark_bn254::Fq2::zero());
    let (x, y) = p.xy().unwrap_or(zero_point);

    Ok([
        x.c1.into_bigint().to_bytes_be(),
        x.c0.into_bigint().to_bytes_be(),
        y.c1.into_bigint().to_bytes_be(),
        y.c0.into_bigint().to_bytes_be(),
    ]
    .concat())
}

#[cfg(test)]
pub mod tests_decider_super {
	use ark_r1cs_std::alloc::AllocVar;
	use crate::folding::circuits::CF1;
	use ark_ec::bn::BnConfig;
    use ark_bn254::{constraints::GVar, Fr, G1Projective as Projective,
		constraints::PairingVar as PairingVar, G2Projective as ProjectiveG2};
    use ark_grumpkin::{constraints::GVar as GVar2, Projective as Projective2};
    use std::time::Instant;
	use std::sync::{Arc, Mutex};

    use super::*;
    use crate::commitment::pedersen::Pedersen;
    use crate::folding::foldpot::{
		PreprocessorParamFoldPot,
		sigma_ir1cs::{SigmaIR1CS_Inst},
		sigma_ir1cs::tests::{SixRootMapper},
	};
    use crate::transcript::poseidon::poseidon_canonical_config;
	use ark_ec::pairing::Pairing;
	use crate::folding::foldpot::{
		sigma_ir1cs::{
			GadgetMapper,ZiPartTwoInst,
			tests::{gen_six_root}
		},
		sigma_cyclepair::{create_sigma_fold_pair},
		//decider_eth::{DeciderFoldPot},
		driver::{Driver, 
			tests_driver::{SumMapper}
		},
	};
	use ark_crypto_primitives::sponge::{
    	poseidon::{PoseidonConfig},
	};



    #[test]
    fn test_decider_super() {
		//1. create instance
		const H: bool = false;
       // type CS1 = Pedersen<Projective>;
		type CS1 = KZG<'static, Bn254>;
        type CS2 = Pedersen<Projective2>;
		type LK = LookupTableTwoCol_Inst<Fr>;
		type F = Fr;
		type C1 = Projective;
		type C2 = Projective2;
		type GC1 = GVar;
		type GC2 = GVar2;
		type FC = SigmaIR1CS_Inst<Fr,Projective,CS1,LK>;
		type S = Groth16<Bn254>;
		type FS = FoldPot<Projective, GVar, Projective2, GVar2, FC,
					CS1, CS2, LK, H>; 
		type E = Bn254;
		type P = PairingVar;
		type C2G2 = ProjectiveG2;

        let mut rng = ark_std::test_rng();
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let lk = LK::new(vec![
			(F::from(0u32), F::from(0u32)), //0, null entry
			(F::from(1u32), F::from(0u32)), //First, we have 5 entries [0,4]
			(F::from(1u32), F::from(1u32)), 
			(F::from(2u32), F::from(0u32)), //real table to look for sum gadget
			(F::from(2u32), F::from(1u32)), 
			(F::from(2u32), F::from(2u32)), 
			(F::from(2u32), F::from(3u32)), 
			(F::from(2u32), F::from(4u32)), 
		]);
		let lkup = Arc::new(lk);
		let (odd_mapper, even_mapper) =  
			(SumMapper::<Fr,LK>::new(true), SumMapper::<Fr,LK>::new(false));
        let mut rng = rand::rngs::OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let b_full = false;
		let vec_circ = vec![
			SigmaIR1CS_Inst::<Fr,C1,CS1,LK,H>::new_adv("oddsum".to_string(),
				poseidon_config.clone(), Rc::new(odd_mapper), b_full).unwrap(),
			SigmaIR1CS_Inst::<Fr,C1,CS1,LK,H>::new_adv("evensum".to_string(),
				poseidon_config.clone(), Rc::new(even_mapper), b_full).unwrap()];

		panic!("STOP HERE 203. Need to fix CS1E definition !!!");
		/*
		//2. create the driver
		// as lookup table 2 contains 0 to 4 will compute sum of
		// 1 + 2 +  4 + 2 + 2 = 11
		let mut num_steps = 2; //will change
		let vec_words= vec![
			vec![Fr::from(1), Fr::from(2), Fr::from(100)],
			vec![Fr::from(4), Fr::from(2), From::from(2)]
		];
		panic!("STOP HERE 702. check if it's ok to set b_full to false");
		let b_full = false;
		let driver = Driver::<E,P,C2G2, C1,GC1,C2,GC2,CS1,CS2,FC,S,LK>
			::new(poseidon_config, lkup, vec_circ, rng, b_full);
		let mut iter = vec_words.iter();
		let mut iter2 = vec_words.iter();
		let mut iter3 = vec_words.iter();
		let (vsi,m_map) = driver.pass_one(&mut iter, vec_words.len());
		panic!("STOP HERE 101");

		//3. pass two to compute the cmF
		let vsi2 = driver.pass_two(&mut iter2, vec_words.len(), &vsi, &m_map);
		println!("DEBUG USE 5017.3: vsi2.len(): {}", vsi2.len());
		panic!("STOP HERE 102");

		//4. prove_steps (and verify inside)
		println!("DEBUG USE 111 PASS 3 -----------");
		let (running_instance, incoming_instance, cyclefold_instance, 
			ivc, num_steps) = 
			driver.pass_three(&mut iter3, vec_words.len(), &vsi2, &m_map);
		panic!("STOP HERE 103");

		//5. generate the decider proof (the proof will be verified
		// in the gen_decider_proof's verifiation when cfg is test.
		let prf = driver.gen_decider_proof(&running_instance, &incoming_instance, &cyclefold_instance, &ivc, num_steps);
		assert!(prf.is_ok());
		panic!("STOP HERE 104");

		/*
        type N = FoldPotSuper<E,P,C2G2, C1, GC1, C2, GC2, FC, CS1, CS2, LK, H, >;
        N::verify(
            driver.nova_param.1.clone(), // verifier_params
            ivc.z_0.clone(),
            ivc.z_i.clone(),
            Fr::from(num_steps as u32),
            running_instance,
            incoming_instance,
            cyclefold_instance,
        )
        .unwrap();

        //4. load the DeciderEthCircuit from the generated Nova instance
        let decider_circuit = DeciderEthCircuitSuper::<E,P,C2G2, C1, GC1, C2, GC2, CS1, CS2, LK >::from_nova(ivc.clone()).unwrap();
        let cs = ConstraintSystem::<Fr>::new_ref();
        decider_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());

        //5. prepare the Decider prover & verifier params
        type D = DeciderFoldPotSuper<E,P,C2G2,C1, GC1, C2, GC2, FC, CS1, CS2, S, N, LK>;
        let (decider_pp, decider_vp) = D::preprocess(&mut rng, &driver.nova_param, ivc.clone()).unwrap();

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, ivc.clone()).unwrap();
        println!("Decider prove, {:?}", start.elapsed());


        // decider proof verification
        let start = Instant::now();
		let u_i_wrapper = CommittedInstanceFoldPotSuper{
			vec_inst: vec![ivc.u_i.clone()], //effect one
			x_1: ivc.U_i.x_1.clone(),//fake value never used
			pc_i: ivc.pc_i.clone(), //fake value never used
		};
        let verified = D::verify(
            decider_vp, ivc.i, ivc.z_0, ivc.z_i, &ivc.U_i, &u_i_wrapper,&proof,			).unwrap();
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
		*/
		*/
    }


}
