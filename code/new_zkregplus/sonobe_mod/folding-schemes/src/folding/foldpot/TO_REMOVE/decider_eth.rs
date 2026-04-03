/* Modified 08/14/2024.
   Mainly to add the handling of cfF (the fixed segment
   Modified 08/26/2024
   Mainly to add lookup and word batching support
*/
/// This file implements the onchain (Ethereum's EVM) decider.
use ark_relations::r1cs::ConstraintSystem;
use ark_relations::r1cs::ConstraintSynthesizer;
use ark_bn254::Bn254;
use ark_crypto_primitives::sponge::Absorb;
use ark_ec::{AffineRepr, CurveGroup, Group};
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::Groth16;
use ark_r1cs_std::{groups::GroupOpsBounds, prelude::CurveVar, ToConstraintFieldGadget};
use ark_snark::SNARK;
use ark_std::rand::{CryptoRng, RngCore};
use ark_std::{One, Zero};
use core::marker::PhantomData;

pub use super::decider_eth_circuit::{DeciderEthCircuit, KZGChallengesGadget};
use crate::folding::{
	foldpot::{FoldPot,CommittedInstanceFoldPot,NIFSFoldPot},
};
use crate::commitment::{
    kzg::{Proof as KZGProof, KZG},
    pedersen::Params as PedersenParams,
    CommitmentScheme,
};
use crate::folding::circuits::{nonnative::affine::NonNativeAffineVar, CF2};
use crate::frontend::FCircuit;
use crate::Error;
use crate::{Decider as DeciderTrait, FoldingScheme};
use crate::folding::{foldpot::
	sigma_ir1cs::{SigmaIR1CS, LookupTableTwoCol,LookupTableTwoCol_Inst}
};
use ark_crypto_primitives::sponge::{
	poseidon::{PoseidonConfig, PoseidonSponge},
	CryptographicSponge,
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
pub struct DeciderFoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS, LK> {
    _c1: PhantomData<C1>,
    _gc1: PhantomData<GC1>,
    _c2: PhantomData<C2>,
    _gc2: PhantomData<GC2>,
    _fc: PhantomData<FC>,
    _cs1: PhantomData<CS1>,
    _cs2: PhantomData<CS2>,
    _s: PhantomData<S>,
    _fs: PhantomData<FS>,
	_lk: PhantomData<LK>,
}

impl<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS, LK> DeciderTrait<C1, C2, FC, FS>
    for DeciderFoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, S, FS, LK>
where
    C1: CurveGroup,
    C2: CurveGroup,
    GC1: CurveVar<C1, CF2<C1>> + ToConstraintFieldGadget<CF2<C1>>,
    GC2: CurveVar<C2, CF2<C2>> + ToConstraintFieldGadget<CF2<C2>>,
    FC: FCircuit<C1::ScalarField> + SigmaIR1CS<C1::ScalarField, LK>,
	LK: LookupTableTwoCol<C1::ScalarField>,
    // CS1 is a KZG commitment, where challenge is C1::Fr elem
    CS1: CommitmentScheme<
        C1,
        ProverChallenge = C1::ScalarField,
        Challenge = C1::ScalarField,
        Proof = KZGProof<C1>,
    >,
    // enforce that the CS2 is Pedersen commitment scheme, since we're at Ethereum's EVM decider
    CS2: CommitmentScheme<C2, ProverParams = PedersenParams<C2>>,
    S: SNARK<C1::ScalarField>,
    FS: FoldingScheme<C1, C2, FC>,
    <C1 as CurveGroup>::BaseField: PrimeField,
    <C2 as CurveGroup>::BaseField: PrimeField,
    <C1 as Group>::ScalarField: Absorb,
    <C2 as Group>::ScalarField: Absorb,
    C1: CurveGroup<BaseField = C2::ScalarField, ScalarField = C2::BaseField>,
    for<'b> &'b GC1: GroupOpsBounds<'b, C1, GC1>,
    for<'b> &'b GC2: GroupOpsBounds<'b, C2, GC2>,
    // constrain FS into Nova, since this is a Decider specifically for Nova
    FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, false>: From<FS>,
    crate::folding::foldpot::ProverParamsFoldPot<C1, C2, CS1, CS2, LK, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::ProverParam>,
    crate::folding::foldpot::VerifierParamsFoldPot<C1, C2, CS1, CS2, false>:
        From<<FS as FoldingScheme<C1, C2, FC>>::VerifierParam>,
{
    type PreprocessorParam = (FS::ProverParam, FS::VerifierParam);
    type ProverParam = (S::ProvingKey, CS1::ProverParams);
    type Proof = Proof<C1, CS1, S>;
    /// VerifierParam = (pp_hash, snark::vk, commitment_scheme::vk, kzg_lk_col1, kzg_lk_col2)
    type VerifierParam = (C1::ScalarField, S::VerifyingKey, CS1::VerifierParams, C1, C1); //ADDED two group elements as the KZG commitments to two cols of lkup
    type PublicInput = Vec<C1::ScalarField>;
    type CommittedInstance = CommittedInstanceFoldPot<C1>;

    fn preprocess(
        mut rng: impl RngCore + CryptoRng,
        prep_param: &Self::PreprocessorParam,
        fs: FS,
    ) -> Result<(Self::ProverParam, Self::VerifierParam), Error> {
        let circuit =
            DeciderEthCircuit::<C1, GC1, C2, GC2, CS1, CS2, LK>::from_nova::<FC>(fs.into()).unwrap();

        // get the Groth16 specific setup for the circuit
        let (g16_pk, g16_vk) = S::circuit_specific_setup(circuit, &mut rng).unwrap();

        // get the FoldingScheme prover & verifier params from Nova
        #[allow(clippy::type_complexity)]
        let nova_pp: <FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::ProverParam = prep_param.0.clone().into();

		//, kzg_lk_col1, kzg_lk_col2);
        #[allow(clippy::type_complexity)]
        let nova_vp: <FoldPot<C1, GC1, C2, GC2, FC, CS1, CS2, LK, false> as FoldingScheme<
            C1,
            C2,
            FC,
        >>::VerifierParam = prep_param.1.clone().into();
        let pp_hash = nova_vp.pp_hash()?;

        let pp = (g16_pk, nova_pp.cs_pp);
		let kzg_lk_col1 = nova_vp.kzg_lk_col1;
		let kzg_lk_col2 = nova_vp.kzg_lk_col2;
        let vp = (pp_hash, g16_vk, nova_vp.cs_vp, kzg_lk_col1, kzg_lk_col2);
        Ok((pp, vp))
    }

    fn prove(
        mut rng: impl RngCore + CryptoRng,
        pp: Self::ProverParam,
        folding_scheme: FS,
    ) -> Result<Self::Proof, Error> {
        let (snark_pk, cs_pk): (S::ProvingKey, CS1::ProverParams) = pp;

        let circuit = DeciderEthCircuit::<C1, GC1, C2, GC2, CS1, CS2, LK>::from_nova::<FC>(
            folding_scheme.into(),
        )?;

		#[cfg(test)]{
        	let cs = ConstraintSystem::<C1::ScalarField>::new_ref();
        	circuit.clone().generate_constraints(cs.clone()).unwrap();
        	assert!(cs.is_satisfied().unwrap());
		}

        let snark_proof = S::prove(&snark_pk, circuit.clone(), &mut rng)
            .map_err(|e| Error::Other(e.to_string()))?;

        let cmT = circuit.cmT.unwrap();
        let r_Fr = circuit.r.unwrap();
        let W_i1 = circuit.W_i1.unwrap();

        // get the challenges that have been already computed when preparing the circuit inputs in
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

		// Added
        let challenge_lkup = circuit
            .kzg_c_lkup
            .ok_or(Error::MissingValue("kzg_c_lkup".to_string()))?;

        // generate KZG proofs
        let U_cmW_proof = CS1::prove_with_challenge(
            &cs_pk,
            challenge_W,
            &W_i1.W,
            &C1::ScalarField::zero(),
            None,
        )?;
        let U_cmE_proof = CS1::prove_with_challenge(
            &cs_pk,
            challenge_E,
            &W_i1.E,
            &C1::ScalarField::zero(),
            None,
        )?;

		//Added
		let (start_F, size_F) = (W_i1.start_F, W_i1.size_F);
		let F = (&W_i1.W)[start_F..start_F+size_F].to_vec();
        let U_cmF_proof = CS1::prove_with_challenge(
            &cs_pk,
            challenge_F,
            &F,
            &C1::ScalarField::zero(),
            None,
        )?;

		//Added for lookup
        let kzg_lkup_col1_proof = CS1::prove_with_challenge(
            &cs_pk,
			challenge_lkup,
            &circuit.lkup_col1_rev.expect("col1 rev null!"),
            &C1::ScalarField::zero(),
            None,
        )?;
        let kzg_lkup_col2_proof = CS1::prove_with_challenge(
            &cs_pk,
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

    fn verify(
        vp: Self::VerifierParam,
        i: C1::ScalarField,
        z_0: Vec<C1::ScalarField>,
        z_i: Vec<C1::ScalarField>,
        running_instance: &Self::CommittedInstance,
        incoming_instance: &Self::CommittedInstance,
        proof: &Self::Proof,
    ) -> Result<bool, Error> {
        if i <= C1::ScalarField::one() {
            return Err(Error::NotEnoughSteps);
        }

        let (pp_hash, snark_vk, cs_vk, kzg_lk_col1, kzg_lk_col2): (C1::ScalarField, S::VerifyingKey, CS1::VerifierParams, C1, C1) = vp;

        // compute U = U_{d+1}= NIFS.V(U_d, u_d, cmT)
        let U = NIFSFoldPot::<C1, CS1>::verify(proof.r, running_instance, incoming_instance, &proof.cmT);

        let (cmE_x, cmE_y) = NonNativeAffineVar::inputize(U.cmE)?;
        let (cmW_x, cmW_y) = NonNativeAffineVar::inputize(U.cmW)?;
        let (cmT_x, cmT_y) = NonNativeAffineVar::inputize(proof.cmT)?;
		//added cmF
        let (cmF_x, cmF_y) = NonNativeAffineVar::inputize(U.cmF)?;

        let public_input: Vec<C1::ScalarField> = vec![
            vec![pp_hash, i],
            z_0,
            z_i,
            vec![U.u], //the following u, x, cmE, cmW, cmF belongs to U_i1
            U.x.clone(), //following the order of to_sponge_field_elements
            cmE_x,		//of CommittedInstanceVarFoldPot
            cmE_y,
            cmW_x,
            cmW_y,
            cmF_x,
            cmF_y,
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


        let snark_v = S::verify(&snark_vk, &public_input, &proof.snark_proof)
            .map_err(|e| Error::Other(e.to_string()))?;
        if !snark_v {
            return Err(Error::SNARKVerificationFail);
        }

        // we're at the Ethereum EVM case, so the CS1 is KZG commitments
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[0],
            &U.cmW,
            &proof.kzg_proofs[0],
        )?;
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[1],
            &U.cmE,
            &proof.kzg_proofs[1],
        )?;
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[2],
            &U.cmF,
            &proof.kzg_proofs[2],
        )?;
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[3],
			&kzg_lk_col1,
            &proof.kzg_proofs[3], //col1 eval passed as public input to circ
        )?;
        CS1::verify_with_challenge(
            &cs_vk,
            proof.kzg_challenges[3], //use the same challenge as col1, later
									 //can batch
			&kzg_lk_col2,
            &proof.kzg_proofs[4], //col2 eval passed as public input to circ
        )?;

        Ok(true)
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
pub mod tests {
    use ark_bn254::{constraints::GVar, Fr, G1Projective as Projective};
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
	use crate::folding::foldpot::{
		sigma_ir1cs::{
			GadgetMapper,ZiPartTwoInst,
			tests::{gen_six_root}
		}
	};
	use ark_crypto_primitives::sponge::{
    	poseidon::{PoseidonConfig},
	};



    #[test]
    fn test_decider() {
        //1. use FoldPot as FoldingScheme
        type CS1 = KZG<'static, Bn254>;
        type CS2 = Pedersen<Projective2>;
		type LK = LookupTableTwoCol_Inst<Fr>;
		type FC = SigmaIR1CS_Inst<Fr,Projective,KZG<'static,Bn254>,LK>;
		const H: bool = false;
		let num_steps = 5usize;


        type N = FoldPot<
            Projective,
            GVar,
            Projective2,
            GVar2,
			FC,
			CS1,
			CS2,
			LK,
            false,
        >;
        type D = DeciderFoldPot<
            Projective,
            GVar,
            Projective2,
            GVar2,
			FC,
			CS1,
			CS2,
            Groth16<Bn254>, // here we define the Snark to use in the decider
            N,              // here we define the FoldingScheme to use
			LK,
        >;

		//2. generate the problem statements for 5 steps
        let mut rng = rand::rngs::OsRng;
        let poseidon_config = poseidon_canonical_config::<Fr>();
		let (lkup, six_ir1cs, vec_stmt) = gen_six_root(num_steps);
		let size_F = six_ir1cs.get_size_f();
        let (F_circuit1, F_circuit) = (six_ir1cs.clone(), six_ir1cs.clone());
        let prep_param = PreprocessorParamFoldPot::new(poseidon_config.clone(), F_circuit.clone(), lkup, size_F);
        let nova_params = N::preprocess(&mut rng, &prep_param).unwrap();

		//3. PASS1: generate cm_F
		let zero = Fr::zero();
		let z0_part2 = ZiPartTwoInst::<Fr>::new(zero, &poseidon_config);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);
		let z_0 = vec![zero, z0_part2_hash];
        let mut nova1 =
            FoldPot::<Projective, GVar, Projective2, GVar2, 
				FC, CS1, CS2, LK, H>::init(
                &nova_params,
                F_circuit.clone(),
                z_0.clone(),
            )
            .unwrap();
		let mut hash_cmF= Fr::zero();
		for i in 0..num_steps{
			hash_cmF = nova1.compute_step_hc_cmF(hash_cmF, &vec_stmt[i])
				.expect("hash_cmf generation error");
		}
		let z0_part2 = ZiPartTwoInst::<Fr>::new(hash_cmF, &poseidon_config);
		let z0_part2_hash = z0_part2.hash(&poseidon_config);


		//4. PASS2. prove steps
        let start = Instant::now();
        let z_0 = vec![hash_cmF, z0_part2_hash]; //[stage hc_cmF, z_0]
        let mut nova = N::init(&nova_params, F_circuit, z_0.clone()).unwrap();
        println!("Nova initialized, {:?}", start.elapsed());
        let start = Instant::now();
		for i in 0..num_steps{
        	nova.prove_step(&mut rng, vec_stmt[i].to_vec(), None).unwrap();
        	println!("prove_step, {:?}", start.elapsed());
		}

        // prepare the Decider prover & verifier params
        let (decider_pp, decider_vp) = D::preprocess(&mut rng, &nova_params, nova.clone()).unwrap();

        // decider proof generation
        let start = Instant::now();
        let proof = D::prove(rng, decider_pp, nova.clone()).unwrap();
        println!("Decider prove, {:?}", start.elapsed());


        // decider proof verification
        let start = Instant::now();
        let verified = D::verify(
            decider_vp, nova.i, nova.z_0, nova.z_i, &nova.U_i, &nova.u_i, &proof,
        )
        .unwrap();
        assert!(verified);
        println!("Decider verify, {:?}", start.elapsed());
    }
}
