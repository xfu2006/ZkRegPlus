use crate::Config;

/// Specifies the constraints for computing a pairing in the BLS12-377 bilinear
/// group.
pub type PairingVar = ark_r1cs_std::pairing::bn::PairingVar<Config>;

#[test]
fn test() {
    use crate::Bn254;
    ark_curve_constraint_tests::pairing::bilinearity_test
		::<Bn254, PairingVar>().unwrap();
    ark_curve_constraint_tests::pairing::g2_prepare_consistency_test
		::<Bn254, PairingVar>().unwrap();
}
