#![allow(warnings)] 
use ark_ff::PrimeField;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
};
use noname::backends::r1cs::LinearCombination as NonameLinearCombination;
use noname::backends::{
    r1cs::{GeneratedWitness, R1CS},
    BackendField,
};
use noname::witness::CompiledCircuit;
use num_bigint::BigUint;

pub mod circuits;
pub mod sonobe;
pub mod utils;

//#[derive(Debug, Clone)]
pub struct NonameCircuit<BF: BackendField> {
    pub compiled_circuit: CompiledCircuit<R1CS<BF>>,
    pub witness: GeneratedWitness<BF>,
}
impl<F: PrimeField, BF: BackendField> ConstraintSynthesizer<F> for NonameCircuit<BF> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let public_io_length = self.compiled_circuit.circuit.backend.public_inputs.len()
            + self.compiled_circuit.circuit.backend.public_outputs.len();

        // arkworks assigns by default the 1 constant
        // assumes witness is: [1, public_outputs, public_inputs, private_inputs, aux]
        let witness_size = self.witness.witness.len();
        for idx in 1..witness_size {
            let value: BigUint = Into::into(self.witness.witness[idx]);
            let field_element = F::from(value);
            if idx <= public_io_length {
                cs.new_input_variable(|| Ok(field_element))?;
            } else {
                cs.new_witness_variable(|| Ok(field_element))?;
            }
        }

        let make_index = |index| {
            if index <= public_io_length {
                match index == 0 {
                    true => Variable::One,
                    false => Variable::Instance(index),
                }
            } else {
                Variable::Witness(index - (public_io_length + 1))
            }
        };

        let make_lc = |lc_data: NonameLinearCombination<BF>| {
            let mut lc = LinearCombination::<F>::zero();
            for (cellvar, coeff) in lc_data.terms.into_iter() {
                let idx = make_index(cellvar.index);
                let coeff = F::from(Into::<BigUint>::into(coeff));
                lc += (coeff, idx)
            }

            // add constant
            let constant = F::from(Into::<BigUint>::into(lc_data.constant));
            lc += (constant, make_index(0));
            lc
        };

        for constraint in self.compiled_circuit.circuit.backend.constraints {
            cs.enforce_constraint(
                make_lc(constraint.a),
                make_lc(constraint.b),
                make_lc(constraint.c),
            )?;
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;
    use ark_bn254::Fr;
    use ark_relations::r1cs::ConstraintSystem;
    use circuits::{SIMPLE_ADDITION, WITH_PUBLIC_OUTPUT_ARRAY};
    use noname::{backends::r1cs::R1csBn254Field, inputs::parse_inputs};
    use utils::compile_source_code;

    #[test]
    fn cs_is_satisfied() {
        let compiled_circuit = compile_source_code::<R1csBn254Field>(SIMPLE_ADDITION).unwrap();
        let inputs_public = r#"{"public_input": "2"}"#;
        let inputs_private = r#"{"private_input": "2"}"#;

        let json_public = parse_inputs(inputs_public).unwrap();
        let json_private = parse_inputs(inputs_private).unwrap();
        let generated_witness = compiled_circuit
            .generate_witness(json_public, json_private)
            .unwrap();

        let noname_circuit = NonameCircuit {
            compiled_circuit,
            witness: generated_witness,
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        noname_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }

    #[test]
    fn cs_is_satisfied_array() {
        let compiled_circuit =
            compile_source_code::<R1csBn254Field>(WITH_PUBLIC_OUTPUT_ARRAY).unwrap();
        let inputs_public = r#"{"public_input": ["2", "5"]}"#;
        let inputs_private = r#"{"private_input": ["8", "2"]}"#;

        let json_public = parse_inputs(inputs_public).unwrap();
        let json_private = parse_inputs(inputs_private).unwrap();
        let generated_witness = compiled_circuit
            .generate_witness(json_public, json_private)
            .unwrap();
        let noname_circuit = NonameCircuit {
            compiled_circuit,
            witness: generated_witness,
        };

        let cs = ConstraintSystem::<Fr>::new_ref();
        noname_circuit.generate_constraints(cs.clone()).unwrap();
        assert!(cs.is_satisfied().unwrap());
    }
}
