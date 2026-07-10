use noname::{
    backends::{r1cs::R1CS, BackendField},
    circuit_writer::CircuitWriter,
    compiler::{typecheck_next_file, Sources},
    type_checker::TypeChecker,
    witness::CompiledCircuit,
};

// from: https://github.com/zksecurity/noname/blob/main/src/tests/modules.rs
// TODO: this will not work in the case where we are using libraries
pub fn compile_source_code<BF: BackendField>(
    code: &str,
) -> Result<CompiledCircuit<R1CS<BF>>, noname::error::Error> {
    let mut sources = Sources::new();

    // parse the transitive dependency
    let mut tast = TypeChecker::<R1CS<BF>>::new();
    let mut node_id = 0;
    node_id = typecheck_next_file(
        &mut tast,
        None,
        &mut sources,
        "main.no".to_string(),
        code.to_string(),
        node_id,
    )
    .unwrap();
    let r1cs = R1CS::<BF>::new();
    // compile
    CircuitWriter::generate_circuit(tast, r1cs)
}
