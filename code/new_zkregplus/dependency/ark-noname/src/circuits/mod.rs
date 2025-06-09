// TODO: add additional circuits
// file containing various circuits to test library

pub const SIMPLE_ADDITION: &str = "fn main(pub public_input: Field, private_input: Field) {
    let xx = private_input + public_input;
    let yy = private_input * public_input;
    assert_eq(xx, yy);
}
";

pub const WITH_PUBLIC_OUTPUT_ARRAY: &str =
    "fn main(pub public_input: [Field; 2], private_input: [Field; 2]) -> [Field; 2]{
    let xx = private_input[0] + public_input[0];
    let yy = private_input[1] * public_input[1];
    assert_eq(yy, xx);
    return [xx, yy];
}";
