fn main() {
    let mut rng1 = ark_std::test_rng();
    let mut rng2 = ark_std::test_rng();
    use rand::Rng;
    println!("rng1: {}", rng1.gen::<u64>());
    println!("rng2: {}", rng2.gen::<u64>());
}
