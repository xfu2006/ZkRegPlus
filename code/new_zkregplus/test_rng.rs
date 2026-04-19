use ark_std::test_rng;
use rand::Rng;

fn main() {
    let mut rng1 = test_rng();
    let mut rng2 = test_rng();
    println!("RNG 1: {}", rng1.gen::<u64>());
    println!("RNG 2: {}", rng2.gen::<u64>());
}
