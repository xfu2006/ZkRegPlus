# COMPILE DEBUG
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --tests 2>&1 | more 
#cargo check --tests 2>dump.txt
#cargo check --tests 2>&1 | less

# COMPILE FULL
#RUSTFLAGS="-Awarnings" cargo build 

# -- TEST release
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" time cargo test --features "light-test" --release -- tests_driver --show-output --nocapture  
#2>&1 | less
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" time cargo test --features "light-test" --release -- tests_sigma_ir1cs --show-output --nocapture  

# -- TEST no release
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 time cargo test -- tests_driver --show-output 
#2>&1 | more 
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 cargo test -- tests_driver --show-output 
#RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" cargo test -- tests_mod --show-output  
#2>&1 | less

# GENERATING doc
#cargo doc --no-deps --open -p folding-schemes

# QUICK COMPILE
#RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" cargo check 2>&1 | less

