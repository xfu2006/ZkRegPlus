# COMPILE DEBUG
#RUSTFLAGS="-Awarnings" cargo build 2>&1 | less

# COMPILE FULL
#RUSTFLAGS="-Awarnings" cargo build 

# -- TEST release
#RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=Full RUSTFLAGS="-Awarnings" cargo test --release -- folding::foldpot::decider_eth::tests --show-output 
#2>&1 | less

# -- TEST no release
RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=Full RUSTFLAGS="-Awarnings" cargo test -- folding::foldpot::veccom --show-output  
# 2>&1 | less
#RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" cargo test -- tests_mod --show-output  
#2>&1 | less

# GENERATING doc
#cargo doc --no-deps --open

# QUICK COMPILE
#RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" cargo check 2>&1 | less

