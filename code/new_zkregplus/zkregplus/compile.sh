# COMPILE DEBUG
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --example foldpot 2>&1 | more 

# COMPILE FULL
#RUSTFLAGS="-Awarnings" cargo build 

# -- TEST release
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" time cargo test --features "light-test" --release -- tests_driver --show-output --nocapture  
#2>&1 | less

# -- TEST no release
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 time cargo test -- tests_qa_nizk --show-output 2>&1 | more 
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 cargo test -- tests_driver --show-output 
#RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" cargo test -- tests_mod --show-output  
#2>&1 | less

# GENERATING doc
#cargo doc --no-deps --open -p folding-schemes

# gen paper discharge-approach stats (was paper_data_gen)
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 cargo test --release -p zkregplus -- test_db_bundle --show-output --nocapture

# ZK discharge of the full clean chr17 DNA sample (heavy)
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 cargo test --release -p zkregplus -- test_full_dna --show-output --nocapture

# discharge FULL clean Enron intl list (~515K) -> full/pass/fail_clean_enron_list (heartbeat + slow-file probes in stdout)
RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 cargo test -p zkregplus --release -- zkp_driver::tests_zkp_driver::collect_enron_list --exact --nocapture 2>&1 | tee /tmp/collect_enron.log

# run zkreg example small
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" time cargo run --release --example zkreg small
#2>&1 | less

# run fold pot
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" RUST_TEST_TIME_INTEGRATION=3600000,36000000 RUST_BACKTRACE=1 RUSTFLAGS="-Awarnings" time cargo run --release --example foldpot
