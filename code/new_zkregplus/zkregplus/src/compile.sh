# quick build 
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --tests 2>&1 | more 
#cargo check --tests 2>&1 | more 

# small example 
#RUST_BACKTRACE=1 cargo run --release --example zkreg small 
#RUST_BACKTRACE=1 

# foldpot example
#RUST_BACKTRACE=1 cargo run --example foldpot --release

# test zkpsmall example
RUST_BACKTRACE=1 cargo test --release -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_zkreg_main --show-output --nocapture

# test zkpsmall example SLOW
# RUST_BACKTRACE=1 cargo test -- test_word_extract_adv --show-output --nocapture
