# quick build 
#cargo check --tests 2>&1 | more 
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --tests 2>&1 | more 

# test zkpsmall example
#RUST_BACKTRACE=1 cargo test --lib -- test_zkreg_main --show-output --nocapture 
RUST_BACKTRACE=1 
cargo test --lib --release -- test_zkreg_main --show-output --nocapture 
#RUST_BACKTRACE=full cargo test -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test -- test_zkreg_main --show-output --nocapture

# small example 
#RUST_BACKTRACE=1 cargo run --release --example zkreg small 
#RUST_BACKTRACE=1 

# foldpot example
#RUST_BACKTRACE=1 cargo run --release --example foldpot 


# test zkpsmall example SLOW
# RUST_BACKTRACE=1 cargo test -- test_word_extract_adv --show-output --nocapture
