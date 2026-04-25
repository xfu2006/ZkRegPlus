# quick build
#cargo check --tests 2>&1 | more
#RUSTFLAGS="-C link-args=-fuse-ld=lld -Awarnings" cargo check --tests 2>&1 | more

# -----------------------------------------------------------------------
# NUMA-aware page placement:
#   On multi-socket boxes (e.g. GCP c2d-highmem-112: 2 NUMA nodes
#   x 56 cores) prefix cargo with `numactl --interleave=all` so
#   memory pages are spread evenly across both memory controllers.
#   On a single-NUMA-node box the wrapper is a no-op.
#   Auto-detect below: count nodes via `numactl --hardware`; if >=2
#   and numactl is on PATH, wrap. Otherwise run plain.
# -----------------------------------------------------------------------

NUMACTL_PREFIX=""
if command -v numactl >/dev/null 2>&1; then
    n_nodes=$(numactl --hardware 2>/dev/null \
              | awk '/^available:/ {print $2}')
    if [ -n "$n_nodes" ] && [ "$n_nodes" -ge 2 ]; then
        NUMACTL_PREFIX="numactl --interleave=all"
        echo "compile.sh: detected $n_nodes NUMA nodes; wrapping with: $NUMACTL_PREFIX"
    else
        echo "compile.sh: single NUMA node (or numactl --hardware failed); no wrap"
    fi
else
    echo "compile.sh: numactl not installed; no wrap"
fi

# test zkpsmall example
#RUST_MIN_STACK=8388608
RUST_BACKTRACE=1 $NUMACTL_PREFIX cargo test --lib --release -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test --lib -- test_zkreg_main --show-output --nocapture
#RUST_BACKTRACE=1 cargo test --lib -- test_zkreg_main --show-output --nocapture
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
