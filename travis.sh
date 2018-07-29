export RUST_TEST_THREADS=1
cargo build --verbose
cargo test -j 1 --verbose

#cargo test --verbose -- --nocapture
#cd eval
#cargo run --release --example adder
#cargo run --release --example filter
#cargo run --release --example to_string
#cargo run --release --example unique_elms
#cargo run --release --example quickhull -- -s 10000 -t 250
