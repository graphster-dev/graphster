.PHONY = build clean doc format lint test test-doc

build:
	cargo build

clean:
	rm -rf target

doc:
	RUSTDOCFLAGS="--cfg docsrs" cargo +nightly doc --no-deps --all-features

format:
	cargo fmt

lint:
	cargo clippy --all-targets --all-features -- -D warnings

test:
	cargo test --lib --all-features

test-doc:
	cargo +nightly test --doc --all-features
