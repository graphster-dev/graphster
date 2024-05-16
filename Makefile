.PHONY = build lint format clean

build:
  cargo build

lint:
  cargo clippy --all-targets --all-features -- -D warnings

format:
  cargo fmt

clean:
  rm -rf target

