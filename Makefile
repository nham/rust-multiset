build: src/multiset.rs
	cargo build
	./target/mod

test: src/multiset.rs
	mkdir -p build
	rustc --test src/mod.rs -o build/test
	./build/test
