test: src/multiset.rs
	mkdir -p build
	rustc --test src/mod.rs -o build/test
	./build/test
