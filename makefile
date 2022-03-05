.DEFAULT_GOAL := frat

frat: ./src/*.rs
	cargo build --release
	mv ./target/release/frat-rs .

clean:
	rm frat-rs
