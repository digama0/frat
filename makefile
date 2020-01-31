.DEFAULT_GOAL := frat

frat: ./src/elab.rs
	cargo build --release 
	mv ./target/release/frat-rs .

clean:
	rm frat-rs
