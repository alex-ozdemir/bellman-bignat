all: timings.pdf

merkle.csv: ./run_merkle.zsh ../../target/release/examples/set_proof
	./run_merkle.zsh > $@

timings.csv: ./run_all.zsh ../../target/release/examples/set_proof
	./run_all.zsh > $@

timings.pdf: ./timings.R ./timings.csv
	R --no-save < $<
