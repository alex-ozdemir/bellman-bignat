all: timings.pdf

timings.csv: ./run_all.zsh ../../target/release/examples/set_proof
	./run_all.zsh > $@

timings.pdf: ./timings.R ./timings.csv
	R --no-save < $<
