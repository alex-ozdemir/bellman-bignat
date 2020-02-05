all: timings.pdf

timings.csv: ./run_all.zsh ../../target/release/examples/set_proof
	$< > $@

timings.pdf: ./timings.R ./timings.csv
	R $@ --no-save < $<
