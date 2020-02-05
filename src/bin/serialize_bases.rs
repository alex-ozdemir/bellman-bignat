extern crate bellman_bignat;
extern crate bincode;

use bellman_bignat::set::int_set_par::ParExpComb;

use std::env::args;

const DFLT_LOG_BITS_PER_ELM: usize = 11;

fn _usage(s: &str, argv0: &str) {
    println!("Usage: {} <file> <max_expt> <ofile>{}", argv0, s);
    std::process::exit(1);
}

fn main() {
    let mut argv = args();
    let argv0 = argv.next().unwrap();
    if argv.len() < 3 {
        _usage("", &argv0);
    }

    // handle arguments
    let ifile = argv.next().unwrap();
    let max_expt = argv.next().unwrap().parse::<usize>();
    let ofile = argv.next().unwrap();
    if max_expt.is_err() {
        _usage("\nERROR: max_expt must be an integer", &argv0);
    }
    let max_expt = max_expt.unwrap();

    let bits_per_elm = if argv.len() > 0 {
        let bpe = argv.next().unwrap().parse::<usize>();
        if bpe.is_err() {
            DFLT_LOG_BITS_PER_ELM
        } else {
            bpe.unwrap()
        }
    } else {
        DFLT_LOG_BITS_PER_ELM
    };

    let pcb = ParExpComb::from_file(&ifile, max_expt, bits_per_elm);
    pcb.serialize(&ofile);

    // read it back in just to double check
    let test = ParExpComb::deserialize(&ofile);
    assert_eq!(pcb, test);
}
