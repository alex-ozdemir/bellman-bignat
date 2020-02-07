extern crate bellman_bignat;
extern crate bincode;

use bellman_bignat::set::int_set_par::ParExpComb;

use std::env::args;

fn _usage(s: &str, argv0: &str) {
    println!("Usage: {} <file> <log_spacing> <ofile>{}", argv0, s);
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
    let log_spacing = argv.next().unwrap().parse::<usize>();
    let ofile = argv.next().unwrap();
    if log_spacing.is_err() {
        _usage("\nERROR: log_spacing must be an integer", &argv0);
    }
    let log_spacing = log_spacing.unwrap();

    let pcb = ParExpComb::from_file(&ifile, log_spacing);
    pcb.serialize(&ofile);

    // read it back in just to double check
    let test = ParExpComb::deserialize(&ofile);
    assert_eq!(pcb, test);
}
