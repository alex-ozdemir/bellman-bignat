use rug::{Assign, Integer};
use std::ops::{AddAssign, MulAssign, ShlAssign, ShrAssign};
use util::verbose::in_verbose_mode;

fn _parallel_sum(v: &mut Vec<Integer>) {
    use rayon::prelude::*;
    if v.len() % 2 == 1 {
        v.push(Integer::from(0));
    }

    while v.len() > 1 {
        // length of list is always even
        assert!(v.len() % 2 == 0);

        // split the list in half and collapse the halves by summing
        let split_point = v.len() / 2;
        let (fst, snd) = v.split_at_mut(split_point);
        fst.par_iter_mut()
            .zip(snd)
            .for_each(|(f, s)| f.add_assign(s as &Integer));

        // cut length of list in half, possibly padding with '0'
        if split_point != 1 && split_point % 2 == 1 {
            v.truncate(split_point + 1);
            v[split_point].assign(0);
        } else {
            v.truncate(split_point);
        }
    }

    if v.is_empty() {
        v.push(Integer::from(0));
    }

    assert!(v.len() == 1);
}

fn _parallel_mul(a: &mut Integer, b: &mut Integer, nproc: usize) {
    use rayon::prelude::*;
    use std::mem::swap;

    // make sure a is the larger of the two values --- gives smaller operands to muls below
    if b.significant_bits() > a.significant_bits() {
        swap(a, b);
    }
    assert!(a.significant_bits() >= b.significant_bits());
    let bits_per_thread = (a.significant_bits() as usize + nproc - 1) / nproc;
    let output_bits = a.significant_bits() as usize + b.significant_bits() as usize;

    // do all the multiplications in parallel
    let mut tmp = vec![Integer::with_capacity(output_bits); nproc];
    tmp.par_iter_mut().enumerate()
        .for_each(|(p, tmp)| {
            // slice out the bits of a we want
            tmp.assign(a as &Integer);
            tmp.shr_assign((p * bits_per_thread) as u32);
            tmp.keep_bits_mut(bits_per_thread as u32);

            // multiply by b
            tmp.mul_assign(b as &Integer);

            // shift back
            tmp.shl_assign((p * bits_per_thread) as u32);
        });

    // add up the result
    _parallel_sum(&mut tmp);
    swap(a, &mut tmp[0]);
}

pub fn parallel_product(v: &mut Vec<Integer>) {
    let verb = in_verbose_mode();
    use rayon::prelude::*;
    if v.len() % 2 == 1 {
        v.push(Integer::from(1));
    }

    let n_threads = rayon::current_num_threads();
    while v.len() > 1 {
        if verb {
            println!("Remaining elements in parallel product: {}", v.len());
        }
        // invariant: length of list is always even
        assert!(v.len() % 2 == 0);

        // split the list in half; multiply first half by second half in parallel
        let split_point = v.len() / 2;
        let (fst, snd) = v.split_at_mut(split_point);

        // try to parallelize the individual multiplications, if possible
        let n_threads_per_mul = n_threads / split_point;
        if n_threads_per_mul > 1 {
            fst.par_iter_mut()
                .zip(snd)
                .for_each(|(f, s)| _parallel_mul(f, s, n_threads_per_mul));
        } else {
            fst.par_iter_mut()
                .zip(snd)
                .for_each(|(f, s)| f.mul_assign(s as &Integer));
        }

        // cut length of list in half, possibly padding with an extra '1'
        if split_point != 1 && split_point % 2 == 1 {
            v.truncate(split_point + 1);
            v[split_point].assign(1);
        } else {
            v.truncate(split_point);
        }
    }

    if v.is_empty() {
        v.push(Integer::from(1));
    }

    assert!(v.len() == 1);
}

#[cfg(test)]
mod tests {
    use super::*;
    use rug::rand::RandState;

    #[test]
    fn parith_prod_test() {
        const NELMS: usize = 2222;

        let mut rnd = RandState::new();
        _seed_rng(&mut rnd);

        let mut v = Vec::with_capacity(NELMS);
        (0..NELMS).for_each(|_| v.push(Integer::from(Integer::random_bits(2048, &mut rnd))));

        // sequential
        let mut prod = Integer::from(1);
        v.iter().for_each(|p| prod.mul_assign(p));

        // parallel
        parallel_product(&mut v);

        assert!(prod == v[0]);
    }

    #[test]
    fn parith_sum_test() {
        const NELMS: usize = 2222;

        let mut rnd = RandState::new();
        _seed_rng(&mut rnd);

        let mut v = Vec::with_capacity(NELMS);
        (0..NELMS).for_each(|_| v.push(Integer::from(Integer::random_bits(2048, &mut rnd))));

        // sequential
        let mut sum = Integer::from(0);
        v.iter().for_each(|p| sum.add_assign(p));

        // parallel
        _parallel_sum(&mut v);

        assert!(sum == v[0]);
    }

    #[test]
    fn parith_mul_test() {
        const NBITS: u32 = 1048576;

        let mut rnd = RandState::new();
        _seed_rng(&mut rnd);

        for nproc in 2..14 {
            let mut a = Integer::from(Integer::random_bits(NBITS, &mut rnd));
            let mut b = Integer::from(Integer::random_bits(2 * NBITS, &mut rnd));
            let c = Integer::from(&a * &b);
            _parallel_mul(&mut a, &mut b, nproc);
            assert_eq!(a, c);
        }
    }

    fn _seed_rng(rnd: &mut RandState) {
        use rug::integer::Order;
        rnd.seed(&Integer::from_digits(
            &rand::random::<[u64; 4]>()[..],
            Order::Lsf,
        ));
    }
}
