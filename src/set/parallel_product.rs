use rug::{Assign, Integer};
use std::ops::{AddAssign, MulAssign, ShlAssign};
use util::verbose::in_verbose_mode;

fn _isqrt(n: usize) -> usize {
    use std::cmp::Ordering;

    if n < 2 {
        return n;
    }

    let mut res = 0;
    let mut linc = n.next_power_of_two().trailing_zeros() - 1;
    loop {
        let try = res | (1 << linc);
        let cres = (try * try).cmp(&n);
        if cres == Ordering::Equal {
            res = try;
            break;
        }

        let cres2 = ((try + 1) * (try + 1)).cmp(&n);
        if cres != cres2 {
            if cres2 == Ordering::Equal {
                res = try + 1;
            } else {
                res = try;
            }
            break;
        }

        if cres == Ordering::Less {
            res = try;
        }
        assert!(linc > 0);
        linc -= 1;
    }

    assert!(res * res <= n);
    assert!((res + 1) * (res + 1) > n);

    res
}

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

// Explicit lifetimes for emphasis
fn borrow_digits<'a>(integer: &'a Integer) -> &'a [u64] {
    unsafe {
        use std::slice::from_raw_parts;
        let raw = integer.as_raw();
        let size = (*raw).size as usize;
        from_raw_parts((*raw).d, size)
    }
}

fn _parallel_mul(a: &mut Integer, b: &mut Integer, nproc: usize) {
    use gmp_mpfr_sys::gmp::limb_t;
    use rayon::prelude::*;
    use std::cmp::{max, min, Ordering};
    use std::mem::{size_of, swap};

    let ac0 = a.cmp0();
    let bc0 = b.cmp0();
    if ac0 == Ordering::Equal || bc0 == Ordering::Equal {
        a.assign(0);
        return;
    }
    let negate = (ac0 == Ordering::Less) ^ (bc0 == Ordering::Less);
    a.abs_mut();
    b.abs_mut();

    // make sure a is the larger of the two values --- gives smaller operands to muls below
    if b.significant_bits() > a.significant_bits() {
        swap(a, b);
    }
    assert!(a.significant_bits() >= b.significant_bits());

    let b_split = _isqrt(nproc);
    let b_limbs = (b.significant_digits::<limb_t>() as usize + b_split - 1) / b_split;
    let b_bits = b_limbs * 8 * size_of::<limb_t>();
    let a_split = nproc / b_split;
    let a_limbs = (a.significant_digits::<limb_t>() as usize + a_split - 1) / a_split;
    let a_bits = a_limbs * 8 * size_of::<limb_t>();
    let total_bits = (a.significant_bits() + b.significant_bits()) as usize;
    let part_bits = max(a_bits, b_bits);

    let mut tmp = {
        let a_const = &*a;
        let b_const = &*b;
        // split a and b into pieces to be multiplied without too much copying
        let mut parts = vec![Integer::new(); a_split + b_split];
        parts.par_iter_mut().enumerate()
            .for_each({
                |(idx, part)| {
                    part.reserve(part_bits);
                    // Safety requires that `a_const` and `b_const` outlive `parts`.
                        let digits = if idx < a_split {
                            let adigits = borrow_digits(a_const);
                            let asize = adigits.len();
                            let adx = idx;
                            &adigits[(adx * a_limbs)..min(asize, (adx + 1) * a_limbs)]
                        } else {
                            let bdigits = borrow_digits(b_const);
                            let bsize = bdigits.len();
                            let bdx = idx - a_split;
                            &bdigits[(bdx * b_limbs)..min(bsize, (bdx + 1) * b_limbs)]
                        };
                        part.assign_digits(digits, rug::integer::Order::Lsf);
                }
            });

        // compute all cross terms in parallel
        let mut tmp = vec![Integer::new(); a_split * b_split];
        tmp.par_iter_mut().enumerate().for_each(|(tdx, tval)| {
            tval.reserve(total_bits + 32);
            let adx = tdx % a_split;
            let bdx = tdx / a_split;
            tval.assign(&parts[adx] * &parts[a_split + bdx]);
            tval.shl_assign((adx * a_bits + bdx * b_bits) as u32);
        });
        tmp
    }; // end-of-life for parts, a_const, b_const

    _parallel_sum(&mut tmp);
    swap(a, &mut tmp[0]);
    if negate {
        a.mul_assign(-1);
    }
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

        // parallelize the final big multiplication
        if split_point < 3 {
            let n_threads_per_mul = n_threads / split_point;
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
        const NBITS: u32 = 10485760;

        let mut rnd = RandState::new();
        _seed_rng(&mut rnd);

        for nproc in 2..14 {
            let mut a = Integer::from(Integer::random_bits(NBITS, &mut rnd));
            let mut b = Integer::from(Integer::random_bits(NBITS, &mut rnd));
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

    #[test]
    fn isqrt_test() {
        (0..1048576).for_each(|i| { _isqrt(i); });
    }
}
