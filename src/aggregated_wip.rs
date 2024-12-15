#![allow(unused_imports)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]
#![feature(core_intrinsics)]
use ff::BatchInverter;
use ff::PrimeField;
use group::Curve;
use group::Group;
use halo2_proofs::arithmetic::best_multiexp;
use halo2_proofs::arithmetic::{CurveAffine, Field};
use halo2_proofs::transcript::Blake2bRead;
use halo2_proofs::transcript::TranscriptRead;
use halo2_proofs::transcript::{
    Blake2bWrite, Challenge255, ChallengeScalar, EncodedChallenge, TranscriptWrite,
};
use pasta_curves::arithmetic::CurveExt;
use pasta_curves::EpAffine;
use pasta_curves::{pallas, Ep, Fq};
use rand::{rngs::OsRng, Rng};
use rayon::iter::ParallelIterator;
use std::intrinsics::log2f64;
use std::io::{self, Write};
use std::mem::size_of_val;
use std::time::Instant;
// use rayon::iter::IntoParallelIterator;
use rayon::prelude::*;

#[derive(Clone)]
pub struct WipWitness<C: CurveAffine> {
    pub(crate) a: Vec<C::Scalar>,
    pub(crate) b: Vec<Vec<C::Scalar>>,
    pub(crate) alpha: C::Scalar,
    pub(crate) s: C::Scalar,
}

#[derive(Debug, Clone)]
pub struct WipProof<C: CurveAffine> {
    L: Vec<C>,
    R: Vec<C>,
    A: C,
    r_answer: C::Scalar,
    delta_answer: C::Scalar,
}

#[derive(PartialEq, Debug)]
pub enum P<C: CurveAffine> {
    Point(C),
    Terms(Vec<(C::Scalar, C)>),
}


pub fn vector_scalar_product<C: CurveAffine>(a: &[C::Scalar], s: C::Scalar) -> Vec<C::Scalar> {
    let mut acc = vec![];
    for val in a.iter() {
        acc.push(*val * s);
    }
    acc
}

pub fn add_vectors<C: CurveAffine>(a: &[C::Scalar], b: &[C::Scalar]) -> Vec<C::Scalar> {
    assert_eq!(a.len(), b.len());

    let mut acc = vec![];
    for (a, b) in a.iter().zip(b.iter()) {
        acc.push((*a) + (*b));
    }

    acc
}

pub fn inner_product<C: CurveAffine>(a: &[C::Scalar], b: &[C::Scalar]) -> C::Scalar {
    assert_eq!(a.len(), b.len());

    let mut acc = C::Scalar::from(0);
    for (a, b) in a.iter().zip(b.iter()) {
        acc += (*a) * (*b);
    }

    acc
}

pub fn multiexp<C: CurveAffine>(p: &P<C>) -> C {
    match p {
        P::Point(p) => *p,
        P::Terms(v) => {
            let (coeffs, bases): (Vec<C::Scalar>, Vec<C>) = v.into_iter().cloned().unzip();
            let mut new_bases = Vec::with_capacity(bases.len());
            for b in bases.iter() {
                let tmp = Into::<C::CurveExt>::into(*b)
                    .to_affine()
                    .coordinates()
                    .expect("Couldn't get coordinates of a point");
                new_bases.push(
                    C::from_xy(*tmp.x(), *tmp.y())
                        .expect("Couldn't construct point from coordinates"),
                );
            }
            best_multiexp::<C>(&coeffs, &new_bases).into()
        }
    }
}

fn split_vector_in_half<T: Clone>(vec: Vec<T>) -> (Vec<T>, Vec<T>) {
    let mid = vec.len() / 2 + vec.len() % 2; // calculate midpoint, extra element goes into the first half if odd length
    let (first_half, second_half) = vec.split_at(mid);
    (first_half.to_vec(), second_half.to_vec()) // convert slices to vectors
}

fn transcript_e<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
) -> C::Scalar {
    let e: ChallengeScalar<C, T> = transcript.squeeze_challenge_scalar();
    if bool::from(e.is_zero()) {
        panic!("zero challenge in final WIP round");
    }
    *e
}

fn transcript_e_v<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    transcript: &mut T,
) -> C::Scalar {
    let e: ChallengeScalar<C, T> = transcript.squeeze_challenge_scalar();
    if bool::from(e.is_zero()) {
        panic!("zero challenge in final WIP round");
    }
    *e
}

fn next_G_H<C: CurveAffine + Clone + Send + Sync, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
    g_bold1: Vec<C>,
    g_bold2: Vec<C>,
) -> (
    C::Scalar,
    C::Scalar,
    C::Scalar,
    C::Scalar,
    Vec<C>,
) {
    assert_eq!(g_bold1.len(), g_bold2.len());

    let e = transcript_e(transcript);
    let inv_e = e.invert().unwrap();

    let new_g_bold: Vec<C> = g_bold1.into_par_iter()
        .zip(g_bold2.into_par_iter())
        .map(|(g1, g2)| {
            let tmp: P<C> = P::Terms(vec![(inv_e.clone(), g1), (e.clone(), g2)]);
            multiexp(&tmp)
        })
        .collect();

    let e_square = e.square();
    let inv_e_square = inv_e.square();

    (e, inv_e, e_square, inv_e_square, new_g_bold)
}


fn next_G_H_v<C: CurveAffine + Clone + Send + Sync, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    transcript: &mut T,
    g_bold1: Vec<C>,
    g_bold2: Vec<C>,
) -> (
    C::Scalar,
    C::Scalar,
    C::Scalar,
    C::Scalar,
    Vec<C>,
) {
    assert_eq!(g_bold1.len(), g_bold2.len());

    let e = transcript_e_v(transcript);
    let inv_e = e.invert().unwrap();

    // Parallelize processing of g_bold1 and g_bold2
    let new_g_bold: Vec<C> = g_bold1.into_par_iter()
        .zip(g_bold2.into_par_iter())
        .map(|(g1, g2)| {
            let tmp: P<C> = P::Terms(vec![(inv_e.clone(), g1), (e.clone(), g2)]);
            multiexp(&tmp)
        })
        .collect();

    let e_square = e.square();
    let inv_e_square = inv_e.square();

    (e, inv_e, e_square, inv_e_square, new_g_bold)
}



pub fn prove<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
    witness: WipWitness<C>,
    generators_g: Vec<C>,
    generator_g: Vec<C>,
    generator_h: C,
    p: P<C>,
    m: usize,
) -> WipProof<C> {
    let rng = OsRng;

    let mut g_bold = generators_g.clone();

    let mut a = witness.a.clone();
    let mut b = witness.b.clone();
    let mut alpha = witness.alpha;
    for b_i in b.iter() {
        assert_eq!(a.len(), b_i.len());
    }

    // // From here on, g_bold.len() is used as n
    assert_eq!(g_bold.len(), a.len());

    let mut L_vec: Vec<C> = vec![];
    let mut R_vec: Vec<C> = vec![];

    // // else n > 1 case from figure 1
    while g_bold.len() > 1 {
        let b_clone = b.clone();
        let (a1, a2) = split_vector_in_half(a.clone());
        let (b1, b2): (Vec<Vec<_>>, Vec<Vec<_>>) =
            b_clone.into_iter().map(split_vector_in_half).unzip();
        let (g_bold1, g_bold2) = split_vector_in_half(g_bold.clone());

        let n_hat = g_bold1.len();
        assert_eq!(a1.len(), n_hat);
        assert_eq!(a2.len(), n_hat);
        for b_i in b1.iter() {
            assert_eq!(n_hat, b_i.len());
        }
        for b_i in b2.iter() {
            assert_eq!(n_hat, b_i.len());
        }
        assert_eq!(g_bold1.len(), n_hat);
        assert_eq!(g_bold2.len(), n_hat);

        let d_l = C::Scalar::random(rng);
        let d_r = C::Scalar::random(rng);

        let mut c_l: Vec<C::Scalar> = vec![];
        let mut c_r: Vec<C::Scalar> = vec![];

        for b_i in b2.iter() {
            let tmp = inner_product::<C>(&a1, b_i);
            c_l.push(tmp);
        }
        for b_i in b1.iter() {
            let tmp = inner_product::<C>(&a2, b_i);
            c_r.push(tmp);
        }

        let mut L_terms: Vec<(C::Scalar, C)> = a1
            .iter()
            .copied()
            .zip(g_bold2.iter().copied())
            .chain(c_l.iter().copied().zip(generator_g.iter().copied()))
            .collect::<Vec<_>>();
        L_terms.push((d_l, generator_h));
        let L = multiexp(&P::Terms(L_terms));
        L_vec.push(L);
        transcript.write_point(L).unwrap();

        let mut R_terms: Vec<(C::Scalar, C)> = a2
            .iter()
            .copied()
            .zip(g_bold1.iter().copied())
            .chain(c_r.iter().copied().zip(generator_g.iter().copied()))
            .collect::<Vec<_>>();
        R_terms.push((d_r, generator_h));
        let R = multiexp(&P::Terms(R_terms));
        R_vec.push(R);
        transcript.write_point(R).unwrap();

        let (e, inv_e, e_square, inv_e_square);
        (e, inv_e, e_square, inv_e_square, g_bold) =
            next_G_H(transcript, g_bold1, g_bold2);

        let tmp1: Vec<C::Scalar> = a1.into_iter().map(|x| x * e).collect();
        let tmp2: Vec<C::Scalar> = a2.into_iter().map(|x| x * inv_e).collect();
        a = tmp1.iter().zip(tmp2.iter()).map(|(&a, &b)| a + b).collect();

        b = vec![];
        for (b1_i, b2_i) in b1.iter().zip(b2.iter()) {
            let tmp1: Vec<C::Scalar> = b1_i.into_iter().map(|x| *x * inv_e).collect();
            let tmp2: Vec<C::Scalar> = b2_i.into_iter().map(|x| *x * e).collect();
            b.push(tmp1.iter().zip(tmp2.iter()).map(|(&a, &b)| a + b).collect());
        }

        alpha += (d_l * e_square) + (d_r * inv_e_square);

        debug_assert_eq!(g_bold.len(), a.len());
        for b_i in b.iter() {
            debug_assert_eq!(g_bold.len(), b_i.len());
        }
    }

    // // n == 1 case from figure 1
    assert_eq!(g_bold.len(), 1);
    assert_eq!(a.len(), 1);
    for b_i in b.iter() {
        assert_eq!(b_i.len(), 1);
    }

    let mut r = C::Scalar::random(rng);
    let mut sum_r = C::Scalar::ZERO;
    for i in 0..m {
        sum_r += r*witness.s.pow_vartime([i as u64, 0, 0, 0]);
    }
    let delta = C::Scalar::random(rng);

    let mut g_terms: Vec<(C::Scalar, C)> = vec![];
    for (g_i, b_i) in generator_g.iter().zip(b.iter()) {
        g_terms.push(((sum_r * b_i[0]), *g_i))
    }

    let mut A_terms: Vec<(C::Scalar, C)> = vec![(sum_r, g_bold[0]), (delta, generator_h)];
    A_terms.extend(g_terms);
    let A: C = multiexp(&P::Terms(A_terms));
    transcript.write_point(A).unwrap();

    let e = transcript_e(transcript);
    let r_answer = r + (a[0] * e);
    let delta_answer = delta + (alpha * e);
    transcript.write_scalar(r_answer).unwrap();
    transcript.write_scalar(delta_answer).unwrap();

    WipProof {
        L: L_vec,
        R: R_vec,
        A,
        r_answer,
        delta_answer,
    }
}

pub fn verify<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    transcript: &mut T,
    generators_g: Vec<C>,
    generator_g: Vec<C>,
    generator_h: C,
    omega: C::Scalar,
    b: Vec<Vec<C::Scalar>>,
    p: P<C>,
) {

    let mut P_terms = match p {
        P::Point(point) => vec![(C::Scalar::ONE, point)],
        P::Terms(terms) => terms,
    };

    let mut g_bold = generators_g.clone();
    let mut b: Vec<Vec<<<C as CurveAffine>::CurveExt as CurveExt>::ScalarExt>> = b.clone();

    while g_bold.len() > 1 {
        let (b1, b2): (Vec<Vec<_>>, Vec<Vec<_>>) =
            b.into_iter().map(split_vector_in_half).unzip();
        let (g_bold1, g_bold2) = split_vector_in_half(g_bold.clone());


        let L = transcript.read_point().unwrap();
        let R = transcript.read_point().unwrap();

        let (e, inv_e, e_square, inv_e_square);
        (e, inv_e, e_square, inv_e_square, g_bold) =
            next_G_H_v(transcript, g_bold1, g_bold2);
    
        b = vec![];
        for (b1_i, b2_i) in b1.iter().zip(b2.iter()) {
            let tmp1: Vec<C::Scalar> = b1_i.into_iter().map(|x| *x * inv_e).collect();
            let tmp2: Vec<C::Scalar> = b2_i.into_iter().map(|x| *x * e).collect();
            b.push(tmp1.iter().zip(tmp2.iter()).map(|(&a, &b)| a + b).collect());
        }

        P_terms.push((e_square, L));
        P_terms.push((inv_e_square, R));
    }
    let A = transcript.read_point().unwrap();

    let e = transcript_e_v(transcript);
    let r_answer = transcript.read_scalar().unwrap();
    let delta_answer = transcript.read_scalar().unwrap();
    
    let mut multiexp_var = P_terms;
    for (scalar, _) in multiexp_var.iter_mut() {
        *scalar *= -e;
    }

    for i in 0..g_bold.len() {
        multiexp_var.push((r_answer, g_bold[i].clone()));
    }

    multiexp_var.push((-C::Scalar::ONE, A));

    let mut i = 0;
    for g_i in generator_g.iter() {
        multiexp_var.push((r_answer * b[i][0], *g_i));
        i += 1;
    }
    multiexp_var.push((delta_answer, generator_h));

    assert_eq!(multiexp(&P::Terms(multiexp_var)), C::identity());
}

pub fn gens<C: CurveAffine>(k: u64, n: u64) -> (Vec<C>, Vec<C>, C) {
    let mut gens_g = vec![];
    let mut gen_g = vec![];
    let hasher = C::CurveExt::hash_to_curve("GENERATORS");

    for _ in 0..n {
        let mut my_array: [u8; 11] = [0; 11];

        let mut rng = rand::thread_rng();
        for i in 0..11 {
            my_array[i] = rng.gen();
        }
        let c = hasher(&my_array);
        gens_g.push(c);
    }

    for _ in 0..k {
        let mut my_array: [u8; 11] = [0; 11];

        let mut rng = rand::thread_rng();
        for i in 0..11 {
            my_array[i] = rng.gen();
        }
        let c = hasher(&my_array);
        gen_g.push(c);
    }


    let mut my_array: [u8; 11] = [0; 11];

    let mut rng = rand::thread_rng();
    for i in 0..11 {
        my_array[i] = rng.gen();
    }
    let c = hasher(&my_array);
    let gen_h = c;

    return (
        gens_g.into_iter().map(|ep| ep.into()).collect(),
        gen_g.into_iter().map(|ep| ep.into()).collect(),
        gen_h.into(),
    );
}

fn main() {
    let k = 64;
    let n = k;
    let m = 10;
    println!("n is {n}");
    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(k);

    for _ in 0..n {
        let mut rng = rand::thread_rng();
        a.push(pallas::Scalar::from(rng.gen::<u64>()));
    }

    let omega = pallas::Scalar::ROOT_OF_UNITY;

    for i in 0..k {
        let mut tmp = vec![];
        for j in 0..n {
            tmp.push(omega.pow_vartime([(j*i) as u64, 0, 0, 0]));        
        }
        b.push(tmp.clone());
    }

    let mut w = WipWitness::<pallas::Affine> {
        a,
        b,
        alpha: pallas::Scalar::from(5),
        s: pallas::Scalar::from(8),
    };

    let (gens_g, gen_g, gen_h) = gens::<pallas::Affine>(k as u64, n as u64);
    
    let mut sum_a = vec![pallas::Scalar::ZERO; n];
    for i in 0..m {
        let exponent: pallas::Scalar = w.s.pow([i as u64, 0, 0, 0]);
        let tmp = vector_scalar_product::<pallas::Affine>(&w.a, exponent);
        sum_a = add_vectors::<pallas::Affine>(&sum_a, &tmp);
    }

    let mut ip = vec![];
    for i in 0..k {
        ip.push(inner_product::<pallas::Affine>(&sum_a, &w.b[i]))
    }

    let mut commit = Ep::identity();
    for i in 0..n {
        commit += gens_g[i] * sum_a[i];
    }

    for i in 0..k {
        commit += gen_g[i] * ip[i];
    }
    commit += gen_h * w.alpha;

    w.a = sum_a;
    let mut transcript = Blake2bWrite::<_, pallas::Affine, Challenge255<_>>::init(vec![]);
    let start_time = Instant::now();
    prove(
        &mut transcript,
        w.clone(),
        gens_g.clone().into_iter().map(|ep| ep.into()).collect(),
        gen_g.clone().into_iter().map(|ep| ep.into()).collect(),
        gen_h.clone().into(),
        P::Point(commit.into()),
        m
    );
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("Elapsed proving time: {:?}ms", elapsed_time.as_millis());
    let proof_bytes = transcript.finalize();

    let mut transcript = Blake2bRead::<_, pallas::Affine, Challenge255<_>>::init(&*proof_bytes);
    let start_time = Instant::now();
    verify(
        &mut transcript,
        gens_g.into_iter().map(|ep| ep.into()).collect(),
        gen_g.into_iter().map(|ep| ep.into()).collect(),
        gen_h.into(),
        omega,
        w.b,
        P::Point(commit.into()),
    );
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("Elapsed verifier time: {:?}ms", elapsed_time.as_millis());
    println!("Proof size is {}kb", (proof_bytes.len()) as f64 / 1024.);
}
