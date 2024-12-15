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
use std::io::{self, Write};
use std::mem::size_of_val;
use std::time::Instant;

#[derive(Clone)]
pub struct WipWitness<C: CurveAffine> {
    pub(crate) a: Vec<C::Scalar>,
    pub(crate) b: Vec<Vec<C::Scalar>>,
    pub(crate) alpha: C::Scalar,
}

#[derive(Debug, Clone)]
pub struct WipProof<C: CurveAffine> {
    L: Vec<C>,
    R: Vec<C>,
    A: C,
    r_answer: C::Scalar,
    delta_answer: C::Scalar,
}

impl<C: CurveAffine> WipProof<C> {
    pub fn write_to_transcript<E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
        &self,
        transcript: &mut T,
    ) -> io::Result<()> {
        for l in self.L.iter() {
            transcript.write_point(*l)?;
        }

        for r in self.R.iter() {
            transcript.write_point(*r)?;
        }

        transcript.write_point(self.A)?;
        transcript.write_scalar(self.r_answer)?;
        transcript.write_scalar(self.delta_answer)?;

        Ok(())
    }

    pub fn read_from_transcript<E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
        transcript: &mut T,
        k: u32,
    ) -> Result<WipProof<C>, io::Error> {
        let mut R = vec![];
        let mut L = vec![];
        for _ in 0..k {
            L.push(transcript.read_point()?);
        }
        for _ in 0..k {
            R.push(transcript.read_point()?);
        }
        let A = transcript.read_point()?;
        let r_answer = transcript.read_scalar()?;
        let delta_answer = transcript.read_scalar()?;
        Ok(WipProof {
            L,
            R,
            A,
            r_answer,
            delta_answer,
        })
    }

    pub fn serialize(&self) -> io::Result<Vec<u8>> {
        let mut buffer = Vec::new();

        // Serialize vectors L and R
        for l in &self.L {
            buffer.write_all(l.to_bytes().as_ref())?;
        }
        for r in &self.R {
            buffer.write_all(r.to_bytes().as_ref())?;
        }

        // Serialize A
        buffer.write_all(self.A.to_bytes().as_ref())?;

        // Serialize Scalars
        buffer.write_all(self.r_answer.to_repr().as_ref())?;
        buffer.write_all(self.delta_answer.to_repr().as_ref())?;

        Ok(buffer)
    }
}

#[derive(PartialEq, Debug)]
pub enum P<C: CurveAffine> {
    Point(C),
    Terms(Vec<(C::Scalar, C)>),
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

fn challenge_products<C: CurveAffine>(challenges: &[(C::Scalar, C::Scalar)]) -> Vec<C::Scalar> {
    let mut products = vec![C::Scalar::ONE; 1 << challenges.len()];

    if !challenges.is_empty() {
        products[0] = challenges[0].1;
        products[1] = challenges[0].0;

        for (j, challenge) in challenges.iter().enumerate().skip(1) {
            let mut slots = (1 << (j + 1)) - 1;
            while slots > 0 {
                products[slots] = products[slots / 2] * challenge.0;
                products[slots - 1] = products[slots / 2] * challenge.1;

                slots = slots.saturating_sub(2);
            }
        }

        // Sanity check since if the above failed to populate, it'd be critical
        for product in &products {
            debug_assert!(!bool::from(product.is_zero()));
        }
    }

    products
}

fn transcript_A<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
    A: C,
) -> C::Scalar {
    transcript.common_point(A.into());

    let e: ChallengeScalar<C, T> = transcript.squeeze_challenge_scalar();
    if bool::from(e.is_zero()) {
        panic!("zero challenge in final WIP round");
    }
    *e
}

fn transcript_A_v<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    transcript: &mut T,
    A: C,
) -> C::Scalar {
    transcript.common_point(A.into());

    let e: ChallengeScalar<C, T> = transcript.squeeze_challenge_scalar();
    if bool::from(e.is_zero()) {
        panic!("zero challenge in final WIP round");
    }
    *e
}

fn transcript_L_R<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
    L: C,
    R: C,
) -> C::Scalar {
    transcript.common_point(L.into());
    transcript.common_point(R.into());

    let e: ChallengeScalar<C, T> = transcript.squeeze_challenge_scalar();
    if bool::from(e.is_zero()) {
        panic!("zero challenge in final WIP round");
    }
    *e
}

fn transcript_L_R_v<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    transcript: &mut T,
    L: C,
    R: C,
) -> C::Scalar {
    transcript.common_point(L.into());
    transcript.common_point(R.into());

    let e: ChallengeScalar<C, T> = transcript.squeeze_challenge_scalar();
    if bool::from(e.is_zero()) {
        panic!("zero challenge in final WIP round");
    }
    *e
}

fn next_G_H<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
    g_bold1: Vec<C>,
    g_bold2: Vec<C>,
    h_bold1: Vec<Vec<C>>,
    h_bold2: Vec<Vec<C>>,
    L: C,
    R: C,
) -> (
    C::Scalar,
    C::Scalar,
    C::Scalar,
    C::Scalar,
    Vec<C>,
    Vec<Vec<C>>,
) {
    assert_eq!(g_bold1.len(), g_bold2.len());
    for (h1, h2) in h_bold1.iter().zip(h_bold2.iter()) {
        assert_eq!(h1.len(), h2.len());
        assert_eq!(g_bold1.len(), h1.len());
    }

    let e = transcript_L_R(transcript, L, R);
    let inv_e = e.invert().unwrap();

    let mut new_g_bold = Vec::with_capacity(g_bold1.len());
    for g_bold in g_bold1.iter().cloned().zip(g_bold2.iter().cloned()) {
        let tmp: P<C> = P::Terms(vec![(inv_e, g_bold.0), (e, g_bold.1)]);
        new_g_bold.push(multiexp(&tmp));
    }

    let mut new_h_bold = Vec::with_capacity(h_bold1.len());
    for (h_bold1_vec, h_bold2_vec) in h_bold1.iter().zip(h_bold2.iter()) {
        let mut inner_results = Vec::with_capacity(h_bold1_vec.len());
        for (h1, h2) in h_bold1_vec.iter().cloned().zip(h_bold2_vec.iter().cloned()) {
            let tmp: P<C> = P::Terms(vec![(e, h1), (inv_e, h2)]);
            inner_results.push(multiexp(&tmp));
        }
        new_h_bold.push(inner_results);
    }

    let e_square = e.square();
    let inv_e_square = inv_e.square();

    (e, inv_e, e_square, inv_e_square, new_g_bold, new_h_bold)
}

fn next_G_H_v<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    transcript: &mut T,
    g_bold1: Vec<C>,
    g_bold2: Vec<C>,
    h_bold1: Vec<Vec<C>>,
    h_bold2: Vec<Vec<C>>,
    L: C,
    R: C,
) -> (
    C::Scalar,
    C::Scalar,
    C::Scalar,
    C::Scalar,
    Vec<C>,
    Vec<Vec<C>>,
) {
    assert_eq!(g_bold1.len(), g_bold2.len());
    for (h1, h2) in h_bold1.iter().zip(h_bold2.iter()) {
        assert_eq!(h1.len(), h2.len());
        assert_eq!(g_bold1.len(), h1.len());
    }

    let e = transcript_L_R_v(transcript, L, R);
    let inv_e = e.invert().unwrap();

    let mut new_g_bold = Vec::with_capacity(g_bold1.len());
    for g_bold in g_bold1.iter().cloned().zip(g_bold2.iter().cloned()) {
        let tmp: P<C> = P::Terms(vec![(inv_e, g_bold.0), (e, g_bold.1)]);
        new_g_bold.push(multiexp(&tmp));
    }

    let mut new_h_bold = Vec::with_capacity(h_bold1.len());
    for (h_bold1_vec, h_bold2_vec) in h_bold1.iter().zip(h_bold2.iter()) {
        let mut inner_results = Vec::with_capacity(h_bold1_vec.len());
        for (h1, h2) in h_bold1_vec.iter().cloned().zip(h_bold2_vec.iter().cloned()) {
            let tmp: P<C> = P::Terms(vec![(e, h1), (inv_e, h2)]);
            inner_results.push(multiexp(&tmp));
        }
        new_h_bold.push(inner_results);
    }

    let e_square = e.square();
    let inv_e_square = inv_e.square();

    (e, inv_e, e_square, inv_e_square, new_g_bold, new_h_bold)
}

pub fn prove<C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptWrite<C, E>>(
    transcript: &mut T,
    witness: WipWitness<C>,
    generators_g: Vec<C>,
    generators_h: Vec<Vec<C>>,
    generator_g: Vec<C>,
    generator_h: C,
    p: P<C>,
) -> WipProof<C> {
    let mut rng = OsRng;

    // Check P has the expected relationship
    if let P::Point(p) = &p {
        let mut p_terms = witness
            .a
            .iter()
            .copied()
            .zip(generators_g.iter().copied())
            .collect::<Vec<_>>();

        for (witness_b_vec, generators_h_vec) in witness.b.iter().zip(generators_h.iter()) {
            let additional_terms: Vec<(C::Scalar, C)> = witness_b_vec
                .iter()
                .copied()
                .zip(generators_h_vec.iter().copied())
                .collect::<Vec<_>>();
            p_terms.extend(additional_terms);
        }
        let mut additional_terms: Vec<(C::Scalar, C)> = vec![];
        for (b_i, g_i) in witness.b.iter().zip(generator_g.iter()) {
            additional_terms.push((inner_product::<C>(&witness.a, b_i), *g_i));
        }
        p_terms.extend(additional_terms);
        p_terms.push((witness.alpha, generator_h));
        assert_eq!(multiexp(&P::Terms(p_terms)), *p);
    }

    let mut g_bold = generators_g.clone();
    let mut h_bold = generators_h.clone();

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
        let (h_bold1, h_bold2): (Vec<Vec<_>>, Vec<Vec<_>>) =
            h_bold.into_iter().map(split_vector_in_half).unzip();

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
        for h_i in h_bold1.iter() {
            assert_eq!(n_hat, h_i.len());
        }
        for h_i in h_bold2.iter() {
            assert_eq!(n_hat, h_i.len());
        }

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
        for (witness_b_vec, generators_h_vec) in b2.iter().zip(h_bold1.iter()) {
            let additional_terms = witness_b_vec
                .iter()
                .copied()
                .zip(generators_h_vec.iter().copied())
                .collect::<Vec<_>>();
            L_terms.extend(additional_terms);
        }
        let L = multiexp(&P::Terms(L_terms));
        L_vec.push(L);

        let mut R_terms: Vec<(C::Scalar, C)> = a2
            .iter()
            .copied()
            .zip(g_bold1.iter().copied())
            .chain(c_r.iter().copied().zip(generator_g.iter().copied()))
            .collect::<Vec<_>>();
        R_terms.push((d_r, generator_h));
        for (witness_b_vec, generators_h_vec) in b1.iter().zip(h_bold2.iter()) {
            let additional_terms = witness_b_vec
                .iter()
                .copied()
                .zip(generators_h_vec.iter().copied())
                .collect::<Vec<_>>();
            R_terms.extend(additional_terms);
        }
        let R = multiexp(&P::Terms(R_terms));
        R_vec.push(R);

        let (e, inv_e, e_square, inv_e_square);
        (e, inv_e, e_square, inv_e_square, g_bold, h_bold) =
            next_G_H(transcript, g_bold1, g_bold2, h_bold1, h_bold2, L, R);

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
        for h_i in h_bold.iter() {
            debug_assert_eq!(g_bold.len(), h_i.len());
        }
        for b_i in b.iter() {
            debug_assert_eq!(g_bold.len(), b_i.len());
        }
    }

    // // n == 1 case from figure 1
    assert_eq!(g_bold.len(), 1);
    for h_i in h_bold.iter() {
        assert_eq!(h_i.len(), 1);
    }
    assert_eq!(a.len(), 1);
    for b_i in b.iter() {
        assert_eq!(b_i.len(), 1);
    }

    let r = C::Scalar::random(rng);
    let delta = C::Scalar::random(rng);

    let mut g_terms: Vec<(C::Scalar, C)> = vec![];
    for (g_i, b_i) in generator_g.iter().zip(b.iter()) {
        g_terms.push(((r * b_i[0]), *g_i))
    }

    let mut A_terms: Vec<(C::Scalar, C)> = vec![(r, g_bold[0]), (delta, generator_h)];
    A_terms.extend(g_terms);
    let A = multiexp(&P::Terms(A_terms));
    // A_terms.zeroize();

    let e = transcript_A(transcript, A);
    let r_answer = r + (a[0] * e);
    let delta_answer = delta + (alpha * e);

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
    proof: WipProof<C>,
    generators_g: Vec<C>,
    generators_h: Vec<Vec<C>>,
    generator_g: Vec<C>,
    generator_h: C,
    b: Vec<Vec<C::Scalar>>,
    p: P<C>,
) {
    // Verify the L/R lengths
    {
        let mut lr_len = 0;
        while (1 << lr_len) < generators_g.len() {
            lr_len += 1;
        }
        assert_eq!(proof.L.len(), lr_len);
        assert_eq!(proof.R.len(), lr_len);
        assert_eq!(generators_g.len(), 1 << lr_len);
    }

    let mut P_terms = match p {
        P::Point(point) => vec![(C::Scalar::ONE, point)],
        P::Terms(terms) => terms,
    };

    let mut b_clone = b.clone();
    let mut challenges = Vec::with_capacity(proof.L.len());
    let product_cache = {
        let mut es = Vec::with_capacity(proof.L.len());
        for (L, R) in proof.L.iter().zip(proof.R.iter()) {
            es.push(transcript_L_R_v(transcript, *L, *R));
        }

        let mut inv_es = es.clone();
        let mut scratch = vec![C::Scalar::ZERO; es.len()];
        BatchInverter::invert_with_external_scratch(&mut inv_es, &mut scratch);
        drop(scratch);

        assert_eq!(es.len(), inv_es.len());
        assert_eq!(es.len(), proof.L.len());
        assert_eq!(es.len(), proof.R.len());
        for ((e, inv_e), (L, R)) in es
            .drain(..)
            .zip(inv_es.drain(..))
            .zip(proof.L.iter().zip(proof.R.iter()))
        {
            debug_assert_eq!(e.invert().unwrap(), inv_e);

            challenges.push((e, inv_e));

            let e_square = e.square();
            let inv_e_square = inv_e.square();
            P_terms.push((e_square, *L));
            P_terms.push((inv_e_square, *R));
        }

        for (e_, inve_) in challenges.iter() {
            let (b1, b2): (Vec<Vec<_>>, Vec<Vec<_>>) =
                b_clone.into_iter().map(split_vector_in_half).unzip();
            b_clone = vec![];
            for (b1_i, b2_i) in b1.iter().zip(b2.iter()) {
                let tmp1: Vec<C::Scalar> = b1_i.into_iter().map(|x| *x * inve_).collect();
                let tmp2: Vec<C::Scalar> = b2_i.into_iter().map(|x| *x * e_).collect();
                b_clone.push(tmp1.iter().zip(tmp2.iter()).map(|(&a, &b)| a + b).collect());
            }
        }

        challenge_products::<C>(&challenges)
    };

    let e = transcript_A_v(transcript, proof.A);

    let mut multiexp_var = P_terms;
    for (scalar, _) in multiexp_var.iter_mut() {
        *scalar *= -e;
    }

    for i in 0..generators_g.len() {
        let mut scalar = product_cache[i] * proof.r_answer;
        multiexp_var.push((scalar, generators_g[i].clone()));
    }

    for i in 0..generators_h.len() {
        let se = b_clone[i][0] * e;
        for j in 0..generators_h[i].len() {
            multiexp_var.push((
                se * product_cache[product_cache.len() - 1 - j],
                generators_h[i][j].clone(),
            ));
        }
    }

    multiexp_var.push((-C::Scalar::ONE, proof.A));
    let mut i = 0;
    for g_i in generator_g.iter() {
        multiexp_var.push((proof.r_answer * b_clone[i][0], *g_i));
        i += 1;
    }
    multiexp_var.push((proof.delta_answer, generator_h));

    assert_eq!(multiexp(&P::Terms(multiexp_var)), C::identity());
}

pub fn gens<C: CurveAffine>(k: u64, n: u64) -> (Vec<C>, Vec<Vec<C>>, Vec<C>, C) {
    let mut gens_g = vec![];
    let mut gens_h = vec![];
    let mut gen_g = vec![];
    let hasher = C::CurveExt::hash_to_curve("GENERATORS");

    for _i in 0..n {
        let mut my_array: [u8; 11] = [0; 11];

        let mut rng = rand::thread_rng();
        for i in 0..11 {
            my_array[i] = rng.gen();
        }
        let c = hasher(&my_array);
        gens_g.push(c);
    }

    for _i in 0..k {
        let mut my_array: [u8; 11] = [0; 11];

        let mut rng = rand::thread_rng();
        for i in 0..11 {
            my_array[i] = rng.gen();
        }
        let c = hasher(&my_array);
        gen_g.push(c);
    }

    for _j in 0..k {
        let mut temp_gens = vec![];
        for _i in 0..n {
            let mut my_array: [u8; 11] = [0; 11];

            let mut rng = rand::thread_rng();
            for i in 0..11 {
                my_array[i] = rng.gen();
            }
            let c = hasher(&my_array);
            temp_gens.push(c);
        }
        gens_h.push(temp_gens);
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
        gens_h
            .into_iter()
            .map(|inner_vec| inner_vec.into_iter().map(|ep| ep.into()).collect())
            .collect(),
        gen_g.into_iter().map(|ep| ep.into()).collect(),
        gen_h.into(),
    );
}

fn main() {
    let k = 1;
    let n = 64;
    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(k);

    for _i in 0..n {
        let mut rng = rand::thread_rng();
        a.push(pallas::Scalar::from(rng.gen::<u64>()));
    }

    for _j in 0..k {
        let mut temp_gens = Vec::with_capacity(n);
        for _i in 0..n {
            let mut rng = rand::thread_rng();
            temp_gens.push(pallas::Scalar::from(rng.gen::<u64>()));
        }
        b.push(temp_gens);
    }

    let w = WipWitness {
        a,
        b,
        alpha: pallas::Scalar::from(5),
    };

    let (gens_g, gens_h, gen_g, gen_h) = gens::<pallas::Affine>(k as u64, n as u64);
    let ip = vec![
        inner_product::<pallas::Affine>(&w.a, &w.b[0]),
        // inner_product(&w.a, &w.b[1]),
        // inner_product(&w.a, &w.b[2]),
        // inner_product(&w.a, &w.b[3]),
    ];
    // let ip = vec![inner_product(&w.a, &w.b[0]), inner_product(&w.a, &w.b[1]), inner_product(&w.a, &w.b[2]), C::Scalar::from(4)];
    let mut commit = Ep::identity();
    for i in 0..n {
        commit += gens_g[i] * w.a[i];
    }
    for i in 0..k {
        for j in 0..n {
            commit += gens_h[i][j] * w.b[i][j];
        }
    }

    for i in 0..k {
        commit += gen_g[i] * ip[i];
    }
    commit += gen_h * w.alpha;

    let mut transcript = Blake2bWrite::<_, pallas::Affine, Challenge255<_>>::init(vec![]);
    let start_time = Instant::now();
    let proof = prove(
        &mut transcript,
        w.clone(),
        gens_g.clone().into_iter().map(|ep| ep.into()).collect(),
        gens_h
            .clone()
            .into_iter()
            .map(|inner_vec| inner_vec.into_iter().map(|ep| ep.into()).collect())
            .collect(),
        gen_g.clone().into_iter().map(|ep| ep.into()).collect(),
        gen_h.clone().into(),
        P::Point(commit.into()),
    );
    println!("proof from porver {:?}", proof);
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("Elapsed proving time: {:?}ms", elapsed_time.as_millis());
    proof.write_to_transcript(&mut transcript).unwrap();

    let proof_bytes = proof.serialize().unwrap();
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&*proof_bytes);
    let proof = WipProof::<pallas::Affine>::read_from_transcript(&mut transcript, 6).unwrap();
    println!("proof from verifer {:?}", proof);
    let mut transcript1 = Blake2bRead::<_, _, Challenge255<_>>::init(&*proof_bytes);

    let start_time = Instant::now();
    verify(
        &mut transcript1,
        proof.clone(),
        gens_g.into_iter().map(|ep| ep.into()).collect(),
        gens_h
            .into_iter()
            .map(|inner_vec| inner_vec.into_iter().map(|ep| ep.into()).collect())
            .collect(),
        gen_g.into_iter().map(|ep| ep.into()).collect(),
        gen_h.into(),
        w.b,
        P::Point(commit.into()),
    );
    let end_time = Instant::now();
    let elapsed_time = end_time.duration_since(start_time);
    println!("Elapsed verifier time: {:?}ms", elapsed_time.as_millis());
    println!("Proof size is {}kb", size_of_val(&proof));
}
