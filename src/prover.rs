use crate::setup::{evaluate_in_exponent, SetupOutput};
use ark_ec::models::short_weierstrass::*;
use ark_ff::*;
use ark_poly::univariate::DensePolynomial;
use ark_poly::*;
use ark_test_curves::bls12_381::Fr;
use ark_test_curves::bls12_381::*;
use rand::prelude::*;

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// https://github.com/ETHorHIL/Plonk_Py/blob/master/prover.py
pub fn prover_algo(witness: Vec<Fr>, setup_output: &SetupOutput) -> Proof {
    println!("Starting setup algorithm");
    let n = witness.len() / 3;
    assert!(n & n - 1 == 0, "n must be a power of 2");
    let (id_domain, perm_domain, k, ss) = &setup_output.perm_precomp;
    let qs = &setup_output.qs;
    let crs = &setup_output.crs;

    /*
    # We need to convert between representations to multiply and divide more
    # efficiently. In round 3 we have to divide a polynomial of degree 4*n+6
    # Not sure if there is a big benefit in keeping the lower order
    # representations or if it makes sense to do everything in the highest
    # order 8*n right away...
     */

    // # polys represented with n points
    let domain_n = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let witness_poly_a =
        Evaluations::from_vec_and_domain(witness[..n].to_vec(), domain_n).interpolate();
    let witness_poly_b =
        Evaluations::from_vec_and_domain(witness[n..n * 2].to_vec(), domain_n).interpolate();
    let witness_poly_c =
        Evaluations::from_vec_and_domain(witness[2 * n..].to_vec(), domain_n).interpolate();

    //#  polys represented with 2*n points
    let domain_2n = Radix2EvaluationDomain::<Fr>::new(2 * n).unwrap();
    let witness_poly_a_ext = witness_poly_a.evaluate_over_domain(domain_2n);
    let witness_poly_b_ext = witness_poly_b.evaluate_over_domain(domain_2n);
    let witness_poly_c_ext = witness_poly_c.evaluate_over_domain(domain_2n);
    // polys correct, same as witness_poly_a etc when I interpolate

    let [s1, s2, s3] = ss;
    let domain_3n = Radix2EvaluationDomain::<Fr>::new(8 * n).unwrap();
    let s1_ext3 = s1.clone().evaluate_over_domain(domain_3n);
    let s2_ext3 = s2.clone().evaluate_over_domain(domain_3n);
    let s3_ext3 = s3.clone().evaluate_over_domain(domain_3n);
    let p_i_poly_ext3 = setup_output
        .p_i_poly
        .clone()
        .evaluate_over_domain(domain_3n);
    let q_l_ext3 = qs[0].clone().evaluate_over_domain(domain_3n);
    let q_r_ext3 = qs[1].clone().evaluate_over_domain(domain_3n);
    let q_m_ext3 = qs[2].clone().evaluate_over_domain(domain_3n);
    let q_o_ext3 = qs[3].clone().evaluate_over_domain(domain_3n);
    let q_c_ext3 = qs[4].clone().evaluate_over_domain(domain_3n);

    /*
    # Following the paper, we are using the Fiat Shamir Heuristic. We are
    # Simulating 5 rounds of communication with the verifier using a
    # random oracle for verifier answers */
    println!("Starting Round 1...");

    // Generate "random" blinding scalars, seeding to make things reproducible for me
    let mut rng = rand::rngs::StdRng::from_seed([0; 32]);
    let rand_scalars: Vec<Fr> = (0..9).map(|_x| Fr::from(rng.next_u64())).collect();

    /*
    # Generate polys with the random scalars as coefficients and convert to
    # evaluation representation. These are needed for zero knowledge to
    # obfuscate the witness.
    */
    let a_blind_poly_ext =
        DensePolynomial::from_coefficients_vec(vec![rand_scalars[1], rand_scalars[0]])
            .mul_by_vanishing_poly(domain_n);
    let b_blind_poly_ext =
        DensePolynomial::from_coefficients_vec(vec![rand_scalars[3], rand_scalars[2]])
            .mul_by_vanishing_poly(domain_n);
    let c_blind_poly_ext =
        DensePolynomial::from_coefficients_vec(vec![rand_scalars[5], rand_scalars[4]])
            .mul_by_vanishing_poly(domain_n);
    let a_blind_poly_ext = a_blind_poly_ext.evaluate_over_domain(domain_2n);
    let b_blind_poly_ext = b_blind_poly_ext.evaluate_over_domain(domain_2n);
    let c_blind_poly_ext = c_blind_poly_ext.evaluate_over_domain(domain_2n);

    /*
    # These polynomals have random evaluations at all points except ROOTS where
    # they evaluate to the witness
    */
    let a_poly_ext = &a_blind_poly_ext + &witness_poly_a_ext;
    let b_poly_ext = &b_blind_poly_ext + &witness_poly_b_ext;
    let c_poly_ext = &c_blind_poly_ext + &witness_poly_c_ext;

    // # Evaluate the witness polynomials in the exponent using the CRS
    let a_eval_exp = evaluate_in_exponent(&crs, &a_poly_ext.clone().interpolate());
    let b_eval_exp = evaluate_in_exponent(&crs, &(b_poly_ext.clone().interpolate()));
    let c_eval_exp = evaluate_in_exponent(&crs, &(c_poly_ext.clone().interpolate()));

    let first_output = [a_eval_exp, b_eval_exp, c_eval_exp];
    println!("Round 1 Finished with output: {:?}", first_output);

    println!("Starting Round 2...");
    //# Compute permutation challenges from imaginary verifier
    let beta = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(first_output, 0))).next_u64());
    let gamma = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(first_output, 1))).next_u64());

    // Compute permutation polynomial. z_1 is the blinding summand needed for ZK
    let z_1 = DensePolynomial::from_coefficients_vec(vec![
        rand_scalars[8],
        rand_scalars[7],
        rand_scalars[6],
    ]);
    let z_1 = z_1.evaluate_over_domain(domain_2n).interpolate();
    let z_1 = z_1.mul_by_vanishing_poly(domain_n);
    let mut accumulator_poly_eval = vec![Fr::from(1)];
    let evaluations_temp: Vec<Fr> = (0..(n - 1))
        .map(|i| accumulator_factor(&n, &i, &witness, &beta, &id_domain, &perm_domain, &gamma))
        .collect();
    accumulator_poly_eval.extend(evaluations_temp);
    let accumulator_poly =
        Evaluations::from_vec_and_domain(accumulator_poly_eval, domain_n).interpolate();
    let accumulator_poly = z_1
        + accumulator_poly
            .evaluate_over_domain(domain_2n)
            .interpolate();

    let second_output = evaluate_in_exponent(&crs, &accumulator_poly);
    println!("Round 2 Finished with output: {}", second_output);

    println!("Starting Round 3...");
    let alpha = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(first_output, second_output))).next_u64(),
    );

    let accumulator_poly_ext3 = accumulator_poly.clone().evaluate_over_domain(domain_3n);

    //# The third summand of t has the accumulator poly evaluated at a shift
    let accumulator_poly_shift_evaluations = evaluate_poly_with_shift(
        accumulator_poly,
        &domain_3n,
        &domain_n.elements().nth(1).unwrap(),
    );
    let accumulator_poly_ext3_shift =
        Evaluations::from_vec_and_domain(accumulator_poly_shift_evaluations, domain_3n);

    let a_poly_ext3 = a_poly_ext
        .clone()
        .interpolate()
        .evaluate_over_domain(domain_3n);

    let b_poly_ext3 = b_poly_ext
        .clone()
        .interpolate()
        .evaluate_over_domain(domain_3n);

    let c_poly_ext3 = c_poly_ext
        .clone()
        .interpolate()
        .evaluate_over_domain(domain_3n);

    let id_poly_1_ext3 =
        DensePolynomial::from_coefficients_vec(vec![gamma, beta]).evaluate_over_domain(domain_3n);
    let id_poly_2_ext3 = DensePolynomial::from_coefficients_vec(vec![gamma, beta * k])
        .evaluate_over_domain(domain_3n);
    let id_poly_3_ext3 = DensePolynomial::from_coefficients_vec(vec![gamma, beta * k.pow([2])])
        .evaluate_over_domain(domain_3n);

    let gamma_poly =
        DensePolynomial::from_coefficients_vec(vec![gamma]).evaluate_over_domain(domain_3n);

    let mut l_1 = vec![Fr::from(1)];
    l_1.extend((0..n - 1).map(|_x| Fr::from(0)).collect::<Vec<Fr>>());
    let l_1 = Evaluations::from_vec_and_domain(l_1, domain_n).interpolate();

    /*
    # Compute quotient polynomial: we are dividing by the vanishing poly which
    # has zeros at n roots so we need to do division by swapping to a coset
    # first summand should have degree 3n+1, second and third should have
    # degree 4n + 5
    */
    let t = &(&a_poly_ext3 * &b_poly_ext3) * &q_m_ext3;
    let t = &t + &(&a_poly_ext3 * &q_l_ext3);
    let t = &t + &(&b_poly_ext3 * &q_r_ext3);
    let t = &t + &(&c_poly_ext3 * &q_o_ext3);
    let t = &t + &q_c_ext3.clone();
    let t = &t + &p_i_poly_ext3;

    let alpha_poly =
        DensePolynomial::from_coefficients_vec(vec![alpha]).evaluate_over_domain(domain_3n);
    let alpha_squared_poly = DensePolynomial::from_coefficients_vec(vec![alpha.pow([2])])
        .evaluate_over_domain(domain_3n);
    let beta_poly =
        DensePolynomial::from_coefficients_vec(vec![beta]).evaluate_over_domain(domain_3n);

    let t_mul = &(&(&(&(&a_poly_ext3.clone() + &id_poly_1_ext3)
        * &(&b_poly_ext3 + &id_poly_2_ext3))
        * &(&c_poly_ext3 + &id_poly_3_ext3))
        * &accumulator_poly_ext3)
        * &alpha_poly;
    let t = &t + &t_mul;

    let t_mul = &(&a_poly_ext3.clone() + &(&s1_ext3 * &beta_poly)) + &gamma_poly.clone();
    let t_mul = &t_mul * &(&(&b_poly_ext3 + &(&s2_ext3 * &beta_poly)) + &gamma_poly.clone());
    let t_mul = &t_mul * &(&(&c_poly_ext3 + &(&s3_ext3 * &beta_poly)) + &gamma_poly.clone());
    let t_mul = &t_mul * &accumulator_poly_ext3_shift;
    let t_mul = &t_mul * &alpha_poly;

    let t = &t - &t_mul;
    let one_poly =
        DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]).evaluate_over_domain(domain_3n);
    let t = &t
        + &(&(&(&accumulator_poly_ext3 - &one_poly)
            * &l_1.clone().evaluate_over_domain(domain_3n))
            * &alpha_squared_poly);

    let t = t.interpolate().divide_by_vanishing_poly(domain_n).unwrap();
    let t = t.0;
    let t_coeff = t.coeffs();

    /*
    # We split up the polynomial t in three polynomials so that:
    # t= t_lo + x^n*t_mid + t^2n*t_hi
    # I found that n has actually to be (n+2) to accomodate the CRS because
    # t can be of degree 4n+5
    */
    let t_lo = DensePolynomial::from_coefficients_vec(t_coeff[..n + 2].to_vec());
    let t_mid = DensePolynomial::from_coefficients_vec(t_coeff[n + 2..2 * (n + 2)].to_vec());
    let t_hi = DensePolynomial::from_coefficients_vec(t_coeff[2 * (n + 2)..].to_vec());

    let t_lo_eval_exp = evaluate_in_exponent(&crs, &t_lo);
    let t_mid_eval_exp = evaluate_in_exponent(&crs, &t_mid);
    let t_hi_eval_exp = evaluate_in_exponent(&crs, &t_hi);

    let third_output = [t_lo_eval_exp, t_mid_eval_exp, t_hi_eval_exp];
    println!("Round 3 Finished with output: {:?}", third_output);

    println!("Starting Round 4...");
    //# Compute the evaluation challenge
    let zeta = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&((first_output, second_output), third_output)))
            .next_u64(),
    );
    let zeta_poly =
        DensePolynomial::from_coefficients_vec([zeta].to_vec()).evaluate_over_domain(domain_3n);

    // Compute the opening evaluations
    let a_zeta =
        DensePolynomial::from_coefficients_vec([a_poly_ext.interpolate().evaluate(&zeta)].to_vec())
            .evaluate_over_domain(domain_3n);
    let b_zeta =
        DensePolynomial::from_coefficients_vec([b_poly_ext.interpolate().evaluate(&zeta)].to_vec())
            .evaluate_over_domain(domain_3n);
    let c_zeta =
        DensePolynomial::from_coefficients_vec([c_poly_ext.interpolate().evaluate(&zeta)].to_vec())
            .evaluate_over_domain(domain_3n);
    let s_1_zeta = DensePolynomial::from_coefficients_vec([s1.evaluate(&zeta)].to_vec())
        .evaluate_over_domain(domain_3n);
    let s_2_zeta = DensePolynomial::from_coefficients_vec([s2.evaluate(&zeta)].to_vec())
        .evaluate_over_domain(domain_3n);
    let t_zeta = DensePolynomial::from_coefficients_vec([t.evaluate(&zeta)].to_vec())
        .evaluate_over_domain(domain_3n);
    let accumulator_shift_zeta = DensePolynomial::from_coefficients_vec(
        [accumulator_poly_ext3
            .clone()
            .interpolate()
            .evaluate(&(zeta * domain_n.elements().nth(1).unwrap()))]
        .to_vec(),
    )
    .evaluate_over_domain(domain_3n);

    let k_poly =
        DensePolynomial::from_coefficients_vec([*k].to_vec()).evaluate_over_domain(domain_3n);
    let k_sq_poly = DensePolynomial::from_coefficients_vec([k.pow([2])].to_vec())
        .evaluate_over_domain(domain_3n);

    //# Compute linerisation polynomial
    let r = &(&q_m_ext3 * &a_zeta) * &b_zeta;
    let r = &r + &(&q_l_ext3 * &a_zeta);
    let r = &r + &(&q_r_ext3 * &b_zeta);
    let r = &r + &(&q_o_ext3 * &c_zeta);
    let r = &r + &q_c_ext3;

    let r_mul = &accumulator_poly_ext3;
    let r_mul = r_mul * &(&(&a_zeta + &(&beta_poly * &zeta_poly)) + &gamma_poly.clone());
    let r_mul =
        &r_mul * &(&(&b_zeta + &(&beta_poly * &(&k_poly * &zeta_poly))) + &gamma_poly.clone());
    let r_mul =
        &r_mul * &(&(&c_zeta + &(&beta_poly * &(&k_sq_poly * &zeta_poly))) + &gamma_poly.clone());
    let r_mul = &r_mul * &alpha_poly;
    let r = &r + &r_mul;
    let r_mul = &s3_ext3 * &(&(&a_zeta + &(&beta_poly * &s_1_zeta)) + &gamma_poly.clone());
    let r_mul = &r_mul * &(&(&b_zeta + &(&beta_poly * &s_2_zeta)) + &gamma_poly);
    let r_mul = &r_mul * &alpha_poly;
    let r_mul = &r_mul * &beta_poly;
    let r_mul = &r_mul * &accumulator_shift_zeta;

    let r = &r - &r_mul;

    let r_mul = &accumulator_poly_ext3
        * &(&DensePolynomial::from_coefficients_vec([l_1.evaluate(&zeta)].to_vec())
            .evaluate_over_domain(domain_3n)
            * &alpha_squared_poly);
    let r = &r + &r_mul;
    let r_coeff = &r.clone().interpolate();

    //# Evaluate r at zeta
    let r_zeta = DensePolynomial::from_coefficients_vec([r_coeff.evaluate(&zeta)].to_vec())
        .evaluate_over_domain(domain_3n);

    let fourth_output = [
        a_zeta.clone().evals[0],
        b_zeta.clone().evals[0],
        c_zeta.clone().evals[0],
        s_1_zeta.clone().evals[0],
        s_2_zeta.clone().evals[0],
        accumulator_shift_zeta.clone().evals[0],
        r_zeta.clone().evals[0],
    ];
    println!("Round 4 Finished with output: {:?}", fourth_output);

    println!("Starting Round 5...");
    //# Compute opening challenge

    let nu = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(
            (first_output, second_output, third_output),
            (&fourth_output),
        )))
        .next_u64(),
    );
    let nu_poly =
        DensePolynomial::from_coefficients_vec([nu].to_vec()).evaluate_over_domain(domain_3n);
    let nu_poly_sq = DensePolynomial::from_coefficients_vec([nu.pow([2])].to_vec())
        .evaluate_over_domain(domain_3n);
    let nu_poly_to3 = DensePolynomial::from_coefficients_vec([nu.pow([3])].to_vec())
        .evaluate_over_domain(domain_3n);
    let nu_poly_to4 = DensePolynomial::from_coefficients_vec([nu.pow([4])].to_vec())
        .evaluate_over_domain(domain_3n);
    let nu_poly_to5 = DensePolynomial::from_coefficients_vec([nu.pow([5])].to_vec())
        .evaluate_over_domain(domain_3n);
    let nu_poly_to6 = DensePolynomial::from_coefficients_vec([nu.pow([6])].to_vec())
        .evaluate_over_domain(domain_3n);

    //# Compute opening proof polynomial
    let zeta_to_n2_poly =
        DensePolynomial::from_coefficients_vec([zeta.pow([n as u64 + 2])].to_vec())
            .evaluate_over_domain(domain_3n);
    let zeta_to_2n2_poly =
        DensePolynomial::from_coefficients_vec([zeta.pow([2 * (n as u64 + 2)])].to_vec())
            .evaluate_over_domain(domain_3n);

    let w_zeta = t_lo.evaluate_over_domain(domain_3n);
    let w_zeta = &w_zeta + &(&t_mid.evaluate_over_domain(domain_3n) * &zeta_to_n2_poly);
    let w_zeta = &w_zeta + &(&t_hi.evaluate_over_domain(domain_3n) * &zeta_to_2n2_poly);
    let w_zeta = &w_zeta - &t_zeta;

    let w_zeta_add = &(&r - &r_zeta) * &nu_poly;
    let w_zeta_add = &w_zeta_add + &(&(&a_poly_ext3 - &a_zeta) * &nu_poly_sq);
    let w_zeta_add = &w_zeta_add + &(&(&b_poly_ext3 - &b_zeta) * &nu_poly_to3);
    let w_zeta_add = &w_zeta_add + &(&(&c_poly_ext3 - &c_zeta) * &nu_poly_to4);
    let w_zeta_add = &w_zeta_add + &(&(&s1_ext3 - &s_1_zeta) * &nu_poly_to5);
    let w_zeta_add = &w_zeta_add + &(&(&s2_ext3 - &s_2_zeta) * &nu_poly_to6);

    let w_zeta = &w_zeta + &w_zeta_add;

    let w_zeta = &w_zeta
        / &DensePolynomial::from_coefficients_vec([Fr::from(-1) * zeta, Fr::from(1)].to_vec())
            .evaluate_over_domain(domain_3n);

    // Compute the opening proof polynomial
    let w_zeta_omega = &accumulator_poly_ext3 - &accumulator_shift_zeta;
    let w_zeta_omega = &w_zeta_omega
        / &DensePolynomial::from_coefficients_vec(
            [
                Fr::from(-1) * zeta * domain_n.elements().nth(1).unwrap(),
                Fr::from(1),
            ]
            .to_vec(),
        )
        .evaluate_over_domain(domain_3n);

    let w_zeta_eval_exp = evaluate_in_exponent(&crs, &w_zeta.interpolate());
    let w_zeta_omega_eval_exp = evaluate_in_exponent(&crs, &w_zeta_omega.interpolate());

    let fifth_output = [w_zeta_eval_exp, w_zeta_omega_eval_exp];

    println!("Round 5 Finished with output: {:?}", fifth_output);

    let u = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(fifth_output))).next_u64());

    Proof {
        first_output,
        second_output,
        third_output,
        fourth_output,
        fifth_output,
        u,
    }
}

#[derive(Debug)]
pub struct Proof {
    pub first_output: [Projective<g1::Config>; 3],
    pub second_output: Projective<g1::Config>,
    pub third_output: [Projective<g1::Config>; 3],
    pub fourth_output:
        [ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>; 7],
    pub fifth_output: [Projective<g1::Config>; 2],
    pub u: Fr,
}

/// This is a helper function used in round 2
/// i am doing permutation[j-1] below because the list starts at 0 and the
/// paper at 1
fn accumulator_factor(
    n: &usize,
    i: &usize,
    witness: &Vec<Fr>,
    beta: &Fr,
    id_domain: &Vec<Fr>,
    perm_domain: &Vec<Fr>,
    gamma: &Fr,
) -> Fr {
    let mut res = Fr::from(1);
    for j in 0..(i + 1) {
        let nom_1 = witness[j] + beta * &id_domain[j] + gamma;
        let denom_1 = witness[j] + beta * &perm_domain[j] + gamma;

        let nom_2 = witness[n + j] + beta * &id_domain[n + j] + gamma;
        let denom_2 = witness[n + j] + beta * &perm_domain[n + j] + gamma;

        let nom_3 = witness[2 * n + j] + beta * &id_domain[2 * n + j] + gamma;
        let denom_3 = witness[2 * n + j] + beta * &perm_domain[2 * n + j] + gamma;
        res = res * (nom_1 / denom_1) * (nom_2 / denom_2) * (nom_3 / denom_3);
    }
    res
}

// doesnt seem like this is how it should be done but thats what I came up with
fn hash_tuple<T: Hash>(t: &T) -> [u8; 32] {
    let mut hasher = DefaultHasher::new();
    t.hash(&mut hasher);
    let result = hasher.finish();
    let bytes = result.to_le_bytes();
    let mut result_array = [0; 32];
    result_array[0..8].copy_from_slice(&bytes);
    result_array[8..16].copy_from_slice(&bytes);
    result_array[16..24].copy_from_slice(&bytes);
    result_array[24..32].copy_from_slice(&bytes);
    result_array
}

// Dont know how to do the shift using the standard functions to evaluate over domain
fn evaluate_poly_with_shift(
    poly: DensePolynomial<Fp<MontBackend<FrConfig, 4>, 4>>,
    domain: &Radix2EvaluationDomain<Fr>,
    shift: &Fr,
) -> Vec<Fr> {
    let poly_coeffs = poly.coeffs;
    let domain_elements: Vec<Fr> = domain.elements().collect();
    let mut eval: Vec<Fr> = Vec::new();
    for j in 0..domain_elements.len() {
        eval.push(
            (0..poly_coeffs.len())
                .map(|i| (domain_elements[j] * shift).pow([i as u64]) * poly_coeffs[i])
                .sum(),
        );
    }
    eval
}
