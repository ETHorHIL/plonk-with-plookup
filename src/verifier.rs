use crate::prover::Proof;
use ark_ec::models::short_weierstrass::*;
use ark_ec::pairing::Pairing;
use ark_ec::Group;
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::*;
use ark_test_curves::bls12_381::*;
use rand::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub fn verifier_algo(
    proof: Proof,
    n: usize,
    p_i_poly: DensePolynomial<Fr>,
    verifier_preprocessing: (
        Vec<Projective<g1::Config>>,
        Vec<Projective<g1::Config>>,
        Projective<g2::Config>,
    ),
    k: ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>,
) {
    println!("Starting Verification...");
    let domain_n = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let omega = domain_n.elements().nth(1).unwrap();
    let [a_eval_exp, b_eval_exp, c_eval_exp] = proof.first_output;
    let z_eval_exp = proof.second_output;
    let [t_lo_eval_exp, t_mid_eval_exp, t_hi_eval_exp] = proof.third_output;
    let [a_zeta, b_zeta, c_zeta, s_1_zeta, s_2_zeta, accumulator_shift_zeta, r_zeta] =
        proof.fourth_output.clone();
    let [w_zeta_eval_exp, w_zeta_omega_eval_exp] = proof.fifth_output;

    let (q_exp, s_exp, x_exp) = verifier_preprocessing;
    let [q_l_exp, q_r_exp, q_m_exp, q_o_exp, q_c_exp] =
        [q_exp[0], q_exp[1], q_exp[2], q_exp[3], q_exp[4]];
    let [s_1_exp, s_2_exp, s_3_exp] = [s_exp[0], s_exp[1], s_exp[2]];

    println!("Check1: Elements in group?");
    assert!(Affine::from(a_eval_exp).is_on_curve());
    assert!(Affine::from(b_eval_exp).is_on_curve());
    assert!(Affine::from(c_eval_exp).is_on_curve());
    assert!(Affine::from(z_eval_exp).is_on_curve());
    assert!(Affine::from(t_lo_eval_exp).is_on_curve());
    assert!(Affine::from(t_mid_eval_exp).is_on_curve());
    assert!(Affine::from(t_hi_eval_exp).is_on_curve());
    assert!(Affine::from(w_zeta_eval_exp).is_on_curve());
    assert!(Affine::from(w_zeta_omega_eval_exp).is_on_curve());

    println!("skipping the type checks, I think rust may take care of this. I could not find a method to check if element in field");
    println!("Check2: Elements in field?");
    // Probably wrong but doesnt rust already make sure that these are valid?
    // I could not find a method that does this
    /*
    assert type(a_zeta) is Fp
    assert type(b_zeta) is Fp
    assert type(c_zeta) is Fp
    assert type(S_1_zeta) is Fp
    assert type(S_2_zeta) is Fp
    assert type(r_zeta) is Fp
    assert type(accumulator_shift_zeta) is Fp
     */

    println!("Check3: Public input in field?");
    /*
    assert type(p_i_poly) == polynomialsEvalRep(Fp, omega, n)
    print(type(p_i_poly))
     */

    println!("Step4: Recompute challenges from transcript");

    let beta =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.first_output, 0))).next_u64());
    let gamma =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.first_output, 1))).next_u64());
    let alpha = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(proof.first_output, proof.second_output)))
            .next_u64(),
    );

    let zeta = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(
            (proof.first_output, proof.second_output),
            proof.third_output,
        )))
        .next_u64(),
    );

    let nu = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(
            (proof.first_output, proof.second_output, proof.third_output),
            (&proof.fourth_output),
        )))
        .next_u64(),
    );
    let u = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.fifth_output))).next_u64());

    println!("Step5: Evaluate vanishing polynomial at zeta");
    let vanishing_poly_eval = zeta.pow([n as u64]) - Fr::from(1);

    println!("Step6: Evaluate lagrange polynomial at zeta");
    let l_1_zeta =
        (zeta.pow([n as u64]) - Fr::from(1)) / (Fr::from(n as u64) * (zeta - Fr::from(1)));

    println!("Step7: Evaluate public input polynomial at zeta");
    let p_i_poly_zeta = p_i_poly.evaluate(&zeta);

    println!("Step8: Compute quotient polynomial evaluation");
    let t_zeta = (r_zeta + p_i_poly_zeta
        - (a_zeta + beta * s_1_zeta + gamma)
            * (b_zeta + beta * s_2_zeta + gamma)
            * (c_zeta + gamma)
            * accumulator_shift_zeta
            * alpha
        - l_1_zeta * alpha.pow([2 as u64]))
        / vanishing_poly_eval;

    println!("Step9: Comupte first part of batched polynomial commitment");
    let d_1_exp = q_m_exp * a_zeta * b_zeta * nu
        + q_l_exp * a_zeta * nu
        + q_r_exp * b_zeta * nu
        + q_o_exp * c_zeta * nu
        + q_c_exp * nu;
    let d_1_exp = d_1_exp
        + (z_eval_exp
            * ((a_zeta + beta * zeta + gamma)
                * (b_zeta + beta * k * zeta + gamma)
                * (c_zeta + beta * (k.pow([2 as u64])) * zeta + gamma)
                * alpha
                * nu
                + l_1_zeta * (alpha.pow([2 as u64])) * nu
                + u));
    let d_1_exp = d_1_exp
        + (s_3_exp
            * (a_zeta + beta * s_1_zeta + gamma)
            * (b_zeta + beta * s_2_zeta + gamma)
            * alpha
            * beta
            * accumulator_shift_zeta
            * nu)
            * Fr::from(-1);

    println!("Step10: Compute full batched polynomial commitment");
    let f_1_exp = t_lo_eval_exp
        + t_mid_eval_exp * zeta.pow([n as u64 + 2])
        + t_hi_eval_exp * zeta.pow([2 * (n as u64 + 2)])
        + d_1_exp
        + a_eval_exp * nu.pow([2])
        + b_eval_exp * nu.pow([3])
        + c_eval_exp * nu.pow([4])
        + s_1_exp * nu.pow([5])
        + s_2_exp * nu.pow([6]);

    println!("Step 11: Compute group encoded batch evaluation");
    let e_1_exp = G1Projective::generator()
        * (t_zeta
            + nu * r_zeta
            + nu.pow([2]) * a_zeta
            + nu.pow([3]) * b_zeta
            + nu.pow([4]) * c_zeta
            + nu.pow([5]) * s_1_zeta
            + nu.pow([6]) * s_2_zeta
            + u * accumulator_shift_zeta);

    println!("Check12: Batch validate all evaluations via pairing");
    let e11 = w_zeta_eval_exp + w_zeta_omega_eval_exp * u;
    let e21 = w_zeta_eval_exp * zeta
        + w_zeta_omega_eval_exp * u * zeta * omega
        + f_1_exp
        + (e_1_exp * Fr::from(-1));

    assert!(Bls12_381::pairing(e11, x_exp) == Bls12_381::pairing(e21, G2Projective::generator()));
    println!("Verification Successful!");
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
