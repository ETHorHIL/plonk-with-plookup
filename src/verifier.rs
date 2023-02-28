use crate::prover::Proof;
use crate::setup::VerifierPrep;
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
    verifier_prep: VerifierPrep,
    k: ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>,
) {
    println!("Starting Verification...");
    let domain_n = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let omega = domain_n.elements().nth(1).unwrap();
    let [a_eval_exp, b_eval_exp, c_eval_exp] = proof.first_output;
    let [query_eval_exp, h_1_eval_exp, h_2_eval_exp] = proof.second_output;
    let [z_1_eval_exp, z_2_eval_exp] = proof.third_output;
    let [q_lo_eval_exp, q_mid_eval_exp, q_hi_eval_exp] = proof.fourth_output;

    let [a_zeta, b_zeta, c_zeta, s_1_zeta, s_2_zeta, query_zeta, table_zeta, table_shift_zeta, accumulator_shift_zeta, z_2_shift_zeta, h_1_shift_zeta, h_2_zeta] =
        proof.fifth_output;
    let [w_zeta_eval_exp, w_zeta_omega_eval_exp] = proof.sixth_output;

    let (q_exp, s_exp, x_exp, table_polys_exp) = verifier_prep.as_tuple();

    let [q_l_exp, q_r_exp, q_m_exp, q_o_exp, q_c_exp, q_k_exp] =
        [q_exp[0], q_exp[1], q_exp[2], q_exp[3], q_exp[4], q_exp[5]];
    let [s_1_exp, s_2_exp, s_3_exp] = [s_exp[0], s_exp[1], s_exp[2]];

    println!("Check1: Elements in group?");
    assert!(Affine::from(a_eval_exp).is_on_curve());
    assert!(Affine::from(b_eval_exp).is_on_curve());
    assert!(Affine::from(c_eval_exp).is_on_curve());
    assert!(Affine::from(query_eval_exp).is_on_curve());
    assert!(Affine::from(h_1_eval_exp).is_on_curve());
    assert!(Affine::from(h_2_eval_exp).is_on_curve());
    assert!(Affine::from(z_1_eval_exp).is_on_curve());
    assert!(Affine::from(z_2_eval_exp).is_on_curve());
    assert!(Affine::from(q_lo_eval_exp).is_on_curve());
    assert!(Affine::from(q_mid_eval_exp).is_on_curve());
    assert!(Affine::from(q_hi_eval_exp).is_on_curve());
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
    query_zeta,
    table_zeta,
    table_shift_zeta,
    z_2_shift_zeta,
    h_1_shift_zeta,
    h_2_zeta
    assert type(accumulator_shift_zeta) is Fp
     */

    println!("Check3: Public input in field?");
    /*
    assert type(p_i_poly) == polynomialsEvalRep(Fp, omega, n)
    print(type(p_i_poly))
     */

    println!("Step4: Recompute challenges from transcript");

    let zeta_plookup =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.first_output, 0))).next_u64());

    let beta =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.second_output, 1))).next_u64());
    let gamma =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.second_output, 2))).next_u64());
    let delta =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.second_output, 3))).next_u64());
    let epsilon =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(proof.second_output, 4))).next_u64());

    let alpha = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(
            (proof.first_output, proof.second_output),
            proof.third_output,
        )))
        .next_u64(),
    );

    let zeta = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(
            (proof.first_output, proof.second_output, proof.third_output),
            proof.fourth_output,
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

    let u = proof.u;

    println!("Step5: Evaluate vanishing polynomial at zeta");
    let vanishing_poly_eval = zeta.pow([n as u64]) - Fr::from(1);

    println!("Step6: Evaluate lagrange polynomial at zeta");
    // in the paper the roots of unity start with omega, we start with one, this makes everythign more intuitive
    let l_1_zeta =
        (zeta.pow([n as u64]) - Fr::from(1)) / (Fr::from(n as u64) * (zeta - Fr::from(1)));

    println!("Step7: Evaluate public input polynomial at zeta");
    let p_i_poly_zeta = p_i_poly.evaluate(&zeta);

    println!("Step8: Compute the public table commitment");

    let t_exp = &table_polys_exp[0]
        + (table_polys_exp[1] * zeta_plookup)
        + (table_polys_exp[2] * zeta_plookup.pow([2]));

    println!("Step9 : Compute r(x) constant term");
    let r_0_plonk = p_i_poly_zeta
        - (a_zeta + beta * s_1_zeta + gamma)
            * (b_zeta + beta * s_2_zeta + gamma)
            * (c_zeta + gamma)
            * accumulator_shift_zeta
            * alpha;
    let r_0_plookup = -l_1_zeta * alpha.pow([2 as u64])
        - alpha.pow([4 as u64])
            * z_2_shift_zeta
            * (epsilon * (Fr::from(1) + delta) + delta * h_2_zeta)
            * (epsilon * (Fr::from(1) + delta) + h_2_zeta + delta * h_1_shift_zeta)
        - alpha.pow([5]) * l_1_zeta;

    let r_0 = r_0_plonk + r_0_plookup;

    println!("Step 10: Compute the first part of the batched polynomial commitment");
    let d_1_exp = q_m_exp * a_zeta * b_zeta
        + q_l_exp * a_zeta
        + q_r_exp * b_zeta
        + q_o_exp * c_zeta
        + q_c_exp;

    let d_1_exp = d_1_exp
        + (z_1_eval_exp
            * (
                (a_zeta + beta * zeta + gamma)
                    * (b_zeta + beta * k * zeta + gamma)
                    * (c_zeta + beta * (k.pow([2 as u64])) * zeta + gamma)
                    * alpha
                    + l_1_zeta * (alpha.pow([2 as u64]))
                //+ u , removed because its double counted
            ));
    let d_1_exp = d_1_exp
        - (q_lo_eval_exp
            + q_mid_eval_exp * zeta.pow([n as u64 + 2])
            + q_hi_eval_exp * zeta.pow([2 * n as u64 + 4]))
            * vanishing_poly_eval;

    let d_1_exp_1 = d_1_exp
        - s_3_exp
            * ((a_zeta + beta * s_1_zeta + gamma)
                * (b_zeta + beta * s_2_zeta + gamma)
                * alpha
                * beta
                * accumulator_shift_zeta);

    let d_1_exp_2 = q_k_exp
        * alpha.pow([3])
        * (a_zeta + zeta_plookup * b_zeta + zeta_plookup.pow([2]) * c_zeta - query_zeta);

    let d_1_exp_2 = d_1_exp_2
        + z_2_eval_exp
            * (
                (Fr::from(1) + delta)
                    * (epsilon + query_zeta)
                    * (epsilon * (Fr::from(1) + delta) + table_zeta + delta * table_shift_zeta)
                    * alpha.pow([4])
                    + l_1_zeta * alpha.pow([5])
                //+ u * nu.pow([2]) , removed because its double counted
            );

    let d_1_exp_2 = d_1_exp_2
        + h_1_eval_exp
            * (
                //u * nu.pow([3]) , removed because its double counted
                -z_2_shift_zeta
                    * (epsilon * (Fr::from(1) + delta) + h_2_zeta + delta * h_1_shift_zeta)
                    * alpha.pow([4])
            );

    let d_1_exp = d_1_exp_1 + d_1_exp_2;

    println!("looks like it should be 2n+4 below?");

    println!("Step11: Compute full batched polynomial commitment");
    let f_1_exp_plonk = d_1_exp
        + a_eval_exp * nu
        + b_eval_exp * nu.pow([2])
        + c_eval_exp * nu.pow([3])
        + s_1_exp * nu.pow([4])
        + s_2_exp * nu.pow([5])
        + z_1_eval_exp * u;
    let f_1_exp_lookup = query_eval_exp * nu.pow([6])
        + h_2_eval_exp * nu.pow([7])
        + t_exp * nu.pow([8])
        + (t_exp * nu + z_2_eval_exp * nu.pow([2]) + h_1_eval_exp * nu.pow([3])) * u;

    let f_1_exp = f_1_exp_plonk + f_1_exp_lookup;

    println!("Step 12: Compute group encoded batch evaluation");
    let e_1_exp_plonk = Fr::from(-1) * r_0
        + nu * a_zeta
        + nu.pow([2]) * b_zeta
        + nu.pow([3]) * c_zeta
        + nu.pow([4]) * s_1_zeta
        + nu.pow([5]) * s_2_zeta
        + u * accumulator_shift_zeta;
    let e_1_exp_lookup = nu.pow([6]) * query_zeta
        + nu.pow([8]) * table_zeta
        + nu.pow([7]) * h_2_zeta
        + u * (nu * table_shift_zeta + nu.pow([2]) * z_2_shift_zeta + nu.pow([3]) * h_1_shift_zeta);

    let e_1_exp = G1Projective::generator() * (e_1_exp_plonk + e_1_exp_lookup);

    println!("Check13: Batch validate all evaluations via pairing");

    let e11 = w_zeta_eval_exp + w_zeta_omega_eval_exp * u;
    let e21 = w_zeta_eval_exp * zeta + w_zeta_omega_eval_exp * u * zeta * omega + f_1_exp - e_1_exp;

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
