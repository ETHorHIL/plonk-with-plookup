use crate::circuit::Circuit;
use crate::setup::{evaluate_in_exponent, SetupOutput};
use ark_ec::models::short_weierstrass::*;
use ark_ff::Field;
use ark_ff::*;
use ark_poly::univariate::DensePolynomial;
use ark_poly::*;
use ark_test_curves::bls12_381::Fr;
use ark_test_curves::bls12_381::*;
use rand::prelude::*;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

// https://github.com/ETHorHIL/Plonk_Py/blob/master/prover.py
pub fn prover_algo(witness: Vec<Fr>, setup_output: &SetupOutput, circuit: Circuit) -> Proof {
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
    // in the paper the roots of unity start with omega, we start withone
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
    let q_k_ext3 = qs[5].clone().evaluate_over_domain(domain_3n);

    /*
    # Following the paper, we are using the Fiat Shamir Heuristic. We are
    # Simulating 5 rounds of communication with the verifier using a
    # random oracle for verifier answers */
    println!("Starting Round 1...");

    // Generate "random" blinding scalars, seeding to make things reproducible for me
    let mut rng = rand::rngs::StdRng::from_seed([0; 32]);
    let rand_scalars: Vec<Fr> = (0..19).map(|_x| Fr::from(rng.next_u64())).collect();

    /*
    # Generate polys with the random scalars as coefficients and convert to
    # evaluation representation. These are needed for zero knowledge to
    # obfuscate the witness.
    */
    let a_blind_poly_ext =
        DensePolynomial::from_coefficients_vec(vec![rand_scalars[2 - 1], rand_scalars[1 - 1]])
            .mul_by_vanishing_poly(domain_n);
    let b_blind_poly_ext =
        DensePolynomial::from_coefficients_vec(vec![rand_scalars[4 - 1], rand_scalars[3 - 1]])
            .mul_by_vanishing_poly(domain_n);
    let c_blind_poly_ext =
        DensePolynomial::from_coefficients_vec(vec![rand_scalars[6 - 1], rand_scalars[5 - 1]])
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

    //1. Compute the compression factor
    let zeta_plookup =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(first_output, 0))).next_u64());
    let zeta_plookup_poly = DensePolynomial::from_coefficients_vec(vec![zeta_plookup]);
    let zeta_sq_plookup_poly = DensePolynomial::from_coefficients_vec(vec![zeta_plookup.pow([2])]);
    let zeta_plookup_poly_ext3 = DensePolynomial::from_coefficients_vec(vec![zeta_plookup])
        .clone()
        .evaluate_over_domain(domain_3n);
    let zeta_sq_plookup_poly_ext3 =
        DensePolynomial::from_coefficients_vec(vec![zeta_plookup.pow([2])])
            .clone()
            .evaluate_over_domain(domain_3n);

    let table = circuit.table;
    let table_polys = table.get_table_polys();

    let table_poly = &table_polys[0]
        + &(&zeta_plookup_poly * &table_polys[1])
        + (&zeta_sq_plookup_poly * &table_polys[2]);

    let table_vector = table.compress_table_vector(zeta_plookup);

    let query_vector: Vec<Fr> = (0..table_vector.len())
        .map(|x| {
            if qs[5].clone().evaluate(&domain_n.elements().nth(x).unwrap()) == Fr::one() {
                witness[x]
                    + zeta_plookup * witness[x + n]
                    + zeta_plookup.pow([2]) * witness[x + 2 * n]
            } else {
                *table_vector.last().unwrap()
            }
        })
        .collect();

    //3. Generate random blinding scalars b7, . . . , b13 ∈ F. -- I have done that all in one swoop above
    // 4. Compute the query polynomial f(X) ∈ F<n+2[x] and the table polynomial t(X) ∈ F<n[X]:
    let query_poly = Evaluations::from_vec_and_domain(query_vector.clone(), domain_n).interpolate()
        + DensePolynomial::from_coefficients_vec(vec![rand_scalars[8], rand_scalars[7]])
            .mul_by_vanishing_poly(domain_n);

    let query_poly_ext3 = query_poly.clone().evaluate_over_domain(domain_3n);

    // 5. Let s ∈ F 2n be the vector that is (f, t) sorted by t. We represent s by the vectors h1, h2 ∈ F n as follows:

    let (h_2, h_1) = table.compute_h1_h2(&query_vector, &table_vector);

    // 6. Compute the polynomials h1(X) ∈ F<n+3[X], and h2(X) ∈ F<n+2[X].
    let h_1_poly = Evaluations::from_vec_and_domain(h_1.clone(), domain_n).interpolate();
    let h_1_poly = h_1_poly
        + DensePolynomial::from_coefficients_vec(vec![
            rand_scalars[11 - 1],
            rand_scalars[10 - 1],
            rand_scalars[9 - 1],
        ])
        .mul_by_vanishing_poly(domain_n);

    let h_1_poly_ext3 = h_1_poly.clone().evaluate_over_domain(domain_3n);

    let h_2_poly = Evaluations::from_vec_and_domain(h_2.clone(), domain_n).interpolate();
    let h_2_poly = &h_2_poly
        + &DensePolynomial::from_coefficients_vec(vec![rand_scalars[13 - 1], rand_scalars[12 - 1]])
            .mul_by_vanishing_poly(domain_n);

    let h_2_poly_ext3 = h_2_poly.clone().evaluate_over_domain(domain_3n);

    let query_eval_exp = evaluate_in_exponent(&crs, &query_poly);
    let h_1_eval_exp = evaluate_in_exponent(&crs, &h_1_poly);
    let h_2_eval_exp = evaluate_in_exponent(&crs, &h_2_poly);

    let second_output = [query_eval_exp, h_1_eval_exp, h_2_eval_exp];

    println!("Round 2 Finished with output: {:?}", second_output);

    println!("Starting Round 3...");

    // 1. Compute the permutation challenges β, γ, δ, ε

    let beta = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(second_output, 1))).next_u64());
    let gamma = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(second_output, 2))).next_u64());
    let delta = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(second_output, 3))).next_u64());
    let epsilon =
        Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(second_output, 4))).next_u64());

    //2. Generate random blinding scalars b14, . . . , b19 -- I have done that above in one swoop

    // 3. Compute the PlonK permutation polynomial z
    let z_1 = DensePolynomial::from_coefficients_vec(vec![
        rand_scalars[16 - 1],
        rand_scalars[15 - 1],
        rand_scalars[14 - 1],
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

    // 4. Compute the plookup permutation polynomial z2(X) ∈ F<n+3[x], which results from the product of the Plookup and the sorted table permutation polynomials
    let z_2 = DensePolynomial::from_coefficients_vec(vec![
        rand_scalars[19 - 1],
        rand_scalars[18 - 1],
        rand_scalars[17 - 1],
    ]);
    let z_2 = z_2.evaluate_over_domain(domain_2n).interpolate();
    let z_2 = z_2.mul_by_vanishing_poly(domain_n);

    let mut accumulator_poly_eval_z2: Vec<Fr> = vec![];
    if table_vector.len() > 0 {
        accumulator_poly_eval_z2.push(Fr::from(1));
        let evaluations_temp_z2: Vec<Fr> = (0..table_vector.len() - 1)
            .map(|i| {
                plookup_accumulator_factor(
                    &i,
                    &delta,
                    &epsilon,
                    &query_vector,
                    &table_vector,
                    &h_1,
                    &h_2,
                )
            })
            .collect();

        accumulator_poly_eval_z2.extend(evaluations_temp_z2);
    }

    let accumulator_poly_z2 =
        Evaluations::from_vec_and_domain(accumulator_poly_eval_z2, domain_n).interpolate();
    let accumulator_poly_z2 = z_2
        + accumulator_poly_z2
            .evaluate_over_domain(domain_2n)
            .interpolate();

    let third_output = [
        evaluate_in_exponent(&crs, &accumulator_poly),
        evaluate_in_exponent(&crs, &accumulator_poly_z2),
    ];
    println!("Round 3 Finished with output: {:?}", third_output);

    //# Compute permutation challenges from imaginary verifier

    println!("Starting Round 4...");
    //1. Compute the quotient challenges α ∈ F:
    let alpha = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&((first_output, second_output), third_output)))
            .next_u64(),
    );

    let alpha_poly =
        DensePolynomial::from_coefficients_vec(vec![alpha]).evaluate_over_domain(domain_3n);
    let alpha_squared_poly = DensePolynomial::from_coefficients_vec(vec![alpha.pow([2])])
        .evaluate_over_domain(domain_3n);
    let alpha_cubed_poly = DensePolynomial::from_coefficients_vec(vec![alpha.pow([3])])
        .evaluate_over_domain(domain_3n);
    let alpha_quad_poly = DensePolynomial::from_coefficients_vec(vec![alpha.pow([4])])
        .evaluate_over_domain(domain_3n);
    let alpha_quint_poly = DensePolynomial::from_coefficients_vec(vec![alpha.pow([5])])
        .evaluate_over_domain(domain_3n);
    let beta_poly =
        DensePolynomial::from_coefficients_vec(vec![beta]).evaluate_over_domain(domain_3n);

    let delta_poly =
        DensePolynomial::from_coefficients_vec(vec![delta]).evaluate_over_domain(domain_3n);
    let epsilon_poly =
        DensePolynomial::from_coefficients_vec(vec![epsilon]).evaluate_over_domain(domain_3n);

    let accumulator_poly_ext3 = accumulator_poly.clone().evaluate_over_domain(domain_3n);
    let accumulator_poly_z_2_ext3 = accumulator_poly_z2.clone().evaluate_over_domain(domain_3n);

    //# The third summand of t has the accumulator poly evaluated at a shift
    let accumulator_poly_shift_evaluations = evaluate_poly_with_shift(
        &accumulator_poly,
        &domain_3n,
        &domain_n.elements().nth(1).unwrap(),
    );
    let accumulator_poly_ext3_shift =
        Evaluations::from_vec_and_domain(accumulator_poly_shift_evaluations, domain_3n);

    let accumulator_poly_z2_shift_evaluations = evaluate_poly_with_shift(
        &accumulator_poly_z2,
        &domain_3n,
        &domain_n.elements().nth(1).unwrap(),
    );
    let accumulator_poly_z2_ext3_shift =
        Evaluations::from_vec_and_domain(accumulator_poly_z2_shift_evaluations, domain_3n);

    let table_poly_ext3 = table_poly.clone().evaluate_over_domain(domain_3n);

    let table_poly_shift_evaluations = evaluate_poly_with_shift(
        &table_poly,
        &domain_3n,
        &domain_n.elements().nth(1).unwrap(),
    );

    let table_poly_ext3_shift =
        Evaluations::from_vec_and_domain(table_poly_shift_evaluations, domain_3n);

    let h_1_shift_evaluations =
        evaluate_poly_with_shift(&h_1_poly, &domain_3n, &domain_n.elements().nth(1).unwrap());

    let h1_poly_ext3_shift = Evaluations::from_vec_and_domain(h_1_shift_evaluations, domain_3n);

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

    // In the paper the roots of unity start with omega, here we start with one, this makes this polynomial more easy
    let mut l_1 = vec![Fr::from(1)];
    l_1.extend((0..n - 1).map(|_x| Fr::from(0)).collect::<Vec<Fr>>());
    let l_1 = Evaluations::from_vec_and_domain(l_1, domain_n).interpolate();

    /*
    # Compute quotient polynomial: we are dividing by the vanishing poly which
    # has zeros at n roots so we need to do division by swapping to a coset
    # first summand should have degree 3n+1, second and third should have
    # degree 4n + 5
    */
    let q_plonk = &(&a_poly_ext3 * &b_poly_ext3) * &q_m_ext3;
    let q_plonk = &q_plonk + &(&a_poly_ext3 * &q_l_ext3);
    let q_plonk = &q_plonk + &(&b_poly_ext3 * &q_r_ext3);
    let q_plonk = &q_plonk + &(&c_poly_ext3 * &q_o_ext3);
    let q_plonk = &q_plonk + &q_c_ext3.clone();
    let q_plonk = &q_plonk + &p_i_poly_ext3;

    let q_second_sumand = &(&(&(&(&a_poly_ext3.clone() + &id_poly_1_ext3)
        * &(&b_poly_ext3 + &id_poly_2_ext3))
        * &(&c_poly_ext3 + &id_poly_3_ext3))
        * &accumulator_poly_ext3)
        * &alpha_poly;

    let q_plonk = &q_plonk + &q_second_sumand;

    let q_plonk_third_summand =
        &(&a_poly_ext3.clone() + &(&s1_ext3 * &beta_poly)) + &gamma_poly.clone();
    let q_plonk_third_summand = &q_plonk_third_summand
        * &(&(&b_poly_ext3 + &(&s2_ext3 * &beta_poly)) + &gamma_poly.clone());
    let q_plonk_third_summand = &q_plonk_third_summand
        * &(&(&c_poly_ext3 + &(&s3_ext3 * &beta_poly)) + &gamma_poly.clone());
    let q_plonk_third_summand = &q_plonk_third_summand * &accumulator_poly_ext3_shift;
    let q_plonk_third_summand = &q_plonk_third_summand * &alpha_poly;

    let q_plonk = &q_plonk - &q_plonk_third_summand;

    let one_poly =
        DensePolynomial::from_coefficients_vec(vec![Fr::from(1)]).evaluate_over_domain(domain_3n);

    let q_plonk_fourth_summand = &q_plonk
        + &(&(&(&accumulator_poly_ext3 - &one_poly)
            * &l_1.clone().evaluate_over_domain(domain_3n))
            * &alpha_squared_poly);

    // Compute the plookup additions to the quotient polynomials
    // first term of plookup quotient poly
    let q_lookup_1 = &q_k_ext3
        * &(&(&(&a_poly_ext3 + &(&zeta_plookup_poly_ext3 * &b_poly_ext3))
            + &(&zeta_sq_plookup_poly_ext3 * &c_poly_ext3))
            - &query_poly_ext3);
    let q_lookup_1 = &q_lookup_1 * &alpha_cubed_poly;

    // second term of plookup quotient poly
    let q_lookup_2 = &epsilon_poly * &(&one_poly + &delta_poly);
    let q_lookup_2 = &q_lookup_2 + &(&table_poly_ext3 + &(&delta_poly * &table_poly_ext3_shift));
    let q_lookup_2 = &(&q_lookup_2 * &(&accumulator_poly_z_2_ext3 * &(&one_poly + &delta_poly)))
        * &(&epsilon_poly + &query_poly_ext3);
    let q_lookup_2 = &q_lookup_2 * &alpha_quad_poly;
    // corret till here (multiplying &r_lookup_2 * &alpha_quad_poly)

    let q_lookup_3_1 = &epsilon_poly * &(&one_poly + &delta_poly);
    let q_lookup_3_1 = &q_lookup_3_1 + &(&h_1_poly_ext3 + &(&delta_poly * &h_2_poly_ext3));
    let q_lookup_3_2 = &epsilon_poly * &(&one_poly + &delta_poly);
    let q_lookup_3_2 = &q_lookup_3_2 + &(&h_2_poly_ext3 + &(&delta_poly * &h1_poly_ext3_shift));
    let q_lookup_3 =
        &q_lookup_3_1 * &(&q_lookup_3_2 * &(&accumulator_poly_z2_ext3_shift * &alpha_quad_poly));

    // corret till here (multiplying &r_lookup_2 * &alpha_quad_poly)

    let q_lookup_4 = &(&(&(&accumulator_poly_z_2_ext3 - &one_poly)
        * &l_1.clone().evaluate_over_domain(domain_3n))
        * &alpha_quint_poly);

    let q_lookup = &(&q_lookup_1 + &(&q_lookup_2 - &q_lookup_3)) + &q_lookup_4;

    let q = &q_plonk_fourth_summand + &q_lookup;

    let q = q.interpolate().divide_by_vanishing_poly(domain_n).unwrap();
    let q = q.0;
    let q_coeff = q.coeffs();

    /*
    # We split up the polynomial t in three polynomials so that:
    # t= t_lo + x^n*t_mid + t^2n*t_hi
    # I found that n has actually to be (n+2) to accomodate the CRS because
    # t can be of degree 4n+5
    */
    let q_lo = DensePolynomial::from_coefficients_vec(q_coeff[..n + 2].to_vec());
    let q_mid = DensePolynomial::from_coefficients_vec(q_coeff[n + 2..2 * (n + 2)].to_vec());
    let q_hi = DensePolynomial::from_coefficients_vec(q_coeff[2 * (n + 2)..].to_vec());
    println!(" q_lo degree: {:?}", q_lo.degree());
    println!(" q_mid degree: {:?}", q_mid.degree());
    println!(" q_hi degree: {:?}", q_hi.degree());

    let q_lo_eval_exp = evaluate_in_exponent(&crs, &q_lo);
    let q_mid_eval_exp = evaluate_in_exponent(&crs, &q_mid);
    let q_hi_eval_exp = evaluate_in_exponent(&crs, &q_hi);

    let fourth_output = [q_lo_eval_exp, q_mid_eval_exp, q_hi_eval_exp];
    println!("Round 4 Finished with output: {:?}", fourth_output);

    println!("Starting Round 5...");

    //# Compute the evaluation challenge
    let zeta = Fr::from(
        rand::rngs::StdRng::from_seed(hash_tuple(&(
            (first_output, second_output, third_output),
            fourth_output,
        )))
        .next_u64(),
    );

    let zeta_shift = &zeta * &domain_n.elements().nth(1).unwrap();
    let zeta_poly =
        DensePolynomial::from_coefficients_vec([zeta].to_vec()).evaluate_over_domain(domain_3n);
    let vanishing_poly_at_zeta = domain_n.evaluate_vanishing_polynomial(zeta);
    let vanishing_poly_at_zeta =
        DensePolynomial::from_coefficients_vec([vanishing_poly_at_zeta].to_vec())
            .evaluate_over_domain(domain_3n);

    // Compute the opening evaluations
    let a_zeta = a_poly_ext.interpolate().evaluate(&zeta);
    let b_zeta = b_poly_ext.interpolate().evaluate(&zeta);
    let c_zeta = c_poly_ext.interpolate().evaluate(&zeta);
    let s_1_zeta = s1.evaluate(&zeta);
    let s_2_zeta = s2.evaluate(&zeta);
    let query_zeta = query_poly.evaluate(&zeta);
    let table_zeta = table_poly.evaluate(&zeta);
    let table_shift_zeta = table_poly.evaluate(&zeta_shift);
    let accumulator_shift_zeta = accumulator_poly_ext3
        .clone()
        .interpolate()
        .evaluate(&(zeta_shift));
    let z_2_shift_zeta = accumulator_poly_z2.evaluate(&zeta_shift);
    let h_1_shift_zeta = h_1_poly.evaluate(&zeta_shift);
    let h_2_zeta = h_2_poly.evaluate(&zeta);
    let p_i_zeta = setup_output.p_i_poly.evaluate(&zeta);

    let fifth_output = [
        a_zeta,
        b_zeta,
        c_zeta,
        s_1_zeta,
        s_2_zeta,
        query_zeta,
        table_zeta,
        table_shift_zeta,
        accumulator_shift_zeta,
        z_2_shift_zeta,
        h_1_shift_zeta,
        h_2_zeta,
    ];
    println!("Round 5 Finished with output: {:?}", fifth_output);

    println!("Starting Round 6...");

    //# Compute the evaluation challenge

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
    let nu_poly_to7 = DensePolynomial::from_coefficients_vec([nu.pow([7])].to_vec())
        .evaluate_over_domain(domain_3n);
    let nu_poly_to8 = DensePolynomial::from_coefficients_vec([nu.pow([8])].to_vec())
        .evaluate_over_domain(domain_3n);

    let p_i_poly_zeta =
        DensePolynomial::from_coefficients_vec([p_i_zeta].to_vec()).evaluate_over_domain(domain_3n);
    //# Compute opening proof polynomial
    let zeta_to_n2_poly =
        DensePolynomial::from_coefficients_vec([zeta.pow([n as u64 + 2])].to_vec())
            .evaluate_over_domain(domain_3n);
    let zeta_to_2n2_poly =
        DensePolynomial::from_coefficients_vec([zeta.pow([2 * (n as u64 + 2)])].to_vec())
            .evaluate_over_domain(domain_3n);

    let k_poly =
        DensePolynomial::from_coefficients_vec([*k].to_vec()).evaluate_over_domain(domain_3n);
    let k_sq_poly = DensePolynomial::from_coefficients_vec([k.pow([2])].to_vec())
        .evaluate_over_domain(domain_3n);

    // need to turn the output of round 5 back into polynomials
    let a_zeta =
        DensePolynomial::from_coefficients_vec(vec![a_zeta]).evaluate_over_domain(domain_3n);
    let b_zeta =
        DensePolynomial::from_coefficients_vec(vec![b_zeta]).evaluate_over_domain(domain_3n);
    let c_zeta =
        DensePolynomial::from_coefficients_vec(vec![c_zeta]).evaluate_over_domain(domain_3n);
    let s_1_zeta =
        DensePolynomial::from_coefficients_vec(vec![s_1_zeta]).evaluate_over_domain(domain_3n);
    let s_2_zeta =
        DensePolynomial::from_coefficients_vec(vec![s_2_zeta]).evaluate_over_domain(domain_3n);
    let query_zeta =
        DensePolynomial::from_coefficients_vec(vec![query_zeta]).evaluate_over_domain(domain_3n);
    let table_zeta =
        DensePolynomial::from_coefficients_vec(vec![table_zeta]).evaluate_over_domain(domain_3n);
    let table_shift_zeta = DensePolynomial::from_coefficients_vec(vec![table_shift_zeta])
        .evaluate_over_domain(domain_3n);
    let accumulator_shift_zeta =
        DensePolynomial::from_coefficients_vec(vec![accumulator_shift_zeta])
            .evaluate_over_domain(domain_3n);
    let z_2_shift_zeta = DensePolynomial::from_coefficients_vec(vec![z_2_shift_zeta])
        .evaluate_over_domain(domain_3n);
    let h_1_shift_zeta = DensePolynomial::from_coefficients_vec(vec![h_1_shift_zeta])
        .evaluate_over_domain(domain_3n);
    let h_2_zeta =
        DensePolynomial::from_coefficients_vec(vec![h_2_zeta]).evaluate_over_domain(domain_3n);

    let l_1_zeta = DensePolynomial::from_coefficients_vec(vec![l_1.clone().evaluate(&zeta)])
        .evaluate_over_domain(domain_3n);

    //# Compute linerisation polynomial
    let r_plonk = &(&q_m_ext3 * &a_zeta) * &b_zeta;
    let r_plonk = &r_plonk + &(&q_l_ext3 * &a_zeta);
    let r_plonk = &r_plonk + &(&q_r_ext3 * &b_zeta);
    let r_plonk = &r_plonk + &(&q_o_ext3 * &c_zeta);
    let r_plonk = &r_plonk + &q_c_ext3;
    let r_plonk = &r_plonk + &p_i_poly_zeta;

    let r_second_summand = &accumulator_poly_ext3;
    let r_second_summand =
        r_second_summand * &(&(&a_zeta + &(&beta_poly * &zeta_poly)) + &gamma_poly.clone());
    let r_second_summand = &r_second_summand
        * &(&(&b_zeta + &(&beta_poly * &(&k_poly * &zeta_poly))) + &gamma_poly.clone());
    let r_second_summand = &r_second_summand
        * &(&(&c_zeta + &(&beta_poly * &(&k_sq_poly * &zeta_poly))) + &gamma_poly.clone());
    let r_second_summand = &r_second_summand * &alpha_poly;

    let r_plonk = &r_plonk + &r_second_summand;

    let r_third_summand = &(&a_zeta + &(&beta_poly * &s_1_zeta)) + &gamma_poly.clone();
    let r_third_summand =
        &r_third_summand * &(&(&b_zeta + &(&beta_poly * &s_2_zeta)) + &gamma_poly);
    let r_third_summand = &r_third_summand * &(&(&c_zeta + &(&beta_poly * &s3_ext3)) + &gamma_poly);
    let r_third_summand = &r_third_summand * &alpha_poly;
    let r_third_summand = &r_third_summand * &accumulator_shift_zeta;

    let r_plonk = &r_plonk - &r_third_summand;

    let r_fourth_summand = &(&accumulator_poly_ext3 - &one_poly)
        * &(&DensePolynomial::from_coefficients_vec([l_1.evaluate(&zeta)].to_vec())
            .evaluate_over_domain(domain_3n)
            * &alpha_squared_poly);
    let r_plonk = &r_plonk + &r_fourth_summand;

    let r_plonk_5 = q_lo.evaluate_over_domain(domain_3n);
    let r_plonk_5 = &r_plonk_5 + &(&q_mid.evaluate_over_domain(domain_3n) * &zeta_to_n2_poly);
    let r_plonk_5 = &r_plonk_5 + &(&q_hi.evaluate_over_domain(domain_3n) * &zeta_to_2n2_poly);
    let r_plonk_5 = &vanishing_poly_at_zeta * &r_plonk_5;

    let r_plonk = &r_plonk - &r_plonk_5;

    // plookup related components of r
    let r_lookup_1 = &a_zeta
        + &(&(&zeta_plookup_poly_ext3 * &b_zeta)
            + &(&(&zeta_sq_plookup_poly_ext3 * &c_zeta) - &query_zeta));
    let r_lookup_1 = &r_lookup_1 * &(&alpha_cubed_poly * &q_k_ext3);

    let r_lookup_2 = &(&(&epsilon_poly * &(&one_poly + &delta_poly)) + &table_zeta)
        + &(&table_shift_zeta * &delta_poly);
    let r_lookup_2 = &(&(&r_lookup_2 * &(&epsilon_poly + &query_zeta))
        * &(&one_poly + &delta_poly))
        * &accumulator_poly_z_2_ext3;

    let r_lookup_3 = &(&(&epsilon_poly * &(&one_poly + &delta_poly)) + &h_1_poly_ext3)
        + &(&delta_poly * &h_2_zeta);
    let r_lookup_3 = &r_lookup_3
        * &(&(&(&epsilon_poly * &(&one_poly + &delta_poly)) + &h_2_zeta)
            + &(&delta_poly * &h_1_shift_zeta));
    let r_lookup_3 = &r_lookup_3 * &z_2_shift_zeta;

    let r_lookup_4 = &(&(&accumulator_poly_z_2_ext3 - &one_poly) * &l_1_zeta) * &alpha_quint_poly;
    // corret till here

    let r_lookup =
        &(&r_lookup_1 + &(&alpha_quad_poly * &(&r_lookup_2 - &r_lookup_3))) + &r_lookup_4;

    let r = &r_plonk + &r_lookup;

    //# Compute opening challenge
    let w_zeta = r.clone();
    let w_zeta = &w_zeta + &(&(&a_poly_ext3 - &a_zeta) * &nu_poly);
    let w_zeta = &w_zeta + &(&(&b_poly_ext3 - &b_zeta) * &nu_poly_sq);
    let w_zeta = &w_zeta + &(&(&c_poly_ext3 - &c_zeta) * &nu_poly_to3);
    let w_zeta = &w_zeta + &(&(&s1_ext3 - &s_1_zeta) * &nu_poly_to4);
    let w_zeta = &w_zeta + &(&(&s2_ext3 - &s_2_zeta) * &nu_poly_to5);
    // plookup additions to w_zeta
    let w_zeta_plookup = &(&query_poly_ext3 - &query_zeta) * &nu_poly_to6;
    let w_zeta_plookup = &w_zeta_plookup + &(&(&h_2_poly_ext3 - &h_2_zeta) * &nu_poly_to7);
    let w_zeta_plookup = &w_zeta_plookup + &(&(&table_poly_ext3 - &table_zeta) * &nu_poly_to8);

    let w_zeta = &w_zeta + &w_zeta_plookup;

    let w_zeta = &w_zeta
        / &DensePolynomial::from_coefficients_vec([Fr::from(-1) * zeta, Fr::from(1)].to_vec())
            .evaluate_over_domain(domain_3n);

    // Compute the opening proof polynomial
    let w_zeta_omega = &accumulator_poly_ext3 - &accumulator_shift_zeta;
    // plookup additions to opening proof poly

    let w_zeta_omega_plookup = &(&table_poly_ext3 - &table_shift_zeta) * &nu_poly;
    let w_zeta_omega_plookup =
        &w_zeta_omega_plookup + &(&(&accumulator_poly_z_2_ext3 - &z_2_shift_zeta) * &nu_poly_sq);
    let w_zeta_omega_plookup =
        &w_zeta_omega_plookup + &(&(&h_1_poly_ext3 - &h_1_shift_zeta) * &nu_poly_to3);

    let w_zeta_omega = &w_zeta_omega + &w_zeta_omega_plookup;

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

    let sixth_output = [w_zeta_eval_exp, w_zeta_omega_eval_exp];

    println!("Round 6 Finished with output: {:?}", sixth_output);

    let u = Fr::from(rand::rngs::StdRng::from_seed(hash_tuple(&(fifth_output))).next_u64());

    Proof {
        first_output,
        second_output,
        third_output,
        fourth_output,
        fifth_output,
        sixth_output,
        u,
    }
}

#[derive(Debug)]
pub struct Proof {
    pub first_output: [Projective<g1::Config>; 3],
    pub second_output: [Projective<g1::Config>; 3],
    pub third_output: [Projective<g1::Config>; 2],
    pub fourth_output: [Projective<g1::Config>; 3],
    pub fifth_output:
        [ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>; 12],
    pub sixth_output: [Projective<g1::Config>; 2],
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

fn plookup_accumulator_factor(
    i: &usize,
    delta: &Fr,
    epsilon: &Fr,
    query_vector: &Vec<Fr>,
    table_vector: &Vec<Fr>,
    h_1: &Vec<Fr>,
    h_2: &Vec<Fr>,
) -> Fr {
    let mut res = Fr::from(1);
    for j in 0..(i + 1) {
        let nom = (Fr::one() + delta)
            * (epsilon + &query_vector[j])
            * (epsilon * &(Fr::one() + delta) + table_vector[j] + delta * &table_vector[j + 1]);

        // the paper and this disagree on using h1 vs h2 below
        // https://hackmd.io/gMXxXhCXQ8GFb1bvnFgOIA?view
        // https://eprint.iacr.org/2022/086.pdf
        println!("here a bug needs to be fixed");
        let denom = (epsilon * &(Fr::one() + delta) + h_1[j] + delta * &h_2[j])
            * (epsilon * &(Fr::one() + delta) + h_2[j] + delta * &h_1[j + 1]);
        res = res * (nom / denom)
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
    poly: &DensePolynomial<Fp<MontBackend<FrConfig, 4>, 4>>,
    domain: &Radix2EvaluationDomain<Fr>,
    shift: &Fr,
) -> Vec<Fr> {
    let poly_coeffs = poly.coeffs.clone();
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
