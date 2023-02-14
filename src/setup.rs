use ark_ec::models::short_weierstrass::*;
use ark_ff::*;
use ark_poly::univariate::DensePolynomial;
use ark_poly::*;
use ark_test_curves::bls12_381::*;
use ark_test_curves::*;

// https://github.com/ETHorHIL/Plonk_Py/blob/master/setup.py
pub fn setup_algo(
    gates_matrix: Vec<Vec<i32>>,
    permutation: Vec<usize>,
    pub_input_position: Vec<usize>,
    pub_input_value: Vec<i32>,
) -> SetupOutput {
    let g1 = G1Projective::generator();

    print!("Starting Setup Phase");
    let (m, n) = (gates_matrix.len() - 1, gates_matrix[0].len());
    assert!(m == 5, "m isnt 5");
    assert!(n == 8);

    let gates_matrix: Vec<Vec<Fr>> = (0..m)
        .map(|i| (0..n).map(|j| (Fr::from(gates_matrix[i][j]))).collect())
        .collect();

    let q_l: Vec<Fr> = gates_matrix[0].iter().map(|x| Fr::from(*x)).collect();
    let q_r: Vec<Fr> = gates_matrix[1].iter().map(|x| Fr::from(*x)).collect();
    let q_m: Vec<Fr> = gates_matrix[2].iter().map(|x| Fr::from(*x)).collect();
    let q_o: Vec<Fr> = gates_matrix[3].iter().map(|x| Fr::from(*x)).collect();
    let q_c: Vec<Fr> = gates_matrix[4].iter().map(|x| Fr::from(*x)).collect();

    println!("\nql: {:?}", q_l);
    println!("qr: {:?}", q_r);
    println!("qm: {:?}", q_m);
    println!("qo: {:?}", q_o);
    println!("qc: {:?}", q_c);

    let domain = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
    let q_l = Evaluations::from_vec_and_domain(q_l, domain).interpolate();
    let q_r = Evaluations::from_vec_and_domain(q_r, domain).interpolate();
    let q_m = Evaluations::from_vec_and_domain(q_m, domain).interpolate();
    let q_o = Evaluations::from_vec_and_domain(q_o, domain).interpolate();
    let q_c = Evaluations::from_vec_and_domain(q_c, domain).interpolate();

    let qs = [q_l, q_r, q_m, q_o, q_c];

    // The public input poly vanishes everywhere except for the position of the
    // public input gate where it evaluates to -(public_input)
    let mut public_input: Vec<Fr> = (0..n).map(|_x| Fr::from(0)).collect();
    for i in 0..pub_input_position.len() {
        public_input[pub_input_position[i]] = Fr::from(-1 * pub_input_value[i]);
        //using -1 is correct
    }

    let p_i_poly = Evaluations::from_vec_and_domain(public_input, domain).interpolate();

    // We generate domains on which we can evaluate the witness polynomials
    let mut rng = ark_std::test_rng();
    let k = Fr::rand(&mut rng);

    let id_domain_a: Vec<Fr> = domain.elements().collect();
    let id_domain_b: Vec<Fr> = domain.get_coset(k).unwrap().elements().collect();
    let id_domain_c: Vec<Fr> = domain.get_coset(k * k).unwrap().elements().collect();
    let mut id_domain: Vec<Fr> = Vec::new();
    id_domain.extend(id_domain_a);
    id_domain.extend(id_domain_b);
    id_domain.extend(id_domain_c);

    let mut perm_domain: Vec<Fr> = Vec::new();

    for i in permutation {
        perm_domain.push(id_domain[i]);
    }
    let perm_domain_a = perm_domain[0..n].to_vec();
    let perm_domain_b = perm_domain[n..2 * n].to_vec();
    let perm_domain_c = perm_domain[2 * n..3 * n].to_vec();
    assert!(perm_domain_a.len() == n);
    assert!(perm_domain_b.len() == n);
    assert!(perm_domain_c.len() == n);

    // Generate polynomials that return the permuted index when evaluated on the domain
    let s_sigma_1 = Evaluations::from_vec_and_domain(perm_domain_a, domain).interpolate();
    let s_sigma_2 = Evaluations::from_vec_and_domain(perm_domain_b, domain).interpolate();
    let s_sigma_3 = Evaluations::from_vec_and_domain(perm_domain_c, domain).interpolate();

    let ss = [s_sigma_1, s_sigma_2, s_sigma_3];

    // We perform the trusted setup.
    let tau = Fr::rand(&mut rng);
    let mut crs = vec![G1Projective::generator() * (tau.pow([0 as u64]))];
    for i in 1..(n + 3) {
        crs.push(g1 * (tau.pow([i as u64])));
    }
    assert!(crs.len() == n + 3);

    // We take some work off the shoulders of the verifier by preprocessing
    println!("Starting Verifier Preprocessing...");
    let q_exp: Vec<Projective<g1::Config>> = (0..qs.len())
        .map(|f| evaluate_in_exponent(&crs, &qs[f]))
        .collect();
    let s_exp: Vec<Projective<g1::Config>> = (0..ss.len())
        .map(|f| evaluate_in_exponent(&crs, &ss[f]))
        .collect();
    let x_exp = G2Projective::generator() * tau;

    //let lookup_table: (Vec<Fr>, Vec<Fr>, Vec<Fr>) =

    let verifier_preprocessing = (q_exp, s_exp, x_exp);
    let perm_precomp = (id_domain, perm_domain, k, ss);

    SetupOutput {
        crs,
        qs,
        p_i_poly,
        perm_precomp,
        verifier_preprocessing,
    }
}

#[derive(Debug, Clone)]
pub struct SetupOutput {
    pub crs: Vec<Projective<g1::Config>>,
    pub qs: [DensePolynomial<Fp<MontBackend<FrConfig, 4>, 4>>; 5],
    pub p_i_poly: DensePolynomial<
        ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>,
    >,
    pub perm_precomp: (
        Vec<ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>>,
        Vec<ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>>,
        ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>,
        [DensePolynomial<
            ark_ff::Fp<ark_ff::MontBackend<ark_test_curves::bls12_381::FrConfig, 4>, 4>,
        >; 3],
    ),
    pub verifier_preprocessing: (
        Vec<Projective<g1::Config>>,
        Vec<Projective<g1::Config>>,
        Projective<g2::Config>,
    ),
}

pub fn evaluate_in_exponent(
    powers_of_tau: &Vec<Projective<g1::Config>>,
    poly: &DensePolynomial<Fr>,
) -> Projective<g1::Config> {
    if poly.degree() >= powers_of_tau.len() {
        println!(
            "poly.degree(): {} , powers_of_tau.len(){}",
            poly.degree(),
            powers_of_tau.len()
        );
        assert!(poly.degree() <= powers_of_tau.len());
    }

    let coeffs = poly.coeffs.clone();

    let product: Vec<Projective<g1::Config>> = (0..poly.len())
        .map(|x| powers_of_tau[x] * coeffs[x])
        .collect();

    product.iter().sum::<Projective<g1::Config>>() + g1::G1Projective::zero()
}
