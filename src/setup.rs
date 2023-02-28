use crate::circuit::Circuit;
use crate::utils::evaluate_in_exponent;
use ark_ec::models::short_weierstrass::*;
use ark_ff::*;
use ark_poly::univariate::DensePolynomial;
use ark_poly::*;
use ark_test_curves::bls12_381::*;
use ark_test_curves::*;

///use crate::plookup::lookup::lookup::LookUp;
//use crate::plookup::lookup::table::{Generic, LookUpTable};

#[derive(Debug, Clone)]
pub struct Setup {
    // Powers of Tau
    pub crs: Vec<Projective<g1::Config>>,
    // Gates Polynomials
    pub qs: Qs,
    // Public input polynomual
    pub pub_input: DensePolynomial<Fr>,
    // Precomuptation of permutation
    pub perm_precomp: Permutation,
    // Preprocessing for verifier
    pub verifier_prep: VerifierPrep,
}

impl Setup {
    pub fn process(circuit: &mut Circuit) -> Self {
        let n = circuit.len();
        let domain = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
        let mut rng = ark_std::test_rng();
        let tau = Fr::rand(&mut rng);

        // Perform the trusted setup: ([1]_1, [x]_1, ... . [x^n+5]_1)
        let crs = trusted_setup(tau, n);

        // Make a polynomial out of the public inputs
        let pub_input = pub_input_poly(&circuit, domain);

        // Generate Gate Polynomials (Q_M, Q_L, Q_R, Q_O, Q_C and Q_K)
        let qs = Qs::new(circuit, domain);

        // Generate the lookup table polynomials (T_1, T_2, T,3)
        let tables = circuit.get_mut_table().generate_table_polys();

        // Generate the polynomials and values for the permutation argument: (S_1, S_2, S3 and the domains)
        let perm_precomp = Permutation::new(circuit.get_permuted_indices(), domain);

        // Evaluate the polynomials in the exponent (commit) and create tau * G2
        let verifier_prep = VerifierPrep::new(&qs, &perm_precomp, tables, &tau, &crs);

        Self {
            crs,
            qs,
            pub_input,
            perm_precomp,
            verifier_prep,
        }
    }
}

fn trusted_setup(tau: Fr, n: usize) -> Vec<Projective<g1::Config>> {
    let mut crs = vec![G1Projective::generator() * (tau.pow([0 as u64]))];
    for i in 1..(n + 5) {
        crs.push(G1Projective::generator() * (tau.pow([i as u64])));
    }
    assert!(crs.len() == n + 5);
    crs
}

fn pub_input_poly(circuit: &Circuit, domain: Radix2EvaluationDomain<Fr>) -> DensePolynomial<Fr> {
    let pub_input_position = &circuit.pub_gate_position;
    let pub_input_value = &circuit.pub_gate_value;
    let mut public_input: Vec<Fr> = (0..circuit.len()).map(|_x| Fr::from(0)).collect();
    for i in 0..pub_input_position.len() {
        public_input[pub_input_position[i]] = Fr::from(Fr::from(-1) * pub_input_value[i]);
    }
    Evaluations::from_vec_and_domain(public_input, domain).interpolate()
}

#[derive(Debug, Clone)]
pub struct VerifierPrep {
    q_exp: Vec<Projective<g1::Config>>,
    s_exp: Vec<Projective<g1::Config>>,
    x_exp: Projective<g2::Config>,
    table_exp: Vec<Projective<g1::Config>>,
}

impl VerifierPrep {
    pub fn new(
        qs: &Qs,
        perm_precomp: &Permutation,
        table_polys: [DensePolynomial<Fp<MontBackend<FrConfig, 4>, 4>>; 3],
        tau: &Fr,
        crs: &Vec<Projective<g1::Config>>,
    ) -> Self {
        let q_exp: Vec<Projective<g1::Config>> = qs
            .as_vec()
            .into_iter()
            .map(|f| evaluate_in_exponent(&crs, &f))
            .collect();

        let s_exp: Vec<Projective<g1::Config>> = [
            &perm_precomp.s_sigma_1,
            &perm_precomp.s_sigma_2,
            &perm_precomp.s_sigma_3,
        ]
        .into_iter()
        .map(|f| evaluate_in_exponent(&crs, f))
        .collect();

        let x_exp = G2Projective::generator() * tau;

        let table_exp: Vec<Projective<g1::Config>> = (0..3)
            .map(|i| evaluate_in_exponent(&crs, &table_polys[i]))
            .collect();

        Self {
            q_exp,
            s_exp,
            x_exp,
            table_exp,
        }
    }

    pub fn as_tuple(
        &self,
    ) -> (
        &Vec<Projective<g1::Config>>,
        &Vec<Projective<g1::Config>>,
        &Projective<g2::Config>,
        &Vec<Projective<g1::Config>>,
    ) {
        (&self.q_exp, &self.s_exp, &self.x_exp, &self.table_exp)
    }
}

#[derive(Debug, Clone)]
pub struct Permutation {
    id_domain: Vec<Fr>,
    perm_domain: Vec<Fr>,
    pub k: Fr,
    s_sigma_1: DensePolynomial<Fr>,
    s_sigma_2: DensePolynomial<Fr>,
    s_sigma_3: DensePolynomial<Fr>,
}

impl Permutation {
    fn new(permutation: Vec<usize>, domain: Radix2EvaluationDomain<Fr>) -> Self {
        // We generate domains on which we can evaluate the witness polynomials
        let n = permutation.len() / 3;
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

        Self {
            id_domain,
            perm_domain,
            k,
            s_sigma_1,
            s_sigma_2,
            s_sigma_3,
        }
    }

    pub fn as_tuple(&self) -> (&Vec<Fr>, &Vec<Fr>, &Fr, [&DensePolynomial<Fr>; 3]) {
        (
            &self.id_domain,
            &self.perm_domain,
            &self.k,
            [&self.s_sigma_1, &self.s_sigma_2, &self.s_sigma_3],
        )
    }

    pub fn get_ss(&self) -> [&DensePolynomial<Fr>; 3] {
        [&self.s_sigma_1, &self.s_sigma_2, &self.s_sigma_3]
    }
}

#[derive(Debug, Clone)]
pub struct Qs {
    q_l: DensePolynomial<Fr>,
    q_r: DensePolynomial<Fr>,
    q_m: DensePolynomial<Fr>,
    q_o: DensePolynomial<Fr>,
    q_c: DensePolynomial<Fr>,
    q_lookup: DensePolynomial<Fr>,
}

impl Qs {
    pub fn new(circuit: &Circuit, domain: Radix2EvaluationDomain<Fr>) -> Self {
        let gates_matrix = circuit.get_gates_matrix();

        let q_l = Evaluations::from_vec_and_domain(gates_matrix[0].clone(), domain).interpolate();
        let q_r = Evaluations::from_vec_and_domain(gates_matrix[1].clone(), domain).interpolate();
        let q_m = Evaluations::from_vec_and_domain(gates_matrix[2].clone(), domain).interpolate();
        let q_o = Evaluations::from_vec_and_domain(gates_matrix[3].clone(), domain).interpolate();
        let q_c = Evaluations::from_vec_and_domain(gates_matrix[4].clone(), domain).interpolate();
        let q_lookup =
            Evaluations::from_vec_and_domain(gates_matrix[5].clone(), domain).interpolate();
        Self {
            q_l,
            q_r,
            q_m,
            q_o,
            q_c,
            q_lookup,
        }
    }

    pub fn as_vec(&self) -> Vec<&DensePolynomial<Fr>> {
        vec![
            &self.q_l,
            &self.q_r,
            &self.q_m,
            &self.q_o,
            &self.q_c,
            &self.q_lookup,
        ]
    }
}
