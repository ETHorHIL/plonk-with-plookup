use ark_poly::univariate::DensePolynomial;
use ark_poly::*;
use ark_test_curves::bls12_381::Fr;
use ark_test_curves::Field;
pub struct Table {
    pub x: Vec<Fr>,
    pub y: Vec<Fr>,
    pub z: Vec<Fr>,
    poly_x: Option<DensePolynomial<Fr>>,
    poly_y: Option<DensePolynomial<Fr>>,
    poly_z: Option<DensePolynomial<Fr>>,
}

impl Table {
    pub fn len(&self) -> usize {
        let n = self.x.len();
        assert!(self.y.len() == n);
        assert!(self.z.len() == n);
        n
    }
    pub fn new() -> Self {
        Self {
            x: Vec::new(),
            y: Vec::new(),
            z: Vec::new(),
            poly_x: None,
            poly_y: None,
            poly_z: None,
        }
    }

    pub fn insert(&mut self, x: Fr, y: Fr, z: Fr) {
        self.x.push(x);
        self.y.push(y);
        self.z.push(z);
    }

    pub fn get(&self, x: Fr, y: Fr) -> Option<Fr> {
        for i in 0..self.x.len() {
            if self.x[i] == x {
                if self.y[i] == y {
                    return Some(self.z[i]);
                }
            }
        }
        None
    }

    pub fn generate_table_polys(&mut self) -> [DensePolynomial<Fr>; 3] {
        let n = self.x.len();
        assert!(self.y.len() == n);
        assert!(self.z.len() == n);
        let domain: Radix2EvaluationDomain<Fr> = EvaluationDomain::new(n).unwrap();

        // Pad

        self.poly_x = Some(Evaluations::from_vec_and_domain(self.x.clone(), domain).interpolate());
        self.poly_y = Some(Evaluations::from_vec_and_domain(self.y.clone(), domain).interpolate());
        self.poly_z = Some(Evaluations::from_vec_and_domain(self.z.clone(), domain).interpolate());
        [
            self.poly_x.clone().unwrap(),
            self.poly_y.clone().unwrap(),
            self.poly_z.clone().unwrap(),
        ]
    }

    pub fn get_table_polys(&self) -> [DensePolynomial<Fr>; 3] {
        [
            self.poly_x.clone().unwrap(),
            self.poly_y.clone().unwrap(),
            self.poly_z.clone().unwrap(),
        ]
    }

    pub fn compress_table_vector(&self, compression_factor: Fr) -> Vec<Fr> {
        // First find the set with the most elements
        let mut res = vec![];
        for i in 0..self.x.len() {
            let val = self.x[i]
                + compression_factor * self.y[i]
                + compression_factor.pow([2]) * self.z[i];
            res.push(val)
        }
        res
    }

    pub fn compute_h1_h2(&self, f: &Vec<Fr>, t: &Vec<Fr>) -> (Vec<Fr>, Vec<Fr>) {
        //
        // 1. Compute s
        // XXX: we no longer use sorted by t definition
        let sorted_s = self.concatenate_and_sort(&f, &t);

        //2 . Compute h_1 and h_2
        let (h_1, h_2) = self.alternate(sorted_s);
        // assert that the last element of h_1 is equal to the first element of h_2
        (h_1, h_2)
    }

    pub fn concatenate_and_sort(&self, f: &Vec<Fr>, t: &Vec<Fr>) -> Vec<Fr> {
        assert!(self.is_subset_of(&f, &t));
        let mut result = t.clone();

        for element in f.iter() {
            let index = self.position(&result, element);
            result.insert(index, *element);
        }

        result
    }

    pub fn is_subset_of(&self, one: &Vec<Fr>, other: &Vec<Fr>) -> bool {
        let mut is_subset = true;

        for x in one.iter() {
            is_subset = other.contains(x);
            if is_subset == false {
                break;
            }
        }
        is_subset
    }

    fn position(&self, vec: &Vec<Fr>, element: &Fr) -> usize {
        let index = vec.iter().position(|&x| x == *element).unwrap();
        index
    }

    pub fn alternate(&self, vec: Vec<Fr>) -> (Vec<Fr>, Vec<Fr>) {
        let n = vec.len();

        let mut uneven: Vec<Fr> = vec![];
        let mut even: Vec<Fr> = vec![];

        for i in 0..n {
            if i % 2 == 0 {
                even.push(vec[i])
            } else {
                uneven.push(vec[i])
            }
        }

        assert!(uneven.len() == even.len());
        assert!(uneven.len() == n / 2);
        (uneven, even)
    }
}
