use crate::utils::{permute_indices, transpose};
use ark_test_curves::bls12_381::Fr;

pub struct Witness {
    a: Vec<i32>,
    b: Vec<i32>,
    c: Vec<i32>,
}

impl Witness {
    pub fn new(a: Vec<i32>, b: Vec<i32>, c: Vec<i32>) -> Self {
        assert_eq!(a.len(), b.len());
        assert_eq!(a.len(), c.len());
        Self { a, b, c }
    }

    pub fn combined(&self) -> Vec<i32> {
        let mut concatenated = vec![];
        concatenated.extend(&self.a);
        concatenated.extend(&self.b);
        concatenated.extend(&self.c);
        concatenated
    }

    pub fn as_field_elements(&self) -> Vec<Fr> {
        let res = self.combined();
        (0..res.len()).map(|f| Fr::from(res[f])).collect()
    }
}
pub struct Circuit<'l> {
    a: Vec<&'l str>,
    b: Vec<&'l str>,
    c: Vec<&'l str>,
    q_l: Vec<i32>,
    q_r: Vec<i32>,
    q_m: Vec<i32>,
    q_o: Vec<i32>,
    q_c: Vec<i32>,
    q_lookup: Vec<i32>,

    pub pub_gate_position: Vec<usize>,
    pub pub_gate_value: Vec<i32>,
}

impl<'l> Circuit<'l> {
    pub fn new() -> Self {
        let a = Vec::new();
        let b = Vec::new();
        let c = Vec::new();

        let q_l = Vec::new();
        let q_r = Vec::new();
        let q_m = Vec::new();
        let q_o = Vec::new();
        let q_c = Vec::new();
        let q_lookup = Vec::new();

        let pub_gate_position = Vec::new();
        let pub_gate_value = Vec::new();
        Circuit {
            a,
            b,
            c,
            q_l,
            q_r,
            q_m,
            q_o,
            q_c,
            q_lookup,
            pub_gate_position,
            pub_gate_value,
        }
    }

    pub fn add_constraint(
        &mut self,
        a: &'l str,
        operation: Operation,
        b: &'l str,
        equals_c: &'l str,
    ) {
        self.a.push(a);
        self.b.push(b);
        self.c.push(equals_c);

        match operation {
            Operation::Add => {
                self.assign_operation(vec![1, 1, 0, -1, 0, 0]);
            }
            Operation::Mul => self.assign_operation(vec![0, 0, 1, -1, 0, 0]),
            Operation::Const => {
                self.assign_operation(vec![0, 1, 0, 0, -1 * b.parse::<i32>().unwrap(), 0])
            }
            Operation::PublicInput => {
                self.pub_gate_position.push(self.a.len());
                self.pub_gate_value.push(b.parse::<i32>().unwrap());
                self.assign_operation(vec![0, 1, 0, 0, 0, 0]);
            }
            Operation::Empty => self.assign_operation(vec![0, 0, 0, 0, 0, 0]),
        }
    }
    fn assign_operation(&mut self, operation: Vec<i32>) {
        self.q_l.push(operation[0]);
        self.q_r.push(operation[1]);
        self.q_m.push(operation[2]);
        self.q_o.push(operation[3]);
        self.q_c.push(operation[4]);
        self.q_lookup.push(operation[5]);
    }

    pub fn get_wires(&self) -> Vec<&str> {
        let mut wires = self.a.to_vec();
        wires.append(self.b.to_vec().as_mut());
        wires.append(self.c.to_vec().as_mut());
        wires
    }

    pub fn get_permuted_indices(&self) -> Vec<usize> {
        permute_indices(self.get_wires())
    }

    pub fn lenght(&self) -> usize {
        assert!(self.a.len() == self.b.len());
        assert!(self.b.len() == self.c.len());
        assert!(self.c.len() == self.q_m.len());
        assert!(self.c.len() == self.q_l.len());
        assert!(self.c.len() == self.q_c.len());
        assert!(self.c.len() == self.q_o.len());
        assert!(self.c.len() == self.q_r.len());
        let n = self.a.len();
        assert!(n & n - 1 == 0, "n must be a power of 2");
        n
    }

    pub fn check_witness(&self, witness: &Vec<i32>) -> bool {
        let n = witness.len();
        assert!(n % 3 == 0);
        let a = witness[..n / 3].to_vec();
        let b = witness[n / 3..(2 * n) / 3].to_vec();
        let c = witness[(2 * n) / 3..n].to_vec();
        for i in 0..self.lenght() {
            if a[i] * self.q_l[i]
                + b[i] * self.q_r[i]
                + c[i] * self.q_m[i]
                + a[i] * b[i] * self.q_o[i]
                + self.q_c[i]
                != 0
            {
                return false;
            }
        }
        true
    }

    pub fn add_lookup(&mut self) {
        self.q_lookup[5] = 1;
    }

    pub fn get_gates_matrix(&self) -> Vec<Vec<i32>> {
        vec![
            self.q_l.clone(),
            self.q_r.clone(),
            self.q_m.clone(),
            self.q_o.clone(),
            self.q_c.clone(),
            self.q_lookup.clone(),
        ]
    }

    pub fn add_constraint_with_lookup(
        &mut self,
        a: &'l str,
        operation: Operation,
        b: &'l str,
        equals_c: &'l str,
    ) {
        self.add_constraint(a, operation, b, equals_c);
        self.add_lookup();
    }
}

pub enum Operation {
    Add,
    Mul,
    Const,
    PublicInput,
    Empty,
}
