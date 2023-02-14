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
    op: Vec<Vec<i32>>,
    pub pub_gate_position: Vec<usize>,
    pub pub_gate_value: Vec<i32>,
    lookup: Vec<bool>,
}

impl<'l> Circuit<'l> {
    pub fn new() -> Self {
        let a = Vec::new();
        let b = Vec::new();
        let c = Vec::new();
        let op = Vec::new();
        let lookup: Vec<bool> = Vec::new();
        let pub_gate_position = Vec::new();
        let pub_gate_value = Vec::new();
        Circuit {
            a,
            b,
            c,
            op,
            pub_gate_position,
            pub_gate_value,
            lookup,
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
        self.lookup.push(false);

        match operation {
            Operation::Add => self.op.push(vec![1, 1, 0, -1, 0]),
            Operation::Mul => self.op.push(vec![0, 0, 1, -1, 0]),
            Operation::Const => self
                .op
                .push(vec![0, 1, 0, 0, -1 * b.parse::<i32>().unwrap()]),
            Operation::PublicInput => {
                self.pub_gate_position.push(self.op.len());
                self.pub_gate_value.push(b.parse::<i32>().unwrap());
                self.op.push(vec![0, 1, 0, 0, 0]);
            }
            Operation::Empty => self.op.push(vec![0, 0, 0, 0, 0]),
        }
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

    pub fn get_gates_matrix(&self) -> Vec<Vec<i32>> {
        transpose(self.op.clone())
    }

    pub fn lenght(&self) -> usize {
        assert!(self.a.len() == self.b.len());
        assert!(self.b.len() == self.c.len());
        assert!(self.c.len() == self.op.len());
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
        for i in 0..self.op.len() {
            if a[i] * self.op[i][0]
                + b[i] * self.op[i][1]
                + c[i] * self.op[i][2]
                + a[i] * b[i] * self.op[i][3]
                + self.op[i][4]
                != 0
            {
                return false;
            }
        }
        true
    }

    pub fn add_lookup(&mut self) {
        self.lookup[self.a.len() - 1] = true;
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
