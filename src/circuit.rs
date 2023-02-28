use crate::table::Table;
use crate::utils::permute_indices;
use ark_test_curves::bls12_381::Fr;

pub struct Witness {
    a: Vec<Fr>,
    b: Vec<Fr>,
    c: Vec<Fr>,
}

impl Witness {
    pub fn new(a: Vec<i32>, b: Vec<i32>, c: Vec<i32>) -> Self {
        assert_eq!(a.len(), b.len());
        assert_eq!(a.len(), c.len());

        let a = a.iter().map(|x| Fr::from(*x)).collect();
        let b = b.iter().map(|x| Fr::from(*x)).collect();
        let c = c.iter().map(|x| Fr::from(*x)).collect();

        Self { a, b, c }
    }

    pub fn combined(&self) -> Vec<Fr> {
        let mut concatenated = vec![];
        concatenated.extend(&self.a);
        concatenated.extend(&self.b);
        concatenated.extend(&self.c);
        concatenated
    }
    pub fn len(&self) -> usize {
        assert!(self.a.len() == self.b.len());
        assert!(self.b.len() == self.c.len());
        self.a.len()
    }
}
pub struct Circuit<'l> {
    a: Vec<&'l str>,
    b: Vec<&'l str>,
    c: Vec<&'l str>,
    q_l: Vec<Fr>,
    q_r: Vec<Fr>,
    q_m: Vec<Fr>,
    q_o: Vec<Fr>,
    q_c: Vec<Fr>,
    q_lookup: Vec<Fr>,
    pub pub_gate_position: Vec<usize>,
    pub pub_gate_value: Vec<Fr>,
    pub table: Table,
}

impl<'l> Circuit<'l> {
    pub fn new() -> Self {
        let a = Vec::new();
        let b = Vec::new();
        let c = Vec::new();

        let q_l: Vec<Fr> = Vec::new();
        let q_r: Vec<Fr> = Vec::new();
        let q_m: Vec<Fr> = Vec::new();
        let q_o: Vec<Fr> = Vec::new();
        let q_c: Vec<Fr> = Vec::new();
        let q_lookup: Vec<Fr> = Vec::new();
        let pub_gate_position = Vec::new();
        let pub_gate_value = Vec::new();
        let table: Table = Table::new();
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
            table,
        }
    }

    pub fn get_mut_table(&mut self) -> &mut Table {
        &mut self.table
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
            Operation::Add => self.apply_operation(vec![1, 1, 0, -1, 0, 0]),
            Operation::Mul => self.apply_operation(vec![0, 0, 1, -1, 0, 0]),
            Operation::Const => {
                self.apply_operation(vec![0, 1, 0, 0, -1 * equals_c.parse::<i32>().unwrap(), 0])
            }
            Operation::PublicInput => {
                self.pub_gate_position.push(self.q_r.len());
                self.pub_gate_value
                    .push(Fr::from(b.parse::<i32>().unwrap()));
                self.apply_operation(vec![0, 1, 0, 0, 0, 0]);
            }
            Operation::Empty => self.apply_operation(vec![0, 0, 0, 0, 0, 0]),
        }
    }

    fn apply_operation(&mut self, op: Vec<i32>) {
        self.q_l.push(Fr::from(op[0]));
        self.q_r.push(Fr::from(op[1]));
        self.q_m.push(Fr::from(op[2]));
        self.q_o.push(Fr::from(op[3]));
        self.q_c.push(Fr::from(op[4]));
        self.q_lookup.push(Fr::from(op[5]));
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

    pub fn get_gates_matrix(&self) -> Vec<Vec<Fr>> {
        vec![
            self.q_l.clone(),
            self.q_r.clone(),
            self.q_m.clone(),
            self.q_o.clone(),
            self.q_c.clone(),
            self.q_lookup.clone(),
        ]
    }

    pub fn len(&self) -> usize {
        let n = self.a.len();
        n
    }

    pub fn width(&self) -> usize {
        self.get_gates_matrix().len()
    }

    pub fn check(&self, witness: &Witness) -> bool {
        let n = self.a.len();
        assert!(n > 0);
        assert!(self.b.len() == n);
        assert!(self.c.len() == n);
        assert!(self.q_l.len() == n);
        assert!(self.q_r.len() == n);
        assert!(self.q_m.len() == n);
        assert!(self.q_o.len() == n);
        assert!(self.q_c.len() == n);
        assert!(self.q_c.len() == n);
        assert!(self.table.len() == n);
        assert!(n & n - 1 == 0, "n must be a power of 2");
        self.check_witness(witness)
    }

    pub fn check_witness(&self, witness: &Witness) -> bool {
        let n = witness.len();
        let a = &witness.a;
        let b = &witness.b;
        let c = &witness.c;

        for i in 0..n / 3 {
            if self.q_lookup[i] == Fr::from(1) {
                assert!(self.table.get(a[i], b[i]).unwrap() == c[i]);
            }
            if a[i] * self.q_l[i]
                + b[i] * self.q_r[i]
                + c[i] * self.q_m[i]
                + a[i] * b[i] * self.q_o[i]
                + self.q_c[i]
                != Fr::from(0)
            {
                return false;
            }
        }
        true
    }

    pub fn add_lookup(&mut self) {
        self.q_lookup[self.a.len() - 1] = Fr::from(1);
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
