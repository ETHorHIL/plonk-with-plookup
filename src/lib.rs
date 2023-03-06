pub mod circuit;
pub mod prover;
pub mod setup;
pub mod table;
pub mod utils;
pub mod verifier;

#[cfg(test)]
pub mod tests {
    use crate::circuit::{Circuit, Operation, Witness};

    use super::*;
    use ark_test_curves::bls12_381::Fr;
    use prover::prover_algo;
    use setup::Setup;
    use verifier::verifier_algo;

    #[test]
    fn test_plookup() {

/*
        The constraints:
        a      |   op   | b      |c
        -------------------------------
        1      |  const | 1      | = 1
        1      |  const | 5      | = 5
        1      |  const | 9      | = 9
        1      | lookup | 5      | = 9


        The lookup table:
        x | y | z
        ---------
        0 | 4 | 8
        1 | 5 | 9
        2 | 6 | 10
        3 | 7 | 11


        A satisfying witness is
        a | b  | c
        ---------
        1 | 1 | 1
        1 | 5 | 5
        1 | 9 | 9
        1 | 5 | 9
         */

        let mut circuit = Circuit::new();
        circuit.add_constraint("null", Operation::Const, "b_1", "1");
        circuit.add_constraint("null", Operation::Const, "b_2", "5");
        circuit.add_constraint("null", Operation::Const, "b_3", "9");
        circuit.add_constraint_with_lookup("b_1", Operation::Empty, "b_2", "b_3");

        let table = circuit.get_mut_table();
        table.insert(Fr::from(0), Fr::from(4), Fr::from(8));
        table.insert(Fr::from(1), Fr::from(5), Fr::from(9));
        table.insert(Fr::from(2), Fr::from(6), Fr::from(10));
        table.insert(Fr::from(3), Fr::from(7), Fr::from(11));

        let witness = Witness::new(vec![0, 0, 0, 1], vec![1, 5, 9, 5], vec![1, 5, 9, 9]);
        circuit.check(&witness);
        let n = circuit.len();

        let setup_output = Setup::process(&mut circuit);

        let proof = prover_algo(witness.combined(), &setup_output, circuit);

        verifier_algo(
            proof,
            n,
            setup_output.pub_input,
            setup_output.verifier_prep,
            setup_output.perm_precomp.k,
        );
    }

    #[test]
    fn test_plookup_bigger() {
        /*

        Adding a lookup to vitaliks example. The example doesnt make sense other than to show that the looup works.

        a     |op| b   | c
        -----------------------
        x      * x      = var1
        var1   * x      = var2
        var2   + x      = var3
        1      ° 5      = 5
        1      ° 35     = 35
        var3   + 5      = 35
        x     lu 5      = 35
        empty2 ° empty4 = empty6


        The lookup table:
        x | y | z
        ---------
        0 | 4 | 8
        1 | 5 | 9
        2 | 6 | 10
        3 | 5 | 35
        4 | 4 | 8
        5 | 5 | 9
        6 | 6 | 10
        7 | 7 | 11


        A satisfying witness is
        a | b  | c
        ---------
        3  | 3  | 9
        9  | 3  | 27
        27 | 3  | 30
        1  | 5  | 5
        1  | 35 | 35
        30 | 5  | 35
        3  | 5  | 35
        0  | 0  | 0


         */

        let mut circuit = Circuit::new();
        circuit.add_constraint("x", Operation::Mul, "x", "var1");
        circuit.add_constraint("var1", Operation::Mul, "x", "var2");
        circuit.add_constraint("var2", Operation::Add, "x", "var3");
        circuit.add_constraint("1", Operation::Const, "5", "5");
        circuit.add_constraint("1", Operation::PublicInput, "35", "35");
        circuit.add_constraint("var3", Operation::Add, "5", "35");
        circuit.add_constraint_with_lookup("x", Operation::Empty, "5", "35");
        circuit.add_constraint("empty", Operation::Empty, "empty", "empty");

        let table = circuit.get_mut_table();
        table.insert(Fr::from(0), Fr::from(4), Fr::from(8));
        table.insert(Fr::from(1), Fr::from(5), Fr::from(9));
        table.insert(Fr::from(2), Fr::from(6), Fr::from(10));
        table.insert(Fr::from(3), Fr::from(5), Fr::from(35));
        table.insert(Fr::from(4), Fr::from(4), Fr::from(8));
        table.insert(Fr::from(5), Fr::from(5), Fr::from(9));
        table.insert(Fr::from(6), Fr::from(6), Fr::from(10));
        table.insert(Fr::from(7), Fr::from(7), Fr::from(11));

        let a = vec![3, 9, 27, 1, 1, 30, 3, 0];
        let b = vec![3, 3, 3, 5, 35, 5, 5, 0];
        let c = vec![9, 27, 30, 5, 35, 35, 35, 0];

        let witness = Witness::new(a, b, c);
        circuit.check_witness(&witness);
        let n = circuit.len();

        let setup_output = Setup::process(&mut circuit);
        let proof = prover_algo(witness.combined(), &setup_output.clone(), circuit);

        verifier_algo(
            proof,
            n,
            setup_output.pub_input,
            setup_output.verifier_prep,
            setup_output.perm_precomp.k,
        );
    }
}
