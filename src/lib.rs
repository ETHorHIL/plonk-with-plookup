pub mod circuit;
pub mod plookup;
pub mod prover;
pub mod setup;
pub mod utils;
pub mod verifier;
use std::collections::HashMap;

#[cfg(test)]
pub mod tests {
    use crate::circuit::{Circuit, Operation, Witness};

    use super::*;
    use ark_test_curves::bls12_381::Fr;
    use plookup::lookup::lookup::LookUp;
    use plookup::lookup::table::LookUpTable;
    use prover::prover_algo;
    use setup::setup_algo;
    use utils::{permute_indices, transpose};
    use verifier::verifier_algo;

    #[test]
    fn test_plookup() {
        /*
        Test simple circuit with a lookup. We want to know if the prover knows x, y binary numbers that add up to 1. So we use lookup tables to enforce that x and y are binary

        a  |   op | b    |c
        x   lookup  y    = 0
        x      +    y   = 1
        1    const  1   = 1
        empty1 ° empty3 = empty5
        empty2 ° empty4 = empty6

        We use this lookup table to enforce that x and y are binary

        The lookup table would be used
        x | y | z
        ---------
        0 | 0 | 0
        1 | 0 | 0
        0 | 1 | 0
        1 | 1 | 0

        A satisfying witness is

        a | b | c
        ---------
        1 | 0 | 0
        1 | 0 | 1
        1 | 1 | 1
        0 | 0 | 0

        we have one read to our table: (1,0,0)
         */
        let zero = Fr::from(0);
        let one = Fr::from(1);
        let mut table: HashMap<(Fr, Fr), Fr> = HashMap::new();
        table.insert((zero, zero), zero);
        table.insert((one, zero), zero);
        table.insert((zero, one), zero);
        table.insert((one, one), zero);
        //let table = LookUp::new(table);

        let mut circuit = Circuit::new();
        circuit.add_constraint_with_lookup("x", Operation::Empty, "y", "0");
        circuit.add_constraint("x", Operation::Add, "y", "1");
        circuit.add_constraint("1", Operation::Const, "1", "1");
        circuit.add_constraint("empty1", Operation::Empty, "empty3", "empty5");

        let witness = Witness::new(vec![1, 1, 1, 0], vec![0, 0, 1, 0], vec![0, 1, 1, 0]);
        circuit.check_witness(&witness.combined());
        let witness = witness.as_field_elements();

        let setup_output = setup_algo(
            circuit.get_gates_matrix(),
            circuit.get_permuted_indices(),
            circuit.pub_gate_position,
            circuit.pub_gate_value,
        );
    }

    #[test]
    fn test_vitalik_example() {
        /*
        In this example we prove that we know x such that P(x) = x^3 + x  + 5 (hint x = 3).
        We can break this down to contraint equations like this.

        a     |op| b   | c
        -----------------------
        x      * x      = var1
        var1   * x      = var2
        var2   + x      = var3
        1      ° 5      = 5
        1      ° 35     = 35
        var3   + 5      = 35
        empty1 ° empty3 = empty5
        empty2 ° empty4 = empty6

        Note that we always want the number of constraints to be a power of two. Hence we added
        two empty constraints. The result of this excercise are four vectors a,b,c and op.


        */

        let mut circuit = Circuit::new();
        // We only care about detecting repeating values in the equations. So it doesnt matter whats
        // in the strings. Except for Const and Public input where we parse the b value into a i32.
        // right any number of public inputs other than 1 is unsupportend (also zero)
        circuit.add_constraint("x", Operation::Mul, "x", "var1");
        circuit.add_constraint("var1", Operation::Mul, "x", "var2");
        circuit.add_constraint("var2", Operation::Add, "x", "var3");
        circuit.add_constraint("1", Operation::Const, "5", "5");
        circuit.add_constraint("1", Operation::PublicInput, "35", "35");
        circuit.add_constraint("var3", Operation::Add, "5", "35");
        circuit.add_constraint("empty1", Operation::Empty, "empty3", "empty5");
        circuit.add_constraint("empty2", Operation::Empty, "empty4", "empty6");

        // satisfying witness for the circuit. Plugging in these numbers will make all equations above check out
        let a = vec![3, 9, 27, 1, 1, 30, 0, 0];
        let b = vec![3, 3, 3, 5, 35, 5, 0, 0];
        let c = vec![9, 27, 30, 5, 35, 35, 0, 0];

        let witness = Witness::new(a, b, c);
        circuit.check_witness(&witness.combined());
        let witness = witness.as_field_elements();

        // We start with a setup that computes the trusted setup and does some
        // precomputation
        let n = circuit.lenght();

        let setup_output = setup_algo(
            circuit.get_gates_matrix(),
            circuit.get_permuted_indices(),
            circuit.pub_gate_position,
            circuit.pub_gate_value,
        );
        println!("Setup Complete. Output:");

        // # The prover calculates the proof
        let proof = prover_algo(witness, &setup_output.clone());
        println!("Computed Proof: {:?}", proof);

        //# Verifier checks if proof checks out
        verifier_algo(
            proof,
            n,
            setup_output.p_i_poly,
            setup_output.verifier_preprocessing,
            setup_output.perm_precomp.2,
        );
    }

    #[test]
    fn test_my_example() {
        /*
        I wan to prove that I know x so that x^2 + 1 = 10

        # Constrains
        x     * x = var1
        1 const 1 = 1
        1 pub_i 10 = 10
        var1  + 1 = 10

        # Witness
        a   b   c
        3 * 3 = 9
        1 ° 1 = 1
        1 ° 10 = 10
        9 + 1 = 10

        */

        let mut circuit = Circuit::new();
        // We only care about detecting repeating values in the equations. So it doesnt matter whats
        // in the strings. Except for Const and Public input where we parse the b value into a i32.
        // right any number of public inputs other than 1 is unsupportend (also zero)
        circuit.add_constraint("x", Operation::Mul, "x", "var1");
        circuit.add_constraint("1", Operation::Const, "1", "1");
        circuit.add_constraint("1", Operation::PublicInput, "10", "10");
        circuit.add_constraint("var1", Operation::Add, "1", "10");

        // satisfying witness for the circuit. Plugging in these numbers will make all equations above check out
        let witness = vec![
            3, 1, 1, 9, // a
            3, 1, 10, 1, // b
            9, 1, 10, 10, // c
        ];
        let witness: Vec<Fr> = (0..witness.len()).map(|f| Fr::from(witness[f])).collect();

        // We start with a setup that computes the trusted setup and does some
        // precomputation
        let n = circuit.lenght();

        let setup_output = setup_algo(
            circuit.get_gates_matrix(),
            circuit.get_permuted_indices(),
            circuit.pub_gate_position,
            circuit.pub_gate_value,
        );
        println!("Setup Complete. Output: {:?}", setup_output);

        // # The prover calculates the proof
        let proof = prover_algo(witness, &setup_output.clone());
        println!("Computed Proof: {:?}", proof);

        //# Verifier checks if proof checks out
        verifier_algo(
            proof,
            n,
            setup_output.p_i_poly,
            setup_output.verifier_preprocessing,
            setup_output.perm_precomp.2,
        );
    }

    #[test]
    fn test_two_public_inputs() {
        /*
        I wan to prove that I know x,y so that x^2 + y + 1 = 12
        solution x =3, y =2

        # Constrains
        x     * x = var1
        1 const 1 = 1
        1 pub_i 10 = 10
        1 pub_i  = 2
        var1  + 1 = 10
        10 + 2 = 12
        empty1 ° empty3 = empty5
        empty2 ° empty4 = empty6

        # Witness
        a   b   c
        ---------
        3 * 3 = 9
        1 ° 1 = 1
        1 ° 10 = 10
        1 ° 2  = 2
        9 + 1 = 10
        10 + 2 = 12
        0 ° 0 = 0
        0 ° 0 = 0
        */

        let mut circuit = Circuit::new();
        // We only care about detecting repeating values in the equations. So it doesnt matter whats
        // in the strings. Except for Const and Public input where we parse the b value into a i32.
        // right any number of public inputs other than 1 is unsupportend (also zero)
        circuit.add_constraint("x", Operation::Mul, "x", "var1");
        circuit.add_constraint("1", Operation::Const, "1", "1");
        circuit.add_constraint("1", Operation::PublicInput, "10", "10");
        circuit.add_constraint("1", Operation::PublicInput, "2", "2");
        circuit.add_constraint("var1", Operation::Add, "1", "10");
        circuit.add_constraint("10", Operation::Add, "2", "12");
        circuit.add_constraint("empty1", Operation::Empty, "empty3", "empty5");
        circuit.add_constraint("empty2", Operation::Empty, "empty4", "empty6");

        // satisfying witness for the circuit. Plugging in these numbers will make all equations above check out
        let witness = vec![
            3, 1, 1, 1, 9, 10, 0, 0, // a
            3, 1, 10, 2, 1, 2, 0, 0, // b
            9, 1, 10, 2, 10, 12, 0, 0, // c
        ];
        circuit.check_witness(&witness);
        let witness: Vec<Fr> = (0..witness.len()).map(|f| Fr::from(witness[f])).collect();

        // We start with a setup that computes the trusted setup and does some
        // precomputation
        let n = circuit.lenght();

        let setup_output = setup_algo(
            circuit.get_gates_matrix(),
            circuit.get_permuted_indices(),
            circuit.pub_gate_position,
            circuit.pub_gate_value,
        );
        println!("Setup Complete. Output: {:?}", setup_output);

        // # The prover calculates the proof
        let proof = prover_algo(witness, &setup_output.clone());
        println!("Computed Proof: {:?}", proof);

        //# Verifier checks if proof checks out
        verifier_algo(
            proof,
            n,
            setup_output.p_i_poly,
            setup_output.verifier_preprocessing,
            setup_output.perm_precomp.2,
        );
    }

    #[test]
    fn vitalik_example_old() {
        /*
        Old code that doesnt use the Circuit struct. Keeping it around for myself
        because my python implementation is equivalent

        */
        // We only care about detecting repeating values in the equations
        let a = ["x", "var1", "var2", "1", "1", "var3", "empty1", "empty2"];
        let b = ["x", "x", "x", "5", "35", "5", "empty3", "empty4"];
        let c = ["var1", "var2", "var3", "5", "35", "35", "empty5", "empty6"];

        let mut wires = a.to_vec();
        wires.append(b.to_vec().as_mut());
        wires.append(c.to_vec().as_mut());

        // Gates
        let add = vec![1, 1, 0, -1, 0];
        let mul = vec![0, 0, 1, -1, 0];
        let const5 = vec![0, 1, 0, 0, -5];
        let public_input = vec![0, 1, 0, 0, 0];
        let empty = vec![0, 0, 0, 0, 0];

        let gates_matrix = vec![
            mul.clone(),
            mul,
            add.clone(),
            const5,
            public_input,
            add,
            empty.clone(),
            empty,
        ];

        let permutation = permute_indices(wires);

        // To enable a public input 35 we need to specify the position
        // of the gate in L and the value of the public input in p_i
        let pub_gate_position = vec![4 as usize];
        let pub_input_value = vec![35];
        let n = gates_matrix.len();

        let gates_matrix = transpose(gates_matrix);

        // To get the witness, the prover applies his private input x=3 to the
        //circuit and writes down the value of every wire.
        let witness = vec![
            3, 9, 27, 1, 1, 30, 0, 0, 3, 3, 3, 5, 35, 5, 0, 0, 9, 27, 30, 5, 35, 35, 0, 0,
        ];
        let witness: Vec<Fr> = (0..witness.len()).map(|f| Fr::from(witness[f])).collect();

        // We start with a setup that computes the trusted setup and does some
        // precomputation
        let setup_output = setup_algo(
            gates_matrix,
            permutation,
            pub_gate_position,
            pub_input_value,
        );
        println!("Setup Complete. Output: {:?}", setup_output);

        // # The prover calculates the proof
        let proof = prover_algo(witness, &setup_output.clone());
        println!("Computed Proof: {:?}", proof);

        //# Verifier checks if proof checks out
        verifier_algo(
            proof,
            n,
            setup_output.p_i_poly,
            setup_output.verifier_preprocessing,
            setup_output.perm_precomp.2,
        );
    }
}
