/// Takes an vector "wires" of string of size n.
/// Returns a vector of position indices 0,1,2...,n
/// where the positions are swapped if the value of "wires repeats"
/// E.g. if wires = [a,b,b,c] then function creates [0,1,2,3], swaps positions
/// and returns [0,2,1,3]
pub fn permute_indices(wires: Vec<&str>) -> Vec<usize> {
    let size = wires.len();
    let mut permutation: Vec<usize> = (0..size).into_iter().collect();
    for i in 0..size {
        for j in i + 1..size {
            if wires[i] == wires[j] {
                let perm_i = permutation[i];
                permutation[i] = permutation[j];
                permutation[j] = perm_i;
                break;
            }
        }
    }
    permutation
}

pub fn transpose<T>(v: Vec<Vec<T>>) -> Vec<Vec<T>>
where
    T: Clone,
{
    assert!(!v.is_empty());
    (0..v[0].len())
        .map(|i| v.iter().map(|inner| inner[i].clone()).collect::<Vec<T>>())
        .collect()
}
