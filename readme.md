# PLONK with Plookup

This repository contains an educational implementation of the PLONK proof system with Plookup extension, based on the [PLONKUP paper](https://eprint.iacr.org/2020/315.pdf).

**Warning**: This implementation is for educational purposes only and should not be used in any environment. It has not been tested or optimized, and contains vulnerabilities.

## Overview

This implementation aims to help me better understand the inner workings of PLONK with Plookup. It was developed as a personal project and should be treated as such.

Some tests are provided in the `lib.rs` file, which can serve as examples of how to use the implementation.

## Todo List

1. Check if I am using the correct function to switch from evaluation to coefficient representations.
2. Check if typechecks in `verifier_algo` are really not needed.
3. Breake down the `prover_algo` function into smaller, more focused functions.
4. Use more descriptive variable names.
5. Replace `for` loops with iterators.
6. Use type aliases for complex types.

## Contributing

As this project is primarily for personal educational purposes, contributions are not actively sought. However, if you find any issues or have suggestions for improvements, feel free to open an issue on the GitHub repository.
