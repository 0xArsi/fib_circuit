# fib_circuit

## This is a Rust implementation of a circuit which verifies knowledge of $x, y, z, k$ such that, given $f(0) = x$ and $f(1) = y$, $f(k) = z$ (without exposing $k$, which would reveal the whole witness). Implementation is done with Halo2 (plonk(ish) arithmetization).
