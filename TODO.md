# Improvements

## BGJT

### To deal or not to deal with the constants

In the code, particular effort has been made to follow precisely what is
happening with the constants, i.e. the elements of F_q². This is probably
useless and costly. Instead, we could just make all our computations and deal
with the constant just at the end, when needed. In particular, in the `dlog` 
function, we have a whole column filled with the discrete logarithm of the 
constants that will vanish during the computation modulo the big primes.

### Sparse linear algebra

We presently use Gaussian elimination to solve our linear systems, but the
matrices involved are sparse, typically, the density is around 1/q. Using
algorithms designed for sparse systems would probably speed up the process.

### Fq vs Fp

Make the implementation available not only for prime fields, but for any kind
of field like done with the powers-of-2 algorithm

## powers-of-2

### Root finding

Make it better: X^{q^m} mod Δ is really expensive right now, but the
algorithm does not take into account the fact that the exponent is a power of q

### Factor base

Finish to implement the Joux-Pierrot precomputation algorithm for the factor
base.
