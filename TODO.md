# Improvements

## To deal or not to deal with the constants

In the code, particular effort has been made to follow precisely what is
happening with the constants, i.e. the elements of F_q². This is probably
useless and costly. Instead, we could just make all our computations and deal
with the constant just at the end, when needed. In particular, in the `dlog` 
function, we have a whole column filled with the discrete logarithm of the 
constants that will vanish during the computation modulo the big primes.

## Sparse linear algebra

We presently use Gaussian elimination to solve our linear systems, but the
matrices involved are sparse, typically, the density is around 1/q. Using
algorithms designed for sparse systems would probably speed up the process.
