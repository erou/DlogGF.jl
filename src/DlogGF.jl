"""
# DlogGF

A library containing algorithms for computing discrete logarithm in finite
field.

# References

1. R. Barbulescu, P. Gaudry, A. Joux and E. Thomé : A quasi-polynomial algorithm
  for discrete logarithm in finite fields of small characteristic.
2. Stephen C. Pohlig and Martin E. Hellman : An Improved Algorithm for Computing
  Logarithms over GF(p) and Its Cryptographic Signifiance, IEEE transactions on
  information theory, vol. it-24, no. 1, January 1978.
"""
module DlogGF

using Nemo

# Iterator over medium subfields (of type F_q²)
# The elements are iterated in the order 0, 1, ..., q-1, x, 1 + x, 2 + x,
# ..., (q-1) + (q-1)x, where x is the generator of F_q²

function Base.start(::Nemo.FqNmodFiniteField)
    return (0,0)
end

function Base.next(F::Nemo.FqNmodFiniteField, state::Tuple{Int, Int})
    q = F.p - 1
    if state[1] < q
        nex = (state[1] + 1, state[2])
    else
        nex = (0, state[2] + 1)
    end
    return (state[1]+state[2]*gen(F), nex)
end

function Base.done(F::Nemo.FqNmodFiniteField, state::Tuple{Int, Int})
    return state[2] == F.p
end

function Base.eltype(::Type{Nemo.FqNmodFiniteField})
    return Nemo.fq_nmod
end

function Base.length(F::Nemo.FqNmodFiniteField)
    return BigInt((F.p))^(F.mod_length - 1)
end

# Random suite over medium subfields (of type F_q²)
# That is all we need as we use it only to find h0 and h1

export randomElem
"""
    randomElem(ring::Nemo.Ring)

Return an random element in `ring`.
"""
function randomElem(ring::Nemo.Ring)
    x = gen(ring)
    c::Int = characteristic(ring) - 1
    return ring(rand(0:c)) + rand(0:c)*x
end

export randomList
"""
    randomList(ring::Nemo.Ring, len::Integer)

Return an `Array` of length `len` with random elements in `ring`.
"""
function randomList(ring::Nemo.Ring, len::Integer)
    A = Array(ring, len)
    for i in 1:len
        A[i] = randomElem(ring)
    end
    return A
end
    
export randomPolynomial
"""
    randomPolynomial(polyRing::Nemo.PolyRing, degree::Integer)

Return a random polynomial of degree `degree` in the ring `polyRing`.
"""
function randomPolynomial(polyRing::Nemo.PolyRing, degree::Integer)
    L = randomList(base_ring(polyRing), degree + 1)
    while L[degree + 1] == 0
        L = randomList(base_ring(polyRing), degree + 1)
    end
    return polyRing(L)
end

# Composite types

## SmsrField : used to create and gather all the informations needed to
##             perform the algorithm of Barbulescu et al.

export SmsrField
"""
    SmsrField

Sparse medium subfield representation of a field of the form ``K = \\mathbb
F_{q^{2k}}``.

# Cautions

* this should never be called as a constructor, due to the number of
  the fields. To create such a representation, see `smsrField`

# Fields

* `characteristic::Integer` : characteristic of the field ``q``
* `extensionDegree::Integer` : degree of the extension ``K/\\mathbb F_{q^2}``
* `cardinality::Integer` : cardinality of the field
* `h0::PolyElem` and `h1::PolyElem` are polynomials such that ``h1*X^q-h0`` has
  a degree ``k`` irreducible factor, named `definingPolynomial::PolyElem`
* `mediumSubField::Nemo.Ring : the field ``\\mathbb F_{q^2}``
* `gen::RingElem` is a generator of the group of the inversible elements of the
  field, it is actually taken at random *without* checking that it is indeed a
  generator by default
* `bigField::Nemo.Ring` : the field ``K = \\mathbb F_{q^{2k}}``
"""
immutable SmsrField
    characteristic::Integer
    extensionDegree::Integer
    cardinality::Integer
    h0::PolyElem
    h1::PolyElem
    definingPolynomial::PolyElem
    mediumSubField::Nemo.Ring
    gen::RingElem
    bigField::Nemo.Ring
end

export smsrField
"""
    smsrField(q::Integer, k::Integer, deg::Integer = 1, check::Bool = false)

Construct a field ``K = \\mathbb F_{q^{2k}}`` of type `SmsrField`.

The polynomials `h0` and `h1` will be of degree `deg`. See `SmsrField` for more
informations. If `check` is `true`, the generator will be checked. *Note* that
this will call `factor(K.cardinality-1)`, so it should not be performed with
finite fields of large cardinality.
"""
function smsrField(q::Integer, k::Integer, deg::Integer = 1, check::Bool = false)

    # We compute the cardinal of the field, the medium subfield and its
    # polynomial ring
    card = BigInt(q)^(2*k)
    mediumSubField, x = FiniteField(q, 2, "x")
    polyRing, T = PolynomialRing(mediumSubField, "T")

    # We seek (at random) polynomials h0 and h1 such that h1×X^q - h0 has an
    # irreducible factor of degree `k`, hence defining the big field over the
    # medium, we also impose that h1 is monic since it does not change the
    # factors
    boo = true
    h0, h1, definingPolynomial = polyRing(), polyRing(), polyRing()

    while boo
        h0 = randomPolynomial(polyRing, deg)
        h1 = randomPolynomial(polyRing, deg - 1) + T^deg
        fact = factor(h1*T^q - h0)
        for f in fact
            if degree(f[1]) == k
                definingPolynomial = f[1]
                boo = false
                break
            end
        end
    end

    # We then create the big field as a residue ring and compute a generator
    # of the group of the inversible elements of the big field (at random)
    bigField = ResidueRing(polyRing, definingPolynomial)
    gen = bigField(randomPolynomial(polyRing, k))

    # We optionally check that `gen` is indeed a generator
    if check
        while !isGenerator(gen, card)
            gen = bigField(randomPolynomial(polyRing, k))
        end
    end

    # And we call the constructor of the type `SmsrField`
    return SmsrField(q, k, card, h0, h1, definingPolynomial,
                     mediumSubField, gen, bigField)
end

export isGenerator
"""
    isGenerator(gen::RingElem, card::Integer)

Return `true` if gen is a generator of the group of the inversible elements of
the finite field of cardinal `card`. Return `false` otherwise.
"""
function isGenerator(gen::RingElem, card::Integer)
    # We compute the factorisation of card-1 
    fact = factor(card-1)
    d::Integer = 0

    # If gen is not a generator, there is a integer d < card-1 of that form for
    # which we have gen^d = 1
    for x in fact
        d = (card-1)//x[1]
        if gen^d == 1
            return false
        end
    end
    return true
end

## FactorsList : this type is used to represent a factorisation of the type 
##               P = (unit) × P_1^(e_1) × ... × P_n^(e_n), we use it because
##               the algorithm of Barbulescu et al. consist of finding such
##               a relation with P_i's of degree 1.

export FactorsList
"""
    FactorsList

Represent a factorisation.

# Fields

* `factors::Array{Nemo.fq_nmod_poly, 1}` : the polynomials of the factorisation
* `coefs::Array{Int, 1}` : the exponents of these polynomials
* `unit::Nemo.fq_nmod` : the unit part of the factorisation
"""
type FactorsList
    factors::Array{Nemo.fq_nmod_poly, 1}
    coefs::Array{Int, 1}
    unit::Nemo.fq_nmod
end

export factorsList
"""
    factorsList(P::Nemo.fq_nmod_poly)

Construct an element of type `FactorsList`.
"""
function factorsList(P::Nemo.fq_nmod_poly)
    return FactorsList([P], [1], base_ring(parent(P))(1))
end

function Base.push!(L::FactorsList, P::Nemo.fq_nmod_poly, coef::Int)

    # We try to find if `P` is already in `L`
    i = findfirst(L.factors, P)

    # If it is, we just change the associated coefficient
    if i != 0
        L.coefs[i] += coef
    # Otherwise, we add `P` and its coefficient `coef` to `L`
    else
        push!(L.factors, P)
        push!(L.coefs, coef)
    end
end

function Base.deleteat!(L::FactorsList, i::Int)
    deleteat!(L.factors, i)
    deleteat!(L.coefs, i)
end

# Some functions

export pglUnperfect
"""
    pglUnperfect(x::RingElem)

Construct an `Array` contaning matrices.

This matrices are representants of equivalence classes. There should at be at
most one matrix per class, but it is not the case here, that is why it is
called *unperfect*.
"""
function pglUnperfect(x::RingElem)

    # We create the space of the 2×2 matrices of coefficients in F_q²
    F = parent(x)
    MS = MatrixSpace(F, 2, 2)
    M = MS()

    # Then we fill an `Array` of matrices of the form
    # [1        b + ax]
    # [b + cx   a + cx]
    # and we return the result
    M[1, 1] = F(1)
    A = Array{typeof(M), 1}()
    n::Int = characteristic(F) - 1
    for a in 1:n, b in 0:n, c in 1:n
        M[1, 2] = b + a*x
        M[2, 1] = b + c*x
        M[2, 2] = a + c*x 
        push!(A, deepcopy(M))
    end
    return A
end

export homogene
"""
    homogene{T <: PolyElem}(P::T, h0::T, h1::T)

Homogenize ``π`` with `h0` and `h1` seen as indeterminates. The polynomial
``π`` is the polynomial `P` with coefficients powered by ``q``, the
characteristic in the context.
"""
function homogene{T <: PolyElem}(P::T, h0::T, h1::T)

    # We compute the characteristic of the context and the degree of `P`
    R = parent(P)
    q = characteristic(base_ring(R))
    H = R()
    d = degree(P)

    # Then we compute the homogenized polymonial and return it
    for i in 0:d
        H += (coeff(P, i)^q)*(h0^i)*(h1^(d-i))
    end
    return H
end

export makeEquation
"""
    makeEquation{T <: RingElem, Y <: PolyElem}(m::Nemo.GenMat{T},
                                               P::Y, h0::Y, h1::Y)

Compute the denomimator of the left-side of the equation generated by `m`.

See reference **[1]** in the documentation of the module for more informations.
"""
function makeEquation{T <: RingElem, Y <: PolyElem}(m::Nemo.GenMat{T},
                                                    P::Y, h0::Y, h1::Y)

    # We compute some constants depending on the context
    a, b, c, d = m[1, 1], m[1, 2], m[2, 1], m[2, 2]
    D = degree(P)
    q = characteristic(base_ring(parent(P)))

    # We compute the homogenized version of `P`
    H = homogene(P, h0, h1)

    # And we compute the denominator of the left side of the equation defined
    # in the paper of Barbulescu et al.
    return ((a^q)*H + (b^q)*h1^D)*(c*P+d) - (a*P+b)*((c^q)*H + (d^q)*h1^D)
end

export isSmooth
"""
    isSmooth(P::PolyElem, D::Int)

Test if the polynomial `P` is `D`-smooth.

A polynomial is said to be *n-smooth* if all its irreducible factors have
degree ≤ D.
"""
function isSmooth(P::PolyElem, D::Int)

    # We iterate through the factors of `P` and return `false` if one of them
    # is not `D`-smooth
    for f in factor(P)
        if degree(f[1]) > D
            return false
        end
    end
    return true
end

export dlogSmallField
"""
    dlogSmallField{T}(carac::Integer, degExt::Integer, gen::T, elem::T)

Compute the discrete logarithm of `elem` in the base `gen`.

This strategy works if `elem` is in fact in the medium subfield.
"""
function dlogSmallField{T}(carac::Integer, degExt::Integer, gen::T, elem::T)

    # We compute the norm of `gen`
    q = BigInt(carac)^2
    c = div(q^degExt-1, q-1)
    n = gen^c

    # Then we find the logarithm of `elem` is the base `n`
    i = 1
    while n^i != elem
        i += 1
    end

    # Amd we translate the result in base `gen`
    return i*c
end


# Pohlig Hellman suite

export pohligHellmanPrime
"""
    pohligHellmanPrime{T <: RingElem}(card::Integer, prime::Integer,
                                      gen::T, elem::T)
                                      
Compute the discrete logarithm of `elem` mod `prime^n` in base `gen`.

Where `prime` si a prime number dividing `card` and `n` is the largest integer
such that `prime^n` divides `card`. See reference **[2]** for more information about
this algorithm, the references can be found in the documentation of the module.
"""
function pohligHellmanPrime{T <: RingElem}(card::Integer, prime::Integer,
                                           gen::T, elem::T)

    # We compute a table of the `prime`-th roots of unit
    d::Integer = (card-1)/prime
    g = gen^d
    arr = Array(T, prime)
    for i in 0:(prime-1)
        arr[i + 1] = g^i
    end

    res = 0
    tmp = elem
    inverse = inv(gen)

    # We compute the largest integer `n` such that `prime^n` divides `card`
    n = 1
    while divisible(fmpz(card-1), prime^(n+1))
        n += 1
    end

    # We compute the coefficients `b_i` such that x = Σ b_i × prime^i, meaning
    # that we compute `x` in base `prime`
    d = card-1
    for i in 0:(n-1)
        d = d/prime
        b = findfirst(arr, tmp^d) - 1
        res += b*prime^i
        tmp = tmp*inverse^(b*prime^i)
    end

    return (fmpz(res), fmpz(prime)^n)
end

export pohligHellman
"""
    pohligHellman{T}(card::Integer, gen::T, elem::T)

Compute the discrete logarithm of `elem` in the base `gen`, modulo the small
prime factors of card - 1.
"""
function pohligHellman{T}(card::Integer, gen::T, elem::T)

    # We find the small (meaning, less that log(card)) prime factors of card
    l::Int = ceil(log2(card))
    A = Array{Int, 1}()
    for i in primes(l)
        if card%i == 1
            push!(A, i)
        end
    end

    # We set some variables
    res::Nemo.fmpz = 0
    n::Nemo.fmpz = 0

    # And we compute the discrete logarithm of `elem` in the base `gen`, for
    # each prime factor, using pohligHellmanPrime, then we compute our final
    # result using chinese remindering theorem
    if length(A) > 1
        a = pohligHellmanPrime(card, A[1], gen, elem)
        b = pohligHellmanPrime(card, A[2], gen, elem)
        res, n = crt(a[1], a[2], b[1], b[2]), a[2]*b[2]
        for i in 1:(length(A)-2)
            a = pohligHellmanPrime(card, A[i+2], gen, elem)
            res, n = crt(res, n, a[1], a[2]), n*a[2]
        end
        return res, n
    else 
        return pohligHellmanPrime(card, 2, gen, elem)
    end
end

# BGJT algorithm

# End of module
end
