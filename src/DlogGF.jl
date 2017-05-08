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
3. Jincheng Zhuang and Qi Cheng : On Generating Coset Representatives of
  PGL_2(F-q) in PGL_2(F_q²)
"""
module DlogGF

using Nemo, Primes

# C functions

function rrefMod!(M::Nemo.fmpz_mat, n::Nemo.fmpz)
#    perm::Array{Int, 1} = collect(1:rows(M))
    perm = C_NULL
    rank = ccall((:fmpz_mat_rref_mod, :libflint), Cint, (Ptr{Int}, Ptr{fmpz_mat},
                                                  Ptr{fmpz}), perm, &M, &n)
    return M, rank, perm
end

function rrefMod!(M::Nemo.fmpz_mat, d::Integer)
    n = Nemo.fmpz(d) 
#    perm::Array{Int, 1} = collect(1:rows(M))
    perm = C_NULL
    rank = ccall((:fmpz_mat_rref_mod, :libflint), Cint, (Ptr{Int}, Ptr{fmpz_mat},
                                                  Ptr{fmpz}), perm, &M, &n)
    return M, rank, perm
end


function rrefMod(M::Nemo.fmpz_mat, n::Nemo.fmpz)
    N = deepcopy(M)
    M, rank, perm = rrefMod!(N, n)
    return N, rank, perm
end

function rrefMod(M::Nemo.fmpz_mat, n::Integer)
    N = deepcopy(M)
    M, rank, perm = rrefMod!(N, n)
    return N, rank, perm
end

# Missing functions in Nemo/Julia

Base.one(x::Nemo.GenRes{Nemo.fq_nmod_poly}) = parent(x)

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
    gen = bigField(randomPolynomial(polyRing, 0) + T)

    # We optionally check that `gen` is indeed a generator
    if check
        while !isGenerator(gen, card)
            gen = bigField(randomPolynomial(polyRing, 0) + T)
        end
    else
        while !miniCheck(gen, card)
            gen = bigField(randomPolynomial(polyRing, 0) + T)
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

export miniCheck
"""
    miniCheck(gen::RingElem, card::Integer)

Check that `gen` is not trivially not generator.

By trivially not generator, we mean that ``gen^(k/d) = 1``, for ``k`` the cardinal of
the group of the invertible elements of the field, and ``d`` a small divisor of this
cardinal. 

Passing this test does *not* guarantee that `gen` is a generator.
"""
function miniCheck(gen::RingElem, card::Integer)

    # We find the small primes dividing our cardinal
    d::Integer = 0
    l::Int = ceil(Integer, log2(card))
    A = Array{Int, 1}()
    for i in primes(l)
        if card%i == 1
            push!(A, i)
        end
    end

    # And we test the generator on those primes
    for x in A
        d = (card-1)//x
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
    coefs::Array{Nemo.fmpz, 1}
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

function Base.push!(L::FactorsList, P::Nemo.fq_nmod_poly, coef::Nemo.fmpz)

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

function Base.deleteat!(L::FactorsList, i::Integer)
    deleteat!(L.factors, i)
    deleteat!(L.coefs, i)
end

function Base.getindex(L::FactorsList, i::Integer)
    return (L.factors[i],L.coefs[i])
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
        if (b+a*x)*(b+c*x) != a + c*x
            push!(A, deepcopy(M))
        end
    end
    return A
end

export pglCosets
"""
    pglCosets(g::RingElem)

Compute the coset representatives of PGL(F_q²)/PGL(F_q).

This algorithm is due to Jincheng Zhuang and Qi Cheng **[3]**, see References in
the module documentation for more details.
"""
function pglCosets(g::RingElem)
    F = parent(g)
    q::Int = characteristic(F)
    R = zeros(F, 5, q)
    MS = MatrixSpace(F, 2, 2)
    M = MS()
    A = Array{typeof(M), 1}()

    # We compute a table with containing at most q+1-th root
    # for each element in F_q, these roots are taken in F_q²
    for y in F
        t = y^(q+1)
        i = coeff(t, 0) + q*coeff(t, 1) + 1

        for j in 1:5
            if R[j, i] == y
                break
            elseif R[j, i] == 0
                R[j, i] = y
                break
            end
        end
    end

    # STEP 1: We add cosets representatives of the form
    # [1, x]
    # [y, 1]
    # with x, y in F_q²\F_q and xy ≠ 1 and where x and y were chosen in a way
    # that we have to do only O(q³) steps instead of O(q⁴).
    M[1, 1], M[2, 2] = F(1), F(1)
    for v in 1:(q-1)
        for w in F
            ι = inv(F(v))
            t = (ι*w^q)^(q+1)-ι
            i = coeff(t, 0) + q*coeff(t, 1) + 1
            if i != 1
                for j in 1:5
                    r = R[j, i]
                    if r != 0
                        y = ι*w^q + r
                        x = -v*y + w + w^q
                        if x*y != 1 && coeff(x, 1) != 0 && coeff(y, 1) != 0
                            M[1, 2], M[2, 1] = x, y
                            push!(A, deepcopy(M))
                            break
                        end
                    else
                        break
                    end
                end
            else
                y = ι*w^q
                x = -v*y + w + w^q
                if x*y != 1 && coeff(x, 1) != 0 && coeff(y, 1) != 0
                    M[1, 2], M[2, 1] = x, y
                    push!(A, deepcopy(M))
                end
            end
        end
    end

    # STEP 2: We add cosets representatives of the form
    # [1,  a]
    # [g, bg]
    # with a, b in F_q*, g in F_q²\F_q, and a ≠ b
    M[2, 1] = g
    for a in 1:(q-1)
        for b in 1:(q-1)
            if a != b
                M[1, 2] = F(a)
                M[2, 2] = b*g
                push!(A, deepcopy(M))
            end
        end
    end

    # STEP 3: We add cosets representatives of the form
    # [0,  1]
    # [g, ag]
    # with a in F_q
    M[1, 1] = F(0)
    M[1, 2] = F(1)
    for a in 0:(q-1)
        M[2, 2] = a*g
        push!(A, deepcopy(M))
    end
 
    # STEP 4: We add cosets representatives of the form
    # [     0,  1]
    # [1 + ag, bg]
    # with a, b in F_q
    for a in 0:(q-1)
        for b in 0:(q-1)
            M[2, 1] = 1 + a*g
            M[2, 2] = b*g
            push!(A, deepcopy(M))
        end
    end
                
    # STEP 5: We add cosets representatives of the form
    # [  1, 0]
    # [ ag, g]
    # with a in F_q
    M[1, 1] = F(1)
    M[1, 2] = F(0)
    M[2, 2] = g
    for a in 0:(q-1)
        M[2, 1] = a*g
        push!(A, deepcopy(M))
    end

    # STEP 6: We add cosets representatives of the form
    # [  1,      0]
    # [ ag, 1 + bg]
    # with a, b in F_q
    for a in 0:(q-1)
        for b in 0:(q-1)
            M[2, 1] = a*g
            M[2, 2] = 1 + b*g
            push!(A, deepcopy(M))
        end
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

Compute the discrete logarithm of `elem` in the basis `gen`.

This strategy works if `elem` is in fact in the medium subfield.
"""
function dlogSmallField{T}(carac::Integer, degExt::Integer, gen::T, elem::T)

    # We compute the norm of `gen`
    q = BigInt(carac)^2
    c = div(q^degExt-1, q-1)
    n = gen^c

    # Then we find the logarithm of `elem` is the basis `n`
    i = 1
    while n^i != elem
        i += 1
    end

    # Amd we translate the result in basis `gen`
    return (i*c)%(q^degExt-1)
end

export subMatrix
"""
    subMatrix(M::MatElem, nrow::Integer, ncol::Integer)

Return the submatrix consisting of the first `nrow` rows and `ncol` colums of
`M`.
"""
function subMatrix(M::MatElem, nrow::Integer, ncol::Integer)

    # We create the matrix subspace
    S = MatrixSpace(parent(M[1,1]), nrow, ncol)

    # We create a new matrix
    sub = S()
    
    # And we copy the entries of the given matrix
    for j in 1:ncol
        for i in 1:nrow
            sub[i, j] = M[i, j]
        end
    end
    return sub
end

export pivots
"""
    pivots(M::MatElem)

Find `r` pivots in the row reduced echelon form matrix `M`.
"""
function pivots(M::MatElem, r::Int = 0)

    # There is as many pivots as the rank of 
    if r == 0
        r = rank(M)
    end

    # We set an array with the coordinates of the pivots
    piv = Array(Int, r)
    c = 1

    # And we find these coordinates
    for i in 1:r
        while M[i, c] == 0
            c += 1
        end
        piv[i] = c
    end
    return piv
end

# Pohlig Hellman suite

export pohligHellmanPrime
"""
    pohligHellmanPrime{T <: RingElem}(card::Integer, prime::Integer,
                                      gen::T, elem::T)
                                      
Compute the discrete logarithm of `elem` mod `prime^n` in basis `gen`.

Where `prime` si a prime number dividing `card` and `n` is the largest integer
such that `prime^n` divides `card`. See reference **[2]** for more information about
this algorithm, the references can be found in the documentation of the module.
"""
function pohligHellmanPrime{T <: RingElem}(card::Integer, prime::Integer,
                                           gen::T, elem::T)

    # We compute a table of the `prime`-th roots of unit
    d::Integer = div(card-1, prime)
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
    # that we compute `x` in basis `prime`
    d = card-1
    for i in 0:(n-1)
        d = div(d, prime)
        b = findfirst(arr, tmp^d) - 1
        res += b*prime^i
        tmp = tmp*inverse^(b*prime^i)
    end

    return (fmpz(res), fmpz(prime)^n)
end

export pohligHellman
"""
    pohligHellman{T}(card::Integer, gen::T, elem::T)

Compute the discrete logarithm of `elem` in the basis `gen`, modulo the small
prime factors of card - 1.
"""
function pohligHellman{T}(card::Integer, gen::T, elem::T)

    # We find the small (meaning, less that log(card)) prime factors of card
    q::BigInt = characteristic(base_ring(base_ring(parent(gen))))
    l::Int = ceil(Integer, (q^2-1)/2)
    l = max(l, ceil(Integer, log2(card)))
    A = Array{Int, 1}()
    for i in primes(l)
        if card%i == 1
            push!(A, i)
        end
    end

    # We set some variables to fmpz to use `crt`
    res::Nemo.fmpz = 0
    n::Nemo.fmpz = 0

    # And we compute the discrete logarithm of `elem` in the basis `gen`, for
    # each prime factor, using pohligHellmanPrime, then we compute our final
    # result using Chinese remindering theorem
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

pohligHellman{T}(card::Nemo.fmpz, gen::T, elem::T) = pohligHellman(BigInt(card),
                                                                   gen, elem)

# BGJT algorithm

export fillMatrixBGJT!
"""
    fillMatrixBGJT!(M::MatElem, j::Integer, m::MatElem, F::Nemo.Field)

Fill the `j`-th column of the matrix `M`, using the action of `m` on ``P_1(F)``
and returns the unit generated in the process.

See reference **[1]** for more informations, the references are listed in the
documentation of the module.
"""
function fillMatrixBGJT!(M::MatElem, j::Integer, m::MatElem, F::Nemo.Field)

    # We set some constants to the coefficients of `m`
    a, b, c, d = m[1, 1], m[1, 2], m[2, 1], m[2, 2]

    # We compute the one of our ring
    Z = parent(M[1, 1])
    u = Z(1)

    # We first set our unit to 1 and our index to 0
    i = 0
    unit = F(1)

    # We iterate over the projective line P_1(F), with elements of the form
    # (y, 1) where y is in F
    for y in F
        # In fact the columns of `M` can be indexed by elements of P_1(F)
        i += 1

        # We compute m⋅(y, 1) = (α, β)
        α = a*y + b
        β = c*y + d
        # If (α, β) is in P_1(GF(q)), meaning if δ = α/β is in GF(q) or (α, β) is
        # the infinite element, we set M[i, j] to 1
        if β != 0
            δ = divexact(α, β)
            if δ.length < 2
                M[i, j] = u
                
                # We compute the constant (λ in [2]) needed for the two 
                # sides of the equation to match
                tmp = -c*δ+a
                if tmp != 0
                    unit *= tmp
                else
                    unit *= -d*δ + b
                end
            end

        # Else we are in the case where m⋅(y, 1) = (., 0) = infinite
        # element = (-1, 0), so we are in P_1(GF(q))
        else
            M[i, j] = u
            if c != 0
                unit *= c
            else
                unit *= d
            end
        end
    end

    # We do the same for the last element of P_1(F)
    # the infinite element (-1, 0)
    i += 1
    if c != 0
        δ = divexact(a, c)
        if δ.length < 2
            M[i, j] = u
        # In this case tmp = -c*δ + a = -c*a/c + a = 0, so no need to test
        unit *= -d*δ + b
        end
    else
        M[i, j] = u
        unit *= d
    end
    return unit
end

export descentBGJT
"""
    descentBGJT{T <: PolyElem}(L::FactorsList, i0::Integer, F::Nemo.Field,
                               h0::T, h1::T, card::Nemo.fmpz)

The descent phase of the BGJT algorithm.
"""
function descentBGJT{T <: PolyElem}(L::FactorsList, i0::Integer, F::Nemo.Field,
                                    h0::T, h1::T, card::Nemo.fmpz)

    # We set some constants, arrays, matrices
    elem, coef = L[i0]
    deg = degree(elem)
    smoothBound = ceil(Integer, deg/2)
    numerators = Array{fq_nmod_poly, 1}()
    charac::Int = characteristic(F)
    units = Array{fq_nmod, 1}()
    x = gen(F)
    j = 1

    S = MatrixSpace(ZZ, charac^2+1,charac^3+charac+1)
    M = zero(S)
#   Pq = pglUnperfect(x)
    Pq = pglCosets(x)

    # We iterate over Pq = PGL(P_1(F_q²))/PGL(P_1(F_q)) to create new equations 
    # involving P and its translations P - μ with μ in F_q², we keep only the 
    # one with a smooth left side and we fill a matrix to remember which
    # translations were used
    for m in Pq
        N = makeEquation(m, elem, h0, h1)

        if isSmooth(N, smoothBound)
            unit = fillMatrixBGJT!(M, j, m, F)
            push!(units, unit)
            j += 1
            push!(numerators, N)
        end
    end

    # We set the last column to the vector (1, 0, ..., 0), which
    # represent the polynomial P
    M[1,j] = 1
    M = subMatrix(M, charac^2 + 1, j)

    # We compute the row echelon form of M, such that M/det is reduced
    M, det = rref(M)

    # We compute the inverse of `det` mod `card`
    det %= card
    if det <= 0
        det += card
    end
    g, s = gcdinv(det, card)

    # If it is not invertible, we return the problematic factor
    if g != 1
        println("The following number was a factor")
        return g
    end

    # We compute a solution
    sol = Nemo.fmpz[(s*M[i,j])%card for i in 1:(charac^2+1)]

    # We compute the coordinates of the pivots (because we have redundant
    # equations)
    piv = pivots(M, charac^2)

   # We add the new polynomials and their coefficients in our list
    for j in 1:charac^2
        fact = factor(numerators[piv[j]])
        for f in fact
            push!(L, f[1], f[2]*sol[j]*coef)
        end
        push!(L, h1, -deg*sol[j]*coef)
        leadcoef = coeff(numerators[piv[j]], degree(numerators[piv[j]]))
        L.unit *= (inv(units[piv[j]])*leadcoef)^(sol[j]*coef)
    end
    deleteat!(L, i0)
end

function descentBGJT{T <: PolyElem}(L::FactorsList, i0::Integer, F::Nemo.Field,
                                    h0::T, h1::T, card::Integer)
    return descentBGJT(L, i0, F, h0, h1, Nemo.fmpz(card))
end

export linearDlog
"""
    linearDlog{T <: PolyElem}(basis:: Nemo.Ring, degExt::Integer,
                              F::Nemo.Field, h0::T, h1::T, card::Nemo.fmpz,
                              Q::Nemo.Ring)


Compute the discrete logarithm of the elements of type ``X + μ`` and of `h1`.

This algorithm works only if the provided basis is *linear*.
"""
function linearDlog{T <: PolyElem}(basis:: Nemo.RingElem, degExt::Integer,
                                   F::Nemo.Field, h0::T, h1::T, card::Nemo.fmpz,
                                   Q::Nemo.Ring)

    # We set some constants, arrays, matrices
    charac::Int = characteristic(F)
    x = gen(F)
    X = gen(parent(h0))
    j = 0
    n = 0
    ind = 0

    S = MatrixSpace(ZZ, charac^2+3,charac^3+charac+1)
    M = zero(S)
#    Pq = pglUnperfect(x)
    Pq = pglCosets(x)

    # We iterate over Pq = PGL(P_1(F_q²))/PGL(P_1(F_q)) to create new equations 
    # involving X and its translations X - μ with μ in F_q², we keep only the 
    # one with a smooth left side and we fill a matrix to remember which
    # translations were used. Contrary to the descent algorithm, we also keep
    # trace of the linear factors in the left side.
    for m in Pq
        N = makeEquation(m, X, h0, h1)

        if isSmooth(N, 1)
            j += 1
            unit = fillMatrixBGJT!(M, j, m, F)
            leadcoef = coeff(N, degree(N))
            fact = factor(N)
            for f in fact
                cst = -coeff(f[1], 0)
                index::Int = coeff(cst, 0) + coeff(cst, 1)*charac + 1
                M[index, j] -= f[2] 
            end
            M[charac^2+2, j] = 1
            M[charac^2+3, j] = dlogSmallField(charac, degExt, basis,
                                             Q(inv(unit)*leadcoef))
        end
    end

    M = subMatrix(M, charac^2 + 3, j)
    M = transpose(M)

    # We compute the logarithm of the linear elements and h1 
    # modulo the small factors using Pohling Hellman algorithm
    # We also look for the linear factor X-y that is the basis, this is a type
    # problem, we cannot do it directly; but the types could be better managed
    # in order not to do that
    dlogs = Array(Nemo.fmpz, charac^2+1)
    i = 0
    for y in F
        i += 1
        dlogs[i] = pohligHellman(card, basis, Q(X-y))[1]
        if basis == Q(X-y)
            ind = i
        end
    end

    i += 1
    dlogs[i], n = pohligHellman(card, basis, Q(h1))

    # We next look at the big factors of ``card-1``, we compute the result
    # modulo each factor and reconstruct the result using Chinese remaindering
    # theorem
    v = div(card-1, n)
    bigFactors = factor(v)

    # We compute the one-dimensionnal kernel, and we choose the vector with a 1
    # at index `ind`, because this is the index of our basis (we chose it linear
    # for that purpose)
    for p in bigFactors
        Mred = rrefMod(M, p[1])[1]
        ker = Nemo.fmpz[Mred[i, charac^2+2] for i in 1:charac^2]
        s = gcdinv(ker[ind], p[1])[2]
        for i in 1:charac^2
            dlogs[i] = crt(dlogs[i], n, ker[i]*s, p[1])
        end
        dlogs[charac^2+1] = crt(dlogs[charac^2+1], n, -s, p[1])
        n *= p[1]
    end

    # And we put the results in a dictionnary, to be more easy to use
    dico = Dict()
    i = 0
    for y in F
        i += 1
        dico[X-y] = dlogs[i]
    end
    dico[h1] = dlogs[i+1]

    return dico
end

function linearDlog{T <: PolyElem}(basis:: Nemo.RingElem, degExt::Integer,
                                   F::Nemo.Field, h0::T, h1::T, card::Integer,
                                   Q::Nemo.Ring)
    return linearDlog(basis, degExt, F, h0, h1, Nemo.fmpz(card), Q)
end

export dlogBGJT
"""
    dlogBGJT(P::Nemo.RingElem, K::SmsrField, dlogs::Dict{Any, Any})

Compute the discrete logarithm of `P` in the field `K`.

The field `K` must have a sparse medium subfield representation. All the
informations needed in the algorithm, like the basis, are in the object `K`.
This algorithm need the discrete logarithms of the linear factors, they can be
computed using **linearDlog**.
"""
function dlogBGJT(P::Nemo.fq_nmod_poly, K::SmsrField, dlogs::Dict{Any, Any})

    # We first compute the discrete logarithm of `P` modulo 
    # the small factors with Pohlig Hellman algorithm
    s, n = pohligHellman(K.cardinality, K.gen, K.bigField(P))

    # Then we work with the large factors, using the descent algorithm to
    # express log P in function of logarithms of polynomials with smaller degree
    # and we stop once we have only linear polynomials, which logarithms are
    # known
    N = div(Nemo.fmpz(K.cardinality-1), n)
    i = 1
    L = factorsList(P)

    while i < length(L.factors) + 1
        while degree(L.factors[i]) > 1
            descentBGJT(L, i, K.mediumSubField, K.h0, K.h1, N)
        end
        i += 1
    end

    # Once we have only linear polynomials, we compute the linear sum
    # log P = Σ e_i × log P_i (mod N) where the e_is where calculated during the
    # descent, and where the log P_is are given
    S = sum([L.coefs[j]*dlogs[L.factors[j]] for j in 1:length(L.factors)])
    S += dlogSmallField(K.characteristic, K.extensionDegree, K.gen,
                              K.bigField(L.unit))

    # Then we reconstruct the result using Chinese remindering theorem
    return crt(s, n, S, N)
end

# Internal debugging functions, not documented

function checkeq(P, M, m, K)
    i = 1
    Q = K.bigField
    F = K.mediumSubField
    tmp2=Q(1)
    for y in F
        if M[i, 1] == 1
            tmp2 *= P-y
        end
        i += 1
    end

    tmp1 = makeEquation(m, P, K.h0, K.h1)*inv(Q(K.h1))^degree(P)

    
    return tmp1,tmp2
end

function checklog(L, Q)
    l = length(L.factors)
    res = Q(1)
    for i in 1:l
        if L.coefs[i] < 0
            exp = -BigInt(L.coefs[i])
            tmp = inv(Q(L.factors[i]))
            res *= tmp^(exp)
        elseif L.coefs[i] > 0
            exp = BigInt(L.coefs[i])
            res *= Q(L.factors[i])^exp
        end
    end
    return res*L.unit
end

function checknum(num, M, P, h1, Q)
    res1 = Q(1)
    res2 = Q(1)
    N, det = rref(M)
    m, j = size(M)
    sol = fmpz[N[i, j] for i in 1:m]
    d = degree(P)

    piv = pivots(N, m-1)
    for i in 1:(m-1)
        loc = num[piv[i]]
        if sol[i] < 0
            exp = -BigInt(sol[i])
            res1 *= inv(Q(loc))^(exp)*Q(h1)^(d*exp)
            for f in factor(loc)
                res2 *= inv(Q(f[1]))^(f[2]*exp)
            end
            res2 *= Q(h1)^(d*exp)*inv(coeff(loc, degree(loc)))^exp
        else
            exp = BigInt(sol[i])
            for f in factor(loc)
                res2 *= Q(f[1])^(f[2]*exp)
            end
            res1 *= Q(loc)^exp*inv(Q(h1))^(d*exp)
            res2 *= inv(Q(h1))^(d*exp)*coeff(loc, degree(loc))^exp
        end
    end
    return res1, res2
end

function checkcol(M, j, P, F)
    i = 0
    ζ = parent(P)(1)
    for y in F
        i += 1
        if M[i, j] == 1
            ζ *= P-y
        end
    end
    return ζ
end

function checkmat(M::MatElem, K, T::PolyElem)
    g = K.gen
    F = K.mediumSubField
    Q = K.bigField
    r, c = size(M)
    for j in 1:c
        ζ = Q(1)
        i = 0
        for y in F
            i += 1
            if M[i, j] != 0
                τ = Q(T-y)
                exp = Int(M[i, j])
                ζ *= τ^exp
            end
        end
        ζ *= Q(K.h1)
        ξ = g^BigInt(M[r, j])
        if ζ != ξ
            break
        end
    end
end

function isConjugate(A, B)
    C = A*inv(B)
    if C[1, 1] != 0
        C = inv(C[1, 1])*C
        if coeff(C[1, 2], 1) == 0 && coeff(C[2, 1], 1) == 0 && coeff(C[2, 2], 1) == 0
            return true
        end
    else
        C = inv(C[1, 2])*C
        if coeff(C[2, 1], 1) == 0 && coeff(C[2, 2], 1) == 0
            return true
        end
    end
    return false
end

function truePgl(pgl)
    new = Array{typeof(pgl[1]), 1}()
    for M in pgl
        b = true
        for N in new
            if isConjugate(M, N)
                b = false
                break
            end
        end
        if b
            push!(new, M)
        end
    end
    return new
end

# end of module
end
