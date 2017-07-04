################################################################################
#
#   bgjt.jl : functions for the BGJT algorithm
#
################################################################################

export dlogBGJT, smsrField

# Composite types

## SmsrField : used to create and gather all the informations needed to
##             perform the algorithm of Barbulescu et al.

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
* `gen::RingElem` is a generator of the group of the inversible elements of the
  field, it is actually taken at random *without* checking that it is indeed a
  generator by default
"""
immutable SmsrField
    characteristic::Integer
    extensionDegree::Integer
    cardinality::Integer
    h0::PolyElem
    h1::PolyElem
    definingPolynomial::PolyElem
    gen::PolyElem
end

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
    gen = randomPolynomial(polyRing, 0) + T

    # We optionally check that `gen` is indeed a generator
    if check
        while !isGenerator(gen, card, definingPolynomial)
            gen = randomPolynomial(polyRing, 0) + T
        end
    else
        while !miniCheck(gen, card, definingPolynomial)
            gen = randomPolynomial(polyRing, 0) + T
        end
    end

    # And we call the constructor of the type `SmsrField`
    return SmsrField(q, k, card, h0, h1, definingPolynomial, gen)
end

## FactorsList : this type is used to represent a factorisation of the type 
##               P = (unit) × P_1^(e_1) × ... × P_n^(e_n), we use it because
##               the algorithm of Barbulescu et al. consist of finding such
##               a relation with P_i's of degree 1.

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

# The functions

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

"""
    descentBGJT{T <: PolyElem}(L::FactorsList, i0::Integer, h0::T, h1::T,
                                    card::Nemo.fmpz)

The descent phase of the BGJT algorithm.
"""
function descentBGJT{T <: PolyElem}(L::FactorsList, i0::Integer, h0::T, h1::T,
                                    card::Nemo.fmpz)

    # We set some constants, arrays, matrices
    F = base_ring(h0)
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
#    sol = Nemo.fmpz[M[i,j] for i in 1:(charac^2+1)]


    # We compute the coordinates of the pivots (because we have redundant
    # equations)
    piv = pivots(M, charac^2+1)

    # We add the new polynomials and their coefficients in our list
    for j in 1:(charac^2+1)
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

"""
    dlogBGJT(P::Nemo.RingElem, K::SmsrField, dlogs::Dict{Any, Any})

Compute the discrete logarithm of `P` in the field `K`.

The field `K` must have a sparse medium subfield representation. All the
informations needed in the algorithm, like the basis, are in the object `K`.
This algorithm need the discrete logarithms of the linear factors, they can be
computed using **linearDlog**.
"""
function dlogBGJT(P::Nemo.fq_nmod_poly, K::SmsrField, dlogs::Dict{Any, Any})

    defPol = K.definingPolynomial
    R = parent(K.gen)
    # We first compute the discrete logarithm of `P` modulo 
    # the small factors with Pohlig Hellman algorithm
    s, n = pohligHellman(K.cardinality, K.gen, P, defPol)

    # Then we work with the large factors, using the descent algorithm to
    # express log P in function of logarithms of polynomials with smaller degree
    # and we stop once we have only linear polynomials, which logarithms are
    # known
    N = div(Nemo.fmpz(K.cardinality-1), n)
    i = 1
    L = factorsList(P)

    while i < length(L.factors) + 1
        while degree(L.factors[i]) > 1
            descentBGJT(L, i, K.h0, K.h1, N)
        end
        i += 1
    end

    # Once we have only linear polynomials, we compute the linear sum
    # log P = Σ e_i × log P_i (mod N) where the e_is where calculated during the
    # descent, and where the log P_is are given
    S = sum([L.coefs[j]*dlogs[L.factors[j]] for j in 1:length(L.factors)])
    #S += dlogSmallField(K.characteristic, K.extensionDegree, K.gen,
    #                    R(L.unit), defPol)

    # Then we reconstruct the result using Chinese remindering theorem
    return crt(s, n, S, N)
end
