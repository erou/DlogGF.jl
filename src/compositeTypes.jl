################################################################################
#
#   compositeTypes.jl : CompositeTypes
#
################################################################################

# Types for Barculescu, Gaudry, Joux and Thomé algorithm

# bgjtContext: used to create and gather all the informations needed to
#             perform the algorithm of Barbulescu et al.

"""
    bgjtContext

Sparse medium subfield representation of a field of the form ``K = \\mathbb
F_{q^{2k}}``.

# Cautions

* this should never be called as a constructor, due to the number of
  the fields. To create such a representation, see `smsrField`

# Fields

* `h0::PolyElem` and `h1::PolyElem` are polynomials such that ``h1*X^q-h0`` has
  a degree ``k`` irreducible factor, named `definingPolynomial::PolyElem`
* `gen::RingElem` is a generator of the group of the inversible elements of the
  field, it is actually taken at random *without* checking that it is indeed a
  generator by default
"""
immutable BgjtContext{T <: PolyElem}
    h0::T
    h1::T
    definingPolynomial::T
    gen::T
end

"""
    bgjtContext(p::Integer, l::Integer, n::Integer = 1, check::Bool = false)

Construct a field ``K = \\mathbb F_{q^{n/2}}`` of type `BgjtContext`,
where q = p^(2l).

If `check` is `true`, the generator will be checked. *Note* that
this will call `factor(K.cardinality-1)`, so it should not be performed with
finite fields of large cardinality.
"""
function bgjtContext(p::Integer, l::Integer, n::Integer, check::Bool = false)

    if n%2 == 0

        # We create the base field ``F_q``
        F = FiniteField(p, 2*l, "z")[1]

    else
        error("In BGJT algorithm, the extension degree must be even.")
    end

    # And we find the parameters
    h0, h1, definingPolynomial, gen = findParametersBgjt(F, div(n, 2), check)

   return BgjtContext(h0, h1, definingPolynomial, gen)
end

"""
    findParametersBgjt(F::FinField, n::Integer, check::Bool = false)
    
Find suitable parameters in order to perform the GKZ algorithm.
"""
function findParametersBgjt(F::FinField, n::Integer, check::Bool = false)

    # We set our polynomials
    # With BGJT, the polynomials are represented by polynomials over F_q²
    q::Int = sqrt(length(F))
    Q = length(F)
    polyRing, T = PolynomialRing(F, "T")
    h0, h1, definingPolynomial = polyRing(), polyRing(), polyRing()

    # And we search suitable polynomials h0, h1
    boo = true
    while boo
        h0 = randomElem(F)*T + randomElem(F)
        h1 = T^2 + randomElem(F)*T
        fact = factor(h1*T^q - h0)
        for f in fact
            if degree(f[1]) == n
                boo = false
                definingPolynomial = f[1]
                break
            end
        end
    end

    # Finally we find a generator
    gen = T + randomElem(F)

    if check
        while !isGenerator(gen, Q^n, definingPolynomial)
            gen = T + randomElem(F)
        end
    else
        while !miniCheck(gen, Q^n, definingPolynomial)
            gen = T + randomElem(F)
        end
    end

    return h0, h1, definingPolynomial, gen
end

# FactorsList : this type is used to represent a factorisation of the type 
#               P = (unit) × P_1^(e_1) × ... × P_n^(e_n), we use it because
#               the algorithm of Barbulescu et al. consist of finding such
#               a relation with P_i's of degree 1.

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

function Base.length(L::FactorsList)
    return length(L.coefs)
end

# Types for Granger, Kleinjung and Zumbrägel algorithm

"""
    GkzContext

Important elements in the context of the GKZ algorithm over a field ``F_{q^n}``.

# Cautions

* This should never be called as a constructor, see `gkzContext` instead.

# Fields

* `characteristic::Integer` : characteristic of the field
* `baseField::FinField` : the field ``F_q``
* `h0` and `h1` are polynomials such that ``h1*X^q - h0`` as a degree `n`
  irreducible factor, which will be the `definingPolynomial`
* `gen` is a generator of the group of invertible elements of the field, by
  default, it is taken at random *without* warranty that it is indeed a
  generator.
"""
immutable GkzContext{T <: PolyElem}
    h0::T
    h1::T
    definingPolynomial::T
    gen::T
end

"""
    gkzContext(p::Integer, l::Integer, n::Integer, check::Bool = false)

Construct the field ``F_{q^n}`` where ``q = p^l`` in the context of the GKZ
algorithm.
"""
function gkzContext(p::Integer, l::Integer, n::Integer, check::Bool = false)

    # We create the base field ``F_q``
    z = string("z", l)
    F = FiniteField(p, l, z)[1]

    # And we find the parameters 
    h0, h1, definingPolynomial, gen = findParametersGkz(F, n, check)

    return GkzContext(h0, h1, definingPolynomial, gen)
end

"""
    findParametersGkz(F::FinField, n::Integer, check::Bool = false)
    
Find suitable parameters in order to perform the GKZ algorithm.
"""
function findParametersGkz(F::FinField, n::Integer, check::Bool = false)

    # We set our polynomials
    q = length(F)
    p::Int = characteristic(F)
    d::Int = log(p, q)
    sT = string("T", d)
    polyRing, T = PolynomialRing(F, sT)
    h0, h1, definingPolynomial = polyRing(), polyRing(), polyRing()

    # And we search suitable polynomials h0, h1
    boo = true
    while boo
        h0 = randomElem(F)*T + randomElem(F)
        h1 = T^2 + randomElem(F)*T
        fact = factor(h1*T^q - h0)
        for f in fact
            if degree(f[1]) == n
                boo = false
                definingPolynomial = f[1]
                break
            end
        end
    end

    # Finally we find a generator
    gen = T + randomElem(F)

    if check
        while !isGenerator(gen, q^n, definingPolynomial)
            gen = T + randomElem(F)
        end
    else
        while !miniCheck(gen, q^n, definingPolynomial)
            gen = T + randomElem(F)
        end
    end

    return h0, h1, definingPolynomial, gen
end

"""
    WeightedList

Represent a list of polynomials with weights.

# Fields

* `poly::Array{Nemo.fq_nmod_poly, 1}` : the polynomials
* `weight::Array{Int, 1}` : the weights of the polynomials
"""
type WeightedList
    poly::Array{Nemo.fq_nmod_poly, 1}
    weight::Array{Integer, 1}
end

"""
    weightedList(P::Nemo.fq_nmod_poly)

Construct an element of type `WeightedList`.
"""
function weightedList(P::Nemo.fq_nmod_poly)
    return WeightedList([P], [1])
end

function weightedList()
    A = Array{fq_nmod_poly, 1}()
    B = Array{Integer, 1}()
    return WeightedList(A, B)
end

function Base.push!(L::WeightedList, P::Nemo.fq_nmod_poly, coef::Integer)

    # We try to find if `P` is already in `L`
    i = findfirst(L.poly, P)

    # If it is, we just change the associated coefficient
    if i != 0
        L.weight[i] += coef
    # Otherwise, we add `P` and its coefficient `coef` to `L`
    else
        push!(L.poly, P)
        push!(L.weight, coef)
    end
end

function Base.deleteat!(L::WeightedList, i::Integer)
    deleteat!(L.poly, i)
    deleteat!(L.weight, i)
end

function Base.getindex(L::WeightedList, i::Integer)
    return (L.poly[i],L.weight[i])
end

function Base.length(L::WeightedList)
    return length(L.weight)
end

