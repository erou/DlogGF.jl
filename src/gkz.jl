################################################################################
#
#   gkz.jl : functions for Granger, Kleinjung, Zumbrägel algorithm
#
################################################################################

# Types for GKZ algorithm

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
immutable GkzContext
    characteristic::Integer
    baseField::FinField
    h0::PolyElem
    h1::PolyElem
    definingPolynomial::PolyElem
    gen::PolyElem
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
    h0, h1, definingPolynomial, gen = findParameters(F, n, check)

    return GkzContext(p, F, h0, h1, definingPolynomial, gen)
end

"""
    findParameters(F::FinField, n::Integer, check::Bool = false)
    
Find suitable parameters in order to perform the GKZ algorithm.
"""
function findParameters(F::FinField, n::Integer, check::Bool = false)

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

# Ascent phase in the GKZ algorithm

"""
    ascent(Q::fq_nmod_poly)

Find an irreducible factor of degree two of `Q` in an extension.
"""
function ascent(Q::fq_nmod_poly)

    # We compute d such that deg(Q) = 2^d
    d::Int = log2(degree(Q))

    # Then we embed `Q` in degree two extensions and keep only one factor of
    # degree 2^(d-1), and we do the same with this factor, until we have a
    # factor of degree 2.

    F = base_ring(Q)
    deg = degree(F)
    c::Int = characteristic(F)
    P = Q

    for j in 1:d-1

        # We create the name of the variable of the extension
        z = string("z", deg*2^j)

        # We create the extension
        Fext = FiniteField(c, deg*2^j, z)[1]

        # We embed the polynomial in that extension
        img = findImg(Fext, F)
        F = Fext
        T = string("T", deg*2^j)
        R = PolynomialRing(Fext, T)[1]

        # And we compute a factor
        P = anyFactor(R(P, img))
    end

    return P
end

"""
    latticeBasis(Q::fq_nmod_poly, h0::fq_nmod_poly, h1::fq_nmod_poly)

Find a basis of the latice L_Q of the form (u0, X + u1), (X + v0, v1).

``L_Q = {(w0, w1) \in F_{q^k}[X]^2 | w0h0 + w1h1 = 0 (mod Q)}``
"""
function latticeBasis(Q::fq_nmod_poly, h0::fq_nmod_poly, h1::fq_nmod_poly)

    # We compute our variables a, a0, a1, b, b0, b1
    h0b = h0 % Q
    h1b = h1 % Q

    Qb = monic(Q)
    a, b = -coeff(Qb, 1), -coeff(Qb, 0)
    
    a0, b0 = coeff(h0b, 1), coeff(h0b, 0)
    a1, b1 = coeff(h1b, 1), coeff(h1b, 0)

    # We set some variables
    t = (a0*b1-b0*a1)^(-1)
    u = a0^(-1)

    # We compute the result
    v1 = (b0*u*(a*a0+b0) - a0*b)*a0*t
    u1 = (b0*u*(a*a1+b1) - a1*b)*a0*t
    v0 = -u*(a1*v1 + a*a0 + b0)
    u0 = -u*(a1*u1 + a*a1 + b1)

    return u0, u1, v0, v1
end

"""
    onTheFlyAbc(Q::fq_nmod_poly, h0::fq_nmod_poly, h1::fq_nmod_poly, q::Int)

Perform the 'on-the-fly' elimination of degree 2 elements.

In other words, return a, b, c such that the polynomial P = X^(q+1) + aX^q + bX + c
splits completely in the base field of `Q` and such that h1*P (mod h1*X^q - h0)
= 0 mod Q.
"""
function onTheFlyAbc(Q::fq_nmod_poly, h0::fq_nmod_poly, h1::fq_nmod_poly, q::Int)

    # We set some usefull variables
    R = parent(Q)
    T = gen(R)
    F = base_ring(Q)

    # We pick B such that T^(q+1) - BT + B splits completely
    B = randomSplitElem(R, q)

    # We find ui's and vi's such that (u0, T+u1), (T+v0, v1) is a basis of the
    # lattice L_Q = {(w0, w1) | w0h0 + w1h1 = 0 (mod Q)}
    u0, u1, v0, v1 = latticeBasis(Q, h0, h1)

    # We write the polynomial arising from the conditions wanted
    P = (-u0^q*T^q+T-v0^q)^(q+1)-B*(-u0*T^2+(u1-v0)*T+v1)^q
    
    # We find a root
    r = anyRoot(P)

    # If there is no root, we try the process with an other B
    while r == nothing
        B = randomSplitElem(R, q)
        P = (-u0^q*T^q+T-v0^q)^(q+1)-B*(-u0*T^2+(u1-v0)*T+v1)^q
        r = anyRoot(P)
    end

    # And we return a, b, c
    return r*u0+v0, r, r*u1+v1
end

"""
    onTheFlyElimination(Q::fq_nmod_poly, h0::fq_nmod_poly,
                        h1::fq_nmod_poly, q::Int)

Eliminate the polynomial `Q`. In other words, return polynomials L_i of degree 1
such that Π_i P_i^e_i = Q (mod h1×X^q - h0) for some coefficients e_i.
"""
function onTheFlyElimination(Q::fq_nmod_poly, h0::fq_nmod_poly,
                             h1::fq_nmod_poly, q::Int)

    # We define some usefull variables
    R = parent(Q)
    T = gen(R)

    # We find suitable constants a, b, c to perform the elimination
    a, b, c = onTheFlyAbc(Q, h0, h1, q)

    # We define the a polynomial that splits into linear factors
    P = T^(q+1) + a*T^q + b*T + c
    fact = factor(P)

    # And such that it is also divisible by Q modulo h1×X^q - h0, in the sense
    # that we have h1×P = L×Q (mod h1×Q - h0), with L of degree 1
    L = divexact((T+a)*h0+(b*T+c)*h1, Q)

    # Finally we return the factors of `P` and the linear polynomial `L`
    res = Array(fq_nmod_poly, q+2)
    j = 1
    for f in fact
        res[j] = f[1]
        j += 1
    end

    res[j] = L
    return res
end

"""
    norm2(Q::fq_nmod_poly, q::Integer)

Compute the norm of `Q` with respect to the field `F_q`, where the base field of
`Q` is an extension of degree 2 of `F_q`.
"""
function norm2(Q::fq_nmod_poly, q::Integer)

    # We compute the (only) conjugate of `Q`, meaning that all coefficients of
    # `Q` are raised to the power `q`
    conj = parent(Q)([coeff(Q, i)^q for i in 0:degree(Q)])

    # And we return the norm, i.e. the product of `Q` and its conjugate
    return Q*conj
end

"""
    norm4(Q::fq_nmod_poly, q::Integer)

Compute the norm of `Q` with respect to the field `F_q`, where the base field of
`Q` is an extension of degree 4 of `F_q`.
"""
function norm4(Q::fq_nmod_poly, q::Integer)

    # We compute the different conjugates and we compute the product as the same
    # time, the conjugate are just the polynomial `Q` with coefficients raised
    # to the power q^i
    res = Q
    conj = Q

    for j in 1:3
        conj = parent(conj)([coeff(conj, i)^q for i in 0:degree(conj)])
        res *= conj
    end

    # We return the product, i.e. the norm
    return res
end

"""
    descentGKZ(Q::fq_nmod_poly, h0::fq_nmod_poly, h1::fq_nmod_poly)

Perform the descent of the GKZ algorithm.

I.e. return a list of polynomials P_i and associated coefficients e_i such that
Π_i P_i^e_i = P, where `P` is the polynomial such that `Q` is the result of the
ascent in GKZ algorithm.
"""
function descentGKZ(Q::fq_nmod_poly, h0::fq_nmod_poly, h1::fq_nmod_poly)

    # We first compute f such that the base field of `Q` is an extension of
    # degree 2^f of the base field of h0
    F = base_ring(Q)
    p::Int = characteristic(F)
    ff = base_ring(h0)
    q::Int = length(ff)
    c::Int = log(p, q)
    d::Int = log(p, length(F))/c
    f::Int = log2(d)

    # Through the descent, we count the number of times we have h1 in an
    # equation
    cpt_h1 = BigInt()

    # We will use a composite type to store the involved polynomials and their
    # coefficients, L contains only Q and L2 is empty
    L = weightedList(Q)
    L2 = weightedList()

    # We start the descent through the tower 
    # 
    #   F_q^(2^f)
    #    |
    #   F_q^(2^(f-1))
    #    |
    #    :
    #    |
    #   F_q^(2^2)
    #    |
    #   F_q
    #
    # The last step is treated differently after that loop.

    for j in f:-1:3

        # We compute the embedding of h0 and h1 in the current floor of the
        # tower, and precompute data to be able to perform the projection
        # towards the floor below efficiently

        l = length(L)
        R = parent(L[1][1])
        img = findImg(base_ring(R), ff)
        t0, t1 = R(h0, img), R(h1, img)
        exp = c*BigInt(2)^(j-1)
        n = BigInt(p)^exp
        s = string("z", exp)
        G = FiniteField(p, exp, s)[1]
        T = string("T", exp)
        Rg = PolynomialRing(G, T)[1]
        M, piv = projectFindInv(base_ring(R), G)

        # For each element in L, we perform an on-the-fly elimination, we
        # project the obtained polynomials and store them in L2

        for i in 1:l

            # We perforn the elimination
            P, coef = L[i][1], L[i][2]
            A = onTheFlyElimination(P, t0, t1, q)

            # We add 2*coef because h1 will appear in the equation, and then it
            # will appear a second time when compute its norm, because h1 is its
            # own conjugate, so ||h1|| = h1²
            cpt_h1 += 2*coef

            for k in 1:(q+1)
                N = norm2(A[k], n)
                push!(L2, projectLinAlgPoly(Rg, N, M, piv), coef)
            end

            N = norm2(A[q+2], n)
            push!(L2, projectLinAlgPoly(Rg, N, M, piv), -coef)

        end

        # We replace L by L2 to perform the same thing in the next floor
        L = L2

        # And we empty the list L2
        L2 = weigthedList()
    end

    # We treat the case 
    #
    # F_q⁴
    #  |
    # F_q
    #
    # where after the degree two elimination, we compute the norm of a degree 4
    # extension instead of a degree 2 extension like we did for the first steps.

    l = length(L)
    R = parent(L[1][1])
    img = findImg(base_ring(R), ff)
    t0, t1 = R(h0, img), R(h1, img)
    Rg = parent(h0)
    G = base_ring(Rg)
    M, piv = projectFindInv(base_ring(R), G)

    for i in 1:l

        P, coef = L[i][1], L[i][2]
        A = onTheFlyElimination(P, t0, t1, q)

        # Here we have ||h1||=h1⁴
        cpt_h1 += 4*coef

        for k in 1:(q+1)
            N = norm4(A[k], q)
            push!(L2, projectLinAlgPoly(Rg, N, M, piv), coef)
        end

        N = norm4(A[q+2], q)
        push!(L2, projectLinAlgPoly(Rg, N, M, piv), -coef)

    end

    # We add h1 in the resulting list
    push!(L2, h1, cpt_h1)

    return L2
end
