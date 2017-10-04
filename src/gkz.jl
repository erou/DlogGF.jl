################################################################################
#
#   gkz.jl : functions for Granger, Kleinjung, Zumbrägel algorithm
#
################################################################################


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
        P = anyFactor(embedPoly(R, P, img))
    end

    return P
end

"""
    ascent{Y <: PolyElem}(Q::Y, h0::Y, h1::Y)

Compute an embedding of `h0` and `h1` by going through all the fields in the
tower appearing in the power-of-2 algorithm.
"""
function ascent{Y <: PolyElem}(Q::Y, h0::Y, h1::Y)

    # We compute d such that deg(Q) = 2^d
    d::Int = log2(degree(Q))

    # Then we create all the fields of the extension appearing in the
    # powers-of-2 algorithm and we embed h0 and h1 at each step.

    F = base_ring(Q)
    deg = degree(F)
    c::Int = characteristic(F)
    P = Q
    t0, t1 = h0, h1

    for j in 1:d-1

        # We create the name of the variable of the extension
        z = string("z", deg*2^j)

        # We create the extension
        Fext = FiniteField(c, deg*2^j, z)[1]

        # We create the associated polynomial rings
        img = findImg(Fext, F)
        F = Fext
        T = string("T", deg*2^j)
        R = PolynomialRing(Fext, T)[1]

        # And we embed the polynomials, and in the case of `P` we keep only one
        # factor
        P = anyFactor(embedPoly(R, P, img))
        t0, t1 = embedPoly(R, t0, img), embedPoly(R, t1, img)
    end

    return P, t0, t1
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
    descentGKZ{Y <: PolyElem}(Q::Y, h0::Y, h1::Y, Rinit::PolyRing)

Perform the descent of the GKZ algorithm.

I.e. return a list of polynomials P_i and associated coefficients e_i such that
Π_i P_i^e_i = P, where `P` is the polynomial such that `Q` is the result of the
ascent in GKZ algorithm.
"""
function descentGKZ{Y <: PolyElem}(Q::Y, h0::Y, h1::Y, Rinit::PolyRing)

    # We first compute f such that the base field of `Q` is an extension of
    # degree 2^f of the base field of h0
    F = base_ring(Q)
    p::Int = characteristic(F)
    ff = base_ring(Rinit)
    q::Int = length(ff)
    c::Int = floor(log(p, q))
    d::Int = log(p, length(F))/c
    f::Int = log2(d)
    t0, t1 = h0, h1

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

        # We precompute data to be able to perform the projection
        # towards the floor below efficiently

        l = length(L)
        R = parent(L[1][1])
        exp = c*2^(j-1)
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

        # We project t0 and t1 (aka h0, h1) in the floor below in the tower
        t0 = projectLinAlgPoly(Rg, t0, M, piv)
        t1 = projectLinAlgPoly(Rg, t1, M, piv)

        # We replace L by L2 to perform the same thing in the next floor
        L = L2

        # And we empty the list L2
        L2 = weightedList()
    end

    return L

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
    Rg = Rinit
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

    t1 = projectLinAlgPoly(Rg, t1, M, piv)

    # We add t1 = h1 in the resulting list
    push!(L2, t1, cpt_h1)

    return L2
end
