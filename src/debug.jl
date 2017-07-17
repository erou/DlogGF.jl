################################################################################
#
#   debug.jl : debugging functions
#
################################################################################

# Internal debugging functions, not documented

function checkeq(P, M, m, K)
    i = 1
    R = parent(P)
    F = base_ring(P)
    defPol = K.definingPolynomial
    tmp2=R(1)
    for y in F
        if M[i, 1] == 1
            tmp2 *= P-y
        end
        i += 1
    end
    tmp2 %= defPol

    tmp1 = powmod(gcdinv(K.h1, defPol)[2], degree(P), defPol)
    tmp1 = mulmod(makeEquation(m, P, K.h0, K.h1), tmp1, defPol)

    return tmp1,tmp2
end

function checklog(L, defPol)
    l = length(L.factors)
    R = parent(L.factors[1])
    res = R(1)
    for i in 1:l
        tmp = powmod(L.factors[i], L.coefs[i], defPol)
        res = mulmod(res, tmp, defPol)
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

function checkcol(M, j, P, defPol)
    i = 0
    F = base_ring(P)
    ζ = parent(P)(1)
    for y in F
        i += 1
        if M[i, j] == 1
            ζ *= P-y
        end
    end
    return ζ%defPol
end

function checkmat(M::MatElem, K, T::PolyElem)
    g = K.gen
    R = parent(g)
    F = base_ring(g)
    defPol = K.definingPolynomial
    r, c = size(M)
    for j in 1:c
        ζ = R(1)
        i = 0
        for y in F
            i += 1
            if M[i, j] != 0
                exp = Int(M[i, j])
                ζ *= powmod(T-y, exp, defPol)
            end
        end
        ζ *= K.h1
        ζ %= defPol
        ξ = powmod(g, M[r, j], defPol)
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

function isSplit(P::PolyElem)
    for f in factor(P)
        if degree(f[1]) != 1
            return false
        end
    end
    return true
end

function substitute(P::PolyElem, S::PolyElem)
    R = parent(S)()
    for i in 0:degree(P)
        R += coeff(P, i)*S^i
    end
    return R
end
