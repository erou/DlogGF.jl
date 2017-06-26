################################################################################
#
#   gkz.jl : functions for Granger, Kleinjung, Zumbrägel algorithm
#
################################################################################

function ascent(Q::fq_nmod_poly)
    d::Int = log2(degree(Q))
    F = base_ring(Q)
    deg = degree(F)
    c::Int = characteristic(F)
    P = Q

    for j in 1:d-1
        z = string("z", deg*2^j)
        Fext = FiniteField(c, deg*2^j, z)[1]
        img = findImg(Fext, F)
        F = Fext
        R, T = PolynomialRing(Fext, "T")
        P = anyFactor(R(P, img))
    end

    return P
end

function ascent2(Q::fq_nmod_poly)
    d::Int = log2(degree(Q)) - 1
    F = base_ring(Q)
    deg = degree(F)
    c::Int = characteristic(F)
    z = string("z", deg*2^d)
    Fext = FiniteField(c, deg*2^d, z)[1]
    Rext, T = PolynomialRing(Fext, "T") 
    img = findImg(Fext, F)
    return anyFactor(Rext(Q, img))
end
