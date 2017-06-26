################################################################################
#
#   random.jl : random functions
#
################################################################################

# Random suite over finite fields in Nemo

export randomPolynomial

"""
    randomElem(finField::Nemo.FinField)

Return a random element in `finField`.
"""
function randomElem(finField::Nemo.FinField)
    x = gen(finField)
    c::Int = characteristic(finField) - 1
    n = finField.mod_length - 2
    res = finField(rand(0:c))
    for j in 1:n
        res += rand(0:c)*x^j
    end
    return res
end

"""
    randomList(finField::Nemo.FinField, len::Integer)

Return an `Array` of length `len` with random elements in `finField`.
"""
function randomList(finField::Nemo.FinField, len::Integer)
    A = Array(finField, len)
    for i in 1:len
        A[i] = randomElem(finField)
    end
    return A
end
    
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

"""
    randomIrrPolynomial(polyRing::Nemo.PolyRing, degree::Integer)

Return a randon irreducible polynomial of degree `degree` in the ring
`polyRing`.
"""
function randomIrrPolynomial(polyRing::Nemo.PolyRing, degree::Integer)
    P = randomPolynomial(polyRing, degree)
    while length(factor(P)) != 1
        P = randomPolynomial(polyRing, degree)
    end
    return P
end


# Random B such that X^(q+1) - BX + B factors

"""
    randomSplitElem(polyRing::Nemo.Ring, q::Int)

Return a random element B in the base ring of `polyRing` such that the
polynomial X^(q+1) - BX + B splits into linear factors.

See Reference **[4]** for an explanation about the formula. The references can
be found in the module documentation.
"""
function randomSplitElem(polyRing::Nemo.Ring, q::Int)

    # We pick a random element in F_q^k\F_q^2, where F_q^k is the base ring of
    # `polyRing`
    F = base_ring(polyRing)
    randEl = randomElem(F)
    while randEl == randEl^(q^2)
        randEl = randomElem(F)
    end

    # Then we apply the formula
    res = (randEl-randEl^(q^2))^(q+1)*(randEl-randEl^q)^(-q^2-1)

    return res
end
