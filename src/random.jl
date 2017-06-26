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

function randomSplitElem(polyRing::Nemo.Ring, defPol)
    F = base_ring(polyRing)
    n = F.mod_length - 1
    randElem = polyRing(randomList(F, n))
    card = length(F)
    while randElem == powmod(randElem, card^2, defPol)
        randElem = polyRing(randomList(F, n))
    end
    res = randElem - powmod(randElem, card, defPol)
#    res = 
end
