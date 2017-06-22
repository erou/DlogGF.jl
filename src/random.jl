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

# Random B such that X^(q+1) - BX + B factors

function randomSplitElem(polyRing::Nemo.Ring, defPol)
    randElem = polyRing(randomList(base_ring(polyRing)))
end
