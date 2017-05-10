################################################################################
#
#   random.jl : random functions
#
################################################################################

# Random suite over medium subfields (of type F_q²)
# That is all we need as we use it only to find h0 and h1

export randomPolynomial

"""
    randomElem(ring::Nemo.Ring)

Return an random element in `ring`.
"""
function randomElem(ring::Nemo.Ring)
    x = gen(ring)
    c::Int = characteristic(ring) - 1
    return ring(rand(0:c)) + rand(0:c)*x
end

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
