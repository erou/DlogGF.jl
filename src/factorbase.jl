################################################################################
#
#   factorbase.jl : functions for computing factor base logarithms
#
################################################################################

"""
    bracket{T <: PolyElem}(D::Int , A::T, B::T, h0::T, h1::T)

Compute the `D`-bracket of `A` and `B`.

This is equal to ``h1^D(B×A(h0/h1) - A×B(h0/h1))``.
"""
function bracket{T <: PolyElem}(D::Int , A::T, B::T, h0::T, h1::T)

    # We create zero polynomials
    R = parent(A)
    Ahomo = R()
    Bhomo = R()

    # We compute h1^D × A(h0/h1) 
    for j in 0:degree(A)
        Ahomo += coeff(A, j)*(h0^j)*(h1^(D-j))
    end

    # We compute h1^D × B(h0/h1) 
    for j in 0:degree(B)
        Bhomo += coeff(B, j)*(h0^j)*(h1^(D-j))
    end

    # We return the result h1^D(B×A(h0/h1) - A×B(h0/h1))
    return B*Ahomo - A*Bhomo
end

"""
    fillMatrixGKZ!{T <: PolyElem}(M::MatElem, j::Int, A::T, B::T, f1::T,
                                  D::Int, fact::Nemo.Fac{T},
                                  tmpFact::Nemo.Fac{T}, unknowns::Dict{T,
                                                                       Int})

Fill the `j`-th column of the matrix M, according to the relation generated by
`Α` and `B`.
"""
function fillMatrixGKZ!{T <: PolyElem}(M::MatElem, j::Int, A::T, B::T, f1::T,
                                       D::Int, fact::Nemo.Fac{T},
                                       tmpFact::Nemo.Fac{T}, unknowns::Dict{T,
                                                                            Int})

    # We define the finite field
    F = base_ring(A)

    # We fill the matrix M to represent the factors involved in the equation
    # generated by `A` and `B`:
    # 
    # B×Π_{a\in F} (A-aB) = 1/h1^D×([A, B]_D)
    # where [A, B]_D = h1^D(A(h0/h1)×B - B(h0/h1)×A)

    # We begin with the factors in the product Π (A-aB)
    for a in F
        tmp = factor(A-a*B)
        for f in tmp
            M[unknowns[f[1]],j] += f[2]
        end
    end

    # We add the factors of B
    tmp = factor(B)
    for f in tmp
        M[unknowns[f[1]],j] += f[2]
    end

    # Then the factors of h1 = X(X+t), where f1 := X+t 
    M[unknowns[f1], j] += D
    M[unknowns[gen(parent(A))], j] += D

    # We add the factors on the other side of the equation
    # First the factors of h1×X-h0, indeed we always have h1×X-h0 | [A, B]_D
    for f in fact
        M[unknowns[f[1]],j] -= f[2]
    end

    # Finally the factors of [A, B]_D / (h1×X-h0)
    for f in tmpFact
        M[unknowns[f[1]],j] -= f[2]
    end
end

function factorBaseDeg2{T <: PolyElem}(K::GkzContext{T})

    h0, h1 = K.h0, K.h1
    g = K.gen
    defPol = K.definingPolynomial
    D = max(degree(h0), degree(h1))
    F = base_ring(h0)
    card = ZZ(length(F))^degree(defPol)
    q::Int = length(F)
    X = gen(parent(h0))
    f1 = divexact(h1, X)
    systFactor = h1*X-h0

    fact = factor(systFactor)
    unknownsToCoord, coordToUnknowns = irreduciblesDeg2(parent(h0))
    nbukn = length(unknownsToCoord)
    dlogs = Dict{T, Nemo.fmpz}()
    j = 0

    if length(fact) > 1

        Sp = MatrixSpace(ZZ, nbukn, q^2)
        M = zero(Sp)

        for a in F
            for b in F
                A = X^D + a
                B = X^(D-1) + b
                N = bracket(D, A, B, h0, h1)
                O = divexact(N, systFactor)

                tmpFact = factor(O)
                if isSmooth(tmpFact, 2)
                    
                    j += 1
                    fillMatrixGKZ!(M, j, A, B, f1, D, fact, tmpFact,
                                   unknownsToCoord)

                end
            end
        end

        M = subMatrix(M, nbukn, j)
        M = transpose(M)

        n = ZZ()

        for k in keys(unknownsToCoord)
            dlogs[k], n = pohligHellman(card, g, k, defPol)
        end

        v = div(card-1, n)
        bigFactors = factor(v)

        for p in bigFactors
            Mred = rrefMod(M, p[1])[1]
            ker = Nemo.fmpz[Mred[i, nbukn] for i in 1:(nbukn-1)]
            s = gcdinv(ker[unknownsToCoord[g]], p[1])[2]
            for j in 1:(nbukn-1)
                dlogs[coordToUnknowns[j]] =
                crt(dlogs[coordToUnknowns[j]], n, ker[j]*s, p[1])
            end
            dlogs[coordToUnknowns[nbukn]] =
            crt(dlogs[coordToUnknowns[nbukn]], n, -s, p[1])
            n *= p[1]
        end
        return dlogs
    end
end
