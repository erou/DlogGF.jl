################################################################################
#
#   linfactors.jl : functions for computing linear factors
#
################################################################################

export linearDlog

"""
    linearDlog{T <: PolyElem}(basis::T, degExt::Integer, h0::T, h1::T,
                              card::Nemo.fmpz, defPol::T)

Compute the discrete logarithm of the elements of type ``X + μ`` and of `h1`.

This algorithm works only if the provided basis is *linear*.
"""
function linearDlog{T <: PolyElem}(basis::T, degExt::Integer, h0::T, h1::T,
                                   card::Nemo.fmpz, defPol::T)

    # We set some constants, arrays, matrices
    F = base_ring(h0)
    charac::Int = characteristic(F)
    x = gen(F)
    X = gen(parent(h0))
    j = 0
    n = 0
    o = -coeff(basis, 0)
    ind::Int = coeff(o, 0) + coeff(o, 1)*charac + 1

    S = MatrixSpace(ZZ, charac^2+2,charac^3+charac+1)
    M = zero(S)
    Pq = pglCosets(x)

    # We iterate over Pq = PGL(P_1(F_q²))/PGL(P_1(F_q)) to create new equations 
    # involving X and its translations X - μ with μ in F_q², we keep only the 
    # one with a smooth left side and we fill a matrix to remember which
    # translations were used. Contrary to the descent algorithm, we also keep
    # trace of the linear factors in the left side.
    for m in Pq
        N = makeEquation(m, X, h0, h1)

        if isSmooth(N, 1)
            j += 1
            unit = fillMatrixBGJT!(M, j, m, F)
            fact = factor(N)
            for f in fact
                cst = -coeff(f[1], 0)
                index::Int = coeff(cst, 0) + coeff(cst, 1)*charac + 1
                M[index, j] -= f[2] 
            end
            M[charac^2+2, j] = 1
        end
    end

    M = subMatrix(M, charac^2 + 2, j)
    M = transpose(M)

    # We compute the logarithm of the linear elements and h1 
    # modulo the small factors using Pohling Hellman algorithm
    # We also look for the linear factor X-y that is the basis, this is a type
    # problem, we cannot do it directly; but the types could be better managed
    # in order not to do that
    dlogs = Array(Nemo.fmpz, charac^2+1)
    i = 0
    for y in F
        i += 1
        dlogs[i] = pohligHellman(card, basis, X-y, defPol)[1]
    end

    i += 1
    dlogs[i], n = pohligHellman(card, basis, h1, defPol)

    # We next look at the big factors of ``card-1``, we compute the result
    # modulo each factor and reconstruct the result using Chinese remaindering
    # theorem
    v = div(card-1, n)
    bigFactors = factor(v)

    # We compute the one-dimensionnal kernel, and we choose the vector with a 1
    # at index `ind`, because this is the index of our basis (we chose it linear
    # for that purpose)
    for p in bigFactors
        Mred = rrefMod(M, p[1])[1]
        ker = Nemo.fmpz[Mred[i, charac^2+2] for i in 1:charac^2]
        s = gcdinv(ker[ind], p[1])[2]
        for i in 1:charac^2
            dlogs[i] = crt(dlogs[i], n, ker[i]*s, p[1])
        end
        dlogs[charac^2+1] = crt(dlogs[charac^2+1], n, -s, p[1])
        n *= p[1]
    end

    # And we put the results in a dictionnary, to be more easy to use
    dico = Dict()
    i = 0
    for y in F
        i += 1
        dico[X-y] = dlogs[i]
    end
    dico[h1] = dlogs[i+1]

    return dico
end

function linearDlog{T <: PolyElem}(basis:: Nemo.RingElem, degExt::Integer,
                                   h0::T, h1::T, card::Integer, defPol::T)
    return linearDlog(basis, degExt, h0, h1, Nemo.fmpz(card), defPol)
end
