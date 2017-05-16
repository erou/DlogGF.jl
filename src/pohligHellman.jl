################################################################################
#
#   pohligHellman.jl : functions for Pohlig-Hellman algorithm
#
################################################################################

export pohligHellman

"""
    pohligHellmanPrime{T <: PolyElem}(prime::Int, n::Int, k::Int,
                                      mid::T, elem::T, defPol::T)
                                      
Compute the discrete logarithm of `elem` mod `prime^n` in basis `gen`.

Where `prime` si a prime number dividing `card` and `n` is the largest integer
such that `prime^n` divides `card`. See reference **[2]** for more information about
this algorithm, the references can be found in the documentation of the module.
"""
function pohligHellmanPrime{T <: PolyElem}(prime::Int, n::Int, k::Int,
                                           mid::T, elem::T, defPol::T)

    f = div(k, prime^n)
    g = powmod(mid, f, defPol)
    inverse = gcdinv(g, defPol)[2]
    tmp = powmod(elem, f, defPol)
    g = powmod(g, prime^(n-1), defPol)
    
    # We compute a table of the `prime`-th roots of unit
    arr = Array(T, prime)
    for i in 0:(prime-1)
        arr[i + 1] = powmod(g, i, defPol)
    end

    res = 0

    # We compute the coefficients `b_i` such that x = Σ b_i × prime^i, meaning
    # that we compute `x` in basis `prime`
    d = prime^n
    for i in 0:(n-1)
        d = div(d, prime)
        b = findfirst(arr, powmod(tmp, d, defPol)) - 1
        res += b*prime^i
        tmp = mulmod(tmp, powmod(inverse, b*prime^i, defPol), defPol)
    end

    return (fmpz(res), fmpz(prime)^n)
end

"""
    pohligHellman{T}(card::Integer, gen::T, elem::T, defPol::T)

Compute the discrete logarithm of `elem` in the basis `gen`, modulo the small
prime factors of card - 1.
"""
function pohligHellman{T}(card::Integer, gen::T, elem::T, defPol::T)

    # We find the small (meaning, less that log(card)) prime factors of card
    q::BigInt = characteristic(base_ring(parent(gen)))
    l::Int = ceil(Integer, (q^2-1)/2)
    l = max(l, ceil(Integer, log2(card)))
    A = Array{Int, 1}()
    for i in primes(l)
        if card%i == 1
            push!(A, i)
        end
    end


    B = Array(Int, (2, length(A)))

    for i in 1:length(A)
        prime = A[i]
        B[1, i] = A[i]
        ex = 1
        while divisible(fmpz(card-1), prime^(ex+1))
            ex += 1
        end
        B[2, i] = ex
    end

    k = prod(Int[B[1, i]^B[2, i] for i in 1:length(A)])
    d = div(card-1, k)
    mid = powmod(gen, d, defPol)
    elemid = powmod(elem, d, defPol)

    # We set some variables to fmpz to use `crt`
    res::Nemo.fmpz = 0
    n::Nemo.fmpz = 0

    # And we compute the discrete logarithm of `elem` in the basis `gen`, for
    # each prime factor, using pohligHellmanPrime, then we compute our final
    # result using Chinese remindering theorem
    if length(A) > 1
        a = pohligHellmanPrime2(B[1, 1], B[2, 1], k, mid, elemid, defPol)
        b = pohligHellmanPrime2(B[1, 2], B[2, 2], k, mid, elemid, defPol)
        res, n = crt(a[1], a[2], b[1], b[2]), a[2]*b[2]
        for i in 1:(length(A)-2)
            a = pohligHellmanPrime2(B[1, i+2], B[2, i+2], k, mid, elemid, defPol)
            res, n = crt(res, n, a[1], a[2]), n*a[2]
        end
        return res, n
    else 
        return pohligHellmanPrime2(B[1, 1], B[2, 1], k, mid, elemid, defPol)
    end
end

pohligHellman{T}(card::Nemo.fmpz, gen::T, elem::T, defPol::T) =
pohligHellman(BigInt(card), gen, elem, defPol)

"""
Deprecated function, 5 times slower
"""
function pohligHellmanPrimedep{T <: PolyElem}(card::Integer, prime::Integer,
                                           gen::T, elem::T, defPol::T)

    # We compute a table of the `prime`-th roots of unit
    d::Integer = div(card-1, prime)
    g = powmod(gen, d, defPol)
    arr = Array(T, prime)
    for i in 0:(prime-1)
        arr[i + 1] = powmod(g, i, defPol)
    end

    res = 0
    tmp = elem
    inverse = gcdinv(gen, defPol)[2]

    # We compute the largest integer `n` such that `prime^n` divides `card`
    n = 1
    while divisible(fmpz(card-1), prime^(n+1))
        n += 1
    end

    # We compute the coefficients `b_i` such that x = Σ b_i × prime^i, meaning
    # that we compute `x` in basis `prime`
    d = card-1
    for i in 0:(n-1)
        d = div(d, prime)
        b = findfirst(arr, powmod(tmp, d, defPol)) - 1
        res += b*prime^i
        tmp = mulmod(tmp, powmod(inverse, b*prime^i, defPol), defPol)
    end

    return (fmpz(res), fmpz(prime)^n)
end

"""
Deprecated function, 5 times slower
"""
function pohligHellmandep{T}(card::Integer, gen::T, elem::T, defPol::T)

    # We find the small (meaning, less that log(card)) prime factors of card
    q::BigInt = characteristic(base_ring(parent(gen)))
    l::Int = ceil(Integer, (q^2-1)/2)
    l = max(l, ceil(Integer, log2(card)))
    A = Array{Int, 1}()
    for i in primes(l)
        if card%i == 1
            push!(A, i)
        end
    end

    # We set some variables to fmpz to use `crt`
    res::Nemo.fmpz = 0
    n::Nemo.fmpz = 0

    # And we compute the discrete logarithm of `elem` in the basis `gen`, for
    # each prime factor, using pohligHellmanPrime, then we compute our final
    # result using Chinese remindering theorem
    if length(A) > 1
        a = pohligHellmanPrime(card, A[1], gen, elem, defPol)
        b = pohligHellmanPrime(card, A[2], gen, elem, defPol)
        res, n = crt(a[1], a[2], b[1], b[2]), a[2]*b[2]
        for i in 1:(length(A)-2)
            a = pohligHellmanPrime(card, A[i+2], gen, elem, defPol)
            res, n = crt(res, n, a[1], a[2]), n*a[2]
        end
        return res, n
    else 
        return pohligHellmanPrime(card, 2, gen, elem, defPol)
    end
end
