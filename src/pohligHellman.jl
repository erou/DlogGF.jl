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
        a = pohligHellmanPrime(B[1, 1], B[2, 1], k, mid, elemid, defPol)
        b = pohligHellmanPrime(B[1, 2], B[2, 2], k, mid, elemid, defPol)
        res, n = crt(a[1], a[2], b[1], b[2]), a[2]*b[2]
        for i in 1:(length(A)-2)
            a = pohligHellmanPrime(B[1, i+2], B[2, i+2], k, mid, elemid, defPol)
            res, n = crt(res, n, a[1], a[2]), n*a[2]
        end
        return res, n
    else 
        return pohligHellmanPrime(B[1, 1], B[2, 1], k, mid, elemid, defPol)
    end
end

pohligHellman{T}(card::Nemo.fmpz, gen::T, elem::T, defPol::T) =
pohligHellman(BigInt(card), gen, elem, defPol)

# New idea, precomputed roots of unity and parameters

function pohligHellmanParam{T}(card::Integer, gen::T, defPol::T)

    # We find the small (meaning, less that log(card)) prime factors of card-1
    q::BigInt = characteristic(base_ring(parent(gen)))
    l::Int = ceil(Integer, (q^2-1)/2)
    l = max(l, ceil(Integer, log2(card)))
    A = Array{Int, 1}()
    for i in primes(l)
        if card%i == 1
            push!(A, i)
        end
    end

    # We compute the exponent of these factors
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

    # We compute the product of the small factors and compute a big powering, in
    # order to do smaller powering later
    k = prod(Int[B[1, i]^B[2, i] for i in 1:length(A)])
    d = div(card-1, k)
    mid = powmod(gen, d, defPol)

    return k, d, mid, B
end

pohligHellmanParam{T}(card::Nemo.fmpz, gen::T, defPol::T) =
pohligHellmanParam(BigInt(card), gen, defPol)

function pohligHellmanRoots{T <: PolyElem}(B::Array{Int, 2}, k::Int,
                                           mid::T, defPol::T)

    nbprimes = size(B)[2]
    inverses = Array(T, nbprimes)
    biggestPrime = B[1, nbprimes]
    arr = Array(T, (biggestPrime, nbprimes)) # We create an array that is too big !

    for j in 1:nbprimes
        prime, n = B[1, j], B[2, j]
        f = div(k, prime^n)
        g = powmod(mid, f, defPol)
        inverses[j] = gcdinv(g, defPol)[2]
        g = powmod(g, prime^(n-1), defPol)
    
        # We compute a table of the `prime`-th roots of unit
        for i in 0:(prime-1)
            arr[i + 1, j] = powmod(g, i, defPol)
        end
    end

    return arr, inverses
end

function pohligHellmanPrimePrec{T <: PolyElem}(prime::Int, n::Int, k::Int,
                                           mid::T, elem::T, defPol::T,
                                           arr::Array{T, 1}, inverse::T)

    f = div(k, prime^n)
    tmp = powmod(elem, f, defPol)
    
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

function pohligHellmanPrec{T}(card::Integer, mid::T, elem::T, defPol::T, k::Int,
                              d::Integer, B::Array{Int, 2}, arr::Array{T, 2},
                              inverses::Array{T, 1})

    elemid = powmod(elem, d, defPol)

    # We set some variables to fmpz to use `crt`
    res::Nemo.fmpz = 0
    n::Nemo.fmpz = 0

    # And we compute the discrete logarithm of `elem` in the basis `gen`, for
    # each prime factor, using pohligHellmanPrime, then we compute our final
    # result using Chinese remindering theorem
    if size(B)[2] > 1
        a = pohligHellmanPrimePrec(B[1, 1], B[2, 1], k, mid, elemid, defPol,
                                   arr[1:B[1, 1], 1], inverses[1])
        b = pohligHellmanPrimePrec(B[1, 2], B[2, 2], k, mid, elemid, defPol,
                                   arr[1:B[1, 2], 2], inverses[2])
        res, n = crt(a[1], a[2], b[1], b[2]), a[2]*b[2]
        for i in 1:(size(B)[2]-2)
            a = pohligHellmanPrimePrec(B[1, i+2], B[2, i+2], k, mid, elemid,
                                       defPol, arr[1:B[1, i+2], i+2], inverses[i+2])
            res, n = crt(res, n, a[1], a[2]), n*a[2]
        end
        return res, n
    else 
        return pohligHellmanPrimePrec(B[1, 1], B[2, 1], k, mid, elemid, defPol,
                                      arr[1:B[1, 1], 1], inverses[1])
    end
end

pohligHellmanPrec{T}(card::Nemo.fmpz, gen::T, elem::T, defPol::T, k::Int,
                     d::Integer, B::Array{Int, 2}, arr::Array{T, 2},
                     inverses::Array{T, 1}) = pohligHellmanPrec(BigInt(card), gen, elem,
                                                  defPol, k, d, B, arr, inverses)
