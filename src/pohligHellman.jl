################################################################################
#
#   pohligHellman.jl : functions for Pohlig-Hellman algorithm
#
################################################################################

export pohligHellman

"""
    pohligHellmanPrime{T <: PolyElem}(card::Integer, prime::Integer,
                                      gen::T, elem::T, defPol::T)
                                      
Compute the discrete logarithm of `elem` mod `prime^n` in basis `gen`.

Where `prime` si a prime number dividing `card` and `n` is the largest integer
such that `prime^n` divides `card`. See reference **[2]** for more information about
this algorithm, the references can be found in the documentation of the module.
"""
function pohligHellmanPrime{T <: PolyElem}(card::Integer, prime::Integer,
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

pohligHellman{T}(card::Nemo.fmpz, gen::T, elem::T, defPol::T) =
pohligHellman(BigInt(card), gen, elem, defPol)

"""
This function is faster than `pohligHellmanPrime` when working modulo p^n with
n ≥ 3, but in practice we often work with p = 1.
"""
function pohligHellmanPrime2{T <: PolyElem}(card::Integer, prime::Integer,
                                           gen::T, elem::T, defPol::T)

    # We compute the largest integer `n` such that `prime^n` divides `card`
    n = 1
    while divisible(fmpz(card-1), prime^(n+1))
        n += 1
    end

    d::Integer = div(card-1, prime)
    f::Integer = div(card-1, prime^n)

    # We compute a table of the `prime`-th roots of unit
    g = powmod(gen, d, defPol)
    arr = Array(T, prime)
    for i in 0:(prime-1)
        arr[i + 1] = powmod(g, i, defPol)
    end

    res = 0
    tmp = powmod(elem, f, defPol)
    inverse = gcdinv(gen, defPol)[2]
    inverse = powmod(inverse, f, defPol)

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


