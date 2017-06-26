################################################################################
#
#   basics.jl : basic functions
#
################################################################################

export dlogSmallField

function Nemo.powmod(x::Nemo.fq_nmod_poly, n::Nemo.fmpz, y::Nemo.fq_nmod_poly)
   check_parent(x,y)
   z = parent(x)()

   if n < 0
      g, x = gcdinv(x, y)
      if g != 1
         error("Element not invertible")
      end
      n = -n
   end

   ccall((:fq_nmod_poly_powmod_fmpz_binexp, :libflint), Void,
         (Ptr{fq_nmod_poly}, Ptr{fq_nmod_poly}, Ptr{fmpz}, Ptr{fq_nmod_poly},
         Ptr{FqNmodFiniteField}), &z, &x, &n, &y, &base_ring(parent(x)))
  return z
end

Nemo.powmod(x::Nemo.fq_nmod_poly, n::Integer, y::Nemo.fq_nmod_poly) = Nemo.powmod(x,
                                                                        ZZ(n), y)
function powmodPreinv(x::Nemo.fq_nmod_poly, n::Nemo.fmpz, y::Nemo.fq_nmod_poly,
                     p::Nemo.fq_nmod_poly)
   check_parent(x,y)
   z = parent(x)()

   if n < 0
      g, x = gcdinv(x, y)
      if g != 1
         error("Element not invertible")
      end
      n = -n
   end

   ccall((:fq_nmod_poly_powmod_fmpz_binexp_preinv, :libflint), Void,
         (Ptr{fq_nmod_poly}, Ptr{fq_nmod_poly}, Ptr{fmpz}, Ptr{fq_nmod_poly},
          Ptr{fq_nmod_poly}, Ptr{FqNmodFiniteField}), &z, &x, &n, &y, &p, 
          &base_ring(parent(x)))

  return z
end

# Iterator over finite fields
# The elements are iterated in the order 0, 1, ..., q-1, x, 1 + x, 2 + x,
# ..., (q-1) + (q-1)x + ... + (q-1)x^(n-1), where x is the generator of F_q^n

function Base.start(F::Nemo.FqNmodFiniteField)
    n = F.mod_length - 1
    return zeros(Int, n)
end

function Base.next(F::Nemo.FqNmodFiniteField, state::Array{Int, 1})
    q = F.p - 1
    n = F.mod_length - 1
    x = gen(F)
    nex = deepcopy(state)
    i = 1
    l = n

    if nex[1] < q
        nex[1] += 1
    else
        for i in 1:n
            if nex[i] != q
                l = i
                break
            end
        end

        for i in 1:(l-1)
            nex[i] = 0
        end
        nex[l] += 1
    end

    res = sum(Nemo.fq_nmod[state[i]*x^(i-1) for i in 1:n])
    return (res, nex)
end

function Base.done(F::Nemo.FqNmodFiniteField, state::Array{Int, 1})
    return state[end] == F.p
end

function Base.eltype(::Type{Nemo.FqNmodFiniteField})
    return Nemo.fq_nmod
end

function Base.length(F::Nemo.FqNmodFiniteField)
    return BigInt((F.p))^(F.mod_length - 1)
end

# Some functions

"""
    dlogSmallField{T}(carac::Integer, degExt::Integer, gen::T, elem::T,
                           defPol::T)

Compute the discrete logarithm of `elem` in the basis `gen`.

This strategy works if `elem` is in fact in the medium subfield.
"""
function dlogSmallField{T}(carac::Integer, degExt::Integer, gen::T, elem::T,
                           defPol::T)

    # We compute the norm of `gen`
    q = BigInt(carac)^2
    c = div(q^degExt-1, q-1)
    n = powmod(gen, c, defPol)

    # Then we find the logarithm of `elem` is the basis `n`
    i = 1
    while powmod(n, i, defPol) != elem
        i += 1
    end

    # Amd we translate the result in basis `gen`
    return (i*c)%(q^degExt-1)
end

# Basic functions for finite fields

"""
    modulusCoeffs(F::FqNmodFiniteField)

Return the coefficients of the modulus defining the field `F`.
"""
function modulusCoeffs(F::FqNmodFiniteField)

    # We compute -x^d, where x is the generator of `F` and d its degree
    deg = degree(F)
    tail = -gen(F)^deg

    # Then we read the result, since we know that -x^d = P(x), with the
    # modulus defining `F` being T^d + P(T)
    coeffs = Array(Int, deg+1)
    for j in 1:deg
        coeffs[j] = coeff(tail, j-1)
    end

    coeffs[end] = 1

    return coeffs
end

"""
    (F::FqNmodFiniteField)(a::fq_nmod)

Coercion function between finite fields.
"""

function (F::FqNmodFiniteField)(a::fq_nmod)

    # We first check for impossible embeddings
    f = parent(a)
    df = degree(f)
    if degree(F)%df != 0
        error("There is no embedding: check the degrees of the fields involved")
    
    elseif characteristic(f) != characteristic(F)
        error("Fields must be of the same characteristic")
    end

    # Then we compute the image of the generator of the field in which `a`
    # lives, by finding a root of the polynomial defining `f` over F
    coeffs = modulusCoeffs(f)
    R, T = PolynomialRing(F, "T")
    fact = factor(R(coeffs))
    img = F()
    res = F()
    for r in fact
        img = -coeff(r[1],0)
        break
    end

    # And we compute the final result by linearity
    for j in 0:(degree(f)-1)
        res += coeff(a, j)*img^j
    end

    return res
end
