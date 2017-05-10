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

# Iterator over medium subfields (of type F_q²)
# The elements are iterated in the order 0, 1, ..., q-1, x, 1 + x, 2 + x,
# ..., (q-1) + (q-1)x, where x is the generator of F_q²

function Base.start(::Nemo.FqNmodFiniteField)
    return (0,0)
end

function Base.next(F::Nemo.FqNmodFiniteField, state::Tuple{Int, Int})
    q = F.p - 1
    if state[1] < q
        nex = (state[1] + 1, state[2])
    else
        nex = (0, state[2] + 1)
    end
    return (state[1]+state[2]*gen(F), nex)
end

function Base.done(F::Nemo.FqNmodFiniteField, state::Tuple{Int, Int})
    return state[2] == F.p
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
