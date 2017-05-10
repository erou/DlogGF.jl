################################################################################
#
#   bgjt.jl : functions for the BGJT algorithm
#
################################################################################

# Flint functions

function rrefMod!(M::Nemo.fmpz_mat, n::Nemo.fmpz)
#    perm::Array{Int, 1} = collect(1:rows(M))
    perm = C_NULL
    rank = ccall((:fmpz_mat_rref_mod, :libflint), Cint, (Ptr{Int}, Ptr{fmpz_mat},
                                                  Ptr{fmpz}), perm, &M, &n)
    return M, rank, perm
end

function rrefMod!(M::Nemo.fmpz_mat, d::Integer)
    n = Nemo.fmpz(d) 
#    perm::Array{Int, 1} = collect(1:rows(M))
    perm = C_NULL
    rank = ccall((:fmpz_mat_rref_mod, :libflint), Cint, (Ptr{Int}, Ptr{fmpz_mat},
                                                  Ptr{fmpz}), perm, &M, &n)
    return M, rank, perm
end


function rrefMod(M::Nemo.fmpz_mat, n::Nemo.fmpz)
    N = deepcopy(M)
    M, rank, perm = rrefMod!(N, n)
    return N, rank, perm
end

function rrefMod(M::Nemo.fmpz_mat, n::Integer)
    N = deepcopy(M)
    M, rank, perm = rrefMod!(N, n)
    return N, rank, perm
end

# Julia functions

export subMatrix
"""
    subMatrix(M::MatElem, nrow::Integer, ncol::Integer)

Return the submatrix consisting of the first `nrow` rows and `ncol` colums of
`M`.
"""
function subMatrix(M::MatElem, nrow::Integer, ncol::Integer)

    # We create the matrix subspace
    S = MatrixSpace(parent(M[1,1]), nrow, ncol)

    # We create a new matrix
    sub = S()
    
    # And we copy the entries of the given matrix
    for j in 1:ncol
        for i in 1:nrow
            sub[i, j] = M[i, j]
        end
    end
    return sub
end

export pivots
"""
    pivots(M::MatElem)

Find `r` pivots in the row reduced echelon form matrix `M`.
"""
function pivots(M::MatElem, r::Int = 0)

    # There is as many pivots as the rank of 
    if r == 0
        r = rank(M)
    end

    # We set an array with the coordinates of the pivots
    piv = Array(Int, r)
    c = 1

    # And we find these coordinates
    for i in 1:r
        while M[i, c] == 0
            c += 1
        end
        piv[i] = c
    end
    return piv
end
