################################################################################
#
#   pglCosets.jl : Generating the cosets
#
################################################################################

export pglCosets
"""
    pglCosets(g::RingElem)

Compute the coset representatives of PGL(F_q²)/PGL(F_q).

This algorithm is due to Jincheng Zhuang and Qi Cheng **[3]**, see References in
the module documentation for more details.
"""
function pglCosets(g::RingElem)
    Fq2 = parent(g)
    d = div(degree(Fq2), 2)
    z = string("z", d)
    charac::Int = characteristic(Fq2)
    Fq = FiniteField(charac, d, z)[1]
    Fqx = nonZeroElements(Fq)
    img = findImg(Fq2, Fq)
    MM, piv = projectFindInv(Fq2, Fq)
    q::Int = length(Fq)
    R = zeros(Fq2, 5, q)
    MS = MatrixSpace(Fq2, 2, 2)
    M = MS()
    A = Array{typeof(M), 1}()

    # We compute a table with containing at most q+1-th root
    # for each element in F_q, these roots are taken in F_q²
    for y in Fq2
        t = y^(q+1)
        i = indexin(Fq, projectLinAlg(Fq, t, MM, piv))
        #        i = coeff(t, 0) + q*coeff(t, 1) + 1 # Is coeff(t, 1) always
        #        equal to zero ? (probably)

        for j in 1:5
            if R[j, i] == y
                break
            elseif R[j, i] == 0
                R[j, i] = y
                break
            end
        end
    end

    # STEP 1: We add cosets representatives of the form
    # [1, x]
    # [y, 1]
    # with x, y in F_q²\F_q and xy ≠ 1 and where x and y were chosen in a way
    # that we have to do only O(q³) steps instead of O(q⁴).
    M[1, 1], M[2, 2] = Fq2(1), Fq2(1)
    for v in Fqx
        for w in Fq2
            ι = inv(embed(Fq2, v, img))
            t = (ι*w^q)^(q+1)-ι
            i = indexin(Fq, projectLinAlg(Fq, t, MM, piv))
#            i = coeff(t, 0) + q*coeff(t, 1) + 1
            if i != 1
                for j in 1:5
                    r = R[j, i]
                    if r != 0
                        y = ι*w^q + r
                        x = -embed(Fq2, v, img)*y + w + w^q
                        if x*y != 1 && x^q != x && y^q != y
                            M[1, 2], M[2, 1] = x, y
                            push!(A, deepcopy(M))
                            break
                        end
                    else
                        break
                    end
                end
            else
                y = ι*w^q
                x = -embed(Fq2, v, img)*y + w + w^q
                if x*y != 1 && x^q != x && y^q != y
                    M[1, 2], M[2, 1] = x, y
                    push!(A, deepcopy(M))
                end
            end
        end
    end

    # STEP 2: We add cosets representatives of the form
    # [1,  a]
    # [g, bg]
    # with a, b in F_q*, g in F_q²\F_q, and a ≠ b
    M[2, 1] = g
    for a in Fqx
        for b in Fqx
            if a != b
                M[1, 2] = embed(Fq2, a, img)
                M[2, 2] = embed(Fq2, b, img)*g
                push!(A, deepcopy(M))
            end
        end
    end

    # STEP 3: We add cosets representatives of the form
    # [0,  1]
    # [g, ag]
    # with a in F_q
    M[1, 1] = Fq2(0)
    M[1, 2] = Fq2(1)
    for a in Fq
        M[2, 2] = embed(Fq2, a, img)*g
        push!(A, deepcopy(M))
    end
 
    # STEP 4: We add cosets representatives of the form
    # [     0,  1]
    # [1 + ag, bg]
    # with a, b in F_q
    for a in Fq
        for b in Fq 
            M[2, 1] = 1 + embed(Fq2, a, img)*g
            M[2, 2] = embed(Fq2, b, img)*g
            push!(A, deepcopy(M))
        end
    end
                
    # STEP 5: We add cosets representatives of the form
    # [  1, 0]
    # [ ag, g]
    # with a in F_q
    M[1, 1] = Fq2(1)
    M[1, 2] = Fq2(0)
    M[2, 2] = g
    for a in Fq
        M[2, 1] = embed(Fq2, a, img)*g
        push!(A, deepcopy(M))
    end

    # STEP 6: We add cosets representatives of the form
    # [  1,      0]
    # [ ag, 1 + bg]
    # with a, b in F_q
    for a in Fq
        for b in Fq
            M[2, 1] = embed(Fq2, a, img)*g
            M[2, 2] = 1 + embed(Fq2, b, img)*g
            push!(A, deepcopy(M))
        end
    end

    return A
end
