using Nemo, DlogGF, Base.Test

function testRandomSuite()
    print("randomElem, randomList, randomPolynomial, randomIrrPolynomial, randomSplitElem... ")

    F, x = FiniteField(5, 2, "x")

    @test parent(DlogGF.randomElem(F)) == F
    @test length(DlogGF.randomList(F, 10)) == 10
    @test parent(DlogGF.randomList(F, 5)[1]) == F

    R, T = PolynomialRing(F, "T")

    @test degree(DlogGF.randomPolynomial(R, 34)) == 34
    @test parent(DlogGF.randomPolynomial(R, 34)) == R

    @test length(factor(DlogGF.randomIrrPolynomial(R, 10))) == 1
    @test degree(DlogGF.randomIrrPolynomial(R, 10)) == 10
    @test parent(DlogGF.randomIrrPolynomial(R, 10)) == R

    @test length(factor(DlogGF.randomIrrPolynomial(R, 18))) == 1
    @test degree(DlogGF.randomIrrPolynomial(R, 18)) == 18
    @test parent(DlogGF.randomIrrPolynomial(R, 18)) == R

    q = 3^5
    G, y = FiniteField(3, 40, "y")
    S, U = PolynomialRing(G, "U")
    B = DlogGF.randomSplitElem(S, q)
    P = U^(q+1) - B*U + B
    fact = factor(P)
    boo = true

    for f in fact
        if degree(f[1]) != 1
            boo = false
            break
        end
    end

    @test boo

    println("PASS")
end

function testBgjtContext()
    print("bgjtContext... ")

    K = DlogGF.bgjtContext(3, 2, 4)
    F = FiniteField(3, 4, "z")[1]

    @test length(factor(K.definingPolynomial)) == 1
    @test characteristic(base_ring(K.h0)) == 3
    @test base_ring(K.h0) == F
    @test degree(K.definingPolynomial) == 2
    @test length(base_ring(K.h0)) == 81
    @test (K.h1*gen(parent(K.h0))^9-K.h0)%K.definingPolynomial == 0

    println("PASS")
end

function testHomogeneEq()
    print("homogene, makeEquation, fillMatrixBGJT!... ")

    F, z = FiniteField(3, 4, "z")
    R, T = PolynomialRing(F, "T")
    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((z^2+z+2)*T+(2*z^3),T^2+(z+1)*T,T^2+(z^3+2*z^2+2*z+2)*T+(z^3+2*z^2+z+1),T+(2*z^2+2*z+2))

    P = (2*z^3+2*z^2+z)*T^3+(2*z+2)*T^2+(2*z^3)*T+(z^3+z^2+2*z+1) 
    m = DlogGF.pglCosets(z)[8]
    polDef = K.definingPolynomial

    @test DlogGF.homogene(T, T^2, T^3) == T^2
    @test DlogGF.homogene(T - 2, T^2, T^3) == T^2 - 2*T^3
    @test DlogGF.homogene(R(z), T^2, T^3) == z^9

    tmp = R()
    for j in 0:degree(P)
        tmp += coeff(P, j)^9*T^(9*j)
    end

    tmp %= polDef

    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = ((a^9*tmp+b^9)*(c*P+d)-(a*P+b)*(c^9*tmp+d^9))%polDef
    tmp2 = DlogGF.makeEquation(m, P, K.h0, K.h1)*gcdinv(K.h1,polDef)[2]^3
    tmp2 %= polDef
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 9^2+1, 1)
    M = S()
    u = DlogGF.fillMatrixBGJT!(M, 1, m, F)
    i = 1
    tmp3=R(1)
    for y in F
        if M[i, 1] == 1
            tmp3 *= P-y
        end
        i += 1
    end
    tmp3 %= polDef
    @test tmp2 == u*tmp3

    F, z = FiniteField(17, 2, "z")
    R, T = PolynomialRing(F, "T")
    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((15*z+13)*T+(5*z+3),T^2+(9*z+6)*T,T^17+(2*z+10)*T^16+(7*z+5)*T^15+(4*z+4)*T^14+(9*z+12)*T^13+(7*z+4)*T^12+(15*z+7)*T^11+(8*z+9)*T^10+(6*z+10)*T^9+(10*z+14)*T^8+(7*z+8)*T^7+(6*z+11)*T^6+(16*z+4)*T^5+(6*z)*T^4+(2*z+16)*T^3+(3*z+6)*T^2+(14*z+6)*T+(7*z+10),T+(7*z+16))

    polDef = K.definingPolynomial

    P = (8*z+11)*T^5+(z+1)*T^4+(5*z+5)*T^3+(14*z+16)*T^2+(15*z+5)*T+(4*z+12)
    tmp = R()
    for j in 0:degree(P)
        tmp += coeff(P, j)^17*T^(17*j)
    end

    tmp %= polDef
    m = DlogGF.pglCosets(z)[19]
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = ((a^17*tmp+b^17)*(c*P+d)-(a*P+b)*(c^17*tmp+d^17))%polDef
    tmp2 = DlogGF.makeEquation(m, P, K.h0, K.h1)*gcdinv(K.h1,polDef)[2]^5
    tmp2 %= polDef
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 17^2+1, 1)
    M = S()
    u = DlogGF.fillMatrixBGJT!(M, 1, m, F)
    i = 1
    tmp3=R(1)
    for y in F
        if M[i, 1] == 1
            tmp3 *= P-y
        end
        i += 1
    end
    tmp3 %= polDef
    @test tmp2 == u*tmp3

    P = (15*z+6)*T^15+(12*z)*T^14+T^13+(6*z+4)*T^12+(16*z+10)*T^11+(4*z+11)*T^10+(4*z+16)*T^9+(10)*T^8+(5*z)*T^7+(14*z+8)*T^6+(10*z+16)*T^5+(4*z+2)*T^4+(12*z+15)*T^3+(11*z+14)*T^2+(14*z+15)*T+(9*z+3)

    tmp = R()
    for j in 0:degree(P)
        tmp += coeff(P, j)^17*T^(17*j)
    end

    tmp %= polDef
    m = DlogGF.pglCosets(z)[19]
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = ((a^17*tmp+b^17)*(c*P+d)-(a*P+b)*(c^17*tmp+d^17))%polDef
    tmp2 = DlogGF.makeEquation(m, P, K.h0, K.h1)*gcdinv(K.h1,polDef)[2]^15
    tmp2 %= polDef
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 17^2+1, 1)
    M = S()
    u = DlogGF.fillMatrixBGJT!(M, 1, m, F)
    i = 1
    tmp3=R(1)
    for y in F
        if M[i, 1] == 1
            tmp3 *= P-y
        end
        i += 1
    end
    tmp3 %= polDef
    @test tmp2 == u*tmp3

    println("PASS")
end

function testIsSmooth()
    print("isSmooth... ")

    F, x = FiniteField(5, 2, "x")
    R, T = PolynomialRing(F, "T")
    P = (x)*T^20+(2*x+2)*T^19+(x+1)*T^18+(3*x)*T^17+(4*x)*T^16+(3*x+4)*T^15+(x+3)*T^14+(2*x)*T^13+(4*x)*T^12+(x+4)*T^11+(3*x+1)*T^10+(4*x+3)*T^9+(4*x+3)*T^8+(2*x)*T^7+(x)*T^6+(2*x+2)*T^5+(x)*T^4+(4*x+2)*T^3+(2*x+3)*T^2+(2)*T

    @test DlogGF.isSmooth(P, 2) == false
    @test DlogGF.isSmooth(P, 6) == true
    @test DlogGF.isSmooth(T, 1) == true

    println("PASS")
end

function testFactorsList()
    print("factorsList... ")

    F, x = FiniteField(5, 2, "x")
    R, T = PolynomialRing(F, "T")
    L = DlogGF.factorsList(T)

    @test typeof(L) == DlogGF.FactorsList
    @test L.factors == [T]
    @test L.coefs == [1]

    push!(L, T^2, ZZ(2))

    @test L.factors == [T, T^2]
    @test L.coefs == [1, 2]

    push!(L, T, ZZ(3))

    @test L.factors == [T, T^2]
    @test L.coefs == [4, 2]

    deleteat!(L, 1)

    @test L.factors == [T^2]
    @test L.coefs == [2]

    println("PASS")
end

function testPohligHellman()
    print("pohligHellmanPrime, pohligHellman... ")

    F, z2 = FiniteField(13, 2, "z2")
    R, T2 = PolynomialRing(F, "T2")

    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((2*z2+8)*T2+(7*z2+10),T2^2+(3*z2+3)*T2,T2^13+(9*z2+12)*T2^12+(6*z2+6)*T2^11+(4*z2+8)*T2^10+(5*z2+7)*T2^9+(10*z2+7)*T2^8+(8*z2+11)*T2^7+(z2+1)*T2^6+(10*z2+3)*T2^5+(4*z2+10)*T2^4+(11*z2+8)*T2^3+(4*z2+2)*T2^2+(2*z2+5)*T2+(4*z2+8),T2+(9*z2+12))
    g = K.gen
    c = Nemo.fmpz(13)^26
    defPol = K.definingPolynomial

    @test DlogGF.pohligHellman(c, g, powmod(g, 147, defPol), defPol) == (147, 8904)
    @test DlogGF.pohligHellman(c, g, powmod(g, 5913, defPol), defPol) == (5913, 8904)
    @test DlogGF.pohligHellman(c, g, powmod(g, 81426, defPol), defPol) == (1290, 8904)

    F, z2 = FiniteField(17, 2, "z2")
    R, T2 = PolynomialRing(F, "T2")
    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((z2)*T2+(2*z2),T2^2+(15*z2+14)*T2,T2^17+(16*z2+3)*T2^16+(3*z2+2)*T2^15+(2)*T2^14+(z2+6)*T2^13+(2*z2+13)*T2^12+(6*z2+11)*T2^11+(3*z2+5)*T2^10+(9*z2)*T2^9+(3*z2+14)*T2^8+(11*z2+7)*T2^7+(5*z2+6)*T2^6+(12*z2+9)*T2^5+(12*z2)*T2^4+(3*z2+7)*T2^3+(14*z2+1)*T2^2+(16)*T2+(8),T2+(12*z2+13))
    g = K.gen
    c = Nemo.fmpz(17)^34
    defPol = K.definingPolynomial

    @test DlogGF.pohligHellman(c, g, powmod(g, 814, defPol), defPol) == (238, 288)
    @test DlogGF.pohligHellman(c, g, powmod(g, 135, defPol), defPol) == (135, 288)
    @test DlogGF.pohligHellman(c, g, powmod(g, 79, defPol), defPol) == (79, 288)

    F, z2 = FiniteField(7, 2, "z2")
    R, T2 = PolynomialRing(F, "T2")
    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((6*z2+2)*T2+(6*z2+3),T2^2+(z2+1)*T2,T2^7+(z2+3)*T2^6+(6)*T2^5+(3*z2+6)*T2^4+(2*z2)*T2^3+(4*z2+6)*T2^2+(6*z2+5)*T2+(4*z2+4),T2+(z2+3))
    g = K.gen
    c = Nemo.fmpz(7)^14
    defPol = K.definingPolynomial

    @test DlogGF.pohligHellman(c, g, powmod(g, 514, defPol), defPol) == (514, 1392)
    @test DlogGF.pohligHellman(c, g, powmod(g, 2941, defPol), defPol) == (157, 1392)
    @test DlogGF.pohligHellman(c, g, powmod(g, 602, defPol), defPol) == (602, 1392)

    println("PASS")
end

function testIsGenerator()
    print("isGenerator, miniCheck... ")

    F, z2 = FiniteField(3, 2, "z2")
    R, T2 = PolynomialRing(F, "T2")
    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((z2)*T2+(2*z2+2),T2^2+T2,T2^3+(z2+2)*T2^2+(2*z2)*T2+(2*z2),T2+(2*z2+2))
    g = K.gen
    c = 3^6
    defPol = K.definingPolynomial

    @test DlogGF.isGenerator(R(1), c, defPol) == false
    @test DlogGF.isGenerator(g, c, defPol) == true
    @test DlogGF.isGenerator(g^2, c, defPol) == false
    @test DlogGF.miniCheck(g, c, defPol) == true
    @test DlogGF.miniCheck(g^2, c, defPol) == false
    @test DlogGF.miniCheck(R(1), c, defPol) == false

    println("PASS")
end

function testDlogSmallField()
    print("dlogSmallField... ")

    F, z2 = FiniteField(7, 2, "z2")
    R, T2 = PolynomialRing(F, "T2")

    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((5*z2)*T2+(2*z2+2),T2^2+(5*z2+5)*T2,T2^7+(6*z2+6)*T2^6+(3*z2+3)*T2^5+(3)*T2^4+(2)*T2^3+(2*z2+4)*T2^2+(2*z2)*T2+(z2+6),T2+(2*z2+5))
    g = K.gen
    q::Int = sqrt(length(F))
    defPol = K.definingPolynomial
    k = degree(defPol)

    elem = R(1+z2)
    d = DlogGF.dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem
    elem = R(z2)
    d = DlogGF.dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem
    elem = R(2)
    d = DlogGF.dlogSmallField(q, k, g, elem, defPol)
    @test DlogGF.powmod(g, d, defPol) == elem
    elem = R(z2+2)
    d = DlogGF.dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem

    println("PASS")
end

function testPglCosets()
    print("pglCosets... ")

    F, x = FiniteField(5, 2, "x")
    
    cosets = DlogGF.pglCosets(x)

    @test length(cosets) >= 5^3 + 5

    @test parent(cosets[8][1, 2]) == F

    boo = true

    for a in cosets
        if rank(a) != 2
            boo = false 
        end
    end

    @test boo

    println("PASS")
end


function testLinearDlog()
    print("linearDlog, dlogBGJT... ")

    F, z = FiniteField(17, 2, "z")
    R, T = PolynomialRing(F, "T")
    K = DlogGF.BgjtContext{Nemo.fq_nmod_poly}((10*z+6)*T+(5*z),T+(11*z+12),T^17+(3*z+14)*T^16+(6*z+15)*T^15+(14*z+4)*T^14+(3*z+4)*T^13+(z+12)*T^12+(14)*T^11+(7*z+11)*T^10+(6*z+3)*T^9+(8*z+14)*T^8+(10*z+16)*T^7+(16*z)*T^6+(6*z+10)*T^5+(3*z+11)*T^4+(13*z+9)*T^3+(3*z+7)*T^2+(11*z+1)*T+(z+5),T+(11*z+9))

    g = K.gen
    h0 = K.h0
    h1 = K.h1
    defPol = K.definingPolynomial
    k = degree(defPol)
    card = length(F)^k

    dlogs = DlogGF.linearDlog(g, k, h0, h1, card, defPol)

    i = dlogs[T + 12*z+5]
    @test powmod(g, i, defPol) == T + 12*z+5

    i = dlogs[T + 3*z]
    @test powmod(g, i, defPol) == T + 3*z

    i = dlogs[T + 8*z+11]
    @test powmod(g, i, defPol) == T + 8*z+11

    i = dlogs[T + 10*z+1]
    @test powmod(g, i, defPol) == T + 10*z+1

    i = dlogs[T + z+4]
    @test powmod(g, i, defPol) == T + z+4

    P = T^2+(9)*T+(10*z+6) 
    d = DlogGF.dlogBGJT(P, K, dlogs)
    @test powmod(K.gen, d, defPol) == P

    P = T^2+(8*z+7)*T+(16*z+11)
    d = DlogGF.dlogBGJT(P, K, dlogs)
    @test powmod(K.gen, d, defPol) == P

    P = T^2+(z+7)*T+(13*z+12)
    d = DlogGF.dlogBGJT(P, K, dlogs)
    @test powmod(K.gen, d, defPol) == P

    P = T^2+(4*z+15)*T+(6)
    d = DlogGF.dlogBGJT(P, K, dlogs)
    @test powmod(K.gen, d, defPol) == P

    println("PASS")
end

function testGkzContext()
    print("gkzContext... ")

    K = DlogGF.gkzContext(3, 5, 10)
    F, z5 = FiniteField(3, 5, "z5")

    @test length(factor(K.definingPolynomial)) == 1
    @test characteristic(base_ring(K.h0)) == 3
    @test base_ring(K.h0) == F
    @test degree(K.definingPolynomial) == 10

    println("PASS")
end

function testAscent()
    print("ascent... ")

    F3_5, z5 = FiniteField(3, 5, "z5")
    R3_5, T = PolynomialRing(F3_5, "T5")
    P = (z5^3+z5^2)*T^16+(z5^3+z5^2+2*z5+2)*T^15+(2*z5^4+2*z5^3+z5+1)*T^14+(2*z5^4+2*z5^2+2*z5)*T^13+(2*z5^4+2*z5^2+z5+2)*T^12+(z5^4+z5^3+z5^2+z5+2)*T^11+(z5^4+z5^2+z5)*T^10+(2*z5^2+2)*T^9+(2*z5^3+2*z5+1)*T^8+(z5^3+2*z5^2+2*z5+2)*T^7+(2*z5^4+z5^2+2*z5+1)*T^6+(z5^4+z5^3+z5^2+z5+2)*T^5+(2*z5^3+2*z5+1)*T^4+(z5^4+2*z5^3+z5^2+1)*T^3+(2*z5^4+2*z5^3+z5+2)*T^2+(2*z5^4+2*z5^3)*T+(2*z5^2)
    Q = DlogGF.ascent(P)

    F3_10, z10 = FiniteField(3, 10, "z10")
    F3_20, z20 = FiniteField(3, 20, "z20")
    F3_40, z40 = FiniteField(3, 40, "z40")

    R3_10 = PolynomialRing(F3_10, "T10")[1]
    R3_20 = PolynomialRing(F3_20, "T20")[1]
    R3_40 = PolynomialRing(F3_40, "T40")[1]


    @test length(factor(Q)) == 1
    @test DlogGF.embedPoly(R3_40, DlogGF.embedPoly(R3_20, DlogGF.embedPoly(R3_10, P))) % Q == 0 
    
    P = (2*z5^4+2*z5)*T^16+(z5^3+z5+2)*T^15+(2*z5^4+2*z5^3+2*z5^2+2*z5+2)*T^14+(2*z5^4+z5^3+2*z5^2+z5)*T^13+(2*z5^4+z5^2+1)*T^12+(2*z5^4+2*z5^3+2*z5^2+z5)*T^11+(2*z5^3+z5^2+2)*T^10+(z5^4+2*z5^3+2*z5^2+z5+1)*T^9+(2*z5^4+z5^2)*T^8+(2*z5)*T^7+(2*z5^4+z5^2+2*z5+1)*T^6+(2*z5^4+2*z5)*T^5+(2*z5^4+2*z5^3)*T^4+(2*z5^4+z5^3+2*z5^2+2*z5)*T^3+(z5^3+2)*T^2+(2*z5^4+2*z5^3+1)*T+(z5^4+z5^3+z5^2+2*z5+1)
    Q = DlogGF.ascent(P)

    @test length(factor(Q)) == 1
    @test DlogGF.embedPoly(R3_40, DlogGF.embedPoly(R3_20, DlogGF.embedPoly(R3_10, P))) % Q == 0 

    println("PASS")
end

function testLatticeBasis()
    print("latticeBasis... ")

    F, z5 = FiniteField(3, 5, "z5")
    R, T = PolynomialRing(F, "T")
    h0 = (2*z5+2)*T+(2*z5^4+z5^3+2*z5^2+z5)
    h1 = T^2+(2*z5^4+z5+1)*T
    Q = (2*z5^4+2*z5^3+2*z5^2+z5+2)*T^2+(2*z5^4+2*z5^3+z5+2)*T+(2*z5^3+z5^2+2*z5+1)
    u0, u1, v0, v1 = DlogGF.latticeBasis(Q, h0, h1)

    @test ((T+v0)*h0+(v1)*h1)%Q == 0
    @test ((u0)*h0+(T+u1)*h1)%Q == 0

    Q = (z5^4+2*z5^3+z5^2+2*z5+2)*T^2+(z5^4+2*z5^2+z5+2)*T+(2*z5^3+z5^2)
    u0, u1, v0, v1 = DlogGF.latticeBasis(Q, h0, h1)

    @test ((T+v0)*h0+(v1)*h1)%Q == 0
    @test ((u0)*h0+(T+u1)*h1)%Q == 0

    Q = (z5^4+1)*T^2+(2*z5^2+z5)*T+(2*z5^3+z5^2)
    u0, u1, v0, v1 = DlogGF.latticeBasis(Q, h0, h1)

    @test ((T+v0)*h0+(v1)*h1)%Q == 0
    @test ((u0)*h0+(T+u1)*h1)%Q == 0

    println("PASS")
end

function testProject()
    print("projectLinAlg, projectLinAlgPoly... ")

    F3_5, z5 = FiniteField(3, 5, "z5")
    F3_20, z20 = FiniteField(3, 20, "z20")
    img = DlogGF.findImg(F3_20, F3_5)

    a = z5^2+z5+1
    b = z5^4+2*z5^2+2
    c = z5^4+z5^3+z5^2+z5+1
    d = 2*z5^4+z5^3+z5^2+2*z5
    f = z5^4+z5^3+2*z5^2+2

    M, piv = DlogGF.projectFindInv(F3_20, F3_5)
    
    @test DlogGF.projectLinAlg(F3_5, DlogGF.embed(F3_20, a, img), M, piv) == a
    @test DlogGF.projectLinAlg(F3_5, DlogGF.embed(F3_20, b, img), M, piv) == b
    @test DlogGF.projectLinAlg(F3_5, DlogGF.embed(F3_20, c, img), M, piv) == c
    @test DlogGF.projectLinAlg(F3_5, DlogGF.embed(F3_20, d, img), M, piv) == d
    @test DlogGF.projectLinAlg(F3_5, DlogGF.embed(F3_20, f, img), M, piv) == f

    R3_20, T20 = PolynomialRing(F3_20, "T20")
    F3_40, z40 = FiniteField(3, 40, "z40")
    R3_40, T40 = PolynomialRing(F3_40, "T40")

    P = (z20^19+z20^18+2*z20^17+2*z20^15+z20^13+2*z20^12+2*z20^11+2*z20^10+2*z20^9+2*z20^8+2*z20^6+z20^5+2*z20^3+z20^2+z20+1)*T20^5+(2*z20^19+z20^17+2*z20^15+z20^14+2*z20^13+z20^12+2*z20^11+z20^9+z20^6+z20^5+z20^4+z20^2+2*z20)*T20^4+(z20^19+2*z20^16+2*z20^14+z20^13+2*z20^12+z20^11+z20^10+z20^9+z20^8+2*z20^7+z20^5+2*z20^3+1)*T20^3+(z20^19+z20^16+2*z20^15+2*z20^14+2*z20^13+z20^11+z20^10+z20^8+2*z20+1)*T20^2+(z20^18+z20^17+z20^15+z20^14+2*z20^11+2*z20^10+z20^9+2*z20^8+2*z20^6+2*z20^4+z20^3+2*z20^2)*T20+(z20^18+z20^17+2*z20^16+z20^15+z20^13+z20^12+z20^11+z20^10+2*z20^9+2*z20^6+2*z20^5+2*z20^4+2*z20^3+z20+2)

   Q = (z20^18+2*z20^17+2*z20^16+2*z20^15+z20^14+z20^13+z20^12+z20^10+z20^8+2*z20^7+z20^5+z20^4+2*z20^3+z20+2)*T20^5+(z20^18+2*z20^15+z20^14+2*z20^11+2*z20^9+2*z20^7+z20^5+z20^4+2*z20^3+z20^2+2*z20)*T20^4+(z20^19+z20^18+z20^17+z20^15+2*z20^14+z20^12+z20^11+2*z20^10+2*z20^9+2*z20^8+z20^6+z20^5+z20^4)*T20^3+(z20^19+2*z20^18+z20^16+z20^15+2*z20^13+2*z20^12+z20^11+2*z20^8+2*z20^7+z20^4+z20^3+2*z20^2+2*z20+1)*T20^2+(z20^19+2*z20^18+z20^15+z20^14+2*z20^13+2*z20^11+2*z20^10+z20^9+z20^7+2*z20^6+z20^4+z20^3+2*z20^2+1)*T20+(z20^19+z20^17+z20^16+2*z20^15+z20^14+2*z20^13+2*z20^12+2*z20^9+z20^8+2*z20^7+z20^6+2*z20^5+2*z20^3+2*z20^2+2*z20+2)

  R = (2*z20^19+z20^18+2*z20^17+z20^15+2*z20^12+z20^9+z20^6+z20^4+z20^3+2*z20^2+2*z20)*T20^5+(z20^19+2*z20^18+2*z20^17+2*z20^16+2*z20^15+2*z20^14+2*z20^13+2*z20^11+z20^10+z20^9+z20^8+z20^7+z20^6+z20^3+2*z20^2+z20+1)*T20^4+(2*z20^19+2*z20^16+2*z20^15+2*z20^14+z20^13+2*z20^11+z20^8+z20^7+z20^5+2*z20^4+2*z20^3+z20^2+2*z20)*T20^3+(z20^18+z20^17+z20^15+z20^14+z20^12+2*z20^10+z20^8+z20^7+z20^6+z20^5+2*z20^4+z20^3+z20^2+2*z20)*T20^2+(z20^19+2*z20^18+z20^17+z20^15+2*z20^14+2*z20^13+2*z20^11+2*z20^10+z20^9+z20^8+2*z20^7+2*z20^6+z20^4+z20^3+z20+2)*T20+(z20^17+z20^16+2*z20^15+2*z20^14+z20^13+z20^11+2*z20^10+2*z20^9+2*z20^8+2*z20^7+z20^4+2*z20^3+z20+2)

  M, piv = DlogGF.projectFindInv(F3_40, F3_20)
  img = DlogGF.findImg(F3_40, F3_20)

  @test DlogGF.projectLinAlgPoly(R3_20, DlogGF.embedPoly(R3_40, P, img), M, piv) == P
  @test DlogGF.projectLinAlgPoly(R3_20, DlogGF.embedPoly(R3_40, Q, img), M, piv) == Q
  @test DlogGF.projectLinAlgPoly(R3_20, DlogGF.embedPoly(R3_40, R, img), M, piv) == R
 
    println("PASS")
end

function testOnTheFly()
    print("onTheFlyAbc, onTheFlyElimination... ")

    K = DlogGF.gkzContext(3, 3, 20)
    F3_3, z3 = FiniteField(3, 3, "z3")
    R3_3, T3 = PolynomialRing(F3_3, "T3")
    P = (2*z3^2)*T3^8+(2*z3^2+2*z3+1)*T3^7+(2*z3^2+2*z3+1)*T3^6+(2*z3^2+2*z3+2)*T3^5+(z3^2+z3)*T3^4+(2*z3)*T3^3+(z3+2)*T3^2+(2*z3^2+2*z3+2)*T3+(z3^2+2*z3+1)
    Q = DlogGF.ascent(P)
    R = parent(Q)
    T = gen(R)
    q = 3^3
    h0 = DlogGF.embedPoly(R, K.h0)
    h1 = DlogGF.embedPoly(R, K.h1)

    a, b, c = DlogGF.onTheFlyAbc(Q, h0, h1, q)

    ρ = T^(q+1) + a*T^q + b*T + c

    β = true
    for f in factor(ρ)
        if degree(f[1]) != 1
            β = false
            break
        end
    end

    @test β
    @test ((T+a)*h0+(b*T+c)*h1)%Q == 0

    P = (2*z3^2+z3+1)*T3^8+(z3^2+2*z3)*T3^7+(2*z3^2+z3+2)*T3^6+(z3^2+2*z3+1)*T3^5+(2*z3)*T3^4+(z3+2)*T3^3+(z3^2+z3)*T3^2+(2*z3^2+z3+2)*T3+(2*z3^2+1)
    Q = DlogGF.ascent(P)

    a, b, c = DlogGF.onTheFlyAbc(Q, h0, h1, q)

    ρ = T^(q+1) + a*T^q + b*T + c

    β = true
    for f in factor(ρ)
        if degree(f[1]) != 1
            β = false
            break
        end
    end

    @test β
    @test ((T+a)*h0+(b*T+c)*h1)%Q == 0

    P = (z3^2+2)*T3^8+(2*z3^2+1)*T3^7+(z3+2)*T3^5+(z3+1)*T3^4+(z3^2+2*z3+1)*T3^3+(2*z3^2)*T3^2+(z3^2+2*z3)*T3+(2)
    Q = DlogGF.ascent(P)

    a, b, c = DlogGF.onTheFlyAbc(Q, h0, h1, q)

    ρ = T^(q+1) + a*T^q + b*T + c

    β = true
    for f in factor(ρ)
        if degree(f[1]) != 1
            β = false
            break
        end
    end

    @test β
    @test ((T+a)*h0+(b*T+c)*h1)%Q == 0

    P = (z3^2+2*z3+1)*T3^8+(2*z3^2+z3)*T3^7+(z3+2)*T3^6+(z3^2+2*z3+2)*T3^5+(z3^2)*T3^4+(z3+1)*T3^3+(z3)*T3+(z3+1)
    Q = DlogGF.ascent(P)

    A = DlogGF.onTheFlyElimination(Q, h0, h1, q)
    product = h1
    for j in 1:(q+1)
        product *= A[j]
    end
    
    @test (product - A[end]*Q) % (h1*T^q-h0) == 0

    P = (2*z3^2+2*z3)*T3^8+(2*z3+1)*T3^7+(2*z3+1)*T3^6+(z3^2+z3+2)*T3^5+(z3+1)*T3^4+(2*z3+1)*T3^3+(2*z3)*T3^2+(2*z3+2)*T3+(2*z3^2+2)
    Q = DlogGF.ascent(P)

    A = DlogGF.onTheFlyElimination(Q, h0, h1, q)
    product = h1
    for j in 1:(q+1)
        product *= A[j]
    end
    
    @test (product - A[end]*Q) % (h1*T^q-h0) == 0

    println("PASS")
end

function testDescent()
    print("descentGKZ... ")

    K = DlogGF.gkzContext(3, 3, 20)
    q = 3^3
    F3_3, z3 = FiniteField(3, 3, "z3")
    R3_3, T3 = PolynomialRing(F3_3, "T3")
    H = K.h1*T3^q-K.h0


    P = T3^8+(z3+1)*T3^6+T3^5+(2*z3^2+z3+2)*T3^4+(z3^2+2*z3+1)*T3^3+(z3^2+z3)*T3^2+(2*z3^2)*T3+(2*z3)
    Q, t0, t1 = DlogGF.ascent(P, K.h0, K.h1)
    L = DlogGF.descentGKZ(Q, t0, t1, R3_3)
    product = one(R3_3)
    
    for j in 1:length(L)
        poly = L[j][1]
        coef = L[j][2]
        if coef < 0
            poly = gcdinv(poly, H)[2]
            coef = -coef
        end
        product = mulmod(product, poly^coef, H)
    end
    
    @test product == P

    println("PASS")
end

function testFactorBase()
    print("factorBaseDeg2... ")

    K = DlogGF.gkzContext(3, 3, 20)
    dlogs = DlogGF.factorBaseDeg2(K)

    R = parent(K.h0)
    X = gen(R)
    z = gen(base_ring(R))
    defPol = K.definingPolynomial

    P = X^2+(z^2+1)*X+(2*z^2+z+2)
    Q = X^2+(2)*X+(2*z+1)
    S = X^2+(2*z+1)
    T = X^2+(z^2+z+1)*X+(2*z^2+2*z)

    @test powmod(K.gen, dlogs[X], defPol) == X
    @test powmod(K.gen, dlogs[X+1], defPol) == X+1
    @test powmod(K.gen, dlogs[X+2], defPol) == X+2
    @test powmod(K.gen, dlogs[X+z], defPol) == X+z
    @test powmod(K.gen, dlogs[P], defPol) == P
    @test powmod(K.gen, dlogs[Q], defPol) == Q 
    @test powmod(K.gen, dlogs[S], defPol) == S
    @test powmod(K.gen, dlogs[T], defPol) == T

    println("PASS")
end

function testAll()

    testRandomSuite()
    testBgjtContext()
    testIsGenerator()
    testHomogeneEq()
    testIsSmooth()
    testFactorsList()
    testPohligHellman()
    testDlogSmallField()
    testPglCosets()
    testLinearDlog()
    testGkzContext()
    testAscent()
    testLatticeBasis()
    testProject()
    testOnTheFly()
    testDescent()
    testFactorBase()

    println("\nAll tests passed successfully.\n")
end

testAll()
