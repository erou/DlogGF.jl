using Nemo, DlogGF, Base.Test

function testRandomSuite()
    print("randomElem, randomList, randomPolynomial... ")

    F, x = FiniteField(5, 2, "x")

    @test parent(randomElem(F)) == F
    @test length(randomList(F, 10)) == 10
    @test parent(randomList(F, 5)[1]) == F

    R, T = PolynomialRing(F, "T")

    @test degree(randomPolynomial(R, 34)) == 34
    @test parent(randomPolynomial(R, 34)) == R

    println("PASS")
end

function testSmsrField()
    print("smsrField... ")

    K = smsrField(5, 4)

    @test K.cardinality == 5^8
    @test length(factor(K.definingPolynomial)) == 1
    @test K.characteristic == 5
    @test K.extensionDegree == 4

    println("PASS")
end

function testPglUnperfect()
    print("pglUnperfect... ")

    F, x = FiniteField(5, 2, "x")
    L = pglUnperfect(x)

    @test parent(L[12][2,2]) == F
    @test L[27][1,1] == 1

    boo = true
    for y in L
        if rank(y) != 2
            boo = false
        end
    end

    @test boo

    println("PASS")
end

function testHomogeneEq()
    print("homogene, makeEquation, fillMatrixBGJT!... ")
    K = smsrField(5, 5, 1, true)
    F = base_ring(K.h0)
    x = gen(F)
    R, T = PolynomialRing(F, "T")
    P = (3)*T^3+(x+3)*T^2+(3*x+1)*T+(4*x+1)
    m = pglUnperfect(x)[8]
    polDef = K.definingPolynomial

    @test homogene(T, T^2, T^3) == T^2
    @test homogene(T - 2, T^2, T^3) == T^2 - 2*T^3
    @test homogene(R(x), T^2, T^3) == x^5

    tmp = R()
    for j in 0:degree(P)
        tmp += coeff(P, j)^5*T^(5*j)
    end

    tmp %= polDef

    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = ((a^5*tmp+b^5)*(c*P+d)-(a*P+b)*(c^5*tmp+d^5))%polDef
    tmp2 = makeEquation(m, P, K.h0, K.h1)*gcdinv(K.h1,polDef)[2]^3
    tmp2 %= polDef
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 5^2+1, 1)
    M = S()
    u = fillMatrixBGJT!(M, 1, m, F)
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


    P = T^3 + (x+1)*T^2 +4*x*T+3

    K = smsrField(17, 17, 1, true)
    F = base_ring(K.h0)
    x = gen(F)
    R, T = PolynomialRing(F, "T")
    polDef = K.definingPolynomial
    P = (14*x+1)*T^5+(16*x+6)*T^4+(4*x+10)*T^3+(11*x+6)*T^2+(2*x+2)*T+(8*x+16)
    tmp = R()
    for j in 0:degree(P)
        tmp += coeff(P, j)^17*T^(17*j)
    end

    tmp %= polDef
    m = pglUnperfect(x)[19]
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = ((a^17*tmp+b^17)*(c*P+d)-(a*P+b)*(c^17*tmp+d^17))%polDef
    tmp2 = makeEquation(m, P, K.h0, K.h1)*gcdinv(K.h1,polDef)[2]^5
    tmp2 %= polDef
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 17^2+1, 1)
    M = S()
    u = fillMatrixBGJT!(M, 1, m, F)
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

    P = (5*x+16)*T^15+(10*x+1)*T^14+(6*x+4)*T^13+(15*x+15)*T^12+(7*x+6)*T^11+(12*x+12)*T^10+(5*x+10)*T^9+(12*x+3)*T^8+(15*x+2)*T^7+(9*x+11)*T^6+(15*x+4)*T^5+(13*x+11)*T^4+(9*x+2)*T^3+(10*x+2)*T^2+(14*x+13)*T+(x)
   tmp = R()
    for j in 0:degree(P)
        tmp += coeff(P, j)^17*T^(17*j)
    end

    tmp %= polDef
    m = pglUnperfect(x)[19]
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = ((a^17*tmp+b^17)*(c*P+d)-(a*P+b)*(c^17*tmp+d^17))%polDef
    tmp2 = makeEquation(m, P, K.h0, K.h1)*gcdinv(K.h1,polDef)[2]^17
    tmp2 %= polDef
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 17^2+1, 1)
    M = S()
    u = fillMatrixBGJT!(M, 1, m, F)
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

    @test isSmooth(P, 2) == false
    @test isSmooth(P, 6) == true
    @test isSmooth(T, 1) == true

    println("PASS")
end

function testFactorsList()
    print("factorsList... ")

    F, x = FiniteField(5, 2, "x")
    R, T = PolynomialRing(F, "T")
    L = factorsList(T)

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

    K = smsrField(13, 13, 1, true)
    g = K.gen
    c = K.cardinality
    defPol = K.definingPolynomial

    @test pohligHellmanPrime(c, 3, g, powmod(g, 5, defPol), defPol) == (2, 3)
    @test pohligHellmanPrime(c, 53, g, powmod(g, 5, defPol), defPol) == (5, 53)
    @test pohligHellmanPrime(c, 53, g, powmod(g, 85, defPol), defPol) == (32, 53)
    @test pohligHellmanPrime(c, 2, g, powmod(g, 7, defPol), defPol) == (7, 8)
    @test pohligHellmanPrime(c, 2, g, powmod(g, 17, defPol), defPol) == (1, 8)
    @test pohligHellmanPrime(c, 7, g, powmod(g, 4, defPol), defPol) == (4, 7)
    @test pohligHellmanPrime(c, 7, g, powmod(g, 33, defPol), defPol) == (5, 7)
    @test pohligHellman(c, g, powmod(g, 147, defPol), defPol) == (147, 8904)
    @test pohligHellman(c, g, powmod(g, 5913, defPol), defPol) == (5913, 8904)
    @test pohligHellman(c, g, powmod(g, 81426, defPol), defPol) == (1290, 8904)

    K = smsrField(17, 17, 1, true)
    g = K.gen
    c = K.cardinality

    @test pohligHellmanPrime(c, 2, g, powmod(g, 10, defPol), defPol) == (10, 32)
    @test pohligHellmanPrime(c, 2, g, powmod(g, 14, defPol), defPol) == (14, 32)
    @test pohligHellmanPrime(c, 3, g, powmod(g, 4, defPol), defPol) == (4, 9)
    @test pohligHellmanPrime(c, 3, g, powmod(g, 7, defPol), defPol) == (7, 9)
    @test pohligHellman(c, g, powmod(g, 814, defPol), defPol) == (238, 288)
    @test pohligHellman(c, g, powmod(g, 135, defPol), defPol) == (135, 288)
    @test pohligHellman(c, g, powmod(g, 79, defPol), defPol) == (79, 288)

    K = smsrField(7, 7, 1, true)
    g = K.gen
    c = K.cardinality
    @test pohligHellmanPrime(c, 29, g, powmod(g, 25, defPol), defPol) == (25, 29)
    @test pohligHellmanPrime(c, 29, g, powmod(g, 123, defPol), defPol) == (7, 29)
    @test pohligHellmanPrime(c, 3, g, powmod(g, 4, defPol), defPol) == (1, 3)
    @test pohligHellmanPrime(c, 3, g, powmod(g, 7, defPol), defPol) == (1, 3)
    @test pohligHellman(c, g, powmod(g, 514, defPol), defPol) == (514, 1392)
    @test pohligHellman(c, g, powmod(g, 2941, defPol), defPol) == (157, 1392)
    @test pohligHellman(c, g, powmod(g, 602, defPol), defPol) == (602, 1392)

    println("PASS")
end

function testIsGenerator()
    print("isGenerator, miniCheck... ")

    K = smsrField(3, 3, 1, true)
    g = K.gen
    c = K.cardinality
    R = parent(g)

    @test isGenerator(R(1), c) == false
    @test isGenerator(g, c) == true
    @test isGenerator(g^2, c) == false
    @test miniCheck(g, c) == true
    @test miniCheck(g^2, c) == false
    @test miniCheck(R(1), c) == false

    println("PASS")
end

function testDlogSmallField()
    print("dlogSmallField... ")

    K = smsrField(7, 7, 1, true)
    g = K.gen
    F = base_ring(g)
    R = parent(g)
    x = gen(F)
    q = K.characteristic
    k = K.extensionDegree
    defPol = K.definingPolynomial

    elem = R(1+x)
    d = dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem
    elem = R(x)
    d = dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem
    elem = R(2)
    d = dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem
    elem = R(x+2)
    d = dlogSmallField(q, k, g, elem, defPol)
    @test powmod(g, d, defPol) == elem

    println("PASS")
end

function testLinearDlog()
    print("linearDlog... ")

    K = smsrField(17, 17, 1, true)
    F = base_ring(K.h0)
    x = gen(F)
    g = K.gen
    k = K.extensionDegree
    h0 = K.h0
    h1 = K.h1
    card = K.cardinality
    T = gen(parent(h0))
    defPol = K.definingPolynomial

    dlogs = linearDlog(g, k, h0, h1, card, defPol)

    i = dlogs[T + 12*x+5]
    @test powmod(g, i, defPol) == T + 12*x+5

    i = dlogs[T + 3*x]
    @test powmod(g, i, defPol) == T + 3*x

    i = dlogs[T + 8*x+11]
    @test powmod(g, i, defPol) == T + 8*x+11

    i = dlogs[T + 10*x+1]
    @test powmod(g, i, defPol) == T + 10*x+1

    i = dlogs[T + x+4]
    @test powmod(g, i, defPol) == T + x+4

    println("PASS")
end

function testAll()

    testRandomSuite()
    testSmsrField()
    testPglUnperfect()
    testHomogeneEq()
    testIsSmooth()
    testFactorsList()
    testPohligHellman()
    testIsGenerator()
    testDlogSmallField()
    testLinearDlog()

    println("\nAll tests passed successfully.\n")
end


testAll()
