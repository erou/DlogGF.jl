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
    @test base_ring(base_ring(K.bigField)) == K.mediumSubField
    @test characteristic(K.mediumSubField) == K.characteristic

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
    F = K.mediumSubField
    x = gen(F)
    R, T = PolynomialRing(F, "T")
    Q = K.bigField
    P = (3)*T^3+(x+3)*T^2+(3*x+1)*T+(4*x+1)
    m = pglUnperfect(x)[8]

    @test homogene(T, T^2, T^3) == T^2
    @test homogene(T - 2, T^2, T^3) == T^2 - 2*T^3
    @test homogene(R(x), T^2, T^3) == x^5

    tmp = Q()
    for j in 0:degree(P)
        tmp += Q(coeff(P, j)^5*T^(5*j))
    end
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = (a^5*tmp+b^5)*(c*P+d)-(a*P+b)*(c^5*tmp+d^5)
    tmp2 = makeEquation(m, P, K.h0, K.h1)*inv(Q(K.h1))^3
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 5^2+1, 1)
    M = S()
    u = fillMatrixBGJT!(M, 1, m, F)
    i = 1
    tmp3=Q(1)
    for y in F
        if M[i, 1] == 1
            tmp3 *= P-y
        end
        i += 1
    end
    @test tmp2 == u*tmp3


    P = T^3 + (x+1)*T^2 +4*x*T+3

    K = smsrField(17, 17, 1, true)
    F = K.mediumSubField
    x = gen(F)
    R, T = PolynomialRing(F, "T")
    Q = K.bigField
    P = (14*x+1)*T^5+(16*x+6)*T^4+(4*x+10)*T^3+(11*x+6)*T^2+(2*x+2)*T+(8*x+16)
    tmp = Q()
    for j in 0:degree(P)
        tmp += Q(coeff(P, j)^17*T^(17*j))
    end
    m = pglUnperfect(x)[19]
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = (a^17*tmp+b^17)*(c*P+d)-(a*P+b)*(c^17*tmp+d^17)
    tmp2 = makeEquation(m, P, K.h0, K.h1)*inv(Q(K.h1))^5
    @test tmp == tmp2

    S = MatrixSpace(ZZ, 17^2+1, 1)
    M = S()
    u = fillMatrixBGJT!(M, 1, m, F)
    i = 1
    tmp3=Q(1)
    for y in F
        if M[i, 1] == 1
            tmp3 *= P-y
        end
        i += 1
    end
    @test tmp2 == u*tmp3

    P = (5*x+16)*T^15+(10*x+1)*T^14+(6*x+4)*T^13+(15*x+15)*T^12+(7*x+6)*T^11+(12*x+12)*T^10+(5*x+10)*T^9+(12*x+3)*T^8+(15*x+2)*T^7+(9*x+11)*T^6+(15*x+4)*T^5+(13*x+11)*T^4+(9*x+2)*T^3+(10*x+2)*T^2+(14*x+13)*T+(x)
    tmp = Q()
    for j in 0:degree(P)
        tmp += Q(coeff(P, j)^17*T^(17*j))
    end
    m = pglUnperfect(x)[85]
    a, b, c, d = m[1,1], m[1,2], m[2,1], m[2,2]
    tmp = (a^17*tmp+b^17)*(c*P+d)-(a*P+b)*(c^17*tmp+d^17)
    tmp2 = makeEquation(m, P, K.h0, K.h1)*inv(Q(K.h1))^15
    @test tmp == tmp2

    M = S()
    u = fillMatrixBGJT!(M, 1, m, F)
    i = 1
    tmp3=Q(1)
    for y in F
        if M[i, 1] == 1
            tmp3 *= P-y
        end
        i += 1
    end
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

    @test pohligHellmanPrime(c, 3, g, g^5) == (2, 3)
    @test pohligHellmanPrime(c, 53, g, g^5) == (5, 53)
    @test pohligHellmanPrime(c, 53, g, g^85) == (32, 53)
    @test pohligHellmanPrime(c, 2, g, g^7) == (7, 8)
    @test pohligHellmanPrime(c, 2, g, g^17) == (1, 8)
    @test pohligHellmanPrime(c, 7, g, g^4) == (4, 7)
    @test pohligHellmanPrime(c, 7, g, g^33) == (5, 7)
    @test pohligHellman(c, g, g^147) == (147, 8904)
    @test pohligHellman(c, g, g^5913) == (5913, 8904)
    @test pohligHellman(c, g, g^81426) == (1290, 8904)

    K = smsrField(17, 17, 1, true)
    g = K.gen
    c = K.cardinality

    @test pohligHellmanPrime(c, 2, g, g^10) == (10, 32)
    @test pohligHellmanPrime(c, 2, g, g^14) == (14, 32)
    @test pohligHellmanPrime(c, 3, g, g^4) == (4, 9)
    @test pohligHellmanPrime(c, 3, g, g^7) == (7, 9)
    @test pohligHellman(c, g, g^814) == (238, 288)
    @test pohligHellman(c, g, g^135) == (135, 288)
    @test pohligHellman(c, g, g^79) == (79, 288)

    K = smsrField(7, 7, 1, true)
    g = K.gen
    c = K.cardinality

    @test pohligHellmanPrime(c, 29, g, g^25) == (25, 29)
    @test pohligHellmanPrime(c, 29, g, g^123) == (7, 29)
    @test pohligHellmanPrime(c, 3, g, g^4) == (1, 3)
    @test pohligHellmanPrime(c, 3, g, g^7) == (1, 3)
    @test pohligHellman(c, g, g^514) == (514, 1392)
    @test pohligHellman(c, g, g^2941) == (157, 1392)
    @test pohligHellman(c, g, g^602) == (602, 1392)

    println("PASS")
end

function testIsGenerator()
    print("isGenerator, miniCheck... ")

    K = smsrField(3, 3, 1, true)
    g = K.gen
    c = K.cardinality

    @test isGenerator(K.bigField(1), c) == false
    @test isGenerator(g, c) == true
    @test isGenerator(g^2, c) == false
    @test miniCheck(g, c) == true
    @test miniCheck(g^2, c) == false
    @test miniCheck(K.bigField(1), c) == false

    println("PASS")
end

function testDlogSmallField()
    print("dlogSmallField... ")

    K = smsrField(7, 7, 1, true)
    Q = K.bigField
    F = K.mediumSubField
    x = gen(F)
    g = K.gen
    q = K.characteristic
    k = K.extensionDegree

    elem = Q(1+x)
    d = dlogSmallField(q, k, g, elem)
    @test g^d == elem
    elem = Q(x)
    d = dlogSmallField(q, k, g, elem)
    @test g^d == elem
    elem = Q(2)
    d = dlogSmallField(q, k, g, elem)
    @test g^d == elem
    elem = Q(x^2)
    d = dlogSmallField(q, k, g, elem)
    @test g^d == elem

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

    println("\nAll tests passed successfully.\n")
end


testAll()
