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

    println("PASS")
end

function testHomogeneEq()
    print("homogene, makeEquation... ")
    F, x = FiniteField(5, 2, "x")
    R, T = PolynomialRing(F, "T")

    @test homogene(T, T^2, T^3) == T^2
    @test homogene(T - 2, T^2, T^3) == T^2 - 2*T^3
    @test homogene(R(x), T^2, T^3) == x^characteristic(F)

    P = T^3 + (x+1)*T^2 +4*x*T+3
    m = pglUnperfect(x)[8]

    @test degree(makeEquation(m, P, 3*x*T, T+x)) == degree(P)*(1 + 1)

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

    push!(L, T^2, 2)

    @test L.factors == [T, T^2]
    @test L.coefs == [1, 2]

    push!(L, T, 3)

    @test L.factors == [T, T^2]
    @test L.coefs == [4, 2]

    deleteat!(L, 1)

    @test L.factors == [T^2]
    @test L.coefs == [2]

    println("PASS")
end

function testPohligHellman()
    print("pohligHellmanPrime... ")

    K = smsrField(13, 13, 1, true)
    g = K.gen
    c = K.cardinality

    @test pohligHellmanPrime(c, 3, g, g^5) == 2
    @test pohligHellmanPrime(c, 53, g, g^5) == 5
    @test pohligHellmanPrime(c, 53, g, g^85) == 32
    @test pohligHellmanPrime(c, 2, g, g^7) == 7
    @test pohligHellmanPrime(c, 2, g, g^17) == 1
    @test pohligHellmanPrime(c, 7, g, g^4) == 4
    @test pohligHellmanPrime(c, 7, g, g^33) == 5

    K = smsrField(17, 17, 1, true)
    g = K.gen
    c = K.cardinality

    @test pohligHellmanPrime(c, 2, g, g^10) == 10
    @test pohligHellmanPrime(c, 2, g, g^14) == 14
    @test pohligHellmanPrime(c, 3, g, g^4) == 4
    @test pohligHellmanPrime(c, 3, g, g^7) == 7

    K = smsrField(7, 7, 1, true)
    g = K.gen
    c = K.cardinality

    @test pohligHellmanPrime(c, 29, g, g^25) == 25
    @test pohligHellmanPrime(c, 29, g, g^123) == 7
    @test pohligHellmanPrime(c, 3, g, g^4) == 1
    @test pohligHellmanPrime(c, 2, g, g^7) == 7

    println("PASS")
end

function testIsGenerator()
    print("isGenerator... ")

    K = smsrField(3, 3, 1, true)
    g = K.gen
    c = K.cardinality

    @test isGenerator(K.bigField(1), K.cardinality) == false
    @test isGenerator(g, c) == true
    @test isGenerator(g^2, c) == false

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

    println("\nAll tests passed successfully.\n")
end


testAll()
# TODO 
# tests of isGenerator
