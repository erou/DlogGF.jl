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

function testAll()

    testRandomSuite()

    println("\nAll tests passed successfully.\n")

end

testAll()
