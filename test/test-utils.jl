using PolynomialFactors
using Polynomials
using Compat.Test


## utils
@testset "Testing utils.jl" begin

    ## nextprime
    @test PolynomialFactors.nextprime(4) == 5
    @test PolynomialFactors.nextprime(400) == 401
    @test PolynomialFactors.nextprime(big(400)) == 401
    
    ## XXX TODO: add more tests here
end
