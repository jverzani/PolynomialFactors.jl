using PolynomialFactors
using Polynomials
using Base.Test


## utils
println("Testing utils.jl")

## nextprime
@test PolynomialFactors.nextprime(4) == 5
@test PolynomialFactors.nextprime(400) == 401
@test PolynomialFactors.nextprime(big(400)) == 401

## EEA
a, b = 2*3*7, 3*7*9
rs, ss, ts = PolynomialFactors.EEA(a, b)
@test reduce(&, [rs[i] - (ss[i] * a + ts[i] * b) == 0 for i in eachindex(rs)])


## bezout
g,u,v = PolynomialFactors.bezout(a,b)
@test u*a + v*b == g


## Chinese remainer theorem
ms = [3,5,7]
vs = [2,3,2]
a = PolynomialFactors.crt(ms, vs)
@test reduce(&, [mod(a, m) == v for (m,v) in zip(ms,vs)])

a = 12345
ms = Int[11,  13,  17,  19,  23,  29,  31,  37]
vs = Int[mod(a, m) for m in ms]
b = PolynomialFactors.crt(ms, vs)
@test a == b

a = big(123456789)
ms = BigInt[101, 103, 107, 109, 113, 127, 131, 137, 139, 149]
vs = BigInt[mod(a, m) for m in ms]
b = PolynomialFactors.crt(ms, vs)
@test a == b

