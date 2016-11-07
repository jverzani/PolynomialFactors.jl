using PolynomialFactors
using Base.Test

using Polynomials
PF = PolynomialFactors

println("Testing factor, factormod")

## println("Test distinct degree")
## ## ## distinct degree
## x = variable(PF.GF{3,1})
## f = x * (x+1) * (x^2+1) * (x^2 + x + 2)
## fs = PF.distinct_degree_factorization(f)
## @test all(sort(fs, by=PF.degree) .== [x^2+x, x^4 + x^3 + x + 2])

## ## ## distinct degree factorization over GF{p,1} (slower)
## x = variable(PF.GF{3,1})
## f = x^8 + x^7 - x^6 + x^5 -x^3 - x^2 - x
## fs = PF.distinct_degree_factorization(f)
## @test all(sort(fs, by=degree) .== [x, 1+2x+x^3, x^4 + x^3 + x - 1])


## ## for p in [3,11,17], d in [1,3,11]
## ##     x = variable(GF{p, d})
## ##     f = x^8 + x^7 - x^6 + x^5 -x^3 - x^2 - x
## ##     fs = PF.distinct_degree_factorization(f)
## ##     @test prod(fs) - f == zero(x)
## ## end

println("Test factor over Poly{Int}")
## test of factoring over Z[x]
x = variable(Int)
f = (x-1)*(x-2)*(x-3)
U = factor(f)
@test prod(collect(keys(U))) - f == zero(x)

f = (x-1)*(x-2)^2*(x-3)^3
U = factor(f)
@test U[x-3] == 3

f = (x-2)*(3x-4)^4*(6x-7)^8
U = factor(f)
@test U[6x-7] == 8

f = (x^5 - x - 1)
U = factor(f)
@test U[f] == 1


f = x^4
U = factor(f)
@test U[x] == 4

d = Dict(x-1 => 3, 2x-3=>4, x^2+x+1=>3)
f = prod([k^v for (k,v) in  d])
U = factor(f)
for (k,v) in d
    @test U[k] == v
end

println("Test factor over Poly{BigInt}")
## BigInt
## issue #40 in Roots.jl
x = variable(BigInt)
f = x^2 - big(2)^256
U = factor(f)
@test U[x - big(2)^128] == 1


p = x^15 - 1
@test length(factor(p)) == 4

p = 1 + x^3 + x^6 + x^9 + x^12
@test length(factor(p)) == 2


## Wilkinson (good out to 50 or so, then issues)
W(n) = prod([x-i for i in 1:20])
U = factor(W(20))
@test U[x-5] == 1


## Swinnerton-Dyer Polys are slow to resolve, as over `p` they factor into linears, but over Z are irreducible.
## so the "fish out" step exhausts all possibilities.
S1 = x^2 - 2	
U = factor(S1)
@test U[S1] == 1

S2 = x^4 - 10*x^2 + 1
U = factor(S2)
@test U[S2] == 1

S3 = x^8 - 40x^6 + 352x^4 - 960x^2 + 576
U = factor(S3)
@test U[S3] == 1


## Cyclotomic polys are irreducible over Z[x] too (https://en.wikipedia.org/wiki/Cyclotomic_polynomial)
C5 = x^4 + x^3 + x^2 + x + 1
U = factor(C5)
@test U[C5] == 1

C10 = x^4 - x^3 + x^2 -x + 1
U = factor(C10)
@test U[C10] == 1

C15 = x^8 - x^7 + x^5 - x^4 + x^3 - x + 1
U = factor(C15)
@test U[C15] == 1

C25 = x^20 + x^15 + x^10 + x^5 + 1
U = factor(C25)
@test U[C25] == 1

println("Test factor over Poly{Rational{BigInt}}")
## Rational
x = variable(Rational{Int})
f = (x - 1//2)^3 * (x-3//4)^4
U = factor(f)
@test U[-1 + 2x] == 3


println("Test rational_roots")
### Rational roots
## Wilkinson
x = variable(BigInt)
V = PolynomialFactors.rational_roots(W(20))
@test all(V .== 1:20)

f = (2x-3)^4 * (5x-6)^7
V = PolynomialFactors.rational_roots(f)
@test 3//2 in V
@test 6//5 in V

println("Test factormod")
## factormod
x = variable(BigInt)

C10 = x^4 - x^3 + x^2 -x + 1
U = PolynomialFactors.factormod(C10, 5)
@test U[1+x] == 4

C25 = x^20 + x^15 + x^10 + x^5 + 1
U = PolynomialFactors.factormod(C25, 5)
@test U[x-1] == 20

U = PolynomialFactors.factormod(x^4 + 1, 5)
@test U[x^2 + 2] == 1
@test U[x^2 - 2] == 1
