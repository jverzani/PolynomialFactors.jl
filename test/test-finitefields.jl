using PolynomialFactors
using Base.Test

using Polynomials
PF = PolynomialFactors
Ideal = PF.Ideal

println("Testing Zn{p}, GF{p,d}")
## ModInt{p, false}
m = Zn{7}(3)
@test m + m == Zn{7}(6)
@test m + m + m == Zn{7}(2)
@test inv(m) * m == one(m)


x = Zn{5}(2)
@test x + x == Zn{5}(4)
@test 5x == zero(Zn{5})
@test -x == Zn{5}(5-2)
@test inv(x) == Zn{5}(3)



## Gf{p,d}
x = variable(Zn{5})
u = 1 + 2x + 3x^2
v = convert(GF{5,3}, u)
@test 5v == zero(GF{5,3})
@test v^(5^3 - 1) == one(GF{5,3})

m = GF{17, 11}(1)
@test m + m == GF{17, 11}(2)
@test inv(m) * m == one(m)



## irreducible
for p in [2,3,5,7,11,13,17,23,29,31], d in 1:10
        f = PF.find_irreducible_poly(p,d)
end


## gcd
for p in [2,3,5,7,11,13,17,23,29,31], d in [1,4,7]
    x = variable(GF{p,d})
    u = (x-1)*(x-2)*(x-3)
    v = (x-2)*(x-4)
    g = gcd(u, v)
    @test rem(g, (x-2)) == zero(x)
end


## modular gcd
x = variable(Zn{17})
f = (x-1)*(x-2)^2*(x-3)^3
g = gcd(f, f')
@test g == (x-2) * (x-3)^2

