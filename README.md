# PolynomialFactors

A package for factoring polynomials over the integers and rationals.

[![Build Status](https://travis-ci.org/jverzani/PolynomialFactors.jl.svg?branch=master)](https://travis-ci.org/jverzani/PolynomialFactors.jl)



For polynomials over the integers or rational numbers, this package provides

* a `factor` command to factor over the integers

* a `rational_roots` function to return the rational roots

* a `powermod` function to factor the polynomial over Z/pZ.

The implementation is based on the Cantor-Zassenhaus approach, as
detailed in Chapters 14 and 15 of the excellent text *Modern Computer Algebra* by von zer
Gathen and Gerhard.

There are technical limitations for large primes, so for large
problems, the factoring solutions in `SymPy.jl` or `Nemo.jl` would be
preferred. In general, if those are installed, they may be preferred,
but this package requires no additional external libraries.


Examples:

```
julia> using Polynomials, PolynomialFactors

julia> x = variable(Int)
Poly(x)

julia> factor((x-1)^2 * (x-3)^4 * (x-5)^6)
Dict{Polynomials.Poly{Int64},Int64} with 3 entries:
  Poly(-5 + x) => 6
  Poly(-3 + x) => 4
  Poly(-1 + x) => 2
```

Factoring over the rationals is really done over the integers:

```
julia> x = variable(Rational{Int})
Poly(x)

julia> factor( (1//2 - x)^2 * (1//3 - 1//4 * x)^5 )
Dict{Polynomials.Poly{Int64},Int64} with 2 entries:
  Poly(-1 + 2⋅x) => 2
  Poly(-4 + 3⋅x) => 5
```  


For some problems, big integers are necessary:

```
julia> x = variable(BigInt)
Poly(x)

julia> w = prod([x - i for i in 1:20]);

julia> rational_roots(w)'
1x20 Array{Rational{BigInt},2}:
 1//1  2//1  3//1  4//1  5//1  6//1  7//1  …  15//1  16//1  17//1  18//1  19//1  20//1
```

```
julia> factor(x^2 - big(2)^256)
Dict{Polynomials.Poly{BigInt},Int64} with 2 entries:
  Poly(-340282366920938463463… => 1
  Poly(3402823669209384634633… => 1
```  

Factoring over the field Z_p, p a prime, is also provided by `factormod`:

```
julia> factormod(x^4 + 1, 2)
Dict{Polynomials.Poly{PolynomialFactors.ModInt{2,true}},Int64} with 1 entry:
  Poly(mod(1,2) + mod(1,2)⋅x) => 4

julia> factormod(x^4 + 1, 5)
Dict{Polynomials.Poly{PolynomialFactors.ModInt{5,true}},Int64} with 2 entries:
  Poly(mod(2,5) + mod(1,5)⋅x^… => 1
  Poly(mod(-2,5) + mod(1,5)⋅x… => 1

```
