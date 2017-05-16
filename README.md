# PolynomialFactors

A package for factoring polynomials with integer or rational coefficients over the integers.

[![PolynomialFactors](http://pkg.julialang.org/badges/PolynomialFactors_0.4.svg)](http://pkg.julialang.org/?pkg=PolynomialFactors&ver=0.4)
[![PolynomialFactors](http://pkg.julialang.org/badges/PolynomialFactors_0.5.svg)](http://pkg.julialang.org/?pkg=PolynomialFactors&ver=0.5)
[![PolynomialFactors](http://pkg.julialang.org/badges/PolynomialFactors_0.5.svg)](http://pkg.julialang.org/?pkg=PolynomialFactors&ver=0.6)

Linux: [![Build Status](https://travis-ci.org/jverzani/PolynomialFactors.jl.svg?branch=master)](https://travis-ci.org/jverzani/PolynomialFactors.jl)
&nbsp;
Windows: [![Build Status](https://ci.appveyor.com/api/projects/status/github/jverzani/PolynomialFactors.jl?branch=master&svg=true)](https://ci.appveyor.com/project/jverzani/polynomialfactors-jl)



For polynomials over the integers or rational numbers, this package provides

* a `factor` command to factor into irreducible factors over the integers;

* a `rational_roots` function to return the rational roots;
 
* a `powermod` function to factor the polynomial over Z/pZ.

The implementation is based on the Cantor-Zassenhaus approach, as
detailed in Chapters 14 and 15 of the excellent text *Modern Computer Algebra* by von zer
Gathen and Gerhard and a paper by Beauzamy, Trevisan, and Wang.


The factoring solutions in `SymPy.jl` or `Nemo.jl` would be preferred,
in general, especially for larger problems (degree 30 or more, say) where the performance here is not good. However, this package
requires no additional external libraries. (PRs improving performance are most welcome.)


Examples:

```
julia> using Polynomials, PolynomialFactors

julia> p = poly([1,1,3,3,3,3,5,5,5,5,5,5])
Poly(1265625 - 5737500⋅x + 11306250⋅x^2 - 12877500⋅x^3 + 9505375⋅x^4 - 4818680⋅x^5 + 1728556⋅x^6 - 443800⋅x^7 + 81191⋅x^8 - 10348⋅x^9 + 874⋅x^10 - 44⋅x^11 + x^12)

julia> factor(p)
Dict{Polynomials.Poly{Int64},Int64} with 4 entries:
  Poly(-5 + x) => 6
  Poly(1)      => 1
  Poly(-3 + x) => 4
  Poly(-1 + x) => 2
```

As can be seen `factor` returns a dictionary whose keys are
irreducible factors of the polynomial `p` as `Polynomial` objects, the
values being their multiplicity. The degree $0$ polynomial is there so
that the original polynomial can be recovered as the product of
`[k^v for (k,v) in factor(p)]`.


Here we construct the polynomial in terms of a variable `x`:
```
julia> x = variable(Int)
Poly(x)

julia> factor((x-1)^2 * (x-3)^4 * (x-5)^6)
Dict{Polynomials.Poly{Int64},Int64} with 4 entries:
  Poly(-5 + x) => 6
  Poly(1)      => 1
  Poly(-3 + x) => 4
  Poly(-1 + x) => 2
```

Factoring over the rationals is really done over the integers, The
first step is to find a common denominator for the coefficients. The
constant polynomial term reflects this.

```
julia> x = variable(Rational{Int})
Poly(x)

julia> factor( (1//2 - x)^2 * (1//3 - 1//4 * x)^5 )
Dict{Polynomials.Poly{Rational{Int64}},Int64} with 3 entries:
  Poly(-1//995328)     => 1
  Poly(-1//1 + 2//1⋅x) => 2
  Poly(-4//1 + 3//1⋅x) => 5
```  

For some problems big integers are necessary to express the problem:

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
Dict{Polynomials.Poly{BigInt},Int64} with 3 entries:
  Poly(3402823669209384634633… => 1
  Poly(-340282366920938463463… => 1
  Poly(1)                      => 1
```  

All factorization is done over `BigInt`, regardless of the type of variable.

Factoring polynomials over a finite field of coefficients, `Z_p[x]` with `p` a prime, is also provided by `factormod`:

```
julia> factormod(x^4 + 1, 2)
Dict{Polynomials.Poly{BigInt},Int64} with 2 entries:
  Poly(1)     => 1
  Poly(1 + x) => 4

julia> factormod(x^4 + 1, 5)
Dict{Polynomials.Poly{BigInt},Int64} with 3 entries:
  Poly(2 + x^2)  => 1
  Poly(-2 + x^2) => 1
  Poly(1)        => 1

julia> factormod(2x^2 + x + 1, 3)
Dict{Polynomials.Poly{BigInt},Int64} with 2 entries:
  Poly(2)            => 1
  Poly(-1 - x + x^2) => 1

julia> factormod(5x^5 - x^4 - 1, 7)
Dict{Polynomials.Poly{Int64},Int64} with 3 entries:
  Poly(-3 + 3⋅x - 3⋅x^2 + 3⋅x… => 1
  Poly(-2)                     => 1
  Poly(1 + x)                  => 1
```

The keys are polynomials over the integers whose coefficents are in [-p/2, p/2]. 
