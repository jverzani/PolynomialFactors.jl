## File with ModInt, Finite Fields, #and algorithms over Fq[x]

abstract Ring <: Number
abstract EuclideanRing <: Ring

## Z/nZ elements.

## We modify an example from:
## from https://github.com/JuliaLang/julia/blob/master/examples/modint.jl
## That file is a part of Julia. License is MIT: http://julialang.org/license

## Alternatives could be `IntModN.jl` or `Mod.jl`
## We find that none are fast enough for some computations when used with `Polynomials` so
## we also implement some routines that use arrays to store polynomials.


import Base: +, -, *, /, //
import Base: ==, <, <=

## B=true and in [-n/2, n/2) otherwise in [0,n)
immutable ModInt{n,B} <: EuclideanRing
    k::Integer
    function ModInt(k)
        u = mod(k,n)
        if B
            u = (u > div(n,2) ? u - n : u)
        end
        new(u)
    end
end

order{n,B}(::Type{ModInt{n,B}}) = n

-{n,B}(a::ModInt{n,B}) = ModInt{n,B}(-a.k)
+{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = ModInt{n,B}(a.k+b.k)
-{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = ModInt{n,B}(a.k-b.k)
*{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = ModInt{n,B}(a.k*b.k)
Base.inv{n, B}(a::ModInt{n,B}) = ModInt{n,B}(invmod(a.k, n))
/{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = a * inv(b)

Base.rem{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = ModInt{n,B}(rem(a.k, b.k))
Base.div{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = ModInt{n,B}(div(a.k, b.k))

=={n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = a.k == b.k    
<{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = a.k < b.k
<={n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = a.k <= b.k

random_elements{n, B}(::Type{ModInt{n,B}}, k::Int) = [ModInt{n, B}(k) for k in rand(0:(n-1), k)]

Base.convert{n,B, T<:Integer}(::Type{ModInt{n,B}}, i::T) = ModInt{n,B}(i)
Base.convert{n, B, T<:Integer}(::Type{T}, a::ModInt{n,B}) = convert(T, a.k)

Base.promote_rule{n,B, T<: Integer}(::Type{ModInt{n,B}}, ::Type{T}) = ModInt{n,B}

Base.isless{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = isless(a.k, b.k)
Base.show{n,B}(io::IO, k::ModInt{n,B}) = print(io, "mod($(k.k),$n)")
Base.showcompact(io::IO, k::ModInt) = print(io, k.k)

Base.gcd{n,B}(a::ModInt{n,B}, b::ModInt{n,B}) = bezout(a,b)[1]
Base.gcd{n,B}(as::Vector{ModInt{n,B}}) = reduce(gcd,as)
Base.abs{n,B}(a::ModInt{n,B}) = a

typealias Zn{p} ModInt{p, false}

Base.convert{n,m,B}(::Type{ModInt{n,B}}, a::ModInt{m,B}) = ModInt{n,B}(a.k)

## Finite (Galois) Fields. These are of order q=p^n and are formed by Z_p[z] / <f>, with f irreducible of degree n
## GFpd
## We parameterize by p,d here as that allows one to find an irreducible polynomial to generate the ideal I
## however, one can also pass in h and I directly and the rind operations will still work
## it may not be a field though. This is used in `_remainder_an`
## To create elements:
## a = Z_n([1,2,3], 5)
## convert(GF{5,3}, a)

immutable GF{p,d} <: EuclideanRing
    h
    I
end
order{p,d}(::Type{GF{p,d}}) = p^d

type Ideal{R}
    gens::Vector{R}
end
Ideal(fs::Poly...) = Ideal([fs...])

Base.show{R}(io::IO, k::Ideal{R}) = print(io, "<", join(k.gens, ", "), ">")

# reduce over I: h - f in <I>
function canonicalize{R}(h::R, I::Ideal{R})
    for f in I.gens
        h = rem(h, f)
    end
    h
end

function Base.convert{p,d}(::Type{GF{p,d}}, i::Int)
    f = find_irreducible_poly(p,d)
    GF{p,d}(zero(f)+i, Ideal(f))
end
Base.promote_rule{p, d}(::Type{GF{p, d}}, ::Type{Int}) = GF{p,d}

function Base.convert{p,d}(::Type{GF{p,d}}, i::Poly)
    f = find_irreducible_poly(p,d)
    h = canonicalize(zero(f)+i, Ideal(f))
    GF{p,d}(h, Ideal(f))
end
Base.promote_rule{p, d}(::Type{GF{p, d}}, ::Type{Poly}) = GF{p,d}

import Base: ==, +, -, *, /, ^, zero, one
=={p,d}(a::GF{p,d}, b::GF{p,d}) = a.h == b.h
zero{p,d}(a::GF{p,d}) = convert(GF{p,d}, 0)
one{p,d}(a::GF{p,d}) = convert(GF{p,d}, Z_n([1],p))



+{p,d}(a::GF{p,d}, b::GF{p,d}) = GF{p,d}(canonicalize(a.h + b.h, a.I), a.I)
-{p,d}(a::GF{p,d}, b::GF{p,d}) = GF{p,d}(canonicalize(a.h - b.h, a.I), a.I)
*{p,d}(a::GF{p,d}, b::GF{p,d}) = GF{p,d}(canonicalize(a.h * b.h, a.I), a.I)

-{p,d}(a::GF{p,d}) = GF{p,d}(-a.h, a.I)

_irreducible{p,d}(a::GF{p,d}) = a.I.gens[1]
_canonical{p,d}(a::GF{p,d}) = a.h
function Base.inv{p, d}(a::GF{p, d})
    ah, f = _canonical(a), _irreducible(a)
    u, s, t = bezout(ah, f)  # solves s*(a.h) + t * f = 1 so t * (a.h) is congruent to 1
    if degree(u) == 0 && u != zero(ah)
        GF{p,d}(s * inv(lc(u)), a.I)
    else
        error("No inverse found for $a. GCD was $u")
    end
end


/{p, d}(a::GF{p,d}, b::GF{p,d}) = a * inv(b)
^{p,d}(a::GF{p,d}, n::Int) = repeated_squaring(a, n)

Base.isless{p,d}(a::GF{p,d}, b::GF{p,d}) = false
Base.show{p,d}(io::IO, x::GF{p,d}) = (show(io, x.h), print(io, "/<I>"))

function random_elements{p, d}(::Type{GF{p,d}}, k::Int)
    f = find_irreducible_poly(p,d)
    I = Ideal(f)
    map(_ -> begin
        q = random_poly(Zn{p},d)
        q = canonicalize(q, I)
        GF{p,d}(q,I)
    end, 1:k)
end

## is poly of degree n irreducible over Zp[x]?
function _is_irreducible{p,B}(f::Poly{ModInt{p,B}}, facs=collect(keys(factor(degree(f)))))
    !isprime(p) && error("Need p to be prime")
    n = degree(f)
    x = variable(f)

    gcd(powermod(x,p^n,f) - x, f) != f && return false  # gcd(x^(p^n)-x, f)
    ## _xqmx_gcd(p^n, f) != f && return false
    for t in facs
        ## g = _xqmx_gcd(p^div(n,t), f)
        g =  gcd(powermod(x,p^div(n,t),f) - x, f)
        degree(g) > 0 && return false
    end
    return true
end

"""

Find irreducible polynomial in Zp[x]

Following http://people.mpi-inf.mpg.de/~csaha/lectures/lec8.pdf and 9

Searches deterministically for an irreducible polynomial
"""
function find_irreducible_poly(p, n) # finds g of degree n over Zp[x] where g is irreducible.
    n == 1 && return Z_n([0,1],p)
    rng = 1:(p-1)
    facs = collect(keys(factor(n)))

    for len in 0:(n-1)
        for c in combinations(2:n, len)
            ts = typeof(rng)[]; for i in 1:len push!(ts, rng) end
            x = zeros(Int, n+1)
            x[n+1] = 1

            for x0 = 1:(p-1)
                for vals in product(ts...)
                    x[1:n] = 0
                    x[1] = x0
                    [x[i]=val for (i,val) in zip(c, vals)]
                    ## check for irreducibility
                    f = Z_n(x, p)
                    _is_irreducible(f, facs) && return f
                end
            end
        end
    end
 
    error("whoa nelly")
 
end


    
##################################################
## Some Ring operations

Base.gcd{R <: EuclideanRing}(f::R, g::R) = bezout(f, g)[1]
Base.gcd{R <: EuclideanRing}(f::Poly{R}, g::Poly{R}) = bezout(f, g)[1]



" choose a \in Fq[x] monic, non-zero of degree m < n."
function random_poly{Fq<:EuclideanRing}(::Type{Fq}, n, var=:x)
    ps = random_elements(Fq, n)
    while all(ps .== zero(Fq))
        ps = random_elements(Fq, n)
    end
    monic(Poly(ps, var))
end


"""

find a^n. R is a Ring with a 1

Much faster for some rings

cf. algorithm 4.8 of Gathen-Gehard.

(similar to powermod in intfuncs.jl)
"""
function repeated_squaring{R}(a::R, n::Int)
    n < 0 && return zero(R)
    n == 0 && return one(R)

    local r::R
    r = a

    t = prevpow2(n)
    d = n - t
    while t > 1
        t = t >>>= 1
        r *= r
        if d >= t
            r *=  a
            d = d - t
        end
    end
    r
end
        
