## utility functions

"""

Next prime *after* k

Uses `Primes.isprime`

"""
function nextprime(k::Integer) 
    while true
        k += 1
        isprime(k) && return(k)
    end
end

## http://stackoverflow.com/questions/37142821/prime-iterator-in-julia
function nextprime(y::BigInt)
    x = BigInt()
    ccall((:__gmpz_nextprime,:libgmp), Void, (Ptr{BigInt},Ptr{BigInt}), &x, &y)
    x
end

## list factors on n (https://rosettacode.org/wiki/Factors_of_an_integer#Julia)
function factors(n::Integer)
    f = [one(n)]
    for (p,e) in factor(n)
        f = reduce(vcat, f, [f*p^j for j in 1:e])
    end
    return length(f) == 1 ? [one(n), n] : sort!(f)
end

#### Some number theory things ##################################################

## Extended Euclidean Algorithm

lc{T <: Number}(a::T) = one(T)
normal{T<:Number}(a::T) = lc(a) == 0 ? one(T) : a


"""
Algo 3.6. Extended Euclidean Algorithm

R must be a Euclidean Domain. E.g. Q[x], Fq[x], but not Z[x] as we divide

Type R has `divrem`, `inv`, `lc` and `normal` defined for it

Returns rs, ss, ts, ps, qs where

[invariants]
rs[i] = ss[i] * f[i] + ts[i] * g[i]

"""
function EEA{R}(f::R, g::R)
    ps = [lc(f), lc(g)]
    rs = R[normal(f), normal(g)]
    ss = R[inv(ps[end-1]), zero(R)]
    ts = R[zero(R), inv(ps[end])]
    qs = R[]
 
    while true 
        q,r = divrem(rs[end-1], rs[end])
        r == zero(R) && break
        push!(qs, q)
        push!(ps, lc(r))
        push!(rs, normal(r))
        push!(ss, (ss[end-1] - qs[end]*ss[end]) * inv(ps[end]))
        push!(ts, (ts[end-1] - qs[end]*ts[end]) * inv(ps[end]))
    end
    return rs,ss,ts  #, ps,qs
end

## Bezout factorization
"""

Bezout factorization.

R a Euclidean Domain.

Given numbers or polynomials `p` and `q`, return
* `g`, the gcd
* `u`, `v` with g = u*p + v*q

cf: [wikipedia](https://en.wikipedia.org/wiki/Polynomial_greatest_common_divisor#Euclidean_algorithm)
"""
function bezout{R}(a::R, b::R)
    T = typeof(a)
    const ZERO, ONE = zero(T), one(T)
    if a == ZERO
        return b, ZERO, ONE
    elseif b == ZERO
        return a, ONE, ZERO
    end
        
    rs, ss, ts = EEA(a, b)
    g, u, v = rs[end], ss[end], ts[end]
    convert(T, g), convert(T,u), convert(T,v)
    
end


"""

Chinese Remainder Theorem

Need Euclidean domain, R. (Calls `bezout`.)

input: m1, ..., mr in R pairwise co prime
       v1, ..., vr in R

output v in R where for each i: v = vi mod mi

"""
function crt{R}(ms::Vector{R}, vs::Vector{R})
    tot = zero(eltype(ms))
    M = prod(ms)
    N = length(ms)
    vs = [mod(v,m) for (v,m) in zip(vs, ms)]

    for i in 1:N
        mi = prod(ms[vcat(1:i-1, i+1:N)])  # M / ms[i]
        g,u,v = bezout(mi, ms[i])  # g is 1 by assumption u * mi + v * ms[i] = 1
        ci = vs[i] * u * mi
        tot = tot + ci 
    end

    mod(tot, M)
end
