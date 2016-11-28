## polynomials over Z[x], Z/nZ[x]


## Some R[x] specific things

## """

## compute rem(a^n, f) using powering in Fq[n] / <f>

## T must be a Euclidean Domain for mod to work as desired...
## """
## function Base.powermod{T}(a::Poly{T}, n, m::Poly{T})
##     ## basically powermod in intfuncs.jl with wider type signatures
##     n < 0 && throw(DomainError())
##     n == 0 && return one(T)
##     b = oftype(m,mod(a,m))
    
##     t = prevpow2(n)
##     local r::Poly{T}
##     r = one(Poly{T})
##     while true
##         if n >= t
##             r = mod(r * b, m)
##             n -= t
##         end
##         t >>>= 1
##         t <= 0 && break
##         r = mod(r*r, m)
##     end
##     r
## end

## We will work with Z[x] over Z/pZ by converting the coefficient after the fact
## This function coerce coefficients of poly in Z[x] to those in Z/pZ, centered by default
## functions `poly_*_over_Zp` will be using this.
function MOD(p::Integer, center=true)
    f -> begin
        T = eltype(f)
        ps = copy(coeffs(f))
        S = div(p,2)
        for i in 0:degree(f) #eachindex(f)
            a = mod(f[i], p)::T
            if (center && a > S) a = a - p end
            ps[i+1] = a
        end
        Poly(ps, f.var)
    end
end
        

## a monic, random poly of degree a < n
function poly_random_poly_over_Zp(T, n, p)
    a = rand(0:(p-1), n)
    a = convert(Vector{T}, a)
    b = Poly(a)
    b == zero(b) && return poly_random_poly_over_Zp(T, n, p)
    poly_monic_over_Zp(Poly(b), p)
end


## a,m are polys in Z[x]. About 10 times faster than power using ModInt{p}
function poly_powermod_over_Zp{S<:Integer}(a::Poly{BigInt}, n::S, m::Poly{BigInt}, p::Integer)
    ## basically powermod in intfuncs.jl with wider type signatures
    T = BigInt
    const ONE = one(Poly{T})::Poly{T}
    const ZERO = zero(Poly{T})::Poly{T}
    
    n < 0 && throw(DomainError())
    n == 0 && return ONE
    b = poly_rem_over_Zp(a, m, p)
    b == ZERO && return ZERO
    
    t = prevpow2(n)::S
    local r::Poly{T}
    r = one(a)
    while true
        if n >= t
            r = poly_rem_over_Zp(r * b, m, p)
            n -= t
        end
        t >>>= 1
        t <= 0 && break
        r = poly_rem_over_Zp(r * r, m, p)
    end
    r
end


## divrem() over Z/pZ
function poly_divrem_over_Zp(a::Poly{BigInt}, b::Poly{BigInt}, p::BigInt)
    T = BigInt
    a.var == b.var || throw(DomainError()) #("Symbols must match")
    a,b = MOD(p)(a)::Poly{T}, MOD(p)(b)::Poly{T}

    x = Poly(T[zero(T),one(T)], a.var) #variable(Poly{T})
    
    n, m = degree(a), degree(b)
    b == zero(b) && throw(DomainError()) #error("Division by zero")
    m == 0 && return a[end] * invmod(lc(b), p) * a, zero(a)
    n < m && return zero(a), a

    q = zero(Poly{T})
    a = a - q*b
    while degree(a) >= degree(b)
        qi = (a[end] * invmod(lc(b), p) * x^(degree(a) - degree(b)))::Poly{T}
        qi = MOD(p)(qi)::Poly{T}
        q += qi
        a = MOD(p)(a - qi * b)::Poly{T}
    end

    #vfy = MOD(p)(ao - (b*q + a))
    
    q, a
end

## div() and rem() over Z/pZ
poly_div_over_Zp{T<:Integer}(a::Poly{T}, b::Poly{T}, p::Integer) =  poly_divrem_over_Zp(a,b,p)[1]
poly_rem_over_Zp{T<:Integer}(a::Poly{T}, b::Poly{T}, p::Integer) =  poly_divrem_over_Zp(a,b,p)[2]
poly_divides_over_Zp{T}(g::Poly{T}, h::Poly{T}, p::Integer) = poly_rem_over_Zp(g, h, p) == zero(Poly{T})


## should jut be monic?
function poly_normal_over_Zp{T}(f::Poly{T}, p::T)
    f = MOD(p)(f)
    f == zero(f) && return f
    MOD(p)(invmod(f[end], p) * f)
end

function poly_EEA_over_Zp{T}(f::Poly{T}, g::Poly{T}, p::T)

#    println("Poly EEA: f=$f; g=$g; p=$p")
    const ZERO::Poly{T}, ONE::Poly{T} = zero(Poly{T}), one(Poly{T})

    f, g = Poly{T}[MOD(p)(u) for u in (f,g)]
    (g == ZERO || f == ZERO) && error("need f, g nonzero mod p")
    

    rhos = T[f[end], g[end]]
    qs = Poly{T}[]
    rs = Poly{T}[poly_normal_over_Zp(f, p), poly_normal_over_Zp(g, p)]
    ss = Poly{T}[invmod(f[end], p)*ONE, ZERO]
    ts = Poly{T}[ZERO, invmod(g[end], p)*ONE]

    i = 2
    while rs[i] != ZERO
        q,r = poly_divrem_over_Zp(rs[i-1], rs[i], p)
        r == ZERO && break
        push!(qs, q)
        push!(rhos, r[end])
        push!(rs, poly_normal_over_Zp(r, p))
        rhoi = invmod(rhos[end], p)
        push!(ss, MOD(p)((ss[i-1] - q * ss[i]) * rhoi))
        push!(ts, MOD(p)((ts[i-1] - q * ts[i]) * rhoi))
        i = i + 1
    end
    rhos, rs, ss, ts, qs
end

## return, g, s,t: g gcd, p*s + q*t = g
function poly_bezout_over_Zp{T}(f::Poly{T}, g::Poly{T}, p::T)
    
    const ZERO::Poly{T}, ONE::Poly{T} = zero(Poly{T}), one(Poly{T})
    f, g = Poly{T}[MOD(p)(u) for u in (f,g)]

    f == ZERO && return g, ONE, ZERO
    g == ZERO && return f, ZERO, ONE

    rhos, rs, ss, ts, qs = poly_EEA_over_Zp(f,g,p)
    rs[end], ss[end], ts[end]
    
end

## find gcd(fbar, gbar) where fbar = f mod Z/pZ
function poly_gcd_over_Zp{T<:Integer, S<:Integer}(a::Poly{T}, b::Poly{T}, p::S)
    r0, s0, t0 = poly_bezout_over_Zp(a, b, p)
    return poly_monic_over_Zp(r0, p)
end


"""

GCD of f,g in Z[x] using modular arithmetic.

ALgorithm 6.38 small prime version.

TODO: check edge cases, large values, ...
"""
function modular_gcd_small_prime{T <: Integer}(p::Poly{T}, q::Poly{T})
    f,g = [convert(Poly{BigInt}, u) for u in (p,q)]
    
    A =  max(norm(f, Inf), norm(g, Inf)) 
    b = gcd(lc(f), lc(g))
    n = degree(f)
    B = sqrt(n + 1) * 2.0^n * A * b

    k = 2*(n * log2(n+1.0) + log2(b) + 2n * log2(A))
        
    K = floor(Int, 2k*log(k)) # need Int, for primes?
    l = ceil(Int, log2(2B + 1))


    Ss = unique(rand(primes(3, K), 2l)) # 2 had issues
    Ss = filter(x -> rem(b,x) != 0, Ss) # p does not divide b

    S = convert(Vector{BigInt}, Ss)
    
    vbars = [poly_gcd_over_Zp(f, g, s) for s in S]
    ds  = map(length, vbars)
    minlength = minimum(ds)
    ind = ds .== minlength

    ## try again
    sum(ind) < l && return modular_gcd_small_prime(f,g)
    
    S = S[ind]
    vbars = vbars[ind]
    N = length(S)
    prodS = prod(S)
    halfway = div(prodS - 1,2)
    
    ws = zeros(BigInt, minlength)
    for i in 1:minlength
        vs = BigInt[vbars[j][i-1] for j in 1:N]
        wi = chinese_remainder_theorem(S, b*vs)
        wi > (prodS-1) / 2
        ws[i] = wi > halfway ? wi - prodS : wi
    end

    g = Poly(convert(Vector{T},ws), f.var)
    primitive(g)
end

    


"""

Find gcd of `p` and `g` in `Z[x]` using modular arithmetic, in particular the small prime algorithm in GG.

Example:

```
p = poly([1,1,2,3,4,4,4,4,4])
egcd(p, p')  # (x-1)*(x-4)^4
```

Note: We call this `egcd`, not `gcd`, as the `gcd` function in `Polynomials` is defined for polynomials over `Z[x]`, but is not *e*xact.

"""
function egcd{T<:Integer}(p::Poly{T}, q::Poly{T})
    n,m = degree(p), degree(q)
    if n < m
        q,p = p,q
        m,n = n,m
    end
    m == 0 && return gcd(lc(q), content(p))
    q == zero(q) && return p
    
    modular_gcd_small_prime(p,q)

end


