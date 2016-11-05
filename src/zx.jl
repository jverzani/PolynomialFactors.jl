## polynomials over Z[x], Z/nZ[x], GF[x]


## Some R[x] specific things

"""

compute rem(a^n, f) using powering in Fq[n] / <f>

"""
function Base.powermod{T}(a::Poly{T},p,m::Poly{T})
    ## basically powermod in intfuncs.jl with wider type signatures
    p < 0 && throw(DomainError())
    p == 0 && return one(T)
    b = oftype(m,mod(a,m))
    
    t = prevpow2(p)
    local r::Poly{T}
    r = one(Poly{T})
    while true
        if p >= t
            r = mod(r * b, m)
            p -= t
        end
        t >>>= 1
        t <= 0 && break
        r = mod(r*r, m)
    end
    r
end

## a,m are polys as vectors. About 10 times faster than above
function poly_powermod_over_Zp{T}(a::Vector{T},n,m::Vector{T}, p)
    ## basically powermod in intfuncs.jl with wider type signatures

    n < 0 && throw(DomainError())
    n == 0 && return ones(T,1)
    b = poly_rem_over_Zp(a, m, p)
    b == T[] && return T[]
    
    t = prevpow2(n)
    local r::Vector{T}
    r = ones(T,1)
    while true
        if n >= t
            r = poly_rem_over_Zp(r ⊗ b, m, p)
            n -= t
        end
        t >>>= 1
        t <= 0 && break
        r = poly_rem_over_Zp(r ⊗ r, m, p)
    end
    r
end



##################################################

### Polynomial Ring operations, Z/nZ = Z_n; Z_n[x]

oo = -1
"""
convert poly to one over Zp. If `p=oo`converts Zp[x] poly to Z[x] poly
"""
function Znx(p, f)
    if p == oo
        T = typeof(f[0].k)
        convert(Poly{T}, f)
    else
        convert(Poly{ModInt{p,true}}, f)
    end
end

## hashing of polynomials is work...
function Base.hash{p,B}(f::Poly{ModInt{p,B}})
    ks = [m.k for m in coeffs(f)]
    hash((ks, f.var))
end

function Base.hash{p,d}(f::Poly{GF{p,d}})
    ks = [hash(m.h) for m in coeffs(f)]
    hash((ks, map(hash, f[0].I.gens), f.var))
end


"""

Create polynomials over Zn.

Example
```
Z_n([3,4,5,6], 4)
(Poly(3 + x^2 + 2⋅x^3)) mod 4
```


(Z/pZ)[x] is same as GF{p,1}, but this gives a simpler representation.

"""
Z_n(as, n) = Poly(map(u->Zn{n}(u), as))
Base.eps{n,B}(::Poly{ModInt{n,B}}) = ModInt{n,B}(0)


"""
For coprime g, h find s*g = t*h = 1 mod m
"""
function bezout_over_m{R <: Integer}(f::Poly{R},g::Poly{R}, m)
    us, ss, ts = EEA(Znx(m,f), Znx(m,g))
    sbar, tbar = ss[end] / us[end][end], ts[end] / us[end][end]
    Znx(oo, sbar), Znx(oo, tbar)
end

## solve f * w = q mod p; w,q = Zp[x]
function _solve_fwq(w, q)
    m,n = degree(w), degree(q)
    A = cauchy_matrix(w, n - m + 1)
    M = hcat(A, reverse(q.a))
    p = reverse(q.a)


    m11 = inv(M[1,1])
    fs = m11 * [p[1]]

    for i = 2:n
        a = (p[i] - (fs .* M[i,1:(i-1)])[1]) * m11
        push!(fs, a)
    end
    pop!(fs) == 0 || return zero(w)
    
    Poly(reverse(fs))
end
   
## ### Find a gcd over Z[x] using modular arithmetic
## function _gcd_over_Zp{Z <: Integer}(f::Poly{Z}, g::Poly{Z}, p::Int)
##     #u = gcd(Znx(p,f), Znx(p,g))
##     # u = bezout ...
##     #return monic(u)

##     fbar = convert(Poly{Zn{p}}, f)
##     gbar = convert(Poly{Zn{p}}, g)

    
##     u = _gcd(fbar, gbar)
##     monic(u)

    
## end





"""

Algorithm 6.34 big prime modular GCD for Z[x]

Not complete, but working okay.

Note: being able to handle Zn{BigInt{p}} would be helpful here.

"""
function modular_gcd_big_prime{T<:Integer}(f::Poly{T}, g::Poly{T})
    A =  max(norm(f, Inf), norm(g, Inf))
    b = gcd(lc(f), lc(g))
    n = degree(f)
    B = sqrt(n + 1) * 2^n * A * b

    M = 1000
    Br = M^ceil(Int, log(M, B))  # uses fewer primes, avoid recompilation when parameterized by p
    
    p = Br

    while true
        p = nextprime(p)
    
        fbar = Znx(p, f)
        gbar = Znx(p, g)
        vbar = bezout(fbar, gbar)[1]
        vbar = b * monic(vbar)

        w1 = Znx(oo, vbar)
        return primitive(w1)
        ## XXX something wrong here for certain sizes...
        fstar = _solve_fwq(vbar, b*fbar)
        gstar = _solve_fwq(vbar, b*gbar)
        (fstar == zero(vbar) || gstar == zero(vbar)) && next

        f1, g1 = Znx(oo, fstar), Znx(oo, gstar)
        
        (norm(f1, 1) * norm(w1,1) <= Br) &&  (norm(g1, 1) * norm(w1,1) <= Br) && return primitive(w1)
    end
end

## the big prime gcd can only use primes so big. The small prime gcd suffers as too slow
## if we use ModInt{p,B}, as many things are recompiled for each `p`. Instead we will implement
## the small prime version usng Int[] and not Poly{ModInt{n,B}}.

## convenient way to make Vector{Int} go to mod(k,p)
function MOD(p,center=true)
    ks -> begin
        ps = similar(ks)
        S = div(p,2)
        for i in eachindex(ps)
            a = mod(ks[i], p)
            if (center && a > S) a = a - p end
            ps[i] = a
        end
        poly_zchop(ps)
    end
end
        

## divrem() over Z with *monic* poly
function poly_divrem{T<:Integer}(as::Vector{T}, bs::Vector{T})

    rs = copy(as)
    n,m = length(rs), length(bs)
    n >= m || return as
    qs = zeros(T, n-m+1)
    bmi = invmod(bs[end], p)
    for i in n:-1:m
        lambda = mod(rs[i] * bmi, p)
        qs[i - m + 1] = lambda
        for j in 0:(m-1)
            rs[i-j] = mod(rs[i-j] - lambda * bs[m-j], p)
        end
    end

    rs = poly_zchop(rs)
    length(rs) > 0 ? rs : zeros(T,1)

    qs, rs
end

## divrem() over Z/pZ
function poly_divrem_over_Zp{T<:Integer}(as::Vector{T}, bs::Vector{T}, p::Integer)

    rs = poly_zchop(MOD(p)(as))
    bs = poly_zchop(MOD(p)(bs))

    n,m = length(rs), length(bs)
    n >= m || return ones(T,1), as
    m == 0 && T[], bs
    
    qs = zeros(T, n-m+1)

    bmi = invmod(bs[end], p)
    for i in n:-1:m
        lambda = mod(rs[i] * bmi, p)
        qs[i - m + 1] = lambda
        for j in 0:(m-1)
            rs[i-j] = mod(rs[i-j] - lambda * bs[m-j], p)
        end
    end

    rs = poly_zchop(rs)
    length(rs) > 0 ? rs : zeros(T,1)

    qs, rs
end

## rem() over Z/pZ
poly_rem_over_Zp{T<:Integer}(as::Vector{T}, bs::Vector{T}, p::Integer) =  poly_divrem_over_Zp(as,bs,p)[2]
## div() over Z/pZ
poly_div_over_Zp{T<:Integer}(as::Vector{T}, bs::Vector{T}, p::Integer) =  poly_divrem_over_Zp(as,bs,p)[1]

## return, g, s,t: g gcd, p*s + q*t = g
function poly_bezout_over_Zp{R<:Integer, S<:Integer}(ps::Vector{R}, qs::Vector{R}, p::S)
    T = promote_type(R,S)
    as = convert(Vector{T}, ps)
    bs = convert(Vector{T}, qs)
    m = convert(T, p)

    r0, r1 = as, bs
    s0, s1 = [one(T)], [zero(T)]
    t0, t1 = [zero(T)], [one(T)]

    while poly_degree(r1) >= 0
        q, r = poly_divrem_over_Zp(r0, r1, m)
        r0, r1 = r1, poly_zchop(MOD(m)(r0 ⊕ -q ⊗ r1))
        s0, s1 = s1, poly_zchop(MOD(m)(s0 ⊕ -q ⊗ s1))
        t0, t1 = t1, poly_zchop(MOD(m)(t0 ⊕ -q ⊗ t1))
    end
    r0 = poly_zchop(r0)
    r0 == T[] && return [one(T)], s1, t1
    rni = invmod(r0[end], m)
    r0, s0, t0 = [MOD(m)(rni*u) for u in (r0, s0, t0)]

    ## verify
    ## chk = poly_zchop(MOD(m)(r0  ⊕ -(s0 ⊗ ps ⊕ t0 ⊗ qs)))

    r0, s0, t0
            
    
end

## find gcd(fbar, gbar) where fbar = f mod Z/pZ
function poly_gcd_over_Zp{T<:Integer, S<:Integer}(as::Vector{T}, bs::Vector{T}, p::S)
    r0, s0, t0 = poly_bezout_over_Zp(as, bs, p)
    return poly_monic_over_Zp(r0, p)
    
    ## R = promote_type(T, S)

    ## qs = R[mod(b,p) for b in bs] |> poly_zchop
    ## qs == R[] && return ones(R, 1) # divide by 0?

    ## ps = R[mod(a,p) for a in as] |> poly_zchop
    ## p = convert(R,p)
    
    ## while true
    ##     qs == zeros(R,1) || qs == R[] && break
    ##     ps, qs = qs, poly_rem_over_Zp(ps, qs, p)
    ## end

    ## # monic
    ## T[mod(k,p) for k in ps * invmod(ps[end], p)]
end

## much faster modular gcd


"""

GCD of f,g in Z[x] using modular arithmetic.

ALgorithm 6.38 small prime version.

TODO: check edge cases, large values, ...
"""
function modular_gcd_small_prime{T <: Integer}(f::Poly{T}, g::Poly{T})
    A =  max(norm(f, Inf), norm(g, Inf)) 
    b = gcd(lc(f), lc(g))
    n = degree(f)
    B = sqrt(n + 1) * 2.0^n * A * b

    k = 2*(n * log2(n+1.0) + log2(b) + 2n * log2(A))
    K = floor(Int, 2k*log(k))
    l = ceil(Int, log2(2B + 1))
    Ss = unique(rand(primes(3, K), 2l)) # 2 had issues
    Ss = filter(x -> rem(b,x) != 0, Ss) # p does not divide b

    S = convert(Vector{BigInt}, Ss)
    fs = convert(Vector{BigInt}, f.a)
    gs = convert(Vector{BigInt}, g.a)
    
    vbars = [poly_gcd_over_Zp(fs, gs, s) for s in S]
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
        vs = BigInt[vbars[j][i] for j in 1:N]
        wi = crt(S, b*vs)
        wi > (prodS-1) / 2
        ws[i] = wi > halfway ? wi - prodS : wi
    end
    
    convert(Vector{T}, poly_primitive(ws))
end

    


"""

Find gcd of `p` and `g` in `Z[x]` using modular arithmetic. This thes big small algorithm  in *Modern Computer Algebra*
by Joachim von zur Gathen and Jürgen Gerhard. 


Example:

```
p = poly([1,1,2,3,4,4,4,4,4])
gcd(p, p')  # (x-1)*(x-4)^4
```
"""
function Base.gcd{T<:Integer}(p::Poly{T}, q::Poly{T})
    n,m = degree(p), degree(q)
    if n < m
        q,p = p,q
        m,n = n,m
    end
    m == 0 && return gcd(q[end], content(p))

    Poly(modular_gcd_small_prime(p,q), p.var)

end


