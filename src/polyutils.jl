## Some Polynomial utilities


"""

Reverse polynomial.

E.g. `1 + 2x + 3x^2 -> 3 + 2x + 1x^2`.

Can set `k` so that we reverse poly `3 + 2x + 1x^2 + 0x^3 -> 0 + 1x +2x^2 + 3x^3`

"""
function poly_reverse{T}(p::Poly{T}, k=degree(p))
    k < degree(p) && error("k must be >= degree(p)")
    ps = T[p[i] for i in k:-1:0]
    Poly(ps, p.var)
end

## """

## Truncate terms order n or higher. Same as rem(p, x^(n))

## """
## Base.trunc(p::Poly, n::Int) = (1 <= n <= degree(p)-1) ? Poly(p[0:(n-1)], p.var) : p


#"`mod(f::Poly, g::Poly)` remainder after division. Resulting poly has 0 <= degree < degree(g)"
#Base.mod(f::Poly, g::Poly) = rem(f, g)


"Return  a monic polynomial from `p`. If `p==0` we return `p`"
monic(p::Poly) = lc(p) != 0 ? Poly(p.a * inv(p[degree(p)]), p.var) : p

## make monic as poly in Zp
function poly_monic_over_Zp{T<:Integer}(a::Poly{T}, p)
    b = MOD(p)(a)
    lc(b) == zero(T) && return a
    bi = invmod(lc(b), p)
    MOD(p)(bi * b)::Poly{T}
end



# content in poly ring R[u][v] is monic(gcd(...))
content{T}(p::Poly{T}) = convert(T, gcd(p.a))

function primitive{T}(p::Poly{T})
    ps = p.a
    b = content(p)
    qs = T[div(a,b) for a in ps]
    q = Poly(qs, p.var)
    q[end] < 0 ? -q : q
end
isprimitive{T}(p::Poly{T}) = cont(p) == one(T)

"""
Leading coefficient of a polynomial
"""
lc(p::Poly) = p[end]

"""
normal form of a. Basically same as monic, but may be more general for Euclidean Domain
"""
normal{T}(a::Poly{T}) = lc(a) != 0 ?  a * inv(lc(a)) : a


"""
exact divrem for linear factors
"""
function synthetic_division{T}(p::Poly{T}, c::Number)
    ps = copy(p.a)                    # [p0, p1, ..., pn]
    qs = T[pop!(ps)]           # take from right
    while length(ps) > 0
        unshift!(qs, c*qs[1] + pop!(ps))
    end
    r = shift!(qs)
    Poly(qs, p.var), r
end


"""

If p(x) = (x-c)^k q(x) then return q(x), k (assuming x-c does not divide q(x))

"""
function deflate{T}(p::Poly{T}, c::T)
    k = 0
    q, r = synthetic_division(p,c)
    while abs(r) <= eps(T)
        p = q
        q, r = synthetic_division(p, c)
        k = k + 1
    end
    p, k
end

"""

If `p(x) = f(x)^k * q(x) ` with `f` not dividing `q`, then return `(f, k)`.

"""
function deflate{T,S}(p::Poly{T}, fac::Poly{S})
    k = 0
    fact = convert(Poly{T}, fac)
    q,r = exact_divrem(p, fact)
    while r == zero(Poly{T})
        q == zero(Poly{T}) && break  # exact_divrem(Z[x],Z[x]) returns 0,0 if can't divide
        p = q
        q, r = exact_divrem(p, fact)
        k = k + 1
    end
    p, k
end

function deflate_over_Zp{T}(f::Poly{T}, g::Poly{T}, p)
    const ZERO = zero(f)
    
    q,r = poly_divrem_over_Zp(f, g, p) # returns 0,0 if can't compute
    k = 0
    while r == ZERO
        q == ZERO && break
        f = q
        q, r = poly_divrem_over_Zp(f, g, p)
        k = k + 1
    end
    f, k
end

## find multiplicities
## R a type, f a poly, ps the factors
## finds the order, returns a dictionary
function find_multiplicities(R, f, ps)
    G1 = Dict{Poly{R},Int}()
    for p in ps
        haskey(G1, p) && continue
        f, k = deflate(f, p)
        G1[p] = k
    end
    G1[f] = 1 # constant?
    G1

end


## ##################################################
## ## assume  poly in R[x],  R a ring.
## ## algo 2.5
## ## try to speed up compilation for different types
## function poly_div_exact(a::Poly, b::Poly)
##     const ZERO = zero(a)
##     const ONE = one(a)
##     n,m = degree(a), degree(b)
##     n >= m || return ZERO, a
##     bm = lc(b)
##     bmi = inv(bm)  ## must exist in R for this to work
##     r = copy(a)
##     x = variable(a)
##     qs = zeros(eltype(a), n - m + 1)
    
##     for i in (n-m):-1:0
##         if degree(r) == m + i
##             qi = lc(r) * bmi
##             r = r - qi * x^i * b
##             qs[i+1] = qi
##         end
##     end
##     return Poly(qs, a.var)
## end
    

## Polynomial gcd, ...

## Algorithms for Z[x]

"""

ALgorithm 9.3

Find inverse over <x^l> of f(x) in R[x], with R a ring

Assumes f(0) = 1. Otherwise, use inv(f(0)) * f

"""
function newton_inversion{T}(f::Poly{T}, l::Int)
    if f[0] == -one(T)
        f = -f
    end
    f[0] == one(T) || error("Need f(0) to be 1")
    g  = Poly(T[1])
    r =  ceil(Int, log2(l))
    for i in 1:r
        g = 2g -f * g^2
        g = Poly(g[0:(2^i-1)])  # truncate at power 2^i
    end
    g
end
  
"""

Algorithm 9.5 fast division with remainder

a,b in R[x], R a commutive ring with one. Assume b \neq 0 is monic

a = q * b + r with deg(r) < deg(b)

Does not divide, so a, b in R[x]. Must assume b is monic.
"""
function poly_fast_divrem_over_Zp{T<:Integer,S<:Integer}(a::Poly{T}, b::Poly{T}, p::S)
    
    b == zero(Poly{T})  && error("Assume b is neq 0 and monic; $b")
    b[end] != one(T) && error("Assume b is neq 0 and monic: $b")
    
    degree(a) < degree(b)  && return (zero(a), a)
    m = degree(a) - degree(b)

    ra, rb1 = poly_reverse(a), newton_inversion(poly_reverse(b), m+1)
    
    q = MOD(p)(ra * rb1)
    q = Poly(reverse(q[0:m]), a.var)
    r= MOD(p)(a - b*q)

    (q, r)
end




## function fast_divrem{R}(a::Poly{R}, b::Poly{R})
    
##     b == zero(Poly{R})  && error("Assume b is neq 0 and monic: $b")
##     lc(b) != one(R) && error("Assume b is neq 0 and monic: $b")
    
##     degree(a) < degree(b) && return (zero(Poly{R}), as)
##     m = degree(a) - degree(b)

##     ra, rb1 = poly_reverse(a), newton_inversion(poly_reverse(b), m+1)

##     qstar = ra * rb1
##     qstar = Poly(qstar[0:(m+1)])
    
##     q = Poly(R[qstar[i-1] for i in reverse(1:m+1)]) # reverse q but may need to pad 0s
##     r = a - b * q

##     (q, r)

## end

## """
## pseudo division with remainder over Z[x]. Does not assume b is monic

## Find q, r in Z[x] with lc(b)^(m-n + 1) * a = q * b + r

## (Z[x] is not a Euclidean domain, so divrem does not exist within Z[x])
## """
## function pdivrem{T<:Integer}(a::Poly{T}, b::Poly{T})
    
##     m, n = degree(a), degree(b)
##     m < n && error("degree(a) >= degree(b)")

##     c = b[end]
##     c == 1 && return(fast_divrem(a, b))
    
##     x = variable(a)
##     q = 0
##     r = a * c^(m - n + 1)
##     while degree(r) >= n
##         s = div(r[end], c)  * x^(degree(r) - n )
##         q = q + s
##         r = r - s*b
##     end

##     q, r
## end


"""
Division algorithm for Z[x]

returns q,r with

* `a = q*b + r`
* `degree(r) < degree(b)`

If no such q and r can be found, then both `q` and `r` are 0.

"""
function exact_divrem{T<:Integer}(a::Poly{T}, b::Poly{T})
    f,g = a, b
    x = variable(g)
    q, r = zero(f), f

    while degree(r) >= degree(g)
        u, v = divrem(r[end], g[end])
        v != 0 && return zero(a), zero(a)
        term = u * x^(degree(r) - degree(g))
        q = q + term
        r = r - term * g
    end
    (q, r)
end
    
    
## """
## Is `g` square free? Assumes you can tell by comparing gcd(g, polyder(g))
## """
## function issquarefree(g::Poly)
##     u =  egcd(g,polyder(g))
##     degree(u) == 0
## end


## """

## Yun's square free factorization fora field characteristic 0

## Algo 14.21

## Could use in factoring over Q[x], but don't for now.
## """
## function yun_square_free{T <: Integer}(f::Poly{Rational{T}})
##     u = gcd(f, polyder(f))
##     v,w  = div(f,u), div(polyder(f),u)
##     hs = Poly{Rational{T}}[]
##     while true
##         u = gcd(v, w - polyder(v))
##         v, w = div(v, u), div(w - polyder(v), u)
##         push!(hs, h)
##         degree(v) == 0 && break
##     end
##     hs
## end


"""
Return square free version of `f`
"""
function square_free{T<:Integer}(f::Poly{T})
    degree(f) <= 1 && return f
    
    g = egcd(f, polyder(f))  # monic
    d = degree(g) 
    
    if  d > 0
        fsq,_ = exact_divrem(f, g)
    else
        fsq = f
    end
    fsq
end
 
## bounds
function _bi2up{T}(as::Vector{T}, k, n)
    a = one(T)
    tot = as[1]^2 * a
    for i in 1:k
        a = a * i / (n-i + 1)
        tot += as[i+1]^2 * a
    end
    tot
end

## [f]2 norm = sqrt(sum(a[i]^2/choose(n,i))) 
function bi2norm{T}(as::Vector{T})
    n = length(as) - 1
    k = div(n,2)
    out = _bi2up(as[1:(k+1)], k, n) + _bi2up(reverse(as[(k+2):end]), n-k-1, n)
    sqrt(out)
end

# http://icm.mcs.kent.edu/reports/1992/ICM-9201-26.pdf
function beauzamy_bound{T}(p::Poly{T})
     n = degree(p)
     3.0^(3/4) / 2 / sqrt(pi) * sqrt(3)^n / sqrt(n) * bi2norm(p.a)
end


function landau_mignotte{T}(p::Poly{T})
    d = floor(BigInt, degree(p)/2)
    k = floor(BigInt, d/2)
    a = binomial(d,k)
    (d/2) * norm(p, 2)
end
