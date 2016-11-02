## Some Polynomial utilities

## ## Conversion
## function Base.convert{T,S}(::Poly{T}, p::Poly{S})
##     ps = T[convert(T, u) for u in coeffs(p)]
##     Poly(ps, p.var)
## end


## hashing of polynomials so that expected comparisons work.
## (We use polys for keys in dictionaries with `factor`)
Base.hash(f::Poly) = hash((f.a, f.var))

## ## Make an iterator over terms of the polynomial
## Base.start(f::Poly) = degree(f)
## Base.next(f::Poly, state) = (f[state]*variable(f)^state, state-1)
## Base.done(f::Poly, state) = state < 0

#Base.eps(::Type{Rational{BigInt}}) = 0

## iszero(x) = abs(x) <= eps(x)

## "Is k an approx zero?"
## function isazero{T}(p::Poly{T}, k)
##     thresh = 1e2 * norm(p) * degree(p)^2 * eps(T)
##     abs(polyval(p,k)) <= thresh
## end


## import Base: //
## //(x::Float64, y::Float64) = x/y



"Return  a monic polynomial from `p`. If `p==0` we return `p`"
monic(p::Poly) = p[end] != 0 ? Poly(p.a * inv(p[degree(p)]), p.var) : p
"""

Reverse polynomial.

E.g. `1 + 2x + 3x^2 -> 3 + 2x + 1x^2`.

Can set `k` so that we reverse poly `3 + 2x + 1x^2 + 0x^3 -> 0 + 1x +2x^2 + 3x^3`

"""
function Base.reverse{T}(p::Poly{T}, k=degree(p))
    k < degree(p) && error("k must be >= degree(p)")
    ps = T[p[i] for i in k:-1:0]
    Poly(ps, p.var)
end
reverse_coeffs(p::Poly) = reverse(coeffs(p))


## """

## Truncate terms order n or higher. Same as rem(p, x^(n))

## """
## Base.trunc(p::Poly, n::Int) = (1 <= n <= degree(p)-1) ? Poly(p[0:(n-1)], p.var) : p


"`mod(f::Poly, g::Poly)` remainder after division. Resulting poly has 0 <= degree < degree(g)"
Base.mod(f::Poly, g::Poly) = rem(f, g)

# content in poly ring R[u][v] is monic(gcd(...))
content{T}(p::Poly{T}) = convert(T, gcd(p.a))

function primitive{T}(p::Poly{T})
    ps = p.a
    b = content(p)
    qs = T[div(a,b) for a in ps]
    Poly(qs, p.var)
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



function Base.divrem(p::Poly, c::Number)
    ps = copy(p.a)                    # [p0, p1, ..., pn]
    qs = eltype(p)[pop!(ps)]           # take from right
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
    q, r = divrem(p,c)
    while abs(x) <=eps(x)
        p = q
        q,r = divrem(p, c)
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
    q,r = divrem(p,fact)
    while r == zero(Poly{T})
        q == zero(Poly{T}) && break  # divrem(Z[x],Z[x]) returns 0,0 if can't divide
        p = q
        q,r = divrem(p, fact)
        k = k + 1
    end
    p, k
end



## Special matrices related to polynomial factorization
function cauchy_matrix{T}(p::Poly{T}, k::Integer)
    n = degree(p) + 1
    out = zeros(T, n + k - 1, k)
    for i in 1:k
        out[(1:n) + (i-1), i] = reverse_coeffs(p)
    end
    out
end


function sylvester_matrix(p::Poly, q::Poly, k::Int=0)
    @assert k >= 0
    n,m = degree(p), degree(q)
    if n < m
        p,q = q,p
        n,m = m,n
    end

    del = n - m
    i,j = k + del, k
    if k == 0
        i,j = n,m
    end
    hcat(cauchy_matrix(q, i), cauchy_matrix(p, j))
end


"""
Sylvester matrix from Gathen Gerhard, p144
"""
Syl{R}(f::Poly{R}, g::Poly{R}) = sylvester_matrix(f, g)

"""
Resultant from Gathen Gerhard, p144 with cases
"""
function resultant{R}(f::Poly{R}, g::Poly{R})
    n,m=degree(f), degree(g)
    n == m == 0 && return 1
    g == zero(Poly{R}) && (f == zero(Poly{R}) || n >= 1) && return 0
    g == zero(Poly{R}) && (n == 1) && return 1
    f == zero(Poly{R}) && (g == zero(Poly{R}) || m >= 1) && return 0
    f == zero(Poly{R}) && (m == 1) && return 1

    return det(Syl(f,g))
end


## Polynomial transformations. From XXX
" `R(p)` finds  `x^n p(1/x)` which is a reversal of coefficients "
R(p) = Poly(reverse(p.a), p.var)

" `p(λ x)`: scale x axis by λ "
Hλ(p, λ=1//2) = polyval(p, λ * variable(p))

" `p(x + λ)`: Translate polynomial left by λ "
Tλ(p, λ=1)   = polyval(p, variable(p) + λ)

" shift and scale p so that  [c,c+1]/2^k -> [0,1] "
function Pkc(p::Poly, k, c)
    n = degree(p)
    2^(k*n) * Hλ(Tλ(p, c/2^k), 1/2^k)
end

## some things we can use `Polynomial` class, for others we need
## to use `Vector{T}`. Here are some methods, prefaced with `poly_`
## poly a0 + a1x + ... + an x^n --> [a0, a1,..., an]


function poly_primitive{T}(as::Vector{T})
    g = gcd(as)
    poly_zchop(T[div(a,g) for a in as])
end

## chop off leading 0s or return T[]
function poly_zchop{T}(x::Vector{T})
    for i in length(x):-1:1
        x[i] != zero(T) && return x[1:i]
    end
    T[]
end


poly_pad{T}(as::Vector{T}, n::Int) = length(as) >= n ? as : vcat(as, zeros(T,n-length(as)))
function poly_add{T,S}(as::Vector{T}, bs::Vector{S})
    m,n = length(as), length(bs)
    m == n && return as + bs
    m < n && return poly_pad(as,n) + bs
    poly_zchop(as + poly_pad(bs, m))
end
⊕{T,S}(as::Vector{T}, bs::Vector{S}) = poly_add(as, bs)

## classical multiplication. SHould replace with something faster? (Kurotsaba)
function poly_mul{T,S}(as::Vector{T}, bs::Vector{S})
    m,n = length(as), length(bs)
    cs = zeros(T, m+n-1)
    for i = 1:m
        for j = 1:n
            cs[i+j-1] += as[i] * bs[j]
        end
    end
    poly_zchop(cs)
end
⊗{T,S}(as::Vector{T}, bs::Vector{S}) = poly_mul(as,bs)
    



##################################################
## assume  poly in R[x],  R a ring.
## algo 2.5
## try to speed up compilation for different types
function poly_div_exact(a::Poly, b::Poly)
    const ZERO = zero(a)
    const ONE = one(a)
    n,m = degree(a), degree(b)
    n >= m || return ZERO, a
    bm = b[end]
    bmi = inv(bm)  ## must exist in R for this to work
    r = copy(a)
    x = variable(a)
    qs = zeros(eltype(a), n - m + 1)
    
    for i in (n-m):-1:0
        if degree(r) == m + i
            qi = lc(r) * bmi
            r = r - qi * x^i * b
            qs[i+1] = qi
        end
    end
    return Poly(qs, a.var)
end
    

## Polynomial gcd, ...

### Extended Euclidean Algorithm needs these defined for polys:
### With these defined, `bezout` will work over R[x], R a Euclidean Domain -- not Z[x], though

## Algorithms for Z[x]

"""

ALgorithm 9.3

Find inverse over <x^l> of f(x) in R[x], with R a ring

Assumes f(0) = 1. Otherwise, use inv(f(0)) * f

"""
function newton_inversion{T}(f::Poly{T}, l::Int)
    u = newton_inversion(f.a, l)
    Poly(u, f.var)
end

function newton_inversion{T}(f::Vector{T}, l::Int)
    f[1] == one(T) || error("need f(0) to be 1")
    g = ones(T, 1)
    r = ceil(Int, log2(l))
    for i in 1:r
        g = 2g ⊕ -f ⊗ g ⊗ g
        g = g[1:2^i]
    end
    g[1:l]
end
"""

Algorithm 9.5 fast division with remainder

a,b in R[x], R a commutive ring with one. Assume b \neq 0 is monic

a = q * b + r with deg(r) < deg(b)

Does not divide, so a, b in R[x]. Must assume b is monic.
"""


function fast_divrem{R}(a::Poly{R}, b::Poly{R})
    qs, rs = fast_divrem(a.a, b.a)
    Poly(qs, a.var), Poly(rs, a.var)
end

function fast_divrem{R}(as::Vector{R}, bs::Vector{R})
    bs = poly_zchop(bs)
    bs == zeros(R,1)  && error("Assume b is neq 0 and monic: $bs")
    bs[end] != one(R) && error("Assume b is neq 0 and monic: $bs")
    
    length(as) < length(bs) && return (zeros(eltype(as),1), as)
    m = length(as) - length(bs)

    ra, rb1 = reverse(as), newton_inversion(reverse(bs), m+1)
    
    q = (ra ⊗ rb1)[1:(m + 1)]
    qs = R[q[i] for i in reverse(1:m+1)] # reverse q but may need to pad 0s
    rs = as ⊕ -(bs ⊗ qs)

    (qs, rs)
end

# fast divrem over Z/pZ
function fast_divrem{R,T<:Integer}(as::Vector{R}, bs::Vector{R}, p::T)
    bs = poly_zchop(bs)
    bs == zeros(R,1)  && error("Assume b is neq 0 and monic; $bs")
    bs[end] != one(R) && error("Assume b is neq 0 and monic: $bs")
    
    length(as) < length(bs) && return (zeros(eltype(as),1), as)
    m = length(as) - length(bs)

    ra, rb1 = reverse(as), newton_inversion(reverse(bs), m+1)
    
    q = MOD(p)(ra ⊗ rb1)
    q = q[1:(m + 1)]
    qs = R[q[i] for i in reverse(1:m+1)] # reverse q but may need to pad 0s
    rs = MOD(p)(as ⊕ -(bs ⊗ qs))

    (qs, rs)
end


"""
pseudo division with remainder over Z[x]. Does not assume b is monic

Find q, r in Z[x] with lc(b)^(m-n + 1) * a = q * b + r

(Z[x] is not a Euclidean domain, so divrem does not exist within Z[x])
"""
function pdivrem{T<:Integer}(a::Poly{T}, b::Poly{T})
    
    m, n = degree(a), degree(b)
    m < n && error("degree(a) >= degree(b)")

    c = b[end]
    c == 1 && return(fast_divrem(a, b))
    
    x = variable(a)
    q = 0
    r = a * c^(m - n + 1)
    while degree(r) >= n
        s = div(r[end], c)  * x^(degree(r) - n )
        q = q + s
        r = r - s*b
    end

    q, r
end


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
    
    
"""
Is `g` square free? Assumes you can tell by comparing gcd(g, g')
"""
function issquarefree(g::Poly)
    u =  gcd(g,g')
    degree(u) == 0
end


"""

Yun's square free factorization fora field characteristic 0

Algo 14.21
"""
function yun_square_free{R <: Integer}(f::Poly{R})
    u,a,b= bezout(f, f')
    v,w  = div(f,a), div(f',b)
    hs = Poly{T}[]
    while true
        h,a,b = bezout(v, w - v')
        v, w = div(v, a), div(w - v', b)
        push!(hs, h)
        degree(v) == 0 && break
    end
    hs
end

"""

Square free

Take f(x) in R[x], return (f1, f2, ..., fk) where each is square free

recursively apply g = gcd(f, f'); (div(f,g), square_free(g)) to get this


"""
function square_free_parts{T}(f::Poly{T})
    degree(f) <= 1 && return [f]

    f' == zero(Poly{T}) && return[f]
    
    g, u, v = bezout(f, f')

    degree(g) == 0 && return [f]
    return vcat([div(f,g)], square_free(g))
end

"""
Return square free version of `f`
"""
function square_free{T<:Integer}(f::Poly{T})
    g = gcd(f, f')  # monic
    d = degree(g) 
    
    if  d > 0
        fsq,_ = exact_divrem(f, g)
    else
        fsq = f
    end
    fsq
end
 
    
