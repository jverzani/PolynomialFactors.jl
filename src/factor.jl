##################################################
## Factoring over Fq[x], Z[x], Q[x]
## Following chapters 14 and 15 of Modern Computer Algebra by von zer Gathen and Gerhard
## TODO:
## * There was a paper on making bounds smaller andpicking off one factor, deflating anad repeating.
##   this might make larger ones possible. As right now, limited: can't do x^100 -1 primes to big
## * LLL -- large n are really poor -- can't do x^60 - 1 too many combinations

## Algorithm 14.13 
function poly_factor_over_Zp{R,S}(f::Vector{R}, q::S, d=1)
    T = promote_type(R,S)
    p = convert(T, q)

    hi = x = T[zero(T), one(T)]
    v = poly_monic_over_Zp(convert(Vector{T}, f), p)

    i= 0
    U = Dict{Vector{T}, Int}()

    
    while true
        i = i + 1
        hi = poly_powermod_over_Zp(hi, p, f, p)
        g = poly_gcd_over_Zp(hi ⊕ -x, v, p)

        if poly_degree(g) > 0
            factors = equal_degree_factorization_over_Zp(g, p, i)
            for fac in factors
                fac = MOD(p)(fac)
                v, k = deflate_over_Zp(v, fac, p)
                U[fac] = get(U,fac,0) + k
            end
        end

        poly_degree(v) <= 0 && break
    end

    U
end
###
function equal_degree_factorization_over_Zp{T <: Integer}(f::Vector{T}, p::T, d::Integer, MAXSTEPS=32)

    fail = Any[T[]]

    n = poly_degree(f)
    n == 0 && return fail
    n == 1 && return Any[f]
    n == d && return Any[f]

    g = equal_degree_splitting_over_Zp(f, big(p), d, MAXSTEPS)
    poly_degree(g) <= 0 && return fail

    g1, g2 = g, poly_div_over_Zp(f, g, big(p))

    out = Any[]
    for h in (g1, g2)
        if poly_degree(h) == d
            push!(out, h)
        else
            append!(out, equal_degree_factorization_over_Zp(h, big(p), d, 32)) # must have something
        end
    end
    
    out
end

## use random algorithm to find factor
function equal_degree_splitting_over_Zp{T}(f::Vector{T}, p::Integer, d::Integer, MAXSTEPS=16)
    fail = T[]
    
    n = poly_degree(f)
    n <= 0 && return fail
    n == 1 && return f
    n == d && return f
    
    rem(n, d) == 0 || error("$d is not a divisor of the degree of f, $n")    
  
    ctr = 1
    while ctr <= MAXSTEPS
        g = _equal_degree_splitting_call(f, p, d)
        poly_degree(g) > 0 && return g
        ctr = ctr + 1
    end
    return fail
end


## Algorithm 14.8
## find random monic of degree d that divides f
function _equal_degree_splitting_call{T}(f::Vector{T}, p::T, d::Integer)
    fail = T[]
    # q divides d < n = degree(f)!!
    k = 1
    q = p^k
    n = poly_degree(f)
    

    a = poly_random_poly_over_Zp(T, n, p)

    g = poly_gcd_over_Zp(a, f, p)
    poly_degree(g) > 0 && return g

    if isodd(p)
        n1 = (q^d - 1) ÷ 2
        b = poly_powermod_over_Zp(a, n1, f, p)
    else
        b = reduce(⊕, ([poly_powermod_over_Zp(a, 2^i, f, p) for i in 0:((k*d)-1)]))   # trace polynomial
        b = poly_rem_over_Zp(b, f, p)
    end


    g = poly_gcd_over_Zp(b ⊕ (-ones(T,1)), f, p)
    1 <= poly_degree(g) < n && return g # does split

    return fail
end



### Factor over Z[x]
##################################################
##
## code to find factors from factors over Z/pZ


## Split set S into two pieces by index. Like partition from iterators
_partition_by{T}(S::Vector{T}, inds) = [S[i] for i in inds], [S[j] for j in setdiff(1:length(S), inds)]

## poly
function _poly_fish_out(S::Vector, k, p, l, b,B)
    fail = zero(S[1])
    T = eltype(S[1])
    
    k > length(S) && return fail,Int[]
    
    for cmb in combinations(1:length(S), k)
        gs, hs = _partition_by(S, cmb)
        (length(gs) == 0 || length(hs) == 0)
        if length(gs) == 0
            g = ones(T,1)
        else
            g = MOD(p^l, true)(b * reduce(⊗, [MOD(p^l,true)(g) for g in gs]))
        end
        if length(hs) == 0
            h = ones(T, 1)
        else
            h = MOD(p^l,true)(b * reduce(⊗, [MOD(p^l,true)(h) for h in hs]))
        end
        
        norm(g,1) * norm(h,1) <= B && return (poly_primitive(g), cmb)
    end
    return fail,Int[]
end

## There are terms Ts that need piecing together to make factors
## Here R is a type, 
function poly_fish_out(R, Ts, p, l, b, B)
    T = eltype(Ts[1])
    G = Poly{R}[] #Any[] #Poly{R}[]
    n = length(Ts)
    ZERO = T[]
    for k = 1:n
        k > length(Ts) && break
        fac, inds = _poly_fish_out(Ts, k, p, l, b, B)
        while poly_zchop(fac) != ZERO
            push!(G, Poly(fac))
            Ts = Ts[setdiff(1:length(Ts),inds)]
            k > length(Ts) && break
            fac, inds = _poly_fish_out(Ts, k, p, l, b, B)
        end
    end
    G
end



##################################################
##
## Hensel lifting approach to factoring

"""
algorithm 15.10

One hensel step

for f,g,h,s,t in Z[x]  or Z/pZ[x] with

1) f= gh mod m; sg+th = 1 mod m
2) h is monic
3) degree(f) = degree(g) + degree(h)
4) degree(s) < degree(h), degree(t) < degree(g)

output g*,h*,s*,t* in Z/m^2Z[x] with 1) - 4) holding over m^2
"""
function hensel_step{T}(f::Vector{T}, g::Vector, h::Vector, s::Vector, t::Vector, m)
    ## check
    mod(sum(MOD(m)(f) ⊕ -MOD(m)(g) ⊗ MOD(m)(h)),m) == zero(T) || error("need f = gh mod m for inputs")
    h = poly_zchop(h)
    h[end] == 1 || error("need h monic")
    poly_degree(f) == poly_degree(g) + poly_degree(h)  || error("need deg f = deg g + deg h")
    poly_degree(s) < poly_degree(h) || error("need deg s < deg h")
    poly_degree(t) < poly_degree(g) || error("need deg t < deg g")

    fbar, gbar, hbar, sbar, tbar =   [MOD(m^2)(u) for u in (f,g,h,s,t)]

    ebar = MOD(m^2)(fbar ⊕ (-gbar ⊗ hbar))
    qbar,rbar = fast_divrem(sbar ⊗ ebar, hbar, m^2)

    gstar = MOD(m^2)(gbar  ⊕ (tbar ⊗ ebar) ⊕ (qbar ⊗ gbar))
    hstar = MOD(m^2)(hbar ⊕ rbar)
    
    bbar = MOD(m^2)((sbar ⊗ gstar) ⊕ (tbar ⊗ hstar) ⊕ (-ones(T,1)))
    cbar, dbar = fast_divrem(sbar ⊗ bbar, hstar, m^2)

    
    sstar = MOD(m^2)(sbar ⊕ (-dbar))
    tstar = MOD(m^2)(tbar ⊕ (-tbar ⊗ bbar) ⊕ (-cbar ⊗ gstar))

    vfy = MOD(m^2)(fbar ⊕ (-gstar ⊗ hstar)) ## should be 0
    
    gstar, hstar, sstar, tstar 
end

abstract AbstractFactorTree

type FactorTree <: AbstractFactorTree
    fg
    children
    s
    t
    FactorTree(fg) = new(prod(fg), Any[])
end

type FactorTree_over_Zp <: AbstractFactorTree
    fg
    children
    s
    t
    FactorTree_over_Zp(fg, p) = new(MOD(p)(reduce(⊗,fg)), Any[])
end

function make_factor_tree_over_Zp(x, p)
    N = length(x)
    n = ceil(Int, log2(N))
    tau =  FactorTree_over_Zp(x,p)
    N == 1 && return tau

    k = 2^(n-1)
    l, r = x[1:k], x[(k+1):end]
    tau.children = Any[make_factor_tree_over_Zp(l, p), make_factor_tree_over_Zp(r, p)]
    g, s, t = poly_bezout_over_Zp(tau.children[1].fg, tau.children[2].fg, p)
    gi = invmod(g[1], p)
    tau.s = MOD(p)(s * gi); tau.t = MOD(p)(t * gi)
    tau
end

## ## use array for polys, not `Poly` class
## function factor_tree_as_poly(T, tau, m)
##     tau.fg = T[mod(convert(T,a),m) for a in coeffs(tau.fg)]
##     length(tau.children) == 0 && return
##     l,r = tau.children
##     tau.s =  T[mod(convert(T,a),m) for a in coeffs(tau.s)]
##     tau.t =  T[mod(convert(T,a),m) for a in coeffs(tau.t)]
##     factor_tree_as_poly(T,l,m)
##     factor_tree_as_poly(T,r,m)
## end


has_children(tau::AbstractFactorTree) = length(tau.children) == 2

function all_children(tau::AbstractFactorTree)
    if has_children(tau)
        kids = vcat(all_children(tau.children[1]), all_children(tau.children[2]))
    else
        kids = Any[tau.fg]
    end
    kids
end

function hensel_step_update_factor_tree!(tau, p)
    length(tau.children) == 0 && return 
    l,r = tau.children
    f, g,h,s,t = tau.fg, l.fg, r.fg, tau.s, tau.t
    g1,h1,s1,t1 = hensel_step(f, g, h, s, t, p)
    tau.s, tau.t = s1, t1
    l.fg, r.fg = g1, h1
    hensel_step_update_factor_tree!(l, p)
    hensel_step_update_factor_tree!(r, p)
end


                                        
"""

Algo 15.17 multifactor Hensel lifting

"""
function hensel_lift{T}(f::Vector{T}, m::T, a0, l)
    
    facs = poly_factor_over_Zp(a0 * f, m) |> keys |> collect
    tau = make_factor_tree_over_Zp(facs, m)
    
    d = ceil(Int, log2(l))
    for j = 1:d
        a0 = mod(2*a0 - f[end] * a0^2, m^2^j)
        tau.fg = a0 * f
        hensel_step_update_factor_tree!(tau, m^2^(j-1))
    end

    a0, tau    
end


"""

Algorithm 15.19

Factoring using Hensel Lifting, Zassenhaus' algorithm

"""
function factor_square_free_zassenhaus{T<:Integer}(f::Vector{T})

    f = poly_zchop(f)
    if f[end] < 0
        f = -f
    end

    n = poly_degree(f)
    n == 0 && error("Must have non-constant polynomial")
    n == 1 && return [Poly(f)]

    A = norm(f, Inf)
    b = f[end]
    B = sqrt(n+1) * 2.0^n * A * b
    C = (n+1.0)^(2.0 * n) * A^(2.0 * n-1)
    
    gamma = ceil(BigInt, 2log2(C))
    M = 2gamma * log(gamma)

    isnan(M) && error("Sorry, we need to get smarter, as primes needed are too big")
#    M/2 > typemax(Int) && println("Sorry, primes needed are too big for this implementation")    ## use SymEngine..

    p = floor(BigInt, M/2)
    while true
        p = nextprime(p)
        rem(b,p) != 0 && poly_degree(poly_gcd_over_Zp(f, poly_der(f), p)) <= 0 && break
    end

    l = ceil(T, log(p, 2B+1))
    a0 = invmod(b, p)
    a0, tau = hensel_lift(f, p, a0, l)

    facs = all_children(tau)
    ps = poly_fish_out(T, facs, p, l, b, B) 
    
end
  


function factor_zassenhaus{T<: Integer}(f::Poly{T})
    ## deflate 0s
    nz = 0; while f(0) == zero(T)
        nz += 1
        f = Poly(coeffs(f)[2:end])
    end
    
    fsq = convert(Poly{BigInt}, f) |> square_free |> coeffs |> poly_primitive
    
    ps = factor_square_free_zassenhaus(fsq)

    U = find_multiplicities(T, f, ps)
    nz > 0 && (U[variable(f)] = nz)
    U
end


"""
Take f in Q[x] return l in Z, p in Z[x] where roots are the same
"""
function Qx_to_Zx{T}(f::Poly{Rational{T}})
    n = degree(f)
    l = reduce(lcm, [a.den for a in coeffs(f)])
    p = convert(Poly{T}, l * f)
    (l, p)
end





### External interface for factoring, root finding, ...

"""

Factor f ∈ Z[x] (Z is `Int` or `BigInt`) over the rationals (`px + q`).

Returns a dictionary with factors and multiplicities.

Examples:

```
x = variable(Int)
f = (x-1)^20 * (2x-3) * (x^5 - x - 1)
factor(f)  ## return dictionary with keys (x-1), (2x-3), and (x^5 - x - 1)
f = (12x + 13) * (x-1) * (x^2 - 1) * (x^3 - 1)
factor(f) ##  # Dictionary -1 + x, 13 + 12⋅x, 1 + x, 1 + x + x^2

x = variable(BigInt)
f = (2x-1)^20*(x-2)^10*(2x-3)^10*(3x-4)^10
factor(f)  # as expected


f = prod([x-i for i in 1:20]) 
factor(f)

R = big(2)^256
factor(x^2 - R)


x = variable(Rational{Int})
f = 1//2 * x^3  + 3//4 * x^2 + 4//5 *x
factor(f)
```

Notes:


Uses Zassenhaus' algorithm 15.19 from *Modern Computer Algebra* By Joachim von zur Gathen and
Jürgen Gerhard (GG, [1]). There is some randomness in the algorithm for factorization over a prime.

For this algorithm factorization is done over a finite field over a
"good" prime and then lifted using Hensel's technique to a
factorization over `p^l`, where `l` is large enough that the modular
factors can be used to determine the factors over
`Z[x]`.

Factorization over a finite field can be done in different ways
(Cantor & Zassenhaous, Berlekamp, Kaltofen & Shoup). Figure 14.9 and
the discussion on pages 381-2 in GG illustrate that none is
optimal. This function does not aim for best possible, which would
require implementing more algorithms, and follows the easier to
implement Cantor & Zassenhaus. For technical reasons, the prime `p`
must be of type `Int`, which limits the size of the polynomials that
can be factored (the bound includes both the degree and the size of the coefficients).

The other part of the factorization task implemented that is not
optimal is identifying factors from the factorization over `p^l`. The
short vector lattice approach of LLL is not used, rather a potentially
much slower brute force approach is taken (looking at all factor
combinations).

For faster, more able implementations accessible from within Julia,
see `SymPy.jl` or `Nemo.jl`, for example.

[1] *Modern Computer Algebra* By Joachim von zur Gathen and Jürgen
Gerhard. Cambridge University Press, 785 pages

"""
factor{R<:Integer}(f::Poly{R}) = factor_zassenhaus(f)

## factor over Q[x], returns factors in Z[x].
function factor{T<:Integer}(p::Poly{Rational{T}})
    l, q = Qx_to_Zx(p)
    factor(q)
end


"""
Return all rational roots of a polynomial f in Z[x].
"""
function rational_roots{T<:Integer}(f::Poly{T})
    fsq = square_free(f)
    ps = factor_square_free_zassenhaus(fsq)
    linear_facs = filter(p->degree(p) == 1, ps)
    sort([-p[0] // p[1] for p in linear_facs])
end

rational_roots{T<:Integer}(f::Poly{Rational{T}}) = rational_roots(Qx_to_Zx(f)[2])

"""
Factor a polynomial `f` in Z[x] over Z/pZ[x], p a prime (not equal to 2).

"""
function factormod{T<:Integer,S<:Integer}(f::Poly{T}, p::S)
    U = poly_factor_over_Zp(coeffs(f), p)
    [Poly(k)=>v for (k,v) in U]
end




## Try to speed up the initial calsl
precompile(gcd, (Poly{Int},Poly{Int}))
precompile(modular_gcd_small_prime,  (Poly{Int},Poly{Int}))
precompile(factor_square_free_zassenhaus, (Poly{Int},))
precompile(factor, (Poly{Int},))
precompile(factor, (Poly{BigInt},))
precompile(factor, (Poly{Rational{Int}},))
precompile(factor, (Poly{Rational{BigInt}},))

