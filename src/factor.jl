##################################################
## Factoring over Fq[x], Z[x], Q[x]
## Following chapters 14 and 15 of Modern Computer Algebra by von zer Gathen and Gerhard
## TODO:
## * over Z/2Z
## * LLL



"""

Algorithm 14.3 distinct degree factorizaton

input: square free monic f in Fq[x]
output: distinct degree decomposition

"""
distinct_degree_factorization{p,B}(f::Poly{ModInt{p,B}}) = _distinct_degree_factorization(f, p, 1)
distinct_degree_factorization{p,d}(f::Poly{GF{p,d}}) = _distinct_degree_factorization(f, p, d)


## f monic, q from Fq, a prime power, p^d
function _distinct_degree_factorization{Fq}(f::Poly{Fq}, p, d)
    n = degree(f)
    x = variable(f)
    q = p^d
    gs = Poly{Fq}[]

    h = x
    f0 = f
    i = 0

    while true
        i = i + 1
        h = powermod(h, q, f)
        g = gcd(h-x, f0)
        g = monic(g)

        if g != one(x)
            push!(gs, g) # con't add 1s
            f0 = div(f0, g)
        end

        if degree(f0) < 2*(i+1)
            degree(f0) > 0 && push!(gs, f0)
            break
        end
    end
    gs
end

"""

Algorithm 14.8 equal-degree-splitting

Find factor using random polynomial to guess.

* f is a square free monic polynomial in F_q(x) of degree n > 0
* d a divisor of n so that all irreducible factors of f have degree d
* MAXSTEPS: this is a random algorithm, stop if no success after this many steps (p < 2^-MAXSTEPS)

Retures a proper monic factor of f or the zero polynomial in Z_q
"""
equal_degree_splitting{p,B}(f::Poly{ModInt{p,B}}, d::Int, MAXSTEPS=16) = _equal_degree_splitting(p, 1, f, d::Int, MAXSTEPS)
equal_degree_splitting{p,k}(f::Poly{GF{p,k}}, d::Int, MAXSTEPS=16) = _equal_degree_splitting(p, k, f, d::Int, MAXSTEPS)

function _equal_degree_splitting(p, k, f, d::Int, MAXSTEPS)
    fail = zero(f)
    n = degree(f)
    rem(n,d) == 0 || error("$d is not a divisor of the degree of f")    
    n == 0 && return fail
    n == d && return f

  
    ctr = 1
    while ctr <= MAXSTEPS
        g = _equal_degree_splitting_call(f, p, k, d)
        degree(g) > 0 && return g
        ctr = ctr + 1
    end
    return fail
end


function _equal_degree_splitting_call(f, p, k, d::Int)
    fail = zero(f)
    # q divides d < n = degree(f)!!
    q = p^k
    n = degree(f)
    
    
    a = random_poly(eltype(f), n, f.var)
    # a \in F -> return fail

    g = gcd(a, f)
    (1 <= degree(g) < n) && return monic(g)

    if isodd(p)
        n1 = (q^d - 1) ÷ 2
        b = powermod(a, n1, f)
    else
        b = prod([powermod(a, 2^i, f) for i in 0:(k-1)])   # trace polynomial
        b = mod(b, f)
    end


    g = gcd(b - 1, f)
    (1 <= degree(g) < n) && return monic(g)

    return fail
end


# Algorithm 14.10
"

Find a factor of f \in Fq[x] or return 0. Has some small chance \approx 2^(-k) of being off
"
function equal_degree_factorization(f, d, MAXSTEPS)
    fail = zero(f)
    degree(f) == 0 && return [fail]
    degree(f) == 1 && return [f]
    degree(f) == d && return [f]
    
    g = equal_degree_splitting(f, d, MAXSTEPS)
    degree(g) == 0 && return [f]
    degree(g) == degree(f) && return [f]
    degree(g) == 1 && return vcat([g], equal_degree_factorization(div(f, g), d, MAXSTEPS))
    return vcat(equal_degree_factorization(g,         d, MAXSTEPS),
                equal_degree_factorization(div(f, g), d, MAXSTEPS)
                )
end

function equal_degree_factorization(f, MAXSTEPS=16)
    n = degree(f)
    n == 0 && return [f]
    facs = isprime(n) ? [1] : vcat(1, collect(keys(factor(n))))

    for d in facs
        fs = equal_degree_factorization(f, d, MAXSTEPS)
        length(fs) > 1 && return fs
    end
    return [f]
end
    

"""

Algorithm 14.13, with modifications

input nonconstant f in Fq[x], q = p^n
output monic irreducible factors of f, and multiplicities


"""
factor_over_Fq{p,B}(f::Poly{ModInt{p,B}}) = _factor_over_Fq(f, p, 1)
factor_over_Fq{p,d}(f::Poly{GF{p,d}}) = _factor_over_Fq(f, p, d)

function _factor_over_Fq(f, p, d)
    q = p^d
    T = typeof(f)    

    x = variable(f)

    h = x
    v = monic(f)
    i = 0
    U = Dict{T, Int}()

    gs = distinct_degree_factorization(f)
    for g in gs
        factors = equal_degree_factorization(g)
        for fac in factors
            haskey(U,fac) && continue
            v,k = deflate(v,fac)
            U[fac] = k
        end
    end
    U

    
end


### Factor over Z[x]

"""

Algorithm 15.2 Factorization in Z[x] (big prime version)

Return an array of factors of g

We don't use this, as we need primes that are too big to fit in Int64, which is needed for Zn{p}.
"""
function factor_square_free_big_prime{R<:Integer}(g::Poly{R})
    degree(g) <= 1 && return [g]
    # pull out leading term
    b = lc(g)
    g = primitive(g)
    if b < 0 
        b = -b; g = -g
    end

    # make bound
    n = degree(g)
    A = norm(g, Inf)
    Br = sqrt(n+1) * 2^n * A * b
    M = 1000
    B = M^ceil(Int, log(M, Br)) ## round up to possibly avoid compilation

    ## find p so that gbar(p) is square free
    p = 2B  # need a good prime in [2B, 4B] here we search in order
    while true
        p = nextprime(p)
        issquarefree(convert(Poly{Zn{p}}, g)) && break
    end

    ps = convert(Poly{ModInt{p, true}}, g)  |> factor_over_Fq |> keys |> collect
    ps = fish_out(R, ps, p, 1, b, B)
    
end


"""

Factor using a big prime algorithm

"""
function factor_big_prime{R<:Integer}(f::Poly{R})
    fsq = square_free(f)
    ps = factor_square_free_big_prime(fsq)
    find_multiplicities(R, f, ps)
end

##################################################
##
## code to find factors from factors over Z/pZ


## Split set S into two pieces by index. Like partition from iterators
_partition_by{T}(S::Vector{T}, inds) = [S[i] for i in inds], [S[j] for j in setdiff(1:length(S), inds)]

## fish out a factor or return 0 using k terms of S
function _fish_out(S::Vector, k,  b,B)
    fail = zero(S[1])
    
    k > length(S) && return fail,Int[]
    
    for cmb in combinations(1:length(S), k)
        gs, hs = _partition_by(S, cmb)

        g, h = Znx(oo, b * prod(gs)), Znx(oo, b * prod(hs))
        ## Odd, can't call norm. Znx(oo, .) conversion oddity XXX
        ## norm(g,1) * norm(h,1) <= B && return (primitive(g), cmb)
        sum(Int[abs(u) for u in g.a]) * sum(Int[abs(u) for u in h.a]) <= B && return primitive(g), cmb
    end
    return fail,Int[]
end

## There are terms Ts that need piecing together to make factors
## Here R is a type, 
function fish_out(R, Ts,  b, B)
    T = eltype(Ts)
    G = Poly{R}[] #Any[] #Poly{R}[]
    n = length(Ts)
    ZERO = zero(T)
    for k = 1:n
        k > length(Ts) && break
        fac, inds = _fish_out(Ts, k, b, B)
        while fac != ZERO
            push!(G, fac)
            Ts = Ts[setdiff(1:length(Ts),inds)]
            k > length(Ts) && break
            fac, inds = _fish_out(Ts, k,  b, B)
        end
    end
    G
end


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
            g = MOD(p^l, true)(b * reduce(poly_mul, [MOD(p^l,true)(g) for g in gs]))
        end
        if length(hs) == 0
            h = ones(T, 1)
        else
            h = MOD(p^l, true)(b * reduce(poly_mul, [MOD(p^l,true)(h) for h in hs]))
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

    G1

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
function hensel_step(f::Poly, g::Poly, h::Poly, s::Poly, t::Poly, m)
    [Znx(m^2, a) for a in hensel_step(f.a, g.a, h.a, s.a, t.a, m)]
end

function hensel_step{T}(f::Vector{T}, g::Vector, h::Vector, s::Vector, t::Vector, m)
    ## check
    mod(sum(MOD(m)(f) ⊕ -MOD(m)(g) ⊗ MOD(m)(h)),m) == zero(T) || error("need f = gh mod m for inputs")
    
    h[end] == 1 || error("need h monic")
    length(f) -1  == length(g) -1 + length(h) -1 || error("need deg f = deg g + deg h")
    length(s) < length(h) || error("need deg s < deg h")
    length(t) < length(g) || error("need deg t < deg g")

    fbar, gbar, hbar, sbar, tbar =   [MOD(m^2)(u) for u in (f,g,h,s,t)]

    ebar = fbar ⊕ (-gbar ⊗ hbar)
    qbar,rbar = fast_divrem(sbar ⊗ ebar, hbar, m^2)

    gstar = MOD(m^2)(gbar  ⊕ tbar ⊗ ebar ⊕ qbar ⊗ gbar)
    hstar = MOD(m^2)(hbar ⊕ rbar)
    
    bbar = MOD(m^2)(sbar ⊗ gstar ⊕ tbar ⊗ hstar ⊕ (-ones(T,1)))
    cbar, dbar = fast_divrem(sbar ⊗ bbar, hstar, m^2)

    
    sstar = MOD(m^2)(sbar ⊕ -dbar)
    tstar = MOD(m^2)(tbar ⊕ (-tbar ⊗ bbar) ⊕ (-cbar ⊗ gstar))

    gstar, hstar, sstar, tstar 
end


type FactorTree
    fg
    children
    s
    t
    FactorTree(fg) = new(prod(fg), Any[])
end

function make_factor_tree(x)
    N = length(x)
    n = ceil(Int, log2(N))
    tau =  FactorTree(x)
    N == 1 && return tau

    k = 2^(n-1)
    l, r = x[1:k], x[(k+1):end]
    tau.children = Any[make_factor_tree(l), make_factor_tree(r)]
    g, s, t = bezout(tau.children[1].fg, tau.children[2].fg)
    tau.s = s / g[0]; tau.t = t / g[0]
    tau
end

## use array for polys, not `Poly` class
function factor_tree_as_poly(T, tau, m)
    tau.fg = T[mod(convert(T,a),m) for a in coeffs(tau.fg)]
    length(tau.children) == 0 && return
    l,r = tau.children
    tau.s =  T[mod(convert(T,a),m) for a in coeffs(tau.s)]
    tau.t =  T[mod(convert(T,a),m) for a in coeffs(tau.t)]
    factor_tree_as_poly(T,l,m)
    factor_tree_as_poly(T,r,m)
end


has_children(tau::FactorTree) = length(tau.children) == 2

function all_children(tau::FactorTree)
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
function hensel_lift{T}(f::Poly{T}, m, a0, l)
    fbar = Znx(m, f)
    facs = factor(a0 * fbar) |> keys |> collect

    m = convert(T, m) # need Int in factor over Zp, but not afterwards
    tau = make_factor_tree(facs)
    factor_tree_as_poly(T,tau,m)     ## make poly_ type
    
    d = ceil(Int, log2(l))
    for j = 1:d
        a0 = mod(2*a0 - lc(f) * a0^2, m^2^j)
        tau.fg = a0 * (f.a) 
        hensel_step_update_factor_tree!(tau, m^2^(j-1))
    end

    a0, tau    
end

"""

Algorithm 15.19

Factoring using Hensel Lifting, Zassenhaus' algorithm

"""
function factor_square_free_zassenhaus{T<:Integer}(f::Poly{T})
  
    if lc(f) < 0
        f = -f
    end

    n = degree(f)
    n == 0 && error("Must have non-constant polynomial")
    n == 1 && return [f]

    A = norm(f, Inf)
    b = lc(f)
    B = sqrt(n+1) * 2.0^n * A * b
    C = (n+1.0)^(2n) * A^(2n-1)
    2log2(C) > typemax(Int) && error("Sorry, primes needed are too big for this implementation")
    
    gamma = ceil(Int, 2log2(C))
    M = 2gamma * log(gamma)
    M > typemax(Int) && error("Sorry, primes needed are too big for this implementation")    
    rng = floor(Int, M/2), ceil(Int, M)
    
    # find p
    p = 0
    while true
        p = rand(primes(rng...))
        rem(b,p) != 0 && degree(gcd(Znx(p,f), Znx(p, f'))) == 0 && break
    end
    L = floor(Int, log(p, typemax(p)))
    l = ceil(Int, log(p, 2B+1))

    a0 = invmod(b, p)
    a0, tau = hensel_lift(f, p, a0, l)

    facs = all_children(tau)

    ps = poly_fish_out(T, facs, convert(T,p), l, b, B) 
    
end
                 
function factor_zassenhaus{T<: Integer}(f::Poly{T})
    fsq = square_free(f)
    ps = factor_square_free_zassenhaus(fsq)
    find_multiplicities(T, f, ps)
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
factormod{T<:Integer}(f::Poly{T}, p::Int) = factor(Znx(p, f))
function factor{p,B}(f::Poly{ModInt{p,B}})
    !isprime(p) && error("Factoring over Z/pZ requires a prime value for `p`")
    _factor_over_Fq(f, p, 1)
end

function factor{p, d}(f::Poly{GF{p,d}})
    !isprime(p) && error("Factoring over F_q with q = p^d requires a prime value for `p`")
    _factor_over_Fq(f, p, d)
end





## Try to speed up the initial calsl
precompile(gcd, (Poly{Int},Poly{Int}))
precompile(modular_gcd_small_prime,  (Poly{Int},Poly{Int}))
precompile(factor_square_free_zassenhaus, (Poly{Int},))
precompile(factor, (Poly{Int},))
precompile(factor, (Poly{BigInt},))
precompile(factor, (Poly{Rational{Int}},))
precompile(factor, (Poly{Rational{BigInt}},))

