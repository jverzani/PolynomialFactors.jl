##################################################
## Factoring over Fq[x], Z[x], Q[x]
## Following chapters 14 and 15 of Modern Computer Algebra by von zer Gathen and Gerhard
## TODO:

## * There was a paper on making bounds smaller and picking off one
##   factor, deflating anad
##   repeating. (http://icm.mcs.kent.edu/reports/1992/ICM-9201-26.pdf)
##   this might make larger ones possible. As right now, limited:
##   can't do x^100 -1 primes to big
## * LLL -- large n are really poor -- can't do x^60 - 1 too many combinations
## * ideas here http://www.math.fsu.edu/~hoeij/papers/issac10/A.pdf can be implemented

## Algorithm 14.13
function poly_factor_over_Zp{R,S}(a::Poly{R}, m::S, d=1)
    T = promote_type(R,S)
    f,p = convert(Poly{T}, a), convert(T,m)
    
    hi = x = variable(T)
    v = poly_monic_over_Zp(f, p)

    i= 0
    U = Dict{Poly{T}, Int}()

    while true
        i = i + 1
        hi = poly_powermod_over_Zp(hi, p, f, p)

        g = poly_gcd_over_Zp(hi -x, v, p)

        if degree(g) > 0
            facs = equal_degree_factorization_over_Zp(g, p, i)
            for fac in facs
                fac = MOD(p)(fac)
                v, k = deflate_over_Zp(v, fac, p)
                U[fac] = get(U, fac, 0) + k
            end
        end

        degree(v) <= 0 && break
    end
    U
end

###
function equal_degree_factorization_over_Zp{T <: Integer}(f::Poly{T}, p::T, d::Integer, MAXSTEPS=32)

    fail = Poly{T}[zero(f)]

    n = degree(f)
    n == 0 && return fail
    n == 1 && return Poly{T}[f]
    n == d && return Poly{T}[f]

    g = equal_degree_splitting_over_Zp(f, p, d, MAXSTEPS)::Poly{T}
    degree(g) <= 0 && return fail

    g1, g2 = g, poly_div_over_Zp(f, g, p)
    
    out = Poly{T}[]
    for h in (g1, g2)
        if degree(h) == d
            push!(out, h)
        else
            append!(out, equal_degree_factorization_over_Zp(h, p, d, 32)) # must have something
        end
    end
    
    out
end

## use random algorithm to find factor
function equal_degree_splitting_over_Zp{T}(f::Poly{T}, p::Integer, d::Integer, MAXSTEPS=16)
    fail = zero(f)
    
    n = degree(f)
    n <= 0 && return fail
    n == 1 && return f
    n == d && return f
    
    rem(n, d) == 0 || error("$d is not a divisor of the degree of f, $n")    
  
    ctr = 1
    while ctr <= MAXSTEPS
        g = _equal_degree_splitting_call(f, p, d)
        degree(g) > 0 && return g
        ctr = ctr + 1
    end
    return fail
end


## Algorithm 14.8
## find random monic of degree d that divides f
function _equal_degree_splitting_call{T}(f::Poly{T}, p::T, d::Integer)
    fail = zero(Poly{T})::Poly{T}
    # q divides d < n = degree(f)!!
    k = 1
    q = (p^k)::T
    n = degree(f)::Int
    

    a = poly_random_poly_over_Zp(T, n, p)::Poly{T}

    g = poly_gcd_over_Zp(a, f, p)::Poly{T}
    degree(g) > 0 && return g

    if isodd(p)
        n1 = ((q^d - 1) ÷ 2)::T
        b = poly_powermod_over_Zp(a, n1, f, p)::Poly{T}
    else
        m = k*d
        ## trace poly Tm = x^2^(m-1) + x^2^(m-2) + ... + x^4 + x^2 + x; this is Tm(a) (p399, p14.16)
        b = prod(Poly{T}[poly_powermod_over_Zp(a, 2^i, f, p) for i in 0:(m-1)])::Poly{T}
        b = poly_rem_over_Zp(b, f, p)::Poly{T}
    end

    g = poly_gcd_over_Zp(b - one(f), f, p)
    1 <= degree(g) < n && return g # does split

    return fail
end



##################################################
### Factor over Z[x]
##
## code to find factors from factors over Z/pZ

## Split set S into two pieces by index. Like partition from iterators
_partition_by{T}(S::Vector{T}, inds) = T[S[i] for i in inds], T[S[j] for j in setdiff(1:length(S), inds)]



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
function hensel_step{T}(f::Poly{T}, g::Poly, h::Poly, s::Poly, t::Poly, m)
    ## check conditions
    MOD(m)(f - g*h) == zero(f) || error("need f = gh mod m for inputs")
    lc(h) == 1 || error("need h monic")

    degree(f) == degree(g) + degree(h)  || error("need deg f = deg g + deg h")
    degree(s) < degree(h) || error("need deg s < deg h")
    degree(t) < degree(g) || error("need deg t < deg g")

    const ONE = one(Poly{T})
    fbar, gbar, hbar, sbar, tbar =   [MOD(m^2)(u) for u in (f,g,h,s,t)]

    ebar = MOD(m^2)(fbar -gbar * hbar)
    qbar,rbar = poly_fast_divrem_over_Zp(sbar * ebar, hbar, m^2)

    gstar = MOD(m^2)(gbar  + tbar * ebar + qbar * gbar)
    hstar = MOD(m^2)(hbar + rbar)
    
    bbar = MOD(m^2)(sbar * gstar + tbar * hstar - ONE)
    cbar, dbar = poly_fast_divrem_over_Zp(sbar * bbar, hstar, m^2)

    
    sstar = MOD(m^2)(sbar - dbar)
    tstar = MOD(m^2)(tbar -tbar * bbar - cbar * gstar)

    ## both these should be zero
#    vfy = MOD(m^2)(fbar + (-gstar * hstar)) 
#    vfy = MOD(m^2)(sstar * gstar + tstar * hstar - ONE)
            
    gstar, hstar, sstar, tstar 
end

# collect factors into a tree for apply HenselStep
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
    FactorTree_over_Zp(fg, p) = new(MOD(p)(prod(fg)), Any[])
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
    gi = invmod(g[0], p)  
    tau.s = MOD(p)(s * gi); tau.t = MOD(p)(t * gi)
    tau
end


function hensel_step_update_factor_tree!(tau, p)
    !has_children(tau) && return 
    l,r = tau.children
    f, g,h,s,t = tau.fg, l.fg, r.fg, tau.s, tau.t
    g1,h1,s1,t1 = hensel_step(f, g, h, s, t, p)
    tau.s, tau.t = s1, t1
    l.fg, r.fg = g1, h1
    hensel_step_update_factor_tree!(l, p)
    hensel_step_update_factor_tree!(r, p)
end

has_children(tau::AbstractFactorTree) = length(tau.children) == 2

function all_children(tau::AbstractFactorTree)
   has_children(tau) ? vcat(all_children(tau.children[1]), all_children(tau.children[2])) : [tau.fg]
end

                                        
"""

Algo 15.17 multifactor Hensel lifting

"""
function hensel_lift{T}(f, facs, m::T, a0, l)

    tau = make_factor_tree_over_Zp(facs, m)
    
    d = ceil(Int, log2(l))
    for j = 1:d
        a0 = mod(2*a0 - lc(f) * a0^2, m^2^j)
        tau.fg = a0 * f
        hensel_step_update_factor_tree!(tau, m^2^(j-1))
    end

    tau
end

function find_zassenhaus_bounds{T<:Integer}(f::Poly{T})
    n = degree(f)
    A = norm(f, Inf)
    b = lc(f)
    B = sqrt(n+1) * 2.0^n * A * b
    gamma = ceil(BigInt, 2*n*log2(n+1) + (2n-1)*log2(A))
    M = 2 * gamma * log(gamma)

    B, M
end

## compute values and bounds for zassenhaus factoring
function factor_zassenhaus_variables{T<:Integer}(f::Poly{T})

    n = degree(f)
    if n == 0
        f == zero(f) && return Dict(f => 0)
        return Dict{Poly{T},Int}()
    end
    n == 1 && return [f]

    A = norm(f, Inf)
    b = lc(f)
    B = sqrt(n+1) * 2.0^n * A * b
#    B = beauzamy_bound(f)
#    B = landau_mignotte(f)

    gamma = ceil(BigInt, 2*n*log2(n+1) + (2n-1)*log2(A))
    M = 2 * gamma * log(gamma)
    isnan(M) && error("Sorry, we need to get smarter, as primes needed are too big")

    p = floor(BigInt, M/2)
    while true
        p = nextprime(p)
        rem(b,p) != 0 && degree(poly_gcd_over_Zp(f, polyder(f), p)) <= 0 && break
    end

    l = ceil(T, log(p, 2B+1))
    a0 = invmod(b, p)

    a0, p, l, b, B

end
"""

Algorithm 15.19

Factoring using Hensel Lifting, Zassenhaus' algorithm

"""
function factor_square_free_zassenhaus{T<:Integer}(f::Poly{T})

    n = degree(f)
    n == 1 && return [f]
    n == 0 && return Poly{T}[]
    
    if lc(f) < 0
        f = -f
    end
    
#    facs, p, a0, l, b, B = factor_zassenhaus_variables(f)
    
    ## three steps of factoring: over p; lifting to p^l; sorting out irreducibles over Z
    B, M = find_zassenhaus_bounds(f)

    p, facs = poly_check_five_good_ps(f, M, n < 20 ? 3 : (n < 60 ? 3 : 2)) # engineer this: more takes more time, but can save time...
    length(facs) == 1 && return [f]
    
    b = lc(f)
    l = ceil(T, log(p, 2B+1))
    a0 = invmod(b, p)

    tau = hensel_lift(f, facs, p, a0, l)

    facs = all_children(tau)

    ## one is exponential, the 5th order. 20 is tunable... both are poor for x^40-1 with 40 factors over Zp
    if length(facs) > 20
        ps = identify_factors_lll(f, facs, p, l, b, B)
    else
        ps = identify_factors_exhaustive_search(f, facs, p, l, b, B)
    end
    ps
    
end


function factor_zassenhaus{T<: Integer}(f::Poly{T})
    ## deflate 0s
    nz = 0; while f(0) == zero(T)
        nz += 1
        f = Poly(coeffs(f)[2:end])
    end
    
    fsq = convert(Poly{BigInt}, f) |> square_free |> primitive
    
    ps = factor_square_free_zassenhaus(fsq)

    U = find_multiplicities(T, f, ps)
    nz > 0 && (U[variable(f)] = nz)
    U
end

##################################################
## some efficiencies in Wang, Trevisan, and til
## Check irreducible and if not return smallest number of factors
## after looking at 5 primes
function poly_check_five_good_ps{T}(f::Poly{T}, lambda, k=5)
    no_facs = degree(f) + 1
    facs = Poly{T}[]

    p = ceil(BigInt, lambda)
    P = p
    for i in 1:k
        while true
            p = nextprime(p)
            if rem(lc(f),p) != 0 && degree(poly_gcd_over_Zp(f, polyder(f), p)) <= 0
                # a good prime
                a0 = invmod(lc(f), p)
                f_facs = poly_factor_over_Zp(a0 * f, p)
                if length(f_facs) <= no_facs
                    no_facs = length(f_facs)
                    facs = f_facs
                    P = p
                    if no_facs == 1
                        return (P, [f])
                    end
                end
                break
            end
        end
    end
    return (P, collect(keys(facs)))
end


## return single_term beauzamy bound for f
function get_single_term_bound(f)
    c = 1
    n = degree(f)
    b = 2c * sqrt(2)^n / n^(3/8) * sqrt(bi2norm(f.a))
    beta = b * lc(f) # min(2b^2, 2b*PF.lc(f))

    beta
end


function find_term_exhaust{T}(f, S::Vector{Poly{T}}, k, p, l, b,B)
    fail = zero(Poly{T})
    
    k > length(S) && return fail, Int[]
    
    for cmb in combinations(1:length(S), k)
        gs, hs = _partition_by(S, cmb)
        g = length(gs) > 0 ? MOD(p^l)(b * prod([MOD(p^l)(g) for g in gs])) : one(Poly{T})
        g = primitive(g)
        q,r = exact_divrem(f, g)
        if r == zero(g) && q != zero(g)
            return (g, cmb)
        end
    end
    return fail,Int[]
end


function get_one_factor(f, facs,p, l, beta, k=1)
    a0 = invmod(f[end], p)
    tau = hensel_lift(f, facs, p, a0, l)
    facs = all_children(tau)

    fac = one(Poly{BigInt})
    inds = Int[]
    
    while k <= length(facs)
        fac, inds = find_term_exhaust(f, facs, k, p, l, f[end], beta)
        length(inds) > 0 && break
        k = k + 1
    end

    facs = facs[setdiff(eachindex(facs), inds)]
    fac, facs, k
end


## f a square free polynomial in Z[x] to factor
## return irreducibles f1, f2, ..., fr and c
## follows basic algorithm of http://icm.mcs.kent.edu/reports/1992/ICM-9201-26.pdf
## by Beauzamy, Trevisan and Want.
## Seems faster than factor_zassenhaus.
function beauzamy_trevisan_wang_factor_square_free{T <: Integer}(f::Poly{T})
    n = degree(f)
    n == 1 && return [f]
    n == 0 && return Poly{T}[]
    
    cont = content(f)
    f = primitive(f)
    
    if f[end] < 0
        f = -f
        cont = -cont
    end

    
    ## F-5
    ## reversed = false
    ## if abs(f[end]) > abs(f[0])
    ##     f = poly_reverse(f)
    ##     reversed = true
    ## end

    Fs = Poly{T}[]
    
    ## F-2    
    p, facs =  poly_check_five_good_ps(f, 10, n < 30 ? 5 : 3 ) # for large n, checking can take awhile.

    beta = get_single_term_bound(f)
    l = 0

    while degree(f) > 0
        beta = get_single_term_bound(f)
        if p^l < beta 
            ## must power up
            l = ceil(BigInt, log(p, beta))
            tau = hensel_lift(f, facs, p, invmod(f[end], p), l)
            facs = all_children(tau)
        end
        fac, facs, k = get_one_factor(f, facs, p, l, beta, 1)

        if degree(fac) >= 1
            f,r = exact_divrem(f, fac)
            push!(Fs, fac)
        else
            push!(Fs, f)
            break
        end
    end
    return Fs
end
    


function factor_btw{T<: Integer}(f::Poly{T})
    ## deflate 0s
    nz = 0; while f(0) == zero(T)
        nz += 1
        f = Poly(coeffs(f)[2:end])
    end
    
    fsq = convert(Poly{BigInt}, f) |> square_free |> primitive
    
    ps = beauzamy_trevisan_wang_factor_square_free(fsq)

    U = find_multiplicities(T, f, ps)
    nz > 0 && (U[variable(f)] = nz)
    U
end

##################################################

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

For this algorithm, factorization is done over a finite field using a
"good" prime and then lifted using Hensel's technique to a
factorization over `p^l`, where `l` is large enough that the modular
factors can be used to determine the factors over
`Z[x]`.

Factorization over a finite field can be done in different ways
(Cantor & Zassenhaous, Berlekamp, Kaltofen & Shoup, ...). Figure 14.9 and
the discussion on pages 381-2 in GG illustrate that none is
optimal. This function does not aim for best possible, which would
require implementing more algorithms, and follows the easier to
implement Cantor & Zassenhaus. Some polynomials can not be factored
here, e.g., `x^100 -1` as the primes needed get too big due to a bound
empoloyed.  (the bound includes both the degree and the size of the
coefficients).

The other part of the factorization task is identifying factors from
the factorization over `p^l`.  Two approaches -- a brute force
approach of looking at all factor combinations and the use of the LLL
algorithm are both utilized. The latter for when there are more
factors over Zp, the former when this number is small. Neither is
particularly speedy on the x^40-1 which factors into many linear
factors over Zp for the p found.


For faster, more able implementations accessible from within Julia,
see `SymPy.jl` or `Nemo.jl`, for example.

[1] *Modern Computer Algebra* By Joachim von zur Gathen and Jürgen
Gerhard. Cambridge University Press, 785 pages

"""
factor{R<:Integer}(f::Poly{R}) = factor_btw(f) # factor_zassenhaus(f)

## factor over Q[x], returns factors in Z[x].
function factor{T<:Integer}(p::Poly{Rational{T}})
    l, q = Qx_to_Zx(p)
    U = factor(q)
    V = Dict{Poly{Rational{T}}, Int}()
    for (k,v) in U
        if degree(k) == 0
            j = Poly(Rational{T}[k[0]//l])
        else
            j = convert(Poly{Rational{T}}, k)
        end
        V[j] = v
    end
    V
end


"""
Return all rational roots of a polynomial f in Z[x].
"""
function rational_roots{T<:Integer}(f::Poly{T})
    
    fsq = square_free(convert(Poly{BigInt}, f))
    ps = factor_square_free_zassenhaus(fsq)
    linear_facs = filter(p->degree(p) == 1, ps)
    sort(Rational{T}[-p[0] // p[1] for p in linear_facs])
end

rational_roots{T<:Integer}(f::Poly{Rational{T}}) = rational_roots(Qx_to_Zx(f)[2])

"""
Factor a polynomial `f` in Z[x] over Z/pZ[x], p a prime (not equal to 2).

    A dictionary is returned. The keys are the irreducible factors over Zp as polynomials over the integers. The coefficients are centered about 0.
"""
function factormod{T<:Integer,S<:Integer}(f::Poly{T}, p::S)
    g = convert(Poly{BigInt}, f)
    U = poly_factor_over_Zp(g, p)
    V = Dict{Poly{T}, Int}()
    for (v,k) in U
        V[convert(Poly{T}, v)] = k
    end
    ## add in constant term
    a = f[end]
    if a > div(p,2)  a = a - p end
    V[Poly([a])] = 1
    V
end






