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

## find monic of degree d that is a factor of f
function _equal_degree_splitting_call(f::Poly, p, k, d::Int)
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
        b = sum([powermod(a, 2^i, f) for i in 0:(k-1)])   # trace polynomial
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
function equal_degree_factorization{Fq}(f::Poly{Fq}, d, MAXSTEPS)
    fail = zero(f)
    degree(f) == 0 && return [fail]
    degree(f) == 1 && return [f]
    degree(f) == d && return [f]
    
    g = equal_degree_splitting(f, d, MAXSTEPS)
    degree(g) == 0 && return [f]
    degree(g) == degree(f) && return [f]

    l = equal_degree_factorization(g, d, MAXSTEPS)
    r = equal_degree_factorization(div(f, g), d, MAXSTEPS)

    vcat(l, r)
end


function equal_degree_factorization{Fq}(f::Poly{Fq}, MAXSTEPS=12)
    n = degree(f)
    n == 0 && return [f]
    facs = factors(n) # isprime(n) ? [1] : vcat(1, collect(keys(factor(n))))

    for d in facs
        fs = equal_degree_factorization(f, d, MAXSTEPS)
        length(fs) > 1 && return fs # XXX ERROR!
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
    tm  = time()
    q = p^d
    T = typeof(f)    

    x = variable(f)

    h = x
    v = monic(f)
    i = 0
    U = Dict{T, Int}()
@time     gs = distinct_degree_factorization(f)
    for g in gs
        println("equal degree $g")
@time        factors = equal_degree_factorization(g)
        for fac in factors
            haskey(U,fac) && continue
            v,k = deflate(v,fac)
            U[fac] = k
        end
    end

    println("Factor over fq took: ", time() - tm)
    
    U

    
end




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
    poly_degree(f) == poly_degree(g) + poly_degree(h)  || error("need deg f = deg g + deg h; have: ")
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

                                      
"""

Algo 15.17 multifactor Hensel lifting

"""
function hensel_lift{T}(f::Poly{T}, m, a0, l)
    fbar = Znx(m, f)
    println("factor ov qer $m")
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

function factor{p,B}(f::Poly{ModInt{p,B}})
    !isprime(p) && error("Factoring over Z/pZ requires a prime value for `p`")
    _factor_over_Fq(f, p, 1)
end

function factor{p, d}(f::Poly{GF{p,d}})
    !isprime(p) && error("Factoring over F_q with q = p^d requires a prime value for `p`")
    _factor_over_Fq(f, p, d)
end

