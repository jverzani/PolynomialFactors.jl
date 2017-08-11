### Code to identify irreducible factors of square free f
### from its factors over Zm which are lifted from factoring over Zp
### two main methods: one using short lattice, the other using exchaustive search

mu(i,j,B,Bs) = vecdot(B[i,:], Bs[j,:]) // vecdot( Bs[j,:], Bs[j,:] )

##
function reduce_BU!(i, B::Matrix{T}, U) where {T}
    m,n = size(B)
    for j=(i-1):-1:1
        r = round(T, U[i,j])
        for k in 1:n
            B[i,k] -=  r * B[j,k]
            U[i,k] -=  r * U[j,k]
        end
    end
end

function swaprows!(A, i, j)
    A[[i,j],:] = A[[j,i],:]
end

"""
Implementation of LLL basis reduction algorithm. This is from
http://algo.epfl.ch/_media/en/projects/bachelor_semester/rapportetiennehelfer.pdf .
The one in GG is a bit less efficient.

B is a matrix of row vectors

Modifies B to be a nearly orthogonal matrix of row vectors spannng the same integer lattice as the original B.
"""
function LLLBR!(B::Matrix{T}, c=2) where {T}
    m,n = size(B)
    m == n || throw(DomainError())
    
    const ONE::Rational{T}, ZERO::Rational{T} = one(Rational{T}), zero(Rational{T})

    ## initialize
    U  = zeros(Rational{T}, m, m)
    Bs = zeros(Rational{T}, m, m)

    for i in 1:m
        U[i,i] = ONE
        Bs[i,:] = B[i,:]
        for j in 1:(i-1)
            U[i,j] =  mu(i,j, B, Bs)
            Bs[i,:] -=  U[i,j] * Bs[j,:]
        end
        reduce_BU!(i, B, U)
    end
    
    i = 1
    ctr = 0
    while i < m
        ctr += 1
        if vecnorm(Bs[i,:], 2)^2 <= c * vecnorm(Bs[i+1,:], 2)^2
            i += 1
        else
            Bs[i+1, :] += U[i+1,i] * Bs[i,:]

            U[i:(i+1),i:(i+1)] = [mu(i,i+1, B, Bs) ONE; ONE ZERO]
            Bs[i,:] -=  U[i,i] * Bs[i+1,:]

            swaprows!(U,  i, i+1)
            swaprows!(B,  i, i+1)
            swaprows!(Bs, i, i+1)

            for k = (i+2):m
                U[k,i]   = mu(k,i, B, Bs) 
                U[k,i+1] = mu(k, i+1, B, Bs) 
            end

            abs(U[i+1,i]) > 1/2 && reduce_BU!(i+1, B, U)
            i = max(i-1, 1)
        end
    end
#    println("LLBR took $ctr steps")
end


## For a polynomial p, create a lattice of p, xp, x^2p, ... then find a short vector.
## This will be a potential factor of f
function short_vector(u::Poly{T}, m, j, d) where {T}
    F = zeros(T, j, j)
    us = coeffs(u)
    for i in 0:(j-d-1)
        F[1 + i, (1 + i):(1+i+d)] = us
    end
    for i in 0:(d-1)
        F[1 + j - d + i,1 + i] = m
    end
    LLLBR!(F)
    gstar = Poly(vec(F[1,:]), u.var)
end

## u is a factor over Zp
## we identify irreducible gstar of f
## return gstar, fstar = f / gstar (basically), and reduced Ts
function identify_factor(u::Poly{T}, fstar::Poly{T}, Ts::Vector{Poly{T}}, p::T, l::T, b, B) where {T}
    
    d, nstar = degree(u), degree(fstar)
    d < nstar || throw(DomainError())
    m = p^l
    j = d + 1
    gstar = u
    while j <= nstar+1
        gstar = short_vector(u,m,j,d)
        inds::Vector{Int} = filter(i -> poly_divides_over_Zp(gstar, Ts[i],  p)::Bool, eachindex(Ts))
        Ss::Vector{Poly{T}} = length(inds) > 0 ? Ts[setdiff(1:length(Ts), inds)] : Ts

        # find hstar = prod(Ts)
        hstar = mod(b, m) * one(Poly{T})
        for s in Ss
            hstar = MOD(m)(hstar * s)::Poly{T}
        end

        pd = norm(primitive(gstar),1) * norm(primitive(hstar), 1)
        
        if pd < B
            gstar, hstar = primitive(gstar), primitive(hstar)
            Ts = Ss # modify Ts (Ts[:])or make a copy?
            fstar = primitive(hstar)
            break
        end
        j = j + 1
    end

    primitive(gstar), fstar, Ts
end

"""
Use LLL basis reduction to identify factors of square free f from its factors over Zp
"""
function identify_factors_lll(f, facs, p, l, b, B)
    
    Ts = sort(facs, by=degree, rev=true)

    Gs = similar(Ts, 0)
    fstar = primitive(f)
    m = p^l

    while length(Ts) > 0
        u = shift!(Ts)
        if length(Ts) == 0
            push!(Gs, fstar)
            break
        end
        if degree(fstar) == degree(u)
             push!(Gs, fstar)
            break
        end
        gstar, fstar, Ts = identify_factor(u, fstar, Ts, p, l, b, B)
        push!(Gs, gstar)
    end
    Gs
end



##################################################
## This code tries all combinations of the irreducible factors over Z_p^l to see
## which correspond to irreducible factors over Z. For some polynomials, it
## will try all factors out, which will not scale well. 
function _poly_fish_out(S::Vector{Poly{T}}, k, p, l, b,B) where {T}
#    println("poly fish out: B=$B, $S")
    fail = zero(Poly{T})
    
    k > length(S) && return fail, Int[]
    
    for cmb in combinations(1:length(S), k)
        gs, hs = _partition_by(S, cmb)
        g = length(gs) > 0 ? MOD(p^l)(b * prod([MOD(p^l)(g) for g in gs])) : one(Poly{T})
        h = length(hs) > 0 ? MOD(p^l)(b * prod([MOD(p^l)(h) for h in hs])) : one(Poly{T})
        ## check size
        norm(g,1) * norm(h,1) <= B && return (primitive(g), cmb)
    end
    return fail,Int[]
end

## There are terms Ts that need piecing together to make factors
## Here R is a type, 
function identify_factors_exhaustive_search(f, facs, p, l, b, B)
    Ts = facs
    T = typeof(f)
    
    G = T[] 
    n = length(Ts)
    ZERO = zero(T)
    for k = 1:n
        k > length(Ts) && break
        fac, inds = _poly_fish_out(Ts, k, p, l, b, B)
        while fac != ZERO
            push!(G, fac)
            Ts = Ts[setdiff(1:length(Ts), inds)]
            k > length(Ts) && break
            fac, inds = _poly_fish_out(Ts, k, p, l, b, B)
        end
    end
    G
end

