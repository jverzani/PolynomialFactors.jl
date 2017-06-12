isdefined(Base, :__precompile__) && __precompile__()

module PolynomialFactors


## TODO
## * performance is really poor for larger degrees.




using Polynomials
using Compat

if VERSION < v"0.5.0"
    import Base: factor
else
    using Combinatorics
    using Primes

    import Primes: factor
end

include("utils.jl")
include("polyutils.jl")
include("zx.jl")
include("lll.jl")
include("factor.jl")

export factor, rational_roots, factormod

## Try to speed up the initial calls
precompile(egcd, (Poly{BigInt},Poly{BigInt}))
precompile(modular_gcd_small_prime,  (Poly{BigInt},Poly{BigInt}))
precompile(factor_square_free_zassenhaus, (Poly{BigInt},))
precompile(factor, (Poly{Int},))
precompile(factor, (Poly{BigInt},))
precompile(factor, (Poly{Rational{Int}},))
precompile(factor, (Poly{Rational{BigInt}},))


end # module
