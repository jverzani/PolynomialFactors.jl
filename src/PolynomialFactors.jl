#isdefined(Base, :__precompile__) && __precompile__()

module PolynomialFactors


## TODO
## tidy code base (Repeted squaring is improved; exact_divrem, not divrem;
## add in Z/2Z -- easy, just need Tm's
## README examples
## restructure files: FiniteFields, Znx, Zx, factor, utils, polyutils
## implement EEA1, not generic one of wikipedia
## *maybe* add in real_roots here?

using Polynomials
using Iterators
using Compat

if VERSION < v"0.5.0"
    import Base: factor
else
    using Combinatorics
    using Primes
    
    import Primes: factor
end

## using Roots
##
include("utils.jl")
include("polyutils.jl")
include("finitefields.jl")
include("zx.jl")
include("factor.jl")

export ModInt, Zn, GF
export factor, rational_roots, factormod



end # module
