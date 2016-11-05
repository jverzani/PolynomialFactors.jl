#isdefined(Base, :__precompile__) && __precompile__()

module PolynomialFactors


## TODO
## tidy code base (Repeted squaring is improved; exact_divrem, not divrem;
## * remove p \in Int restriction by either using IntModn.jl or rewriting to use (array,p) representation for Z/nZ[x].
##   This is actually kinda necessary to be competitive time wise with SymPy
## * LLL could be implemented
## * could add real_roots here? But that seems out of place



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
