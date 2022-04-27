using Documenter
using PolynomialFactors

DocMeta.setdocmeta!(PolynomialFactors, :DocTestSetup, :(using PolynomialFactors); recursive=true)

makedocs(
    sitename = "PolynomialFactors",
    format = Documenter.HTML(ansicolor=true),
    modules = [PolynomialFactors]
)

deploydocs(
    repo = "github.com/jverzani/PolynomialFactors.jl"
)
