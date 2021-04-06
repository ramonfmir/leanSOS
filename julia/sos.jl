using Pkg

Pkg.add("SumOfSquares")
Pkg.add("DynamicPolynomials")
Pkg.add("MosekTools")

using SumOfSquares, DynamicPolynomials, MosekTools

#= EXAMPLE 1 =#

# Using Mosek as the SDP solver
model = SOSModel(Mosek.Optimizer)

# Create symbolic variables
@polyvar x y
p = 2*x^4 + 2*x^3*y - x^2*y^2 + 5*y^4

# We want constraint `p` to be a sum of squares
con_ref = @constraint model p >= 0

optimize!(model)

# Solution status is `OPTIMAL` which means `p` is a sum of squares
#@show termination_status(model)

# Solution `FEASIBLE_POINT`
#@show primal_status(model)

# Show the decomposition 
# https://github.com/jump-dev/SumOfSquares.jl/blob/master/examples/Getting%20started.jl
#q = gram_matrix(con_ref)
@show gram_matrix(con_ref)
#@show SOSDecomposition(q)
