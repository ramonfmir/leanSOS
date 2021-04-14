import os
import sys
from parse import *
from julia.api import Julia

def parse_arith(expr):
    return expr

def parse_expr(expr):
    try:
        lhs, rhs = parse("{}<={}", expr)
        lhs = parse_arith(lhs)
        rhs = parse_arith(rhs)
        return lhs, rhs
    except Exception as e:
        print("Invalid")

def run_sos(expr):
    jpath = "/Applications/Julia-1.5.app/Contents/Resources/julia/bin/julia"
    jl = Julia(runtime=jpath)

    jl.using('SumOfSquares')
    jl.using('DynamicPolynomials')
    jl.using('MosekTools')
    jl.eval('model = SOSModel(Mosek.Optimizer)')
    jl.eval('@polyvar x[1:10]')
    jl.eval('p = ' + expr[0])
    jl.eval('q = ' + expr[1])
    jl.eval('con_ref = @constraint model p <= q')
    jl.eval('optimize!(model)')
    result = str(jl.eval('return(gram_matrix(con_ref))'))
    evo, avo = parse("{}GramMatrix{}", result)

    return avo

if __name__ == "__main__":
    #sys.stdout = open(os.devnull, 'w')
    #matrix = run_sos(parse_expr("0 <= x[1]*x[1]"))

    #sys.stdout = sys.__stdout__
    #print(matrix)

    if (len(sys.argv) > 1):
        #expr = parse_expr(sys.argv[1])
        #gram = run_sos(expr)
        #print(gram)
        print("1")
        print("[[1]]") # this means [x1]. [[1,2], [3]] means [x1*x2, x3]
        print("[[1]]")
        print("[[1]]")

    else:
        print("Error")