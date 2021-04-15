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

# Transforms 'a, b; c, d' into '[[a, b], [c, d]].
def format_matrix(M):
    rows = M.split(';')
    return "[[" + "],[".join(rows) + "]]"

# Transforms 'x₁' into "(X 1)"
SUB = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")
SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")
def format_monomial(m):
    if (len(m) == 2):
        return "(X " + m[1].translate(SUB) + ")"
    elif (len(m) == 3):
        s = format_monomial(m[:2])
        e = int(m[2].translate(SUP))
        return " * ".join([s] * e)
    else: 
        if (m[2] == "x"):
            return format_monomial(m[:2]) + " * " + format_monomial(m[2:])
        else:
            return format_monomial(m[:3]) + " * " + format_monomial(m[3:])

# Transforms 'x₁, x₂' into '[(X 1), (X 2)]'
def format_monomials(ms):
    ms = ms.split(", ")
    return "[" + ", ".join(map(format_monomial, ms)) + "]"

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

    _, raw = parse("{}GramMatrix{}", result)
    _, Q, _, ms, _ = parse("{}[{}]{}[{}]{}", raw)
    Q = format_matrix(Q)
    ms = format_monomials(ms)

    return (Q, ms)

if __name__ == "__main__":
    Q, ms = run_sos(parse_expr("0 <= 2*x[1]^4 + 2*x[1]^3*x[2] - x[1]^2*x[2]^2 + 5*x[2]^4"))
    print((Q,ms))

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