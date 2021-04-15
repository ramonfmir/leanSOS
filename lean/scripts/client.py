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

# Transforms 'x₁' into "[[1]]"
SUB = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")
SUP = str.maketrans("⁰¹²³⁴⁵⁶⁷⁸⁹", "0123456789")
def format_monomial(m):
    if (len(m) == 2):
        return m[1].translate(SUB)
    elif (len(m) == 3):
        s = format_monomial(m[:2])
        e = int(m[2].translate(SUP))
        return ", ".join([s] * e)
    else: 
        if (m[2] == "x"):
            return format_monomial(m[:2]) + ", " + format_monomial(m[2:])
        else:
            return format_monomial(m[:3]) + ", " + format_monomial(m[3:])

# Transforms 'x₁, x₂' into '[(X 1), (X 2)]'
def format_monomials(ms):
    ms = ms.split(", ")
    return "[[" + "], [".join(map(format_monomial, ms)) + "]]"

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
    jl.eval('G = gram_matrix(con_ref)')
    jl.eval('d = length(G.basis)')
    jl.eval('Q = G.Q')
    jl.eval('ms = G.basis')
    jl.eval('nM, cM, L = MultivariateMoments.lowrankchol(Matrix(getmat(G)), SVDChol(), 0.0)')

    d_raw, Q_raw, raw_ms, raw_L = jl.eval('return((d, Q, ms, L))')

    d = str(d_raw)
    Q = str(Q_raw)
    ms = format_monomials(parse("{}[{}]{}", str(raw_ms))[1])
    L = str(raw_L).replace('\n', ',')

    return d, Q, ms, L

if __name__ == "__main__":
    if (len(sys.argv) > 1):
        expr = parse_expr(sys.argv[1])
        d, Q, ms, L = run_sos(expr)

        f = open("/Users/ramon/Documents/experiments/leanSOS/lean/scripts/temp.txt", "w")
        f.write(d)
        f.write(Q)
        f.write(ms)
        f.write(L)
        f.close()
    else:
        print("Error")