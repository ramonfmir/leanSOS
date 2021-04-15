import os
import sys
import socket
import subprocess
import argparse
import time
import threading
from parse import *
from julia.api import Julia

DETACHED_PROCESS = 0x00000008

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
    rows = ['[{:s}]'.format(', '.join(['{:.10f}'.format(x) for x in row])) for row in M]
    return '[{:s}]'.format(', '.join(rows))

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

    d_raw, Q_raw, ms_raw, L_raw = jl.eval('return((d, Q, ms, L))')

    d = str(d_raw)
    Q = format_matrix(Q_raw)
    ms = format_monomials(parse("{}[{}]{}", str(ms_raw))[1])
    L = format_matrix(L_raw)

    return d, Q, ms, L

def main(ineq):
    expr = parse_expr(ineq)
    d, Q, ms, L = run_sos(expr)

    f = open("/Users/ramon/Documents/experiments/leanSOS/lean/scripts/temp.txt", "w")
    f.write(d + '\n')
    f.write(Q + '\n')
    f.write(ms + '\n')
    f.write(L + '\n')
    f.close()

    # For testing.
    # p = "0<=x[1]*x[1] + 2*x[1]*x[2] + x[2]*x[2]"
    # d, Q, ms, L = run_sos(parse_expr(p))
    # print((Q,L))

## Process stuff. 

if __name__ == "__main__":
    main(sys.argv[1])
