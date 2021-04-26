from parse import *
import math

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
    rows = ['[{:s}]'.format(', '.join([format_float(x) for x in row])) for row in M]
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

def format_float(f):
    (m, d) = float.as_integer_ratio(f)
    e = math.log2(d)
    return '({:d}, {:d})'.format(int(m), int(e))
