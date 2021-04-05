import sys
from parse import *

def parse_arith(expr):
    return expr

def parse_expr(expr):
    try:
        lhs, rhs = parse("{}<={}", expr)
        lhs = parse_arith(lhs)
        rhs = parse_arith(rhs)
        return lhs + "<=" + rhs
    except Exception as e:
        print("Invalid")

if __name__ == "__main__":
    if (len(sys.argv) > 1):
        print(parse_expr(sys.argv[1]))
    else:
        print("Error")