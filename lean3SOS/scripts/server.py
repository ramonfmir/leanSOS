import socket
from parse import *
from julia.api import Julia

from util import *

jpath = "/Applications/Julia-1.5.app/Contents/Resources/julia/bin/julia"
jl = Julia(runtime=jpath)

jl.using('SumOfSquares')
jl.using('DynamicPolynomials')
jl.using('MosekTools')

print("Julia ready.")

def run_sos(expr):
    expr = parse_expr(expr)

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

    dQ_raw, Q_raw, ms_raw, L_raw = jl.eval('return((d, Q, ms, L))')

    dQ = str(dQ_raw)
    Q = format_matrix(Q_raw)
    ms = format_monomials(parse("{}[{}]{}", str(ms_raw))[1])
    dL = str(len(L_raw[0]))
    L = format_matrix(L_raw)

    f = open("/Users/ramon/Documents/experiments/leanSOS/lean/scripts/temp.txt", "w")
    f.write(dQ + '\n')
    f.write(Q + '\n')
    f.write(ms + '\n')
    f.write(dL + '\n')
    f.write(L + '\n')
    f.close()

HOST = '127.0.0.1'  
PORT = 65432        

with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
    s.bind((HOST, PORT))
    s.listen()
    while True:
        conn, addr = s.accept()
        data = conn.recv(1024)
        if data:
            run_sos(data.decode('utf-8'))
            conn.sendall("Success".encode('utf-8'))
