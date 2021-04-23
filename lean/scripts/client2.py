import os
import sys
import socket

HOST = '127.0.0.1'  
PORT = 65432        

# Communicate with the server.
def send_polynomial(msg):
    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect((HOST, PORT))
        s.sendall(msg.encode('utf-8'))
        data = s.recv(1024)

    return data

if __name__ == "__main__":  
    result = send_polynomial(sys.argv[1])
    print(result.decode('utf-8'))

