import os
import socket
import subprocess
import argparse
import time
import threading

DETACHED_PROCESS = 0x00000008

# Main Julia thread.
class ServerThread(threading.Thread):
    def run(self):
        os.system('/Applications/Julia-1.5.app/Contents/Resources/julia/bin/julia server.jl')

# Method to restart the server.
def restart_server():
    fnull = open(os.devnull, 'w')
    t = ServerThread()
    t.daemon = True
    t.start()

# Communicate with the server.
def process(msg, start_server):
    address = ("localhost", 65432)

    with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as s:
        s.connect(address)
        s.sendall(msg)
        data = s.recv(1024)

    print(repr(data))

# Test.
if __name__ == "__main__":  
    #restart_server()
    #time.sleep(2.0)
    process(b'AVOOOOOO!', True)

