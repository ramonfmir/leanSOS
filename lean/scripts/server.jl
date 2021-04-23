using Sockets 

t = @async begin
    server = listen(2000)
    println("Hello")
    while true
        sock = accept(server)
        println("What up")
        @async while isopen(sock)
            write(sock, readline(sock, keep=true))
        end
    end
end

println("Woohoo")

wait(t)
