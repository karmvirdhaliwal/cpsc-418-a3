#!/usr/bin/env python3

##### IMPORTS

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.backends import default_backend

from secrets import randbits
import socket
from sympy import gcd, isprime, primefactors, sieve

# sieve speed-up courtesy: Wiener, Michael J. "Safe Prime Generation with a Combined Sieve." IACR Cryptol. ePrint Arch. 2003 (2003): 186.
# create a sieve of values to avoid
sieve.extend_to_no(150)                     # somewhere around here is best for my workstation
prime_list  = list( sieve._list )[2:]
prime_avoid = [(r-1)//2 for r in prime_list]

##### METHODS

def split_ip_port( string ):
    """Split the given string into an IP address and port number.
    
    PARAMETERS
    ==========
    string: A string of the form IP:PORT.

    RETURNS
    =======
    If successful, a tuple of the form (IP,PORT), where IP is a 
      string and PORT is a number. Otherwise, returns None.
    """

    assert type(string) == str

    try:
        idx = string.index(':')
        return (string[:idx], int(string[idx+1:]))
    except:
        return None

def int_to_bytes( value, length ):
    """Convert the given integer into a bytes object with the specified
       number of bits. Uses network byte order.

    PARAMETERS
    ==========
    value: An int to be converted.
    length: The number of bytes this number occupies.

    RETURNS
    =======
    A bytes object representing the integer.
    """
    
    assert type(value) == int
    assert length > 0

    return value.to_bytes( length, 'big' )

def i2b( x, l ):
    """The above, but it passes through bytes objects."""
    if type(x) == int:
        return x.to_bytes( l, 'big' )
    elif type(x) == bytes:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')

def bytes_to_int( value ):
    """Convert the given bytes object into an integer. Uses network
       byte order.

    PARAMETERS
    ==========
    value: An bytes object to be converted.

    RETURNS
    =======
    An integer representing the bytes object.
    """
    
    assert type(value) == bytes
    return int.from_bytes( value, 'big' )

def b2i( x ):
    """The above, but it passes through int objects."""
    if type(x) == bytes:
        return int.from_bytes( x, 'big' )
    elif type(x) == int:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')

def create_socket( ip, port, listen=False ):
    """Create a TCP/IP socket at the specified port, and do the setup
       necessary to turn it into a connecting or receiving socket. Do
       not actually send or receive data here, and do not accept any
       incoming connections!

    PARAMETERS
    ==========
    ip: A string representing the IP address to connect/bind to.
    port: An integer representing the port to connect/bind to.
    listen: A boolean that flags whether or not to set the socket up
       for connecting or receiving.

    RETURNS
    =======
    If successful, a socket object that's been prepared according to 
       the instructions. Otherwise, return None.
    """
    
    assert type(ip) == str
    assert type(port) == int

    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

    try:
        if listen:
            sock.bind( (ip, port) )
            sock.listen(2)      # 2 is enough for our needs
        else:
            sock.connect( (ip, port) )

        return sock
    except:
        return None

def send( sock, data ):
    """Send the provided data across the given socket. This is a
       'reliable' send, in the sense that the function retries sending
       until either a) all data has been sent, or b) the socket 
       closes.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    data: A bytes object containing the data to send.

    RETURNS
    =======
    The number of bytes sent. If this value is less than len(data),
       the socket is dead and a new one must be created, plus an unknown
       amount of the data was transmitted.
    """
    
    assert type(sock) == socket.socket
    assert type(data) == bytes

    sent = 0
    while sent < len(data):

        rem = len(data) - sent
        if rem > 4096:
            end = sent + 4096
        else:
            end = len(data)

        try:
            out = sock.send( data[sent:end] )
        except:
            return sent

        if out <= 0:
            return sent
        sent += out

    return sent

def receive( sock, length ):
    """Receive the provided data across the given socket. This is a
       'reliable' receive, in the sense that the function never returns
       until either a) the specified number of bytes was received, or b) 
       the socket closes. Never returning is an option.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    length: A positive integer representing the number of bytes to receive.

    RETURNS
    =======
    A bytes object containing the received data. If this value is less than 
       length, the socket is dead and a new one must be created.
    """
    
    assert type(sock) == socket.socket
    assert length > 0

    intake = b''
    while len(intake) < length:

        rem = length - len(intake)
        try:
            input = sock.recv( rem )
        except:
            return intake

        if input == b'':
            return intake
        intake = b''.join([intake,input])

    return intake

def safe_prime( bits=512 ):
    """Generate a safe prime that is at least 'bits' bits long. The result
       should be greater than 1 << (bits-1).

    PARAMETERS
    ==========
    bits: An integer representing the number of bits in the safe prime.
       Must be greater than 1.

    RETURNS
    =======
    An interger matching the spec.
    """

    assert bits > 5                                   # this algorithm likely breaks for small numbers of bits

    # do a linear search
    maximum = 1 << (bits-1)
    q       = randbits(bits-1) | (1 << (bits-2))      # guarantee the high bit is set
    q      += 5 - (q % 6)                             # make it 5 (mod 6)

    while True:

        # sieve out some known-bad values
        for i,r in enumerate(prime_list):
            if (q % r) == prime_avoid[i]:
                break
        else:
            if isprime( q ):
                cand = (q<<1) + 1
                if isprime( cand ):
                    return cand

        q += 6          # ensure it's always 5 (mod 6)

        if q >= maximum:
            q    = (1 << (bits-2)) + 1
            q   += 5 - (q % 6)                             # reset this back to where we expect

def prim_root( N ):
    """Find a primitive root for N, a large safe prime. Hint: it isn't
       always 2.

    PARAMETERS
    ==========
    N: The prime in question. May be an integer or bytes object.

    RETURNS
    =======
    An integer representing the primitive root. Must be a positive
       number greater than 1.
    """

    # IMPORTANT: This assumes N is a safe prime. Will fail for other cases!
    group   = N-1
    fact    = N>>1      # there's only two prime factors of the group, one of which is 2!

    # do a linear search
    for c in range(2,N):

        if gcd(N,c) != 1:
            continue
        elif pow( c, 2, N ) == 1:
            continue
        elif pow( c, fact, N ) == 1:
            continue
        else:
            return c

def calc_x( s, pw ):
    """Calculate the value of x, according to the assignment.

    PARAMETERS
    ==========
    s: The salt to use. A bytes object consisting of 16 bytes.
    pw: The password to use, as a string.

    RETURNS
    =======
    An integer representing x.
    """

    assert type(pw) == str
    assert type(s) == bytes

    hash = hashes.Hash( hashes.SHA3_256(), default_backend() )
    hash.update( s + pw.encode('utf-8') )
    return bytes_to_int( hash.finalize() )

def calc_A( N, g, a ):
    """Calculate the value of A, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    g: A primitive root of N. Could be an integer or bytes object.
    a: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing A.
    """

    # a compact way to ensure conversions are done:
    N, g, a = map( b2i, [N, g, a] )
    return pow(g, a, N)

def calc_B( N, g, b, k, v ):
    """Calculate the value of B, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    g: A primitive root of N. Could be an integer or bytes object.
    b: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    k: The hash of N and g. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing B.
    """

    N, g, b, k, v = map( b2i, [N, g, b, k, v] )
    return (k*v + pow(g,b,N)) % N

def calc_u( A, B ):
    """Calculate the value of u, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing u.
    """

    # ints to bytes takes more thought
    A, B = map( lambda x: i2b(x,64), [A, B] )

    hash = hashes.Hash( hashes.SHA3_256(), default_backend() )
    hash.update( A + B )
    return bytes_to_int( hash.finalize() )

def calc_K_client( N, B, k, v, a, u, x ):
    """Calculate the value of K_client, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.
    k: The hash of N and g. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.
    a: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    u: The hash of A and B. Could be an integer or bytes object.
    x: See calc_x(). Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing K_client.
    """

    N, B, k, v, a, u, x = map( b2i, [N, B, k, v, a, u, x] )
    return pow(B - k*v, a + u*x, N)

def calc_K_server( N, A, b, v, u ):
    """Calculate the value of K_server, according to the assignment.

    PARAMETERS
    ==========
    N: The safe prime. Could be an integer or bytes object.
    A: See calc_A(). Could be an integer or bytes object.
    b: A random value between 0 and N-1, inclusive. Could be an integer or bytes object.
    v: See the assignment sheet. Could be an integer or bytes object.
    u: The hash of A and B. Could be an integer or bytes object.

    RETURNS
    =======
    An integer representing K_server.
    """

    N, A, b, v, u = map( b2i, [N, A, b, v, u] )
    return pow( A*pow(v,u,N), b, N )

def calc_M1( A, B, K_client ):
    """Calculate the value of M1, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    B: See calc_B(). Could be an integer or bytes object.
    K_client: See calc_K_client(). Could be an integer or bytes object.

    RETURNS
    =======
    A bytes object representing M1.
    """

    A, B, K_client = map( lambda x: i2b(x,64), [A, B, K_client] )

    hash = hashes.Hash( hashes.SHA3_256(), default_backend() )
    hash.update( A + B + K_client )
    return hash.finalize()

def calc_M2( A, M1, K_server ):
    """Calculate the value of M2, according to the assignment.

    PARAMETERS
    ==========
    A: See calc_A(). Could be an integer or bytes object.
    M1: See calc_M1(). Could be an integer or bytes object.
    K_server: See calc_K_server(). Could be an integer or bytes object.

    RETURNS
    =======
    A bytes object representing M2.
    """

    # lengths matter here, so use a different method
    length = [64,32,64]
    A, M1, K_server = [int_to_bytes(c, length[i]) if type(c) == int else c \
            for i,c in enumerate([A, M1, K_server])]

    hash = hashes.Hash( hashes.SHA3_256(), default_backend() )
    hash.update( A + M1 + K_server )
    return hash.finalize()

def client_prepare():
    """Do the preparations necessary to connect to the server. Basically,
       just generate a salt.

    RETURNS
    =======
    A bytes object containing a randomly-generated salt, 16 bytes long.
    """

    return int_to_bytes( randbits(16*8), 16 )

def close_sock( sock ):
    """A helper to close sockets cleanly."""
    try:
        sock.shutdown(socket.SHUT_RDWR)
        sock.close()
    except:
        pass
    return None

def varprint( data, label, source="Client" ):
    """A helper for printing out data."""
    global args

    if not (('args' in globals()) and args.verbose):
        return

    if label is not None:
        middle = f"{label} = "
    else:
        middle = ""

    if type(data) == bytes:
        print( f"{source}: Received {middle}<{data.hex()}>" )
    else:
        print( f"{source}: {middle}{data}" )

def client_register( ip, port, username, pw, s ):
    """Register the given username with the server, from the client.
       IMPORTANT: don't forget to send 'r'!

    PARAMETERS
    ==========
    ip: The IP address to connect to, as a string.
    port: The port to connect to, as an int.
    username: The username to register, as a string.
    pw: The password, as a string.
    s: The salt, a bytes object 16 bytes long.

    RETURNS
    =======
    If successful, return a tuple of the form (N, g, v), all integers.
       On failure, return None.
    """

    varprint( username, "username" )
    varprint( pw, "pw" )
    varprint( s, "salt" )

    # connect to the server
    sock = create_socket( ip, port )
    if sock is None:
        return None

    # send 'r'
    count = send( sock, b'r' )
    if count != 1:
        return close_sock( sock )

    # retrieve N and g
    expected = 128 # 512 bits + 512 bits
    N_g = receive( sock, expected )
    if len(N_g) != expected:
        return close_sock( sock )

    N = N_g[:expected>>1]
    g = N_g[expected>>1:]

    varprint( N_g, None )
    varprint( bytes_to_int(N), "N" )
    varprint( bytes_to_int(g), "g" )

    # calculate x and v
    x = calc_x( s, pw ) 
    v = calc_A( N, g, x )

    varprint( x, "x" )
    varprint( v, "v" )

    # send (username, s, v)
    u_enc = username.encode('utf-8')
    assert len(u_enc) < 256

    data = int_to_bytes( len(u_enc), 1 ) + u_enc + s + int_to_bytes( v, 64 )

    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # kill the connection
    close_sock( sock )

    print( "Client: Registration successful." )
    return tuple(map( b2i, [N, g, v] ))

def server_register( sock, N, g, database ):
    """Handle the server's side of the registration. IMPORTANT: reading the
       initial 'r' has been handled for you.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    N: A safe prime. Could be an integer or bytes object.
    g: A primitive root of the safe prime. Could be an integer or bytes object.
    database: A dictionary of all registered users. The keys are usernames
       (as strings!), and the values are tuples of the form (s, v), where s
       is the salt (16 bytes) and v is as per the assignment (integer).

    RETURNS
    =======
    If the registration process was successful, return an updated version of the
       database. If it was not, return None. NOTE: a username that tries to
       re-register with a different salt and/or password is likely malicious,
       and should therefore count as an unsuccessful registration.
    """

    varprint( N, 'N', "Server" )
    varprint( g, 'g', "Server" )

    N, g = map( lambda x: i2b(x,64), [N, g] )

    # send N and g
    data = N + g
    count = send( sock, data )
    if count != len(data):
        return close_sock( sock )

    # get username
    count = receive( sock, 1 )
    if len(count) != 1:
        return close_sock( sock )
    count = bytes_to_int( count )

    varprint( count, 'username_length', "Server" )

    u_enc = receive( sock, count )
    if len(u_enc) != count:
        return close_sock( sock )

    varprint( u_enc, 'u_enc', "Server" )
    try:
        username = u_enc.decode('utf-8')
    except:
        return close_sock( sock )
    varprint( username, 'username', "Server" )

    # get s, v
    s = receive( sock, 16 )
    if len(s) != 16:
        return close_sock( sock )
    varprint( s, 'salt', "Server" )
    
    v = receive( sock, 64 )  # 512 // 8
    if len(v) != 64:
        return close_sock( sock )
    varprint( v, 'v', "Server" )
    
    v = bytes_to_int( v )
    varprint( v, 'v', "Server" )

    # were we already registered?
    if username in database:
        temp = database[username]
        if (s != temp[0]) or (v != temp[1]):
            return close_sock( sock )
        else:
            print( "Server: Repeat registration attempted." )

    # all finished with the connection
    close_sock( sock )

    print( "Server: Registration successful." )

    # save them and return
    database[username] = (s, v)
    return database

