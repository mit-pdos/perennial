package grove_ffi

import (
	"fmt"
	"github.com/tchajed/marshal"
	"io"
	"net"
	"strconv"
	"strings"
	"sync"
)

type Address = uint64

func MakeAddress(ipStr string) uint64 {
	// XXX: manually parsing is pretty silly; couldn't figure out how to make
	// this work cleanly net.IP
	ipPort := strings.Split(ipStr, ":")
	if len(ipPort) != 2 {
		panic(fmt.Sprintf("Not ipv4:port %s", ipStr))
	}
	port, err := strconv.ParseUint(ipPort[1], 10, 16)
	if err != nil {
		panic(err)
	}

	ss := strings.Split(ipPort[0], ".")
	if len(ss) != 4 {
		panic(fmt.Sprintf("Not ipv4:port %s", ipStr))
	}
	ip := make([]byte, 4)
	for i, s := range ss {
		a, err := strconv.ParseInt(s, 10, 8)
		if err != nil {
			panic(err)
		}
		ip[i] = byte(a)
	}
	return (uint64(ip[0]) | uint64(ip[1])<<8 | uint64(ip[2])<<16 | uint64(ip[3])<<24 | uint64(port)<<32)
}

func AddressToStr(e Address) string {
	a0 := byte(e & 0xff)
	e = e >> 8
	a1 := byte(e & 0xff)
	e = e >> 8
	a2 := byte(e & 0xff)
	e = e >> 8
	a3 := byte(e & 0xff)
	e = e >> 8
	port := e & 0xffff
	return fmt.Sprintf("%s:%d", net.IPv4(a0, a1, a2, a3).String(), port)
}

// / Listener
type listener struct {
	l net.Listener
}

type Listener *listener

func Listen(host Address) Listener {
	l, err := net.Listen("tcp", AddressToStr(host))
	if err != nil {
		// Assume() no error on Listen. This should fail loud and early, retrying makes little sense (likely the port is already used).
		panic(err)
	}
	return &listener{l}
}

func Accept(l Listener) Connection {
	conn, err := l.l.Accept()
	if err != nil {
		// This should not usually happen... something seems wrong.
		panic(err)
	}

	return makeConnection(conn)
}

// / Connection
type connection struct {
	conn    net.Conn
	send_mu *sync.Mutex // guarding *sending* on `conn`
	recv_mu *sync.Mutex // guarding *receiving* on `conn`
}

func makeConnection(conn net.Conn) Connection {
	return &connection{conn: conn, send_mu: new(sync.Mutex), recv_mu: new(sync.Mutex)}
}

type Connection *connection

type ConnectRet struct {
	Err        bool
	Connection Connection
}

func Connect(host Address) ConnectRet {
	conn, err := net.Dial("tcp", AddressToStr(host))
	if err != nil {
		return ConnectRet{Err: true}
	}
	return ConnectRet{Err: false, Connection: makeConnection(conn)}
}

func Send(c Connection, data []byte) bool {
	// Encode message
	e := marshal.NewEnc(8 + uint64(len(data)))
	e.PutInt(uint64(len(data)))
	e.PutBytes(data)
	msg := e.Finish()

	c.send_mu.Lock()
	defer c.send_mu.Unlock()

	// message format: [dataLen] ++ data
	// Writing in a single call is faster than 2 calls despite the unnecessary copy.
	_, err := c.conn.Write(msg)
	// If there was an error, make sure we never send anything on this channel again...
	// there might have been a partial write!
	if err != nil {
		c.conn.Close() // Go promises this makes this connection object "dead"
	}
	return err != nil
}

type ReceiveRet struct {
	Err  bool
	Data []byte
}

func Receive(c Connection) ReceiveRet {
	c.recv_mu.Lock()
	defer c.recv_mu.Unlock()

	// message format: [dataLen] ++ data

	header := make([]byte, 8)
	_, err := io.ReadFull(c.conn, header)
	if err != nil {
		// Looks like this connection is dead.
		// This can legitimately happen when the other side "hung up", so do not panic.
		// But also, we clearly lost track here of where in the protocol we are,
		// so close it.
		c.conn.Close()
		return ReceiveRet{Err: true}
	}
	d := marshal.NewDec(header)
	dataLen := d.GetInt()

	data := make([]byte, dataLen)
	_, err2 := io.ReadFull(c.conn, data)
	if err2 != nil {
		// See comment above.
		c.conn.Close()
		return ReceiveRet{Err: true}
	}

	return ReceiveRet{Err: false, Data: data}
}
