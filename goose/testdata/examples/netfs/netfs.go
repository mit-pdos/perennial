// Package netfs is an example of a crash-safe distributed program, on the toy
// network (netext) and the toy filesystem (crashfs/fsext). Three nodes run it,
// with addresses "a", "b" and "c"; each node's function is its boot program,
// which runs when the node starts and again after every crash of the node:
//   - NodeA sends the contents of its file "in" to "b", and checks (by
//     panicking) that what "b" sends back is the same;
//   - NodeB, the first time, waits for a message from "a", stores its data in
//     its file "out", then marks it stored in its file "sent", and sends it
//     back; once marked, it sends back what "out" holds instead, without
//     waiting for "a" again. That is the data "a" sent only because the write
//     of "out" is durable before that of "sent": "a"'s check depends on the
//     durability of "b"'s writes, across crashes of "b";
//   - NodeC sends junk to both, which they ignore: the network attaches the
//     sender's address to every message, so "c" cannot pose as "a" or "b".
//
// Its proof, with the distributed crash adequacy theorem, is in
// Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/netfs.
package netfs

import (
	"github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsext"
	"github.com/mit-pdos/perennial/goose/testdata/examples/netfs/netext"
)

// recvFrom waits for a message from the node peer and returns its data,
// ignoring the messages of other nodes.
func recvFrom(peer string) []byte {
	for {
		from, data := netext.Recv()
		if from == peer {
			return data
		}
	}
}

func NodeA() {
	s := fsext.Read("in")
	netext.Send("b", []byte(s))
	if string(recvFrom("b")) != s {
		panic("round trip mismatch")
	}
}

func NodeB() {
	if fsext.Read("sent") == "yes" {
		netext.Send("a", []byte(fsext.Read("out")))
		return
	}
	data := string(recvFrom("a"))
	fsext.Write("out", data)
	fsext.Write("sent", "yes")
	netext.Send("a", []byte(data))
}

func NodeC() {
	netext.Send("a", []byte("junk"))
	netext.Send("b", []byte("junk"))
}
