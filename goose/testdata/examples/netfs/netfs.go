// Package netfs is an example of a distributed program, on the toy network
// (netext) and the toy filesystem (crashfs/fsext). Three nodes run it, with
// addresses "a", "b" and "c":
//   - NodeA sends the contents of its file "in" to "b", and checks (by
//     panicking) that what "b" sends back is the same;
//   - NodeB waits for a message from "a", stores its data in its file "out",
//     checks that the file holds it, and sends the file's contents back to "a";
//   - NodeC sends junk to both, which they ignore: the network attaches the
//     sender's address to every message, so "c" cannot pose as "a" or "b".
//
// Its proof, with the distributed adequacy theorem, is in
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
	data := string(recvFrom("a"))
	fsext.Write("out", data)
	stored := fsext.Read("out")
	if stored != data {
		panic("write lost")
	}
	netext.Send("a", []byte(stored))
}

func NodeC() {
	netext.Send("a", []byte("junk"))
	netext.Send("b", []byte("junk"))
}
