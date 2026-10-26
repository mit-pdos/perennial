// Package netext is a toy network between the nodes of a distributed system:
// the Go side of GooseLang's network extension (Perennial/GooseLang/Ext/Net).
// Every node has an address; a node sends data to an address, and receives the
// messages sent to its own address, each with its sender's address, which the
// network attaches.
//
// The primitives send and recv are trusted: Perennial models them with the
// extension's operations (Perennial/TrustedCode/.../netfs/netext.lean) instead
// of translating them. They have no implementation here (they panic): the
// extension is a specification of a network, not a model of existing code.
// Send and Recv, which convert between []byte and the primitives' strings,
// are translated.
package netext

// send sends data to the node with address to.
func send(to string, data string) {
	panic("netext: the toy network has no implementation")
}

// recv waits for a message sent to this node, and returns its sender's address
// and its data.
func recv() (string, string) {
	panic("netext: the toy network has no implementation")
}

// Send sends data to the node with address to. The network may deliver the
// message any number of times, in any order, or never.
func Send(to string, data []byte) {
	send(to, string(data))
}

// Recv waits for a message sent to this node, and returns its sender's address
// and its data.
func Recv() (from string, data []byte) {
	from, s := recv()
	return from, []byte(s)
}
