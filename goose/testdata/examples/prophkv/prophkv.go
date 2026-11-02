// Package prophkv is an example of a proof that needs a prophecy variable which the Go code
// does not contain. GetAny reads a key twice and returns one of the two answers, chosen at
// random. Its proof gives it a logically atomic spec (it behaves as one read, at one point of its
// execution), for which it must know, at the first read, whether that read's answer is the one
// it will return: a prophecy of the result. The proof adds the prophecy to the program in Lean
// (`withProph`, Perennial/GooseLang/ProphInstrument.lean), with a theorem that this is sound
// for the program below, which runs unchanged. The proof is in
// Perennial/Proof/github_com/mit_pdos/perennial/goose/testdata/examples/prophkv.
package prophkv

import "github.com/goose-lang/primitive"

// KV is a key-value map protected by a mutex (primitive.Mutex: a sync.Mutex whose package
// has nothing to initialize).
type KV struct {
	mu *primitive.Mutex
	m  map[string]string
}

func NewKV() *KV {
	return &KV{mu: new(primitive.Mutex), m: make(map[string]string)}
}

func (kv *KV) Put(k string, v string) {
	kv.mu.Lock()
	kv.m[k] = v
	kv.mu.Unlock()
}

func (kv *KV) Get(k string) string {
	kv.mu.Lock()
	v := kv.m[k]
	kv.mu.Unlock()
	return v
}

// GetAny reads k twice and returns either answer.
func GetAny(kv *KV, k string) string {
	v1 := kv.Get(k)
	v2 := kv.Get(k)
	if primitive.RandomUint64()%2 == 0 {
		return v1
	}
	return v2
}

// Test runs a Put concurrently with a GetAny, and returns GetAny's answer: "a" or "b".
func Test() string {
	kv := NewKV()
	kv.Put("k", "a")
	go func() {
		kv.Put("k", "b")
	}()
	return GetAny(kv, "k")
}
