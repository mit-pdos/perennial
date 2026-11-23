// Package atomic holds the evidence for the model of sync/atomic.Value
// (Perennial/TrustedCode/sync/atomic.lean, Value.Store.impl, Value.Swap.impl,
// Value.CompareAndSwap.impl): which calls panic in gc and which do not.
package atomic

import (
	"sync/atomic"
	"testing"
)

func panics(f func()) (p bool) {
	defer func() {
		if recover() != nil {
			p = true
		}
	}()
	f()
	return false
}

type myInt int
type otherInt int

// Store and Swap panic exactly on a nil value and on a value whose dynamic type
// differs from the stored one's (type identity: two named types with the same
// underlying type differ); a store of the same dynamic type over a stored value
// does not panic (the model checks this with TypeOfEq).
func TestValueStoreSwap(t *testing.T) {
	var v atomic.Value
	if !panics(func() { v.Store(nil) }) {
		t.Fatal("Store(nil) did not panic")
	}
	if !panics(func() { v.Swap(nil) }) {
		t.Fatal("Swap(nil) did not panic")
	}
	if panics(func() { v.Store(map[string]bool{"a": true}) }) {
		t.Fatal("first Store panicked")
	}
	if panics(func() { v.Store(map[string]bool{"b": false}) }) {
		t.Fatal("Store of the same dynamic type panicked")
	}
	var old any
	if panics(func() { old = v.Swap(map[string]bool{}) }) {
		t.Fatal("Swap of the same dynamic type panicked")
	}
	if old.(map[string]bool)["b"] != false || len(old.(map[string]bool)) != 1 {
		t.Fatal("Swap did not return the old value")
	}
	if !panics(func() { v.Store(map[string]int{}) }) {
		t.Fatal("Store of another dynamic type did not panic")
	}
	if !panics(func() { v.Swap(3) }) {
		t.Fatal("Swap of another dynamic type did not panic")
	}

	var w atomic.Value
	w.Store(myInt(1))
	if !panics(func() { w.Store(otherInt(1)) }) {
		t.Fatal("Store of a named type with the same underlying type did not panic")
	}
	if !panics(func() { w.Store(1) }) {
		t.Fatal("Store of the underlying type did not panic")
	}
	var e atomic.Value
	if old := e.Swap(1); old != nil {
		t.Fatal("Swap on an empty Value did not return nil")
	}
}

// CompareAndSwap panics on a nil new value, on old and new of different dynamic
// types (even on an empty Value), on a stored value of another dynamic type than
// new, and on comparing old with the stored value when their (equal) dynamic type
// is not comparable; it never checks old's comparability on its own.
func TestValueCompareAndSwap(t *testing.T) {
	var v atomic.Value
	if !panics(func() { v.CompareAndSwap(nil, nil) }) {
		t.Fatal("CompareAndSwap(nil, nil) did not panic")
	}
	if !panics(func() { v.CompareAndSwap("a", 1) }) {
		t.Fatal("CompareAndSwap of differently typed old and new did not panic on an empty Value")
	}
	if v.CompareAndSwap("a", "b") {
		t.Fatal("CompareAndSwap with a non-nil old succeeded on an empty Value")
	}
	if !v.CompareAndSwap(nil, "b") {
		t.Fatal("CompareAndSwap(nil, new) failed on an empty Value")
	}
	if v.CompareAndSwap(nil, "c") {
		t.Fatal("CompareAndSwap(nil, new) succeeded on a non-empty Value")
	}
	if !panics(func() { v.CompareAndSwap(nil, 1) }) {
		t.Fatal("CompareAndSwap of a new value of another type than the stored one did not panic")
	}
	if v.CompareAndSwap("x", "c") {
		t.Fatal("CompareAndSwap with a different old succeeded")
	}
	if !v.CompareAndSwap("b", "c") || v.Load() != "c" {
		t.Fatal("CompareAndSwap with the stored old failed")
	}

	var s atomic.Value
	if s.CompareAndSwap([]int{}, []int{1}) {
		t.Fatal("CompareAndSwap with a non-nil old succeeded on an empty Value")
	}
	s.Store([]int{1})
	if !panics(func() { s.CompareAndSwap([]int{1}, []int{2}) }) {
		t.Fatal("CompareAndSwap comparing non-comparable values did not panic")
	}
	if s.CompareAndSwap(nil, []int{2}) {
		t.Fatal("CompareAndSwap(nil, new) succeeded on a non-empty Value")
	}
}
