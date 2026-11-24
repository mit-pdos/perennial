// Package maps holds the evidence for the model of maps.clone, the runtime's
// maps_clone (Perennial/TrustedCode/maps.lean, clone.impl: the semantics'
// InternalMapClone, internal_map_clone_step in Golang/Defn/Map.lean): the real
// maps.Clone returns a new map with the same entries (each entry copied, NaN
// keys included), nil for nil, and an empty non-nil map for an empty one,
// exactly as cloneModel below, a plain Go loop.
package maps

import (
	"maps"
	"math"
	"math/rand"
	"testing"
)

// cloneModel: a fresh map filled with m's entries.
func cloneModel[M ~map[K]V, K comparable, V any](m M) M {
	if m == nil {
		return nil
	}
	r := make(M, len(m))
	for k, v := range m {
		r[k] = v
	}
	return r
}

type named map[string]int

func sameEntries[K comparable, V comparable](a, b map[K]V) bool {
	if len(a) != len(b) {
		return false
	}
	for k, v := range a {
		if w, ok := b[k]; !ok || w != v {
			return false
		}
	}
	return true
}

// Both preserve nilness: nil gives nil, an empty non-nil map a non-nil map.
func TestCloneNil(t *testing.T) {
	var m map[string]int
	if maps.Clone(m) != nil || cloneModel(m) != nil {
		t.Fatal("clone of nil is not nil")
	}
	var n named
	if maps.Clone(n) != nil || cloneModel(n) != nil {
		t.Fatal("clone of a nil named map is not nil")
	}
	e := map[string]int{}
	if maps.Clone(e) == nil || cloneModel(e) == nil {
		t.Fatal("clone of an empty non-nil map is nil")
	}
}

// On random maps, both return the same entries as m, in a new map: a write to
// the clone is not seen in m, nor a write to m in the clone. The result has
// m's type (a named map type stays named).
func TestCloneEntriesFresh(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for i := 0; i < 5000; i++ {
		m := named{}
		for j := r.Intn(40); j > 0; j-- {
			m[string(rune('a'+r.Intn(26)))+string(rune('a'+r.Intn(26)))] = r.Intn(5)
		}
		for _, c := range []named{maps.Clone(m), cloneModel(m)} {
			if !sameEntries(m, c) {
				t.Fatalf("clone %v of %v differs", c, m)
			}
			c["fresh"] = 1
			if _, ok := m["fresh"]; ok {
				t.Fatal("a write to the clone is seen in m")
			}
			delete(c, "fresh")
			m["other"] = 2
			if _, ok := c["other"]; ok {
				t.Fatal("a write to m is seen in the clone")
			}
			delete(m, "other")
		}
	}
}

// Keys not equal to themselves (NaN): each entry is copied, by both.
func TestCloneNaN(t *testing.T) {
	m := map[float64]int{math.NaN(): 1, math.NaN(): 2, 0: 3}
	if len(maps.Clone(m)) != 3 || len(cloneModel(m)) != 3 {
		t.Fatal("NaN entries not all copied")
	}
}
