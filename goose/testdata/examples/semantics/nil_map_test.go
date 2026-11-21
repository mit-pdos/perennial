package semantics

import "testing"

func TestNilMapBuiltins(t *testing.T) {
	type namedMap map[any]int
	var m namedMap
	delete(m, "key")
	clear(m)
	if m != nil {
		t.Fatal("delete or clear allocated the nil map")
	}

	m = namedMap{"keep": 1, "remove": 2}
	alias := m
	delete(m, "remove")
	if len(alias) != 1 || alias["keep"] != 1 {
		t.Fatalf("after delete, alias = %v", alias)
	}
	clear(m)
	if len(alias) != 0 || m == nil {
		t.Fatalf("after clear, map = %v, alias = %v", m, alias)
	}
}

func TestNilMapDeleteUnhashableKey(t *testing.T) {
	var m map[any]int
	defer func() {
		if recover() == nil {
			t.Fatal("delete accepted an unhashable dynamic key")
		}
	}()
	delete(m, []int{1})
}
