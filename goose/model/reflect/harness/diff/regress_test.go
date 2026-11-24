package diff

import (
	"testing"

	"github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectcore"
	rm "github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectmodel"
)

// Regressions of the adversarial review of S0.

func stuck(f func()) (s bool) {
	defer func() { s = reflectcore.IsStuck(recover()) }()
	f()
	return false
}

// TestReflectOnTypeStuck: reflect's own Type values are *rtype in Go and rtype in the model,
// so reflection on them is stuck in the model.
func TestReflectOnTypeStuck(t *testing.T) {
	ty := rm.TypeOf(0)
	for name, f := range map[string]func(){
		"TypeOf(TypeOf(0))":            func() { rm.TypeOf(ty) },
		"ValueOf(TypeOf(0))":           func() { rm.ValueOf(ty) },
		"ValueOf(&ty).Elem().Elem()":   func() { rm.ValueOf(&ty).Elem().Elem() },
		"ValueOf(any(TypeOf(0))).Kind": func() { rm.ValueOf(any(ty)).Kind() },
	} {
		if !stuck(f) {
			t.Errorf("%s: not stuck", name)
		}
	}
	// the interface itself is still reflected on: kind Interface, not nil
	v := rm.ValueOf(&ty).Elem()
	if v.Kind() != rm.Interface || v.IsNil() {
		t.Errorf("ValueOf(&ty).Elem(): kind %v, IsNil %v", v.Kind(), v.IsNil())
	}
}
