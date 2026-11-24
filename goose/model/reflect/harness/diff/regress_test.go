package diff

import (
	"reflect"
	"testing"
	"unsafe"

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

type z struct{}
type zs struct {
	a z
	b [0]int64
}

func realIndir(x any) bool {
	return reflect.ValueOf(reflect.ValueOf(x)).FieldByName("flag").Uint()&(1<<7) != 0
}

func modelIndir(x any) bool {
	return reflect.ValueOf(rm.ValueOf(x)).FieldByName("flag").Uint()&(1<<7) != 0
}

// TestIndirMatchesGc: the model's flagIndir (isDirectIface) is gc's IfaceIndir, on structs and
// arrays mixing zero-size and pointer fields in every position.
func TestIndirMatchesGc(t *testing.T) {
	p := new(int)
	var f func()
	m := map[int]int{}
	c := make(chan int)
	u := unsafe.Pointer(p)
	cases := map[string]any{
		"*int":           p,
		"func":           f,
		"map":            m,
		"chan":           c,
		"unsafe.Pointer": u,
		"int":            1,
		"string":         "s",
		"[1]*int":        [1]*int{p},
		"[2]*int":        [2]*int{p, p},
		"[0]*int":        [0]*int{},
		"[1][1]*int":     [1][1]*int{{p}},
		"struct{p}":      struct{ p *int }{p},
		"struct{_ z; p}": struct {
			_ z
			p *int
		}{p: p},
		"struct{p; _ z}": struct {
			p *int
			_ z
		}{p: p},
		"struct{zs; [0]int; p}": struct {
			a zs
			b [0]int
			p *int
		}{p: p},
		"struct{z; [1]*int}": struct {
			a z
			b [1]*int
		}{b: [1]*int{p}},
		"struct{[1]z; m}": struct {
			a [1]z
			m map[int]int
		}{m: m},
		"struct{[2][0]int; f}": struct {
			a [2][0]int
			f func()
		}{},
		"struct{int; p}": struct {
			a int
			p *int
		}{p: p},
		"struct{p; q}": struct{ p, q *int }{p, p},
		"[1]struct{_ z; p}": [1]struct {
			_ z
			p *int
		}{{p: p}},
		"[1]struct{p; _ z}": [1]struct {
			p *int
			_ z
		}{{p: p}},
		"struct{struct{_ z; p}}": struct {
			s struct {
				_ z
				p *int
			}
		}{},
		"struct{}": struct{}{},
		"z":        z{},
		"[0]int":   [0]int{},
	}
	for name, x := range cases {
		if r, mo := realIndir(x), modelIndir(x); r != mo {
			t.Errorf("%s: gc flagIndir %v, model %v", name, r, mo)
		}
	}
}
