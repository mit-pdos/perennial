package diff

import (
	"reflect"
	"sync"
	"testing"

	"github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectcore"
	rm "github.com/mit-pdos/perennial/goose/model/reflect/harness/reflectmodel"
)

// Types whose layout a Go model changes (go.layoutModelled) are opaque to reflection, and
// nothing else is: the minimal program of Upamanyu's rule (etcd-grove#40).

// Mutex stands for a sync.Mutex a model redefines: the test declares it layoutModelled.
type Mutex struct {
	state int32
	sema  uint32
}

// MS is the minimal program's struct: a redefined Mutex, then an int.
type MS struct {
	mu Mutex
	n  int
}

// SM is MS with the real sync.Mutex, whose field mu is internal/sync.Mutex, a trusted type
// (Perennial/TrustedCode/internal/sync.lean: underlying bool) in go.layoutModelledNames.
type SM struct {
	mu sync.Mutex
	n  int
}

func init() {
	reflectcore.ExtraLayoutModelled[reflect.TypeFor[Mutex]()] = true
}

func tq(q reflectcore.TypeQ, tok any, i int) any { return reflectcore.TypeQuery(q, tok, i) }

// TestLayoutModelledOpaque: for MS, Kind, NumField, Field(i).Name/Type, ValueOf(s) and the
// address of field 1 (Value.Field(1)'s primitive) answer as in Go; every question about Mutex
// itself, or one that recurses into it or depends on its size, is stuck.
func TestLayoutModelledOpaque(t *testing.T) {
	isyncMutex := reflect.TypeFor[sync.Mutex]().Field(1).Type
	if isyncMutex.PkgPath() != "internal/sync" || !reflectcore.LayoutModelled(isyncMutex) {
		t.Fatalf("sync.Mutex's field %v (%s) is not layoutModelled", isyncMutex, isyncMutex.PkgPath())
	}
	for _, c := range []struct {
		name string
		T    reflect.Type
		tok  any
	}{
		{"MS", reflect.TypeFor[MS](), tk[MS]()},
		{"SM", reflect.TypeFor[SM](), tk[SM]()},
	} {
		T := c.T
		if got := reflectcore.TypeKind(c.tok); got != int(T.Kind()) {
			t.Errorf("Kind(%s) = %d, Go %v", c.name, got, T.Kind())
		}
		if got := reflectcore.TypeNumField(c.tok); got != T.NumField() {
			t.Errorf("NumField(%s) = %d, Go %d", c.name, got, T.NumField())
		}
		for i := 0; i < T.NumField(); i++ {
			if got := tq(reflectcore.QFieldName, c.tok, i); got != T.Field(i).Name {
				t.Errorf("Field(%d).Name of %s = %v, Go %s", i, c.name, got, T.Field(i).Name)
			}
			if got := reflectcore.TypeFieldType(c.tok, i); got != reflectcore.Token(T.Field(i).Type) {
				t.Errorf("Field(%d).Type of %s = %T, Go %v", i, c.name, got, T.Field(i).Type)
			}
		}
		// Kind(MS) in the model, through TypeOf
		if k := rm.TypeOf(reflect.New(T).Elem().Interface()).Kind(); int(k) != int(T.Kind()) {
			t.Errorf("TypeOf(%s{}).Kind() = %v", c.name, k)
		}
	}
	s := MS{n: 7}
	// ValueOf(s): isDirectIface(MS) asks only about MS's last field (int)
	v := rm.ValueOf(s)
	if v.Kind() != rm.Struct || v.Type() != rm.TypeOf(s) {
		t.Errorf("ValueOf(s): kind %v, type %v", v.Kind(), v.Type())
	}
	if got, ok := v.Interface().(MS); !ok || got != s {
		t.Errorf("ValueOf(s).Interface() = %v", v.Interface())
	}
	vm := rm.ValueOf(SM{n: 7})
	if vm.Kind() != rm.Struct {
		t.Errorf("ValueOf(SM{}).Kind() = %v", vm.Kind())
	}
	// Value.Field(1)'s primitive: the address of field 1 of *MS, and of field 0 (a *Mutex)
	if p, ok := reflectcore.FieldRefAt(&s, 1).(*int); !ok || p != &s.n {
		t.Errorf("FieldRefAt(&s, 1) = %v", reflectcore.FieldRefAt(&s, 1))
	}
	if p, ok := reflectcore.FieldRefAt(&s, 0).(*Mutex); !ok || p != &s.mu {
		t.Errorf("FieldRefAt(&s, 0) = %v", reflectcore.FieldRefAt(&s, 0))
	}
	// a pointer to a Mutex is not opaque: only the Mutex itself
	if got := reflectcore.TypeKind(tk[*Mutex]()); got != int(reflect.Pointer) {
		t.Errorf("Kind(*Mutex) = %d", got)
	}
	if got := reflectcore.TypeElem(tk[*Mutex]()); got != tk[Mutex]() {
		t.Errorf("Elem(*Mutex) = %T", got)
	}
	if got := reflectcore.TypeIdentByName(tk[Mutex]()); !got {
		t.Errorf("identByName(Mutex) = false")
	}
	m, ms := &s.mu, &SM{}
	for name, f := range map[string]func(){
		"Kind(Mutex)":               func() { reflectcore.TypeKind(tk[Mutex]()) },
		"NumField(Mutex)":           func() { reflectcore.TypeNumField(tk[Mutex]()) },
		"FieldType(Mutex, 0)":       func() { reflectcore.TypeFieldType(tk[Mutex](), 0) },
		"Underlying(Mutex)":         func() { reflectcore.TypeUnderlying(tk[Mutex]()) },
		"Kind(internal/sync.Mutex)": func() { reflectcore.TypeKind(reflectcore.Token(isyncMutex)) },
		"ValueOf(&s.mu).Elem()":     func() { rm.ValueOf(&s).Elem(); rm.ValueOf(m).Elem() },
		"ValueOf(Mutex{})":          func() { rm.ValueOf(Mutex{}) },
		"ValueOf(&ms.mu.mu).Elem()": func() { rm.ValueOf(&ms.mu).Elem(); rm.ValueOf(reflectcore.FieldRefAt(&ms.mu, 1)).Elem() },
		"FieldRefAt(&m, 0)":         func() { reflectcore.FieldRefAt(m, 0) },
		"arrayOf(MS, 2)":             func() { tq(reflectcore.QArrayOf, tk[MS](), 2) },
		"arrayOf(MS, 1)":             func() { tq(reflectcore.QArrayOf, tk[MS](), 1) },
		"arrayOf([1]MS, 0)":          func() { tq(reflectcore.QArrayOf, tk[[1]MS](), 0) },
		"arrayOf(SM, 2)":            func() { tq(reflectcore.QArrayOf, tk[SM](), 2) },
		"isZeroSize(MS) (struct{MS; *int})": func() {
			rm.ValueOf(struct {
				s MS
				p *int
			}{})
		},
		"isZeroSize(Mutex) (struct{Mutex; *int})": func() {
			rm.ValueOf(struct {
				m Mutex
				p *int
			}{})
		},
		"isDirectIface([1]Mutex)": func() { rm.ValueOf([1]Mutex{}) },
		"ConvertAt(*Mutex, *MS)":   func() { reflectcore.ConvertAt(m, tk[*MS]()) },
	} {
		if !stuck(f) {
			t.Errorf("%s: not stuck", name)
		}
	}
	// arrayOf of a type that does not reach a layoutModelled one still answers
	if got := tq(reflectcore.QArrayOf, tk[struct{ p *Mutex }](), 1); got == nil {
		t.Errorf("arrayOf(struct{ *Mutex }, 1) = nil")
	}
}

// TestTypeOfTypeKindStuck: TypeOf(reflect.TypeOf(0)) is the model's rtype (Go's *rtype), and
// its Kind is stuck (rtype is layoutModelled); identByName still answers.
func TestTypeOfTypeKindStuck(t *testing.T) {
	ty := rm.TypeOf(rm.TypeOf(0))
	if !stuck(func() { ty.Kind() }) {
		t.Errorf("TypeOf(TypeOf(0)).Kind(): not stuck")
	}
}
