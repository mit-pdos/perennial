// Package names exercises goose's naming of Go identifiers (see glang.GoName):
// each declaration below would, under a weaker naming scheme, make a Lean
// name refer to a different declaration than the Go name does (or make two
// declarations share a name).
package names

// A Lean keyword as a type name (Type”), and a field of that name
// and type (the projection Type'): inside namespace IntOrString, the type
// must not resolve to the projection.
type Type int64

type IntOrString struct {
	Type  Type
	Other Type
}

func useIntOrString() Type {
	x := IntOrString{Type: Type(7)}
	x.Type = Type(9)
	return x.Type + x.Other
}

// Other Lean keywords, as a type, function, global, field and method
// (def”, fun”, at”, match', show”), and a name Lean cannot lex (é).
type def int64

var at def

func fun() def { return at }

type K struct {
	match def
}

func (k K) show() def { return k.match }

func (k K) end() def { return k.show() }

// Names Lean's lexer rejects (written in guillemets): a type, function,
// field and method.
type é int64

type Ñ struct {
	ñ é
}

func ü(x é) é { return x }

func (n Ñ) ö() é { return ü(n.ñ) }

// A framework name the generated code refers to unqualified (Pair), as a
// type, and a field of that name and type.
type Pair int64

type HasPair struct {
	Pair Pair
}

// Names Lean and goose declare inside a type's namespace (S.ty,
// S.underlying, S.fields, S.mk, ...) and the reserved names of a definition
// (f.eq_def, f.eq_1), as package-level names referenced inside a type's or
// function's namespace.
type ty int64
type underlying int64
type fields int64

type U struct {
	A ty
	B underlying
	C fields
}

func (u U) get() ty { return u.A }

func mk() int     { return 1 }
func rec() int    { return 2 }
func impl() int   { return 3 }
func eq_def() int { return 4 }
func eq_1() int   { return 5 }

func callsReserved() int { return mk() + rec() + impl() + eq_def() + eq_1() }

func (u U) callsReserved() int { return mk() + rec() + impl() + eq_def() + eq_1() }

// The binders of the generated assumptions (∀ (x : S) (y : T)), and the
// members of a TypeAssumptions class (get_F, set_F, underlying, ...), which
// are in scope in the later members' types, as type names.
type x int64
type get_a int64

type V struct {
	a get_a
	b x
	c get_a
}

// A method named like a package function, type and global, called from
// another method: the function, type and global must not resolve to the
// method.
func f() int { return 1 }

type T int64

var gl int

type S struct{ n int }

func (s S) f() int  { return 2 }
func (s S) T() T    { return T(3) }
func (s S) gl() int { return 4 }
func (s S) g() int  { return f() + int(s.T()) + gl }

// Methods named like the names goose and Lean declare in a type's
// namespace, and like framework names.
func (s S) ty() int         { return 5 }
func (s S) underlying() int { return 6 }
func (s S) mk() int         { return 7 }
func (s S) Val() int        { return 8 }

// Type parameters: named like a framework name (Val), like a binder of the
// generated code (x, l, GF), and like a field of the same struct (T).
type Box[Val any] struct {
	Val Val
	w   Val
}

type Box2[T any, x any, l any, GF any] struct {
	T  T
	U  T
	X  x
	L  l
	GF GF
}

func unbox[Val any](b Box[Val]) Val { return b.Val }

// A Go name with the shape of an encoded generated name.
type Foo_Assumptions struct{ n int }

func useFoo(p Foo_Assumptions) int { return p.n }

// A package type named like a framework value type, used as a field type
// (the field's Lean type must be this GoSlice, not the framework's).
type GoSlice struct{ a, b int }

type HoldsGoSlice struct {
	buf []byte
	s   GoSlice
}

// A type parameter named like a package type that an alias makes reachable
// inside the generic type (the field u has the package type TP).
type TP struct{ n int }

type AliasTP = TP

type GenBox[TP any] struct {
	v TP
	u AliasTP
}

// Class members derived from names: the field `unfold` and the method `get`;
// the methods `ptr_f` and `f`.
type Members struct {
	unfold int
}

func (m Members) get() int    { return m.unfold }
func (m *Members) f() int     { return 1 }
func (m *Members) ptr_f() int { return 2 }

// A function-local constant named like a framework name.
func localConst() int {
	const Val = 3
	const Pair = Val + 1
	return Pair
}
