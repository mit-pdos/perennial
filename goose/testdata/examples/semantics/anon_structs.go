package semantics

// unnamed struct types with fields (each has a generated structure)

func testAnonStructFields() bool {
	d := struct {
		f     int
		valid bool
	}{f: 3}
	d.valid = true
	p := &d.valid
	*p = false
	return d.f == 3 && !d.valid
}

func testAnonStructPointer() bool {
	p := &struct{ x int }{x: 1}
	p.x += 1
	return p.x == 2
}

// the same unnamed type as testAnonStructFields's
func anonStructSameType() struct {
	f     int
	valid bool
} {
	return struct {
		f     int
		valid bool
	}{f: 1, valid: true}
}

func testAnonStructSameType() bool {
	v := anonStructSameType()
	return v.f == 1 && v.valid
}

// as sync.OnceValue: an unnamed struct type with a type parameter, captured
func anonStructBox[T any](v T) func() T {
	d := struct {
		v T
		n int
	}{v: v}
	return func() T {
		d.n++
		return d.v
	}
}

func testAnonStructGeneric() bool {
	f := anonStructBox(5)
	return f() == 5 && f() == 5
}

type anonStructHolder struct {
	inner struct {
		a int
		b struct{ c bool }
	}
}

func testAnonStructNested() bool {
	var h anonStructHolder
	h.inner.a = 4
	h.inner.b.c = true
	return h.inner.a == 4 && h.inner.b.c
}

func testAnonStructArray() bool {
	var a [2]struct{ c bool }
	a[1].c = true
	return !a[0].c && a[1].c
}

// an unnamed struct type with field tags (the tags are part of its type)
func testAnonStructTagged() bool {
	d := struct {
		Name string `json:"name"`
		n    int
	}{Name: "a"}
	d.n = 2
	return d.Name == "a" && d.n == 2
}

// tags are part of an unnamed struct type's identity (Go spec, "Type identity")
func testAnonStructTagTypesEqual() bool {
	return !TypesEqual[struct {
		A int `json:"a"`
	}, struct{ A int }]() &&
		!TypesEqual[struct {
			A int `json:"a"`
		}, struct {
			A int `json:"b"`
		}]() &&
		TypesEqual[struct {
			A int `json:"a"`
		}, struct {
			A int `json:"a"`
		}]()
}
