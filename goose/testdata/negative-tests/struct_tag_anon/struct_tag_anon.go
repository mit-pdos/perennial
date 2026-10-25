package struct_tag_anon

// Go's type identity includes struct tags, so two unnamed struct types that
// differ only in tags are different types (any(x) == any(y) is false for such
// x and y); goose drops tags, so it refuses a tag on a struct type that is not
// a defined type.

func f() any {
	return struct{ A int `json:"a"` }{} // ERROR struct tag on a struct type that is not a defined type
}
