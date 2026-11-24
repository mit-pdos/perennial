package gomodel

// ChooseString is an arbitrary string: every string is a result (and the loop
// may also not terminate). It is translated Go over Choose and ChooseUint64,
// not a primitive: a model uses it where Go's value is outside what the model
// tracks (a linker-set string, a symbol name, a command-line argument). In Go
// it is "".
func ChooseString() string {
	var b []byte
	for Choose() {
		b = append(b, byte(ChooseUint64()))
	}
	return string(b)
}

// ChooseStrings is an arbitrary []string (nil or not, of any length, every
// element any string). It is translated Go over Choose and ChooseString. In Go
// it is nil.
func ChooseStrings() []string {
	var a []string
	for Choose() {
		a = append(a, ChooseString())
	}
	return a
}
