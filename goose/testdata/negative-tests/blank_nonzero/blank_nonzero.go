package blank_nonzero

// Go ignores a blank field's bytes in == and in map keys; the model's values would not.

type T struct {
	a uint32
	_ uint32 // ERROR a blank field of non-zero size
}
