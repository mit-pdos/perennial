package semantics

// recoverPanicNil recovers the panic of panic(nil): since Go 1.21 it panics with
// a *runtime.PanicNilError, so recover() is not nil.
func recoverPanicNil() (ok bool) {
	defer func() {
		ok = recover() != nil
	}()
	panic(nil)
}

func testRecoverPanicNil() bool {
	return recoverPanicNil()
}
