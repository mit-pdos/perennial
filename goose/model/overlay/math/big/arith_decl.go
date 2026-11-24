// The Go models of math/big's six vector primitives that are assembly on
// amd64 (Perennial/Code/math/big.toml, [model]), spliced into arith_decl.go in
// place of the real, body-less declarations; the overlay blanks
// arith_amd64.s, which defines exactly these six.
//
// Each model is Go's own pure-Go build of the function, verbatim
// (arith_decl_pure.go, which the math_big_pure_go build tag selects): a call of
// the generic implementation in arith.go. The assembly computes the same
// function (math/big's own tests check the two against each other,
// arith_test.go), with no other effect; both read x and y and write z
// element by element.

package big

// MODEL: z = x + y over len(z) words, returning the carry: Go's pure-Go build.
func addVV(z, x, y []Word) (c Word) {
	return addVV_g(z, x, y)
}

// MODEL: z = x - y over len(z) words, returning the borrow: Go's pure-Go build.
func subVV(z, x, y []Word) (c Word) {
	return subVV_g(z, x, y)
}

// MODEL: z = x << s, returning the bits shifted out: Go's pure-Go build.
func lshVU(z, x []Word, s uint) (c Word) {
	return lshVU_g(z, x, s)
}

// MODEL: z = x >> s, returning the bits shifted out: Go's pure-Go build.
func rshVU(z, x []Word, s uint) (c Word) {
	return rshVU_g(z, x, s)
}

// MODEL: z = x*m + a, returning the carry word: Go's pure-Go build.
func mulAddVWW(z, x []Word, m, a Word) (c Word) {
	return mulAddVWW_g(z, x, m, a)
}

// MODEL: z = x + y*m + a, returning the carry word: Go's pure-Go build.
func addMulVVWW(z, x, y []Word, m, a Word) (c Word) {
	return addMulVVWW_g(z, x, y, m, a)
}
