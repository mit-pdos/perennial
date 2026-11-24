// The Go model of crypto/internal/rand's reader.Read
// (Perennial/Code/crypto/internal/rand.toml, [model]), spliced into rand.go in
// place of the real declaration.

package rand

import "internal/gomodel"

// MODEL: r.Read(b) fills b with random bytes and returns len(b), nil. Go's
// body reads boring.RandReader (boring.Enabled is false: no boringcrypto
// build) or calls drbg.Read(b), which fills b from the operating system
// (sysrand.Read: getrandom, or /dev/urandom where getrandom is missing) or,
// with GODEBUG=fips140=on, from the FIPS 140-3 CTR_DRBG (AES) seeded from it,
// or from the reader SetTestingReader installed (testing only, not translated).
// Neither the system call, the GODEBUG setting nor the DRBG has a semantics;
// every branch writes each byte of b once and returns len(b), nil. The model
// writes each byte of b with an arbitrary value (gomodel.ChooseUint64), every
// content Go can produce, and returns the same. Known limitation: where the
// operating system fails to provide randomness, Go crashes the program
// (sysrand.Read calls runtime.fatal; Go 1.24 and later); the model returns,
// as Perennial assumes the kernel's random source works (as it assumes
// allocation succeeds).
func (r reader) Read(b []byte) (n int, err error) {
	for i := range b {
		b[i] = byte(gomodel.ChooseUint64())
	}
	return len(b), nil
}
