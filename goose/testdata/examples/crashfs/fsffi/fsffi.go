// Package fsffi is a durable filesystem with whole-file operations: the Go
// side of GooseLang's filesystem extension (Perennial/GooseLang/Ext/Fs). Its
// functions are trusted: Perennial models them with the extension's operations
// (Perennial/TrustedCode/.../crashfs/fsffi.lean) instead of translating them.
package fsffi

import "os"

// Read returns the entire contents of the file name. It panics if the file
// cannot be read (the model is stuck if the file does not exist).
func Read(name string) string {
	b, err := os.ReadFile(name)
	if err != nil {
		panic(err)
	}
	return string(b)
}

// Write replaces the entire contents of the file name by data, creating it if
// needed, atomically and durably: a crash leaves either the old or the new
// contents, and the new ones once Write returns. It panics on an I/O error.
func Write(name string, data string) {
	tmp := name + ".tmp"
	f, err := os.Create(tmp)
	if err != nil {
		panic(err)
	}
	if _, err := f.WriteString(data); err != nil {
		panic(err)
	}
	if err := f.Sync(); err != nil {
		panic(err)
	}
	if err := f.Close(); err != nil {
		panic(err)
	}
	if err := os.Rename(tmp, name); err != nil {
		panic(err)
	}
	dir, err := os.Open(".")
	if err != nil {
		panic(err)
	}
	if err := dir.Sync(); err != nil {
		panic(err)
	}
	if err := dir.Close(); err != nil {
		panic(err)
	}
}
