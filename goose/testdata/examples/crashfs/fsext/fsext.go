// Package fsext is a durable filesystem with whole-file operations: the Go
// side of GooseLang's filesystem extension (Perennial/GooseLang/Ext/Fs). Its
// functions are trusted: Perennial models them with the extension's operations
// (Perennial/TrustedCode/.../crashfs/fsext.lean) instead of translating them.
//
// The model makes each operation one atomic step that cannot fail, and a
// written file durable. The implementation provides that:
//   - mu serializes the operations, so that no Read sees a Write's contents
//     before they are durable;
//   - a write goes to a fresh temporary file in the same directory, which is
//     synced, renamed over the file, and the directory synced;
//   - an operation that fails (an I/O error, a missing file) is retried
//     forever instead of panicking, so the program never sees a failure (it
//     may not return, which the model, as a safety model, allows).
package fsext

import (
	"os"
	"path/filepath"
	"sync"
)

var mu sync.Mutex

// Read returns the entire contents of the file name.
func Read(name string) string {
	mu.Lock()
	defer mu.Unlock()
	for {
		b, err := os.ReadFile(name)
		if err == nil {
			return string(b)
		}
	}
}

// Write replaces the entire contents of the file name by data, creating it if
// needed, atomically and durably.
func Write(name string, data string) {
	mu.Lock()
	defer mu.Unlock()
	for !tryWrite(name, data) {
	}
}

// tryWrite makes one attempt at Write. It changes nothing a Read can see
// unless the rename succeeds, and then the file holds data.
func tryWrite(name string, data string) bool {
	dir := filepath.Dir(name)
	f, err := os.CreateTemp(dir, ".fsext-*")
	if err != nil {
		return false
	}
	tmp := f.Name()
	_, err = f.WriteString(data)
	if err == nil {
		err = f.Sync()
	}
	if err2 := f.Close(); err == nil {
		err = err2
	}
	if err == nil {
		err = os.Rename(tmp, name)
	}
	if err != nil {
		os.Remove(tmp)
		return false
	}
	d, err := os.Open(dir)
	if err != nil {
		return false
	}
	err = d.Sync()
	d.Close()
	return err == nil
}
