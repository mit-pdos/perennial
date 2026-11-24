// Package runtime holds the evidence for the model of runtime.buildVersion's
// initialization (Perennial/TrustedCode/runtime.lean, buildVersion.init: an
// arbitrary string), which runtime.Version (translated) returns: the value is
// whatever the linker writes, and the linker's -X flag writes any string, so
// Version may return a string that is not valid UTF-8; with the default
// toolchain it is the toolchain's version.
package runtime

import (
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"testing"
)

const prog = `package main

import (
	"fmt"
	"runtime"
)

func main() { fmt.Printf("%q", runtime.Version()) }
`

// runVersion builds prog with the extra arguments to go run and returns what
// it prints: Version()'s result, quoted.
func runVersion(t *testing.T, env []string, args ...string) string {
	t.Helper()
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(prog), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module v\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command(filepath.Join(runtime.GOROOT(), "bin", "go"), append(append([]string{"run"}, args...), ".")...)
	cmd.Dir = dir
	cmd.Env = append(append(os.Environ(), "GOFLAGS=", "GOTOOLCHAIN=local"), env...)
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("go run %v: %v\n%s", args, err, out)
	}
	return string(out)
}

// The default build: the toolchain's version, as this test binary's.
func TestDefault(t *testing.T) {
	if got, want := runVersion(t, nil), `"`+runtime.Version()+`"`; got != want {
		t.Errorf("Version() = %s, want %s", got, want)
	}
}

// -X runtime.buildVersion=<s> makes Version return s, any bytes: here
// "a\xffb", not valid UTF-8.
func TestLinkerSetsAnyString(t *testing.T) {
	if got, want := runVersion(t, nil, "-ldflags=-X runtime.buildVersion=a\xffb"), `"a\xffb"`; got != want {
		t.Errorf("Version() = %s, want %s", got, want)
	}
}
