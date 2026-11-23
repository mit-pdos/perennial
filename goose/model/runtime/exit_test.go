package runtime

// Evidence for the model of syscall.Exit (Perennial/TrustedCode/syscall.lean,
// AngelicExit) and for os.Exit's translation over it: the process ends with the
// status, no deferred function runs, no other goroutine takes another step; and
// os.Exit(0) panics in a test binary, where the testing package sets
// internal/testlog's flag (the model's start state is a program's, flag false).

import (
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

const exitProg = `package main

import (
	"fmt"
	"os"
	"time"
)

func main() {
	defer fmt.Println("deferred")
	go func() {
		<-time.After(10 * time.Millisecond)
		fmt.Println("goroutine")
	}()
	fmt.Println("before")
	os.Exit(3)
}
`

func TestExitEndsProgram(t *testing.T) {
	dir := t.TempDir()
	if err := os.WriteFile(filepath.Join(dir, "main.go"), []byte(exitProg), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "go.mod"), []byte("module e\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	bin := filepath.Join(dir, "e")
	build := exec.Command(filepath.Join(runtime.GOROOT(), "bin", "go"), "build", "-o", bin, ".")
	build.Dir = dir
	build.Env = append(os.Environ(), "GOFLAGS=", "GOTOOLCHAIN=local")
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("build: %v\n%s", err, out)
	}
	out, err := exec.Command(bin).Output()
	ee, ok := err.(*exec.ExitError)
	if !ok || ee.ExitCode() != 3 {
		t.Fatalf("exit status: %v", err)
	}
	if string(out) != "before\n" {
		t.Fatalf("output %q: a deferred function or another goroutine ran", out)
	}
}

func TestExit0PanicsInTest(t *testing.T) {
	defer func() {
		r := recover()
		if s, _ := r.(string); !strings.Contains(s, "unexpected call to os.Exit(0)") {
			t.Fatalf("recovered %v", r)
		}
	}()
	os.Exit(0)
}
