package order_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestProgram builds testdata/prog with perennial-order and runs it: its
// checks hold only in Perennial's evaluation order.
func TestProgram(t *testing.T) {
	if testing.Short() {
		t.Skip("builds the standard library with perennial-order")
	}
	bin := filepath.Join(t.TempDir(), "perennial-order")
	if out, err := exec.Command("go", "build", "-o", bin, "../cmd/perennial-order").CombinedOutput(); err != nil {
		t.Fatalf("building perennial-order: %v\n%s", err, out)
	}
	// the program is "translated" (a translation in the code directory, and
	// no configuration: every declaration), its gcorder package is not
	code := t.TempDir()
	prog := filepath.Join(code, "github_com/mit_pdos/perennial/goose/order/testdata/prog.lean")
	if err := os.MkdirAll(filepath.Dir(prog), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(prog, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "run", "-toolexec="+bin+" -code "+code, "./testdata/prog")
	cmd.Env = append(os.Environ(), "GOFLAGS=")
	out, err := cmd.CombinedOutput()
	if err != nil || strings.TrimSpace(string(out)) != "ok" {
		t.Fatalf("%v\n%s", err, out)
	}
}
