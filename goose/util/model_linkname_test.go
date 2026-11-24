package util

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// TestModelRuntimePushLinkname: a model of a function whose definition the
// runtime pushes (internal/bytealg.MakeNoZero, `//go:linkname
// bytealg_MakeNoZero internal/bytealg.MakeNoZero` in runtime/slice.go) gets
// the runtime's directive blanked in the overlay, so that gc links the
// model's body (and not "duplicated definition of symbol").
func TestModelRuntimePushLinkname(t *testing.T) {
	if testing.Short() {
		t.Skip("rebuilds the runtime (-short)")
	}
	root := t.TempDir()
	writeTree(t, root, map[string]string{
		"go.mod":                    "module m\n\ngo 1.26\n",
		"cfg/internal/bytealg.toml": "[model]\ndir = \"model\"\nreplaces = [\"MakeNoZero\"]\n",
		"model/m.go": "package bytealg\n\n// MODEL: a test model, zeroed, of capacity n+1.\n" +
			"func MakeNoZero(n int) []byte { return make([]byte, n, n+1) }\n",
		"main/main.go": "package main\n\nimport \"strings\"\n\nfunc main() {\n" +
			"\tvar b strings.Builder\n\tb.Grow(5)\n\tprintln(b.Cap())\n}\n",
	})
	models, err := buildModels(root, "./main")
	if err != nil {
		t.Fatal(err)
	}
	var slice string
	for path, src := range models.Overlay {
		if filepath.Base(path) == "slice.go" && filepath.Base(filepath.Dir(path)) == "runtime" {
			slice = string(src)
		}
	}
	if slice == "" {
		t.Fatal("runtime/slice.go is not overlaid")
	}
	if strings.Contains(slice, "internal/bytealg.MakeNoZero") {
		t.Fatal("runtime/slice.go keeps its go:linkname to internal/bytealg.MakeNoZero")
	}
	if !strings.Contains(slice, "func bytealg_MakeNoZero(") {
		t.Fatal("runtime/slice.go lost bytealg_MakeNoZero")
	}
	ov, err := models.WriteGoOverlay(LoadOptions{}, filepath.Join(root, "ov"))
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "run", "-overlay", ov, "./main")
	cmd.Dir = root
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=amd64")
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("go run: %v\n%s", err, out)
	}
	if string(out) != "6\n" {
		t.Errorf("go run printed %q, want the model's capacity: \"6\\n\"", out)
	}
}
