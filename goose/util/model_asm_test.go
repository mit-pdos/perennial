package util

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

const asmReal = `package p

// F is in assembly.
func F(x int) int

func G() int { return 1 }
`

const asmModel = `package p

// MODEL: F's Go body, in place of the assembly.
func F(x int) int { return x + 1 }
`

const asmFile = `#include "textflag.h"

TEXT ·F(SB),NOSPLIT,$0-16
	JMP	fbody<>(SB)

TEXT fbody<>(SB),NOSPLIT,$0
	MOVQ	x+0(FP), AX
	MOVQ	AX, ret+8(FP)
	RET
`

// TestModelBlankAsm: a model replaces a function whose body is assembly; the
// overlay blanks the assembly file (which defines only the replaced function
// and a file-local helper), and the program runs the model's body.
func TestModelBlankAsm(t *testing.T) {
	root := modelModule(t, asmReal, asmModel,
		"[model]\ndir = \"model\"\nreplaces = [\"F\"]\nblank_asm = [\"f_amd64.s\"]\n",
		map[string]string{
			"p/f_amd64.s":  asmFile,
			"main/main.go": "package main\n\nimport \"m/p\"\n\nfunc main() { println(p.F(2), p.G()) }\n",
		})
	models, err := buildModels(root, "./main")
	if err != nil {
		t.Fatal(err)
	}
	if s := string(models.Overlay[filepath.Join(root, "p", "f_amd64.s")]); !strings.Contains(s, "blanked") {
		t.Fatalf("f_amd64.s is not blanked: %q", s)
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
	if string(out) != "3 1\n" {
		t.Errorf("go run printed %q, want the model's F: \"3 1\\n\"", out)
	}
}

// TestModelBlankAsmAmd64Header: a file that includes the toolchain's
// asm_amd64.h (only GOAMD64 feature flags, as internal/bytealg's
// count_amd64.s does) is blanked like one that includes textflag.h only.
func TestModelBlankAsmAmd64Header(t *testing.T) {
	root := modelModule(t, asmReal, asmModel,
		"[model]\ndir = \"model\"\nreplaces = [\"F\"]\nblank_asm = [\"f_amd64.s\"]\n",
		map[string]string{"p/f_amd64.s": "#include \"asm_amd64.h\"\n" + asmFile})
	models, err := buildModels(root, "./p")
	if err != nil {
		t.Fatal(err)
	}
	if s := string(models.Overlay[filepath.Join(root, "p", "f_amd64.s")]); !strings.Contains(s, "blanked") {
		t.Fatalf("f_amd64.s is not blanked: %q", s)
	}
}

// TestModelBlankAsmRefused: the checks that guard the blanking.
func TestModelBlankAsmRefused(t *testing.T) {
	for _, c := range []struct {
		name, real, asm, replaces, blank, want string
	}{
		{"unreplaced-exported",
			asmReal + "\nfunc H() int\n",
			asmFile + "\nTEXT ·H(SB),NOSPLIT,$0-8\n\tMOVQ\t$7, ret+0(FP)\n\tRET\n",
			`"F"`, `"f_amd64.s"`, "defines ·H, which is not a replaced bodyless function"},
		{"other-package-symbol",
			asmReal,
			asmFile + "\nTEXT runtime·q(SB),NOSPLIT,$0\n\tRET\n",
			`"F"`, `"f_amd64.s"`, "defines runtime·q"},
		{"data",
			asmReal,
			asmFile + "\nGLOBL ·tab(SB), RODATA, $8\n",
			`"F"`, `"f_amd64.s"`, "defines ·tab"},
		{"local-header",
			asmReal + "\nfunc H()\n",
			"#include \"defs_amd64.h\"\n" + asmFile + "\nDEF(·H)\n",
			`"F"`, `"f_amd64.s"`, `includes "defs_amd64.h", which is not a toolchain header`},
		{"not-listed", asmReal, asmFile, `"F"`, ``, `replaces "F", defined in assembly at`},
		{"no-such-file", asmReal, asmFile, `"F"`, `"f_amd64.s", "g_amd64.s"`,
			`blank_asm "g_amd64.s": not an assembly file of the real package`},
		{"not-asm", asmReal, asmFile, `"F"`, `"p.go"`, `blank_asm "p.go": not the base name of an assembly`},
	} {
		t.Run(c.name, func(t *testing.T) {
			config := "[model]\ndir = \"model\"\nreplaces = [" + c.replaces + "]\nblank_asm = [" + c.blank + "]\n"
			root := modelModule(t, c.real, asmModel, config, map[string]string{"p/f_amd64.s": c.asm,
				"p/defs_amd64.h": "#define DEF(name) TEXT name(SB),NOSPLIT,$0; RET\n"})
			models, err := buildModels(root, "./p")
			if err == nil {
				t.Fatalf("no error, want %q", c.want)
			}
			if !strings.Contains(err.Error(), c.want) {
				t.Errorf("error:\n%v\nwant it to contain %q", err, c.want)
			}
			if models != nil {
				if _, ok := models.Overlay[filepath.Join(root, "p", "f_amd64.s")]; ok {
					t.Errorf("f_amd64.s blanked although refused")
				}
			}
		})
	}
}

// TestModelBytealgDifftest is the difftest of internal/bytealg's model
// (Perennial/Code/internal/bytealg.toml, goose/model/overlay/internal/bytealg):
// the standard library's own strings and bytes tests, under the overlay that
// replaces IndexByte, IndexByteString, Index and IndexString by their Go
// models and blanks indexbyte_amd64.s and index_amd64.s. It runs only under
// the toolchain the translations are generated with (the model is of its
// sources), and not with -short. go vet is off: it cannot enter internal/gomodel,
// a directory only the overlay adds.
func TestModelBytealgDifftest(t *testing.T) {
	if testing.Short() {
		t.Skip("the strings and bytes tests (-short)")
	}
	if out, _ := exec.Command("go", "env", "GOVERSION").Output(); strings.TrimSpace(string(out)) != "go1.26.11" {
		t.Skipf("go is %s; the bytealg model is of go1.26.11's sources", strings.TrimSpace(string(out)))
	}
	repo, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	files := map[string]string{"go.mod": "module m\n\ngo 1.26\n",
		"main/main.go": "package main\n\nimport \"strings\"\n\nfunc main() { println(strings.Index(\"ab\", \"b\")) }\n"}
	for _, c := range []string{"internal/gomodel", "internal/bytealg"} {
		b, err := os.ReadFile(filepath.Join(repo, "Perennial/Code", c+".toml"))
		if err != nil {
			t.Fatal(err)
		}
		files["cfg/"+c+".toml"] = string(b)
	}
	root := t.TempDir()
	writeTree(t, root, files)
	models, err := BuildModels(root, filepath.Join(root, "cfg"), LoadOptions{ModelRoot: repo}, "./main")
	if err != nil {
		t.Fatal(err)
	}
	if models.Packages["internal/bytealg"] == nil {
		t.Fatalf("no model of internal/bytealg: %v", models.Packages)
	}
	for _, s := range []string{"indexbyte_amd64.s", "index_amd64.s"} {
		found := false
		for p, c := range models.Overlay {
			if filepath.Base(p) == s && strings.Contains(string(c), "blanked") {
				found = true
			}
		}
		if !found {
			t.Errorf("%s is not blanked", s)
		}
	}
	ov, err := models.WriteGoOverlay(LoadOptions{}, filepath.Join(root, "ov"))
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "test", "-count=1", "-vet=off", "-overlay", ov, "strings", "bytes")
	cmd.Dir = root
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=amd64")
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("go test strings bytes under the model: %v\n%s", err, out)
	}
}
