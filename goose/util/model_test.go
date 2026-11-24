package util

import (
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// writeTree writes files (relative path -> contents) under root.
func writeTree(t *testing.T, root string, files map[string]string) {
	t.Helper()
	for p, c := range files {
		full := filepath.Join(root, p)
		if err := os.MkdirAll(filepath.Dir(full), 0777); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(full, []byte(c), 0666); err != nil {
			t.Fatal(err)
		}
	}
}

// modelModule writes a module m with package m/p (real), its model in
// model/ and its config cfg/m/p.toml, plus extra files, and returns the
// module's root.
func modelModule(t *testing.T, real, model, config string, extra map[string]string) string {
	root := t.TempDir()
	files := map[string]string{
		"go.mod":       "module m\n\ngo 1.26\n",
		"p/p.go":       real,
		"model/m.go":   model,
		"cfg/m/p.toml": config,
	}
	for k, v := range extra {
		files[k] = v
	}
	writeTree(t, root, files)
	return root
}

func buildModels(root string, patterns ...string) (*Models, error) {
	return BuildModels(root, filepath.Join(root, "cfg"), LoadOptions{ModelRoot: root}, patterns...)
}

const traceReal = `package p

import "strings"

var trace []string

func note(s string) string { trace = append(trace, s); return s }

var a = note("a")

// F is replaced.
//
//go:noinline
func F() string { return strings.ToUpper("f") }

var b = note("b")

var (
	c = note("c")
	d = note("d")
)

func init() { note("init0") }

func init() { note("init1") }

type T struct {
	X int
	y int
}

func (t T) M() int { return t.X }

func Trace() string { return strings.Join(trace, " ") }
`

const traceModel = `package p

import "sync/atomic"

var hits atomic.Int64

// MODEL: F counts its calls.
func F() string { var n atomic.Int32; n.Add(1); hits.Add(1); return "F" }

var b = note("B")

var (
	c = note("C")
)

//gomodel:replace init.0 "note(\"init0\")"
func init() { note("model-init0") }

func init() { note("added-init") }

type T struct {
	X int
	y int
	z bool
}
`

const traceConfig = `[model]
dir = "model"
replaces = ["F", "b", "c", "init.0", "T"]
`

// TestModelSplice runs a program over a package with a model, under the
// overlay goose model-overlay writes: the replaced variables initialize in
// their real places, the replaced init runs in its place, the model's own
// init after the real ones, the import only the replaced F used stays (as a
// blank import, as strings is still used by Trace), and the model's import
// is added.
func TestModelSplice(t *testing.T) {
	root := modelModule(t, traceReal, traceModel, traceConfig, map[string]string{
		"main/main.go": "package main\n\nimport (\n\t\"fmt\"\n\t\"m/p\"\n)\n\n" +
			"func main() { fmt.Println(p.F(), p.T{X: 1}.M(), p.Trace()) }\n",
	})
	models, err := buildModels(root, "./main")
	if err != nil {
		t.Fatal(err)
	}
	if models.Packages["m/p"] == nil {
		t.Fatalf("no model of m/p: %v", models.Packages)
	}
	ov, err := models.WriteGoOverlay(LoadOptions{}, filepath.Join(root, "ov"))
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "run", "-overlay", ov, "./main")
	cmd.Dir = root
	out, err := cmd.CombinedOutput()
	if err != nil {
		t.Fatalf("go run: %v\n%s", err, out)
	}
	want := "F 1 a B C d model-init0 init1 added-init\n"
	if string(out) != want {
		t.Errorf("go run printed %q, want %q", out, want)
	}
	spliced := string(models.Overlay[filepath.Join(root, "p", "p.go")])
	for _, s := range []string{
		`package p; import atomic "sync/atomic"`,
		"//line " + filepath.Join(root, "model", "m.go") + ":7:1\n// MODEL: F counts its calls.",
		"//line " + filepath.Join(root, "p", "p.go") + ":14:48\n",
	} {
		if !strings.Contains(spliced, s) {
			t.Errorf("the spliced p.go lacks %q:\n%s", s, spliced)
		}
	}
	if strings.Contains(spliced, "go:noinline") {
		t.Errorf("the spliced p.go keeps the real F's directive:\n%s", spliced)
	}
}

// TestModelImportBlanked checks that a real import only the replaced
// declaration used becomes a blank import.
func TestModelImportBlanked(t *testing.T) {
	root := modelModule(t,
		"package p\n\nimport \"strings\"\n\nfunc F() string { return strings.ToUpper(\"f\") }\n",
		"package p\n\nfunc F() string { return \"F\" }\n",
		"[model]\ndir = \"model\"\nreplaces = [\"F\"]\n", nil)
	models, err := buildModels(root, "./p")
	if err != nil {
		t.Fatal(err)
	}
	if s := string(models.Overlay[filepath.Join(root, "p", "p.go")]); !strings.Contains(s, `import _ "strings"`) {
		t.Errorf("strings is not blank:\n%s", s)
	}
}

func TestModelErrors(t *testing.T) {
	const real = `package p

import "strings"

var X, Y = 1, 2

const K = 3

func F(x int) int { return len(strings.Repeat("a", x)) }

func init() { _ = 1 }

type T struct {
	A int
	b int
}

func (t *T) M() {}
`
	for _, c := range []struct {
		name, model, replaces, extra, want string
	}{
		{"not-real", "func G() {}", `"G"`, "", `replaces "G": not a declaration of the real package`},
		{"not-in-model", "", `"F"`, "", `replaces "F": the model does not declare it`},
		{"kind", "var F = 1", `"F"`, "", `replaces "F": a func, which the model declares as a var`},
		{"shadow", "func F(x int) int { return 0 }", `"T"`, "", `the model declares "F", a real declaration`},
		{"const", "const K = 4", `"K"`, "", `replaces "K": a constant cannot be replaced`},
		{"partial-var", "var X = 1", `"X"`, "", `replaces "X" but not "Y"`},
		{"var-shape", "var X = 1\nvar Y = 2", `"X", "Y"`, "", `declares X, Y in one spec, the model X`},
		{"init-marker", "//gomodel:replace init.0 \"_ = 2\"\nfunc init() {}", `"init.0"`, "",
			`its first line is "_ = 1", the marker says "_ = 2"`},
		{"init-unlisted", "//gomodel:replace init.0 \"_ = 1\"\nfunc init() {}", `"F"`, "",
			`marked as replacing init.0, which replaces does not list`},
		{"signature", "func F(x int64) int { return 0 }", `"F"`, "",
			"F: type func(x int) int, which the model changes to func(x int64) int"},
		{"exported-field", "type T struct {\n\tA int64\n\tb int\n}", `"T"`, "",
			"T: exported fields [A int embedded=false tag=\"\"], which the model changes to [A int64"},
		{"comparable", "type T struct {\n\tA int\n\tb []int\n}", `"T"`, "", "T: the model changes whether it is comparable"},
		{"added-method", "func (t *T) N() {}", ``, "", "T: the model adds the method N to *T, which added_methods does not list"},
		{"added-unused", "func (t *T) N() {}", ``, `added_methods = ["T.N", "T.Q*"]`,
			`added_methods "T.Q*" matches no method the model adds`},
		{"method-sig", "func (t T) M() {}", `"T.M"`, "", "T.M: (*m/p.T) func(), which the model changes to (m/p.T) func()"},
		{"import-conflict", "import strings \"sync/atomic\"\n\nvar X, Y = strings.AddInt32, 2", `"X", "Y"`, "",
			"which p.go imports as"},
		{"build-tag", "", `"F"`, "", "a model file has no build constraint"},
		{"type-error", "func F(x int) int { return undefined }", `"F"`, "", "undefined: undefined"},
		{"trusted", "func F(x int) int { return 0 }", `"F"`, "", `replaces "F", which is also listed in trusted`},
		{"star-and-names", "func F(x int) int { return 0 }", `"*", "F"`, "", `replaces "*" (a whole-package model) together with names`},
		{"glob", "func F(x int) int { return 0 }", `"F*"`, "", `replaces "F*": a pattern`},
		{"names-only-unmatched", "func F(x int) int { return 0 }\nfunc G() {}", `"F"`, `names_only = ["G", "H*"]`,
			`names_only "H*" matches no model declaration`},
	} {
		t.Run(c.name, func(t *testing.T) {
			model := "package p\n\n" + c.model + "\n"
			if c.name == "build-tag" {
				model = "//go:build goose\n\npackage p\n\nfunc F(x int) int { return 0 }\n"
			}
			config := "[model]\ndir = \"model\"\nreplaces = [" + c.replaces + "]\n" + c.extra + "\n"
			if c.name == "trusted" {
				config = "trusted = [\"F\"]\n" + config
			}
			root := modelModule(t, real, model, config, nil)
			_, err := buildModels(root, "./p")
			if err == nil {
				t.Fatalf("no error, want %q", c.want)
			}
			if !strings.Contains(err.Error(), c.want) {
				t.Errorf("error:\n%v\nwant it to contain %q", err, c.want)
			}
		})
	}
}

func TestModelConfigNoReplaces(t *testing.T) {
	root := modelModule(t, "package p\n", "package p\n", "[model]\ndir = \"model\"\n", nil)
	if _, err := buildModels(root, "./p"); err == nil || !strings.Contains(err.Error(), "[model] has no replaces") {
		t.Errorf("error %v, want [model] has no replaces", err)
	}
}

// TestModelAddedNonStd: only a standard-library path may be added.
func TestModelAddedNonStd(t *testing.T) {
	root := modelModule(t, "package p\n", "package q\n", "", map[string]string{
		"go.mod":                   "module example.com/m\n\ngo 1.26\n",
		"cfg/example_com/m/q.toml": "[model]\ndir = \"model\"\nreplaces = [\"*\"]\n",
	})
	if _, err := buildModels(root, "example.com/m/q"); err == nil ||
		!strings.Contains(err.Error(), "of a standard-library path may add a package") {
		t.Errorf("error %v, want a refusal of an added non-standard package", err)
	}
}

// TestModelWholePackage replaces every file of p.
func TestModelWholePackage(t *testing.T) {
	root := modelModule(t, "package p\n\nimport \"strings\"\n\nfunc F() string { return strings.ToUpper(\"f\") }\n\nfunc G() {}\n",
		"package p\n\nfunc F() string { return \"F\" }\n", "[model]\ndir = \"model\"\nreplaces = [\"*\"]\n", nil)
	models, err := buildModels(root, "./p")
	if err != nil {
		t.Fatal(err)
	}
	if s := string(models.Overlay[filepath.Join(root, "p", "p.go")]); s != "package p\n" {
		t.Errorf("p.go is %q, want only its package clause", s)
	}
	if _, ok := models.Overlay[filepath.Join(root, "p", ModelFilePrefix+"m.go")]; !ok {
		t.Errorf("no %sm.go in the overlay", ModelFilePrefix)
	}
}

// TestModelWholePackageAPI: a whole-package model keeps the exported API;
// its unexported declarations, the unexported methods of an interface that
// has some, and the order of methods are its own.
func TestModelWholePackageAPI(t *testing.T) {
	const real = `package p

type I interface {
	M() int
	m()
}

type impl struct{ x []int }

func (*impl) M() int { return 0 }
func (*impl) m()     {}

type T struct{ X int }

func (T) A() {}
func (T) B() {}

func h(x int) int { return x }
`
	for _, c := range []struct{ name, iface, want string }{
		{"ok", "M() int\n\ttok() any", ""},
		{"no-unexported", "M() int", "I: the model changes whether the interface has unexported methods"},
		{"exported-method", "M() string\n\ttok() any", "I: method M of I has type"},
	} {
		t.Run(c.name, func(t *testing.T) {
			model := "package p\n\ntype I interface {\n\t" + c.iface + "\n}\n\n" +
				"type impl struct{ t any }\n\nfunc (impl) M() int { return 0 }\nfunc (impl) tok() any { return nil }\n\n" +
				"type T struct{ X int }\n\nfunc (T) B() {}\nfunc (T) A() {}\n\nfunc h() {}\n"
			if c.name == "exported-method" {
				model = strings.Replace(model, "func (impl) M() int { return 0 }", "func (impl) M() string { return \"\" }", 1)
			}
			root := modelModule(t, real, model, "[model]\ndir = \"model\"\nreplaces = [\"*\"]\n", nil)
			_, err := buildModels(root, "./p")
			switch {
			case c.want == "" && err != nil:
				t.Errorf("error %v, want none", err)
			case c.want != "" && (err == nil || !strings.Contains(err.Error(), c.want)):
				t.Errorf("error:\n%v\nwant it to contain %q", err, c.want)
			}
		})
	}
}

// TestModelStdAdded is the toolchain check for D3: a standard-library
// model (here, of unicode/utf16, with an addition) that imports the package
// the overlay adds, internal/gomodel (Perennial/Code/internal/gomodel.toml),
// builds with go build -overlay. go1.26.0's go list does not find an added
// standard-library package through go/packages (its overlay files are new):
// there the builder must say so.
func TestModelStdAdded(t *testing.T) {
	repo, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	gomodelConfig, err := os.ReadFile(filepath.Join(repo, "Perennial/Code/internal/gomodel.toml"))
	if err != nil {
		t.Fatal(err)
	}
	root := t.TempDir()
	writeTree(t, root, map[string]string{
		"go.mod":                    "module m\n\ngo 1.26\n",
		"main/main.go":              "package main\n\nimport \"unicode/utf16\"\n\nfunc main() { println(utf16.IsSurrogate(1)) }\n",
		"cfg/internal/gomodel.toml": string(gomodelConfig),
		"cfg/unicode/utf16.toml":    "[model]\ndir = \"" + filepath.Join(root, "model") + "\"\nreplaces = []\n",
		"model/choice.go":           "package utf16\n\nimport \"internal/gomodel\"\n\nfunc modelChoice() bool { return gomodel.Choose() }\n",
	})
	models, err := BuildModels(root, filepath.Join(root, "cfg"), LoadOptions{ModelRoot: repo}, "./main")
	out, _ := exec.Command("go", "version").Output()
	if strings.Contains(string(out), "go1.26.0 ") {
		if err == nil || !strings.Contains(err.Error(), "does not accept a standard-library package added by an overlay") {
			t.Fatalf("under %s: error %v, want the toolchain's refusal", out, err)
		}
		t.Skipf("%s refuses a standard-library package added by an overlay", strings.TrimSpace(string(out)))
	}
	if err != nil {
		t.Fatal(err)
	}
	if models.Packages["internal/gomodel"] == nil || !models.Packages["internal/gomodel"].Added {
		t.Fatalf("internal/gomodel is not an added package: %v", models.Packages)
	}
	ov, err := models.WriteGoOverlay(LoadOptions{}, filepath.Join(root, "ov"))
	if err != nil {
		t.Fatal(err)
	}
	cmd := exec.Command("go", "build", "-o", os.DevNull, "-overlay", ov, "./main", "internal/gomodel")
	cmd.Dir = root
	if out, err := cmd.CombinedOutput(); err != nil {
		t.Fatalf("go build: %v\n%s", err, out)
	}
}

// TestModelRefusals are the models that change the real package's meaning
// through a route other than a replaced declaration's own type.
func TestModelRefusals(t *testing.T) {
	const inner = "type inner struct{ X int }\n\nfunc (inner) M() int { return 1 }\n\ntype E struct{ inner }\n\ntype U struct{ in inner }\n"
	for _, c := range []struct {
		name, real, model, replaces string
		extra                       map[string]string
		want                        string
	}{
		{"universe", "func F() bool { return true }", "const true = false", ``, nil,
			`the model declares "true", a predeclared identifier`},
		{"unexported-underlying", "type t int32\n\nfunc F() t { return 0 }", "type t int64", `"t"`, nil,
			"t: underlying type int32, which the model changes to int64"},
		{"comparable-component", inner, "type inner struct{ X int; y []int }",
			`"inner"`, nil, "U: the model changes whether it is comparable"},
		{"embedded-pointer", inner, "type E struct{ *inner }", `"E"`, nil, "E: exported fields"},
		{"override-promoted", inner, "func (E) M() int { return 2 }", ``, nil, "E: method M of E has type"},
		{"line-directive", "func F() {}", "//line other.go:1\nfunc G() {}", ``, nil, "a model file has no //line directive"},
		{"two-markers", "func init() { _ = 1 }",
			"//gomodel:replace init.0 \"_ = 1\"\nfunc init() {}\n\n//gomodel:replace init.0 \"_ = 1\"\nfunc init() {}",
			`"init.0"`, nil, "a second model init marked as replacing init.0"},
		{"name-suffix", "func F() {}", "func G() {}", ``,
			map[string]string{"model/x_windows.go": "package p\n\nfunc H() {}\n"}, "a model file's name has no GOOS or GOARCH suffix"},
	} {
		t.Run(c.name, func(t *testing.T) {
			root := modelModule(t, "package p\n\n"+c.real+"\n", "package p\n\n"+c.model+"\n",
				"[model]\ndir = \"model\"\nreplaces = ["+c.replaces+"]\n", c.extra)
			_, err := buildModels(root, "./p")
			if err == nil || !strings.Contains(err.Error(), c.want) {
				t.Errorf("error:\n%v\nwant it to contain %q", err, c.want)
			}
		})
	}
}

// TestModelLayoutChanged: the types whose gc layout a model changes, and
// the types that contain one (not through a pointer).
func TestModelLayoutChanged(t *testing.T) {
	root := modelModule(t, "package p\n\ntype T struct{ A, b int64 }\n\ntype U struct{ A int64; b int32 }\n",
		"package p\n\ntype T struct{ A int64 }\n\ntype U struct{ A int64; c int32 }\n",
		"[model]\ndir = \"model\"\nreplaces = [\"T\", \"U\"]\n", nil)
	models, err := buildModels(root, "./p")
	if err != nil {
		t.Fatal(err)
	}
	pkg := types.NewPackage("m/p", "p")
	named := func(n string) types.Type {
		return types.NewNamed(types.NewTypeName(0, pkg, n, nil), types.NewStruct(nil, nil), nil)
	}
	tt, ut := named("T"), named("U")
	field := func(ty types.Type) types.Type {
		return types.NewStruct([]*types.Var{types.NewField(0, nil, "x", ty, false)}, nil)
	}
	for _, c := range []struct {
		ty   types.Type
		want bool
	}{
		{tt, true}, {ut, false}, {types.NewArray(tt, 2), true}, {field(types.NewArray(tt, 1)), true},
		{field(types.NewPointer(tt)), false}, {field(ut), false},
	} {
		if _, got := models.LayoutChanged(c.ty); got != c.want {
			t.Errorf("LayoutChanged(%v) = %v, want %v", c.ty, got, c.want)
		}
	}
}
