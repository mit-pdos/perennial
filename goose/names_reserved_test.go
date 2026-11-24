package goose_test

import (
	"go/ast"
	"go/parser"
	"go/token"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose/glang"
)

// goKeywords cannot be Go identifiers, so an output name that is one cannot be
// captured by a Go name.
var goKeywords = map[string]bool{}

func init() {
	for _, w := range strings.Fields(`break case chan const continue default defer else
	fallthrough for func go goto if import interface map package range return select
	struct switch type var`) {
		goKeywords[w] = true
	}
}

// declaredGoNames are the names of the package-level declarations and methods
// of the Go files in dir: the Go names that become Lean names via GoName.
func declaredGoNames(t *testing.T, dir string) map[string]bool {
	names := map[string]bool{}
	fset := token.NewFileSet()
	files, _ := filepath.Glob(filepath.Join(dir, "*.go"))
	for _, f := range files {
		if strings.HasSuffix(f, "_test.go") {
			continue
		}
		af, err := parser.ParseFile(fset, f, nil, parser.SkipObjectResolution)
		if err != nil {
			t.Fatalf("%s: %v", f, err)
		}
		// types declared inside functions are package-level Lean declarations
		ast.Inspect(af, func(n ast.Node) bool {
			if ds, ok := n.(*ast.DeclStmt); ok {
				if gd, ok := ds.Decl.(*ast.GenDecl); ok && gd.Tok == token.TYPE {
					for _, sp := range gd.Specs {
						names[sp.(*ast.TypeSpec).Name.Name] = true
					}
				}
			}
			return true
		})
		for _, d := range af.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				names[d.Name.Name] = true
			case *ast.GenDecl:
				for _, s := range d.Specs {
					switch s := s.(type) {
					case *ast.TypeSpec:
						names[s.Name.Name] = true
					case *ast.ValueSpec:
						for _, n := range s.Names {
							names[n.Name] = true
						}
					}
				}
			}
		}
	}
	return names
}

var (
	leanBlockComment = regexp.MustCompile(`(?s)/-.*?-/`)
	leanLineComment  = regexp.MustCompile(`--[^\n]*`)
	leanString       = regexp.MustCompile(`"(?:[^"\\]|\\.)*"`)
	leanDeclKeyword  = regexp.MustCompile(`(?:^|\s)(?:def|abbrev|structure|class|instance|theorem|opaque|axiom|inductive)\s+$`)
	leanIdentTok     = regexp.MustCompile(`«[^»]*»|[A-Za-z_][A-Za-z0-9_'!?₀-₉]*`)
)

// bareNames are the identifiers of a Lean file that name-resolution looks up
// unqualified: every identifier not preceded by "." (the first component of a
// dotted name included), outside comments, strings, and the module header.
func bareNames(src string) map[string]bool {
	src = leanBlockComment.ReplaceAllString(src, " ")
	src = leanLineComment.ReplaceAllString(src, " ")
	src = leanString.ReplaceAllString(src, `""`)
	names := map[string]bool{}
	for _, line := range strings.Split(src, "\n") {
		f := strings.Fields(line)
		if len(f) > 0 && (f[0] == "module" || f[0] == "import" || f[0] == "namespace" ||
			f[0] == "end" || f[0] == "section" || (f[0] == "public" && len(f) > 1 && f[1] == "import")) {
			continue
		}
		for _, loc := range leanIdentTok.FindAllStringIndex(line, -1) {
			// a declared name is not a reference (a duplicate declaration is
			// an error, not a capture)
			if leanDeclKeyword.MatchString(line[:loc[0]]) {
				continue
			}
			if loc[0] > 0 {
				prev := line[loc[0]-1]
				if prev == '.' || prev == '#' && loc[0] > 1 && line[loc[0]-2] != ' ' && line[loc[0]-2] != '(' {
					continue
				}
				if prev >= '0' && prev <= '9' {
					continue
				}
			}
			names[line[loc[0]:loc[1]]] = true
		}
	}
	return names
}

// TestOutputNamesReserved checks the premise of the naming scheme's
// collision-freedom (glang.GoName): every name goose's output (the gold
// files) and proofgen's output (the generated proofs of the test packages)
// refer to unqualified is either the Lean name of a Go declaration of the
// package or a reserved name, so a Go declaration can never capture it.
func TestOutputNamesReserved(t *testing.T) {
	missing := map[string][]string{}
	check := func(dir, leanFile string) {
		src, err := os.ReadFile(leanFile)
		if err != nil {
			return
		}
		declared := map[string]bool{}
		// the Go model overlay of the package, if any, declares names too
		rel, _ := filepath.Rel("testdata/examples", dir)
		for g := range declaredGoNames(t, filepath.Join("testdata/models", rel)) {
			declared[glang.GoName(g)] = true
		}
		for g := range declaredGoNames(t, dir) {
			declared[glang.GoName(g)] = true
		}
		for n := range bareNames(string(src)) {
			// proofgen refers to the package's own declarations by their full
			// namespace (github_com.….T): Lean resolves the whole name first,
			// and a Go declaration named like its first component could add
			// only a candidate with field projections on a constant, which
			// does not elaborate (an error, not a capture)
			if n == "github_com" {
				continue
			}
			// go!"…" is a notation: its `go` cannot be a Go identifier
			if strings.ContainsAny(n, "'«₀") || declared[n] || goKeywords[strings.TrimSuffix(n, "!")] || glang.IsReservedName(n) {
				continue
			}
			missing[n] = append(missing[n], leanFile)
		}
	}
	root := "testdata/examples"
	genProof := "../Perennial/GeneratedProof/github_com/mit_pdos/perennial/goose/testdata/examples"
	err := filepath.WalkDir(root, func(path string, d os.DirEntry, err error) error {
		if err != nil || !d.IsDir() {
			return err
		}
		golds, _ := filepath.Glob(filepath.Join(path, "*.gold.lean"))
		for _, g := range golds {
			check(path, g)
		}
		if rel, err := filepath.Rel(root, path); err == nil && rel != "." && len(golds) > 0 {
			check(path, filepath.Join(genProof, rel+".lean"))
		}
		return nil
	})
	if err != nil {
		t.Fatal(err)
	}
	var ns []string
	for n := range missing {
		ns = append(ns, n)
	}
	sort.Strings(ns)
	for _, n := range ns {
		t.Errorf("unqualified output name %q is not reserved (glang.reservedNames); e.g. in %s", n, missing[n][0])
	}
}
