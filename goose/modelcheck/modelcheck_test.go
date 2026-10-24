package modelcheck

import (
	"bufio"
	"go/ast"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"

	"github.com/mit-pdos/perennial/goose/util"
)

// TestCases checks that Assign and Range report exactly the lines of
// testdata/cases marked "// want".
func TestCases(t *testing.T) {
	pkgs, err := packages.Load(util.NewPackageConfig(".", false), "./testdata/cases")
	if err != nil {
		t.Fatal(err)
	}
	if len(pkgs) != 1 || len(pkgs[0].Errors) > 0 {
		t.Fatalf("could not load testdata/cases: %v", pkgs[0].Errors)
	}
	pkg := pkgs[0]

	file := filepath.Join("testdata", "cases", "cases.go")
	want := make(map[int]bool)
	f, err := os.Open(file)
	if err != nil {
		t.Fatal(err)
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for line := 1; sc.Scan(); line++ {
		if strings.HasSuffix(strings.TrimSpace(sc.Text()), "// want") {
			want[line] = true
		}
	}

	got := make(map[int]bool)
	for _, file := range pkg.Syntax {
		ast.Inspect(file, func(n ast.Node) bool {
			var at ast.Node
			var msg string
			var bad bool
			switch s := n.(type) {
			case *ast.AssignStmt:
				at, msg, bad = Assign(pkg.TypesInfo, s)
			case *ast.RangeStmt:
				at, msg, bad = Range(pkg.TypesInfo, s)
			}
			if bad {
				line := pkg.Fset.Position(at.Pos()).Line
				got[line] = true
				if !want[line] {
					t.Errorf("%s:%d: unexpected finding: %s", file.Name.Name, line, msg)
				}
				if !strings.HasPrefix(msg, Prefix) {
					t.Errorf("%s:%d: message without the prefix: %s", file.Name.Name, line, msg)
				}
			}
			return true
		})
	}
	for line := range want {
		if !got[line] {
			t.Errorf("%s:%d: expected a finding", file, line)
		}
	}
}
