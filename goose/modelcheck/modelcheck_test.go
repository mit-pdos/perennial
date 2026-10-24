package modelcheck

import (
	"bufio"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"golang.org/x/tools/go/packages"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/util"
)

// TestCases checks that modelcheck reports exactly the lines of
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

	want := make(map[int]bool)
	file := filepath.Join("testdata", "cases", "cases.go")
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
	for _, finding := range CheckPackage(pkg, declfilter.New(declfilter.FilterConfig{})) {
		got[finding.Pos.Line] = true
		if !want[finding.Pos.Line] {
			t.Errorf("unexpected finding: %v", finding)
		}
	}
	for line := range want {
		if !got[line] {
			t.Errorf("%s:%d: expected a finding", file, line)
		}
	}
}

// TestFilter checks that a declaration goose does not translate is not
// checked.
func TestFilter(t *testing.T) {
	pkgs, err := packages.Load(util.NewPackageConfig(".", false), "./testdata/cases")
	if err != nil {
		t.Fatal(err)
	}
	df := declfilter.New(declfilter.FilterConfig{ToTranslate: []string{"notReported"}})
	if fs := CheckPackage(pkgs[0], df); len(fs) != 0 {
		t.Errorf("findings in untranslated declarations: %v", fs)
	}
}
