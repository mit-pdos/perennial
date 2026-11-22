package skiplint

import (
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/util"
	"golang.org/x/tools/go/packages"
)

func TestCheck(t *testing.T) {
	pkgs, err := packages.Load(util.NewPackageConfig("./testdata", false, nil), ".")
	if err != nil || len(pkgs) != 1 || len(pkgs[0].Errors) != 0 {
		t.Fatalf("load: %v %v", err, pkgs)
	}
	config := declfilter.FilterConfig{Skip: []declfilter.SkipEntry{
		{Names: []string{"A", "B", "C", "D"}, Reason: "test"},
	}}
	ws := Check(pkgs[0], declfilter.New(config))
	if len(ws) != 2 {
		t.Fatalf("want two warnings (A, D), got %q", ws)
	}
	for _, want := range []string{"skipped initializer of A", "stores to registry (in register", "stores to count (in bump"} {
		if !strings.Contains(ws[0], want) {
			t.Errorf("warning %q does not contain %q", ws[0], want)
		}
	}
	if want := "takes the address of tbl (in setTbl"; !strings.Contains(ws[1], want) {
		t.Errorf("warning %q does not contain %q", ws[1], want)
	}
}
