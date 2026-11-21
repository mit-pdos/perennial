package goose

import (
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/util"
	"golang.org/x/tools/go/packages"
)

func TestSkipLint(t *testing.T) {
	pkgs, err := packages.Load(util.NewPackageConfig("./testdata/skiplint", false, nil), ".")
	if err != nil || len(pkgs) != 1 || len(pkgs[0].Errors) != 0 {
		t.Fatalf("load: %v %v", err, pkgs)
	}
	config := declfilter.FilterConfig{Skip: []declfilter.SkipEntry{
		{Names: []string{"A", "B", "C"}, Reason: "test"},
	}}
	ctx := NewPkgCtx(pkgs[0], declfilter.New(config))
	ws := ctx.skipLint(pkgs[0])
	if len(ws) != 1 {
		t.Fatalf("want one warning (A), got %q", ws)
	}
	for _, want := range []string{"skipped initializer of A", "registry (in register", "count (in bump"} {
		if !strings.Contains(ws[0], want) {
			t.Errorf("warning %q does not contain %q", ws[0], want)
		}
	}
}
