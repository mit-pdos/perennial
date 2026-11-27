package declfilter

import (
	"strings"
	"testing"
)

func TestDeclFilterEmpty(t *testing.T) {
	var c FilterConfig
	df := New(c)
	if df.GetAction("something") != Translate {
		t.Errorf("Empty FilterConfig should translate everything")
	}

	if df.HasTrusted() != false {
		t.Errorf("Empty FilterConfig should have nothing trusted")
	}

	if df.ShouldImport("some_package") == false {
		t.Errorf("Empty FilterConfig should import everything")
	}
}

func TestDeclFilterNegativeImport(t *testing.T) {
	c := FilterConfig{
		Imports:     []string{"*", "!NotThisOne"},
		Trusted:     []string{},
		ToTranslate: []string{},
	}

	df := New(c)
	if df.ShouldImport("NotThisOne") {
		t.Errorf("FilterConfig should not contain a negated match")
	}

	if !df.ShouldImport("ThisOneIsOk") {
		t.Errorf("FilterConfig should contain unnegated matches")
	}

	if df.GetAction("something") != Translate {
		t.Errorf("FilterConfig should translate everything if unspecified")
	}
}

func mustParse(t *testing.T, s string) FilterConfig {
	t.Helper()
	c, err := ParseConfig([]byte(s))
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	return c
}

func TestSkipTable(t *testing.T) {
	c := mustParse(t, `
translate = ["*"]
[[skip]]
names = ["A", "B"]
reason = "constants"
[[skip]]
names = ["_@a.go:3"]
reason = "an interface check"
`)
	if errs := c.CheckSkip(); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
	df := New(c)
	for _, n := range []string{"A", "B", "_@a.go:3"} {
		if df.GetAction(n) != Skip {
			t.Errorf("%s should be skipped (skip overrides translate = [\"*\"])", n)
		}
	}
	if r, ok := df.SkipReason("B"); !ok || r != "constants" {
		t.Errorf("SkipReason(B) = %q, %v", r, ok)
	}
	if df.GetAction("C") != Translate {
		t.Errorf("C should be translated")
	}
	// a blank variable at another position is not skipped
	if df.GetAction("_@a.go:4") != Translate || df.GetAction("_") != Translate {
		t.Errorf("only the blank at a.go:3 should be skipped")
	}
	if BlankName("/src/pkg/a.go", 3) != "_@a.go:3" {
		t.Errorf("BlankName = %q", BlankName("/src/pkg/a.go", 3))
	}
	if _, ok := df.SkipReason("C"); ok {
		t.Errorf("C is not skipped")
	}
}

func TestSkipInline(t *testing.T) {
	c := mustParse(t, `skip = [{names = ["X"], reason = "r"}]`)
	if errs := c.CheckSkip(); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
	df := New(c)
	if df.GetAction("X") != Skip {
		t.Errorf("X should be skipped")
	}
	// skip also overrides a type translated by translate_types
	if WithTranslated(df, map[string]bool{"X": true}).GetAction("X") != Skip {
		t.Errorf("X should stay skipped")
	}
}

func TestSkipErrors(t *testing.T) {
	for _, tc := range []struct{ cfg, want string }{
		{`[[skip]]
names = ["X"]
reason = "  "`, "has no reason"},
		{`[[skip]]
reason = "r"`, "has no names"},
		{`[[skip]]
names = ["Err*"]
reason = "r"`, "is a pattern"},
		{`[[skip]]
names = ["!X"]
reason = "r"`, "is a pattern"},
		{`[[skip]]
names = ["X"]
reason = "r"
[[skip]]
names = ["X"]
reason = "s"`, "listed twice"},
		{`translate = ["*", "X"]
[[skip]]
names = ["X"]
reason = "r"`, "also listed in translate"},
		{`translate = ["!X"]
trusted = ["X"]
[[skip]]
names = ["X"]
reason = "r"`, "also listed in trusted"},
		{`[[skip]]
names = ["_"]
reason = "r"`, "by its position"},
		{`[[skip]]
names = ["_@a.go"]
reason = "r"`, `is named "_@file.go:L"`},
		{`[[skip]]
names = ["_@dir/a.go:3"]
reason = "r"`, `is named "_@file.go:L"`},
	} {
		errs := mustParse(t, tc.cfg).CheckSkip()
		if len(errs) != 1 || !strings.Contains(errs[0].Error(), tc.want) {
			t.Errorf("config\n%s\nerrors %v, want one containing %q", tc.cfg, errs, tc.want)
		}
	}
}

func TestModelTranslate(t *testing.T) {
	c := mustParse(t, `
translate = ["*", "!Stub", "!Value.Call*", "!Unmodelled"]
trusted = ["Stub"]
[model]
dir = "m"
replaces = ["*"]
`)
	if errs := c.CheckModel(); len(errs) != 0 {
		t.Fatalf("unexpected errors: %v", errs)
	}
	// translate governs model declarations as real ones: excluded and not
	// trusted is names-only (axiomatized)
	df := New(c)
	for name, want := range map[string]Action{"Unmodelled": Axiomatize, "Value.CallSlice": Axiomatize,
		"Stub": Trust, "Value.Kind": Translate} {
		if got := df.GetAction(name); got != want {
			t.Errorf("GetAction(%q) = %v, want %v", name, got, want)
		}
	}
}

func TestModelTranslateErrors(t *testing.T) {
	for _, tc := range []struct{ cfg, want string }{
		{`translate = ["!*"]
[model]
dir = "m"
replaces = ["F"]`, `replaces "F", which translate does not include`},
		{`translate = ["*", "!T.*"]
[model]
dir = "m"
replaces = ["T.m"]`, `replaces "T.m", which translate does not include`},
		{`trusted = ["Stub"]
[model]
dir = "m"
replaces = ["*"]`, `trusted "Stub", which translate includes`},
		{`translate = ["St*"]
trusted = ["Stub"]
[model]
dir = "m"
replaces = []`, `trusted "Stub", which translate includes`},
	} {
		errs := mustParse(t, tc.cfg).CheckModel()
		if len(errs) != 1 || !strings.Contains(errs[0].Error(), tc.want) {
			t.Errorf("config\n%s\nerrors %v, want one containing %q", tc.cfg, errs, tc.want)
		}
	}
}

func TestModelUnknownKey(t *testing.T) {
	_, err := ParseConfig([]byte("translate = [\"*\"]\n[model]\ndir = \"m\"\nreplaces = [\"*\"]\nnames_only = [\"F\"]\n"))
	if err == nil || !strings.Contains(err.Error(), "[model]") {
		t.Errorf("a [model] key ModelConfig does not have: error %v, want one", err)
	}
	if _, err := ParseConfig([]byte("translate = [\"*\"]\n[model]\ndir = \"m\"\nreplaces = [\"*\"]\nadded_methods = [\"T.m\"]\nblank_asm = []\n")); err != nil {
		t.Errorf("unexpected error %v", err)
	}
}
