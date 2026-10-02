package declfilter

import "testing"

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
