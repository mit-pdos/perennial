// declfilter defines the configuration (using toml) for how Go is translated to
// GooseLang.
//
// See [FilterConfig] for the format of the toml file itself.
package declfilter

import (
	"fmt"
	"regexp"
	"slices"
	"strings"

	"github.com/pelletier/go-toml/v2"
)

// FilterConfig defines the format of the toml files.
//
// Fields that configure sets (e.g., translate) are lists of patterns, which are
// interpreted left to right to build a set of matching strings, starting with the empty set. Literal
// patterns like "foo" match themselves, "!p" removes anything matching p from
// the set, and the wildcard "*" within a pattern matches any sequence of
// characters.
type FilterConfig struct {
	// Declarations to translate. Defaults to "*" (all).
	ToTranslate []string `toml:"translate"`
	// Imports to keep. Defaults to "*" (all).
	Imports []string `toml:"imports"`
	// Declarations that have trusted models, which the translation will
	// reference. Defaults to the empty set.
	Trusted []string `toml:"trusted"`
	// Translate for bootstrapping by importing a subset of golang.
	Bootstrap Bootstrap `toml:"bootstrap"`
	// Set to true to emit Admitted proofs.
	TrustProofGen bool `toml:"trust_proofgen"`
	// Set to true to also translate every type declaration that would
	// otherwise be axiomatized, as long as its definition only refers to
	// imported packages and uses supported constructs (see
	// util.ExtendFilter). Function and method bodies are not affected.
	TranslateTypes bool `toml:"translate_types"`
	// With translate_types, keep struct types axiomatized (their generated
	// proofs are by far the most expensive part of translating types).
	TranslateTypesExceptStructs bool `toml:"translate_types_except_structs"`
	// Package variables that are not translated at all: see [SkipEntry].
	Skip []SkipEntry `toml:"skip"`
}

// A SkipEntry lists package variables of the package that goose does not
// translate, with the reason why that is sound:
//
//	[[skip]]
//	names  = ["ErrFoo", "ErrBar"]
//	reason = "errors.New of a constant: allocates; cannot panic; no effect beyond the variable"
//
// (or inline, skip = [{names = [...], reason = "..."}]). A skipped variable
// gets no Lean name, no allocation and no step in the package's initialize',
// so a reference to it from translated code is a goose error, and one from
// hand-written Lean (another package's TrustedCode) fails to elaborate: that
// verified code never touches the variable holds by construction. What is
// trusted is the reason: that not running the variable's Go initializer is
// unobservable (it terminates, cannot panic, and has no effect beyond the
// variable). The name "_" stands for every blank `var _ = ...` of the
// package.
type SkipEntry struct {
	// Exact identifiers of package-level variables (D2: no globs, no "!").
	Names []string `toml:"names"`
	// Why skipping the initializers is unobservable; required.
	Reason string `toml:"reason"`
}

type Bootstrap struct {
	// Set to true to enable bootstrapping.
	Enabled bool `toml:"enabled"`
	// Lean modules (typically from Perennial.Golang.Defn) imported in addition
	// to Perennial.Golang.Defn.Pre.
	Prelude []string `toml:"prelude"`
}

type setOpType int

const (
	setUnion setOpType = iota
	setSubtract
)

type setOp struct {
	t setOpType
	r *regexp.Regexp
}

// A string set described by a sequence of glob patterns. The set is built up by
// starting from the empty set and then applying each operation left to right.
type stringSet []setOp

func (ss stringSet) contains(s string) bool {
	b := false
	for _, op := range ss {
		if op.r.MatchString(s) {
			switch op.t {
			case setUnion:
				b = true
			case setSubtract:
				b = false
			}
		}
	}
	return b
}

func newOp(pat string) setOp {
	var s setOp
	pattern, negated := strings.CutPrefix(pat, "!")
	if negated {
		s.t = setSubtract
	} else {
		s.t = setUnion
	}

	patternParts := strings.Split(pattern, "*")
	for i := range patternParts {
		patternParts[i] = regexp.QuoteMeta(patternParts[i])
	}
	var err error
	s.r, err = regexp.Compile("^" + strings.Join(patternParts, ".*") + "$")
	if err != nil {
		panic(err)
	}
	return s
}

func sliceMap[Slice ~[]A, A any, B any](s Slice, f func(A) B) []B {
	result := make([]B, len(s))
	for i, v := range s {
		result[i] = f(v)
	}
	return result
}

func newStringSet(s []string) stringSet {
	return sliceMap(s, newOp)
}

type declFilter struct {
	imports       stringSet
	trusted       stringSet
	toTranslate   stringSet
	trustProofGen bool
	// skipped variable -> reason
	skip map[string]string
}

type Action int

const (
	Translate Action = iota
	Axiomatize
	Trust
	// Skip: a package variable that is not translated at all (see SkipEntry).
	Skip
)

// DeclFilter determines how to treat each declaration in a Go package.
type DeclFilter interface {
	GetAction(string) Action
	ShouldImport(string) bool
	HasTrusted() bool
	TrustProofGen() bool
	// SkipReason returns the reason of a skipped name, and whether it is
	// skipped.
	SkipReason(string) (string, bool)
}

// GetAction returns how a declaration is treated. The precedence is skip >
// translate > trusted > axiomatize (D3: a skip entry overrides a translate
// glob, so `translate = ["*"]` needs no "!X"; an exact literal in translate
// or trusted is a config error, see CheckSkip).
func (df *declFilter) GetAction(name string) Action {
	if _, ok := df.skip[name]; ok {
		return Skip
	}
	switch {
	case df.toTranslate.contains(name):
		return Translate
	case df.trusted.contains(name):
		return Trust
	default:
		return Axiomatize
	}
}

func (df *declFilter) ShouldImport(i string) bool {
	return df.imports.contains(i)
}

func (df *declFilter) HasTrusted() bool {
	return len(df.trusted) > 0
}

func (df *declFilter) TrustProofGen() bool {
	return df.trustProofGen
}

func (df *declFilter) SkipReason(name string) (string, bool) {
	r, ok := df.skip[name]
	return r, ok
}

// isGlob says whether a name in a skip entry is a pattern rather than an
// identifier (D2: skip names are exact, so that a variable a Go upgrade adds
// is never skipped silently).
func isGlob(name string) bool {
	return strings.ContainsAny(name, "*!")
}

// CheckSkip returns the errors of the config's skip entries that the config
// alone shows: an entry without names or without a reason, a glob, a name in
// two entries (or twice in one), and a name that is an exact literal in
// translate or trusted (D3). The errors that need the package (a name that
// is not one of its package-level variables, a multi-name initializer only
// partly skipped) are goose's (translatePackage).
func (c FilterConfig) CheckSkip() []error {
	var errs []error
	seen := make(map[string]bool)
	for i, e := range c.Skip {
		if len(e.Names) == 0 {
			errs = append(errs, fmt.Errorf("skip entry %d has no names", i+1))
		}
		if strings.TrimSpace(e.Reason) == "" {
			errs = append(errs, fmt.Errorf("skip entry %d (%s) has no reason: "+
				"say why not running the initializers is unobservable",
				i+1, strings.Join(e.Names, ", ")))
		}
		for _, n := range e.Names {
			switch {
			case n == "":
				errs = append(errs, fmt.Errorf("skip entry %d has an empty name", i+1))
			case isGlob(n):
				errs = append(errs, fmt.Errorf("skip name %q is a pattern: "+
					"skip names are exact identifiers", n))
			case seen[n]:
				errs = append(errs, fmt.Errorf("skip name %q is listed twice", n))
			case slices.Contains(c.ToTranslate, n):
				errs = append(errs, fmt.Errorf("skip name %q is also listed in translate", n))
			case slices.Contains(c.Trusted, n):
				errs = append(errs, fmt.Errorf("skip name %q is also listed in trusted", n))
			}
			seen[n] = true
		}
	}
	return errs
}

func New(c FilterConfig) DeclFilter {
	toTranslate := c.ToTranslate
	if len(toTranslate) == 0 {
		toTranslate = []string{"*"}
	}

	imports := c.Imports
	if len(imports) == 0 {
		imports = []string{"*"}
	}

	var df declFilter
	df.imports = newStringSet(imports)
	df.toTranslate = newStringSet(toTranslate)
	df.trusted = newStringSet(c.Trusted)
	df.trustProofGen = c.TrustProofGen
	df.skip = make(map[string]string)
	for _, e := range c.Skip {
		for _, n := range e.Names {
			if _, ok := df.skip[n]; !ok {
				df.skip[n] = e.Reason
			}
		}
	}
	return &df
}

// withTranslated overrides a filter to translate the given names.
type withTranslated struct {
	DeclFilter
	names map[string]bool
}

func (df withTranslated) GetAction(name string) Action {
	if df.names[name] && df.DeclFilter.GetAction(name) != Skip {
		return Translate
	}
	return df.DeclFilter.GetAction(name)
}

// WithTranslated returns df, except that the given names are translated.
func WithTranslated(df DeclFilter, names map[string]bool) DeclFilter {
	if len(names) == 0 {
		return df
	}
	return withTranslated{DeclFilter: df, names: names}
}

var AxiomatizeConfig FilterConfig = FilterConfig{
	ToTranslate: []string{"!*"},
	Imports:     []string{"!*"},
	Trusted:     nil,
}

func ParseConfig(raw []byte) (c FilterConfig, err error) {
	err = toml.Unmarshal(raw, &c)
	return
}

func Load(raw []byte) DeclFilter {
	c, err := ParseConfig(raw)
	if err != nil {
		panic(fmt.Sprintf("could not parse config: %s", err))
	}
	return New(c)
}
