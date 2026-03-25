// declfilter defines the configuration (using toml) for how Go is translated to
// GooseLang.
//
// See [FilterConfig] for the format of the toml file itself.
package declfilter

import (
	"fmt"
	"regexp"
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
}

type Bootstrap struct {
	// Set to true to enable bootstrapping.
	Enabled bool `toml:"enabled"`
	// These lines (typically imports from New.golang.defn) are joined to form
	// the new prelude.
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
}

type Action int

const (
	Translate Action = iota
	Axiomatize
	Trust
)

// DeclFilter determines how to treat each declaration in a Go package.
type DeclFilter interface {
	GetAction(string) Action
	ShouldImport(string) bool
	HasTrusted() bool
	TrustProofGen() bool
}

func (df *declFilter) GetAction(name string) Action {
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
	return &df
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
