// declfilter defines the configuration (using toml) for how Go is translated to
// GooseLang.
//
// See [FilterConfig] for the format of the toml file itself.
package declfilter

import (
	"bytes"
	"fmt"
	"path/filepath"
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
	// The package's Go model overlay, if any: see [ModelConfig].
	Model *ModelConfig `toml:"model"`
}

// A ModelConfig is the [model] table of a package's config: Go model files
// that are compiled and translated as part of the package (util.BuildModels).
//
//	[model]
//	dir = "goose/model/overlay/internal/sync"
//	replaces = ["Mutex.Lock", "Mutex.TryLock", "Mutex.Unlock"]
//
// The model files are the non-test .go files of dir, a directory relative to
// the repository root, in the package's own package clause. Each name in
// Replaces is a declaration of the real package (a function `f`, a method
// `T.m`, a type `T`, a package variable `X`, or the N-th init function
// `init.N`) that the model declares under the same name: the real one is
// deleted and the model's is put in its place. Replaces = ["*"] replaces
// every real file (a whole-package model, which may also add a
// standard-library package that does not exist); Replaces = [] only adds.
// Every other declaration of the model is an addition.
//
// The config's translate, trusted and skip govern the model's declarations
// as they govern the real package's: a model declaration translate includes
// is translated; one it excludes is a primitive stub if trusted lists it
// (its Go body is for gc builds only) and is otherwise translated
// names-only (axiomatized: a name, and for a type no definition; no body,
// no FuncUnfold). A whole-package model declares the real package's whole
// API so that its callers type-check, and translate excludes the
// declarations it does not model. translate includes every replaced name
// (a replaced declaration is the model's Go, translated), and each of its
// entries matches some declaration of the overlaid package
// (util.BuildModels).
type ModelConfig struct {
	// The directory of the model files, relative to the repository root.
	Dir string `toml:"dir"`
	// The real declarations the model replaces (required; may be empty).
	Replaces []string `toml:"replaces"`
	// Patterns (as in translate) of the methods the model may add to the
	// real package's types, which change their method sets: `T.m` or
	// `*.PbModel*`.
	AddedMethods []string `toml:"added_methods"`
	// Assembly files of the real package (base names, as built for
	// linux/amd64) that the overlay blanks, so that the model's Go bodies of
	// replaced bodyless functions are the definitions instead of the
	// assembly. The builder refuses a file unless every symbol it defines
	// (TEXT or GLOBL) is a replaced bodyless function of the package or a
	// file-local symbol (`name<>`) and it includes only the toolchain's
	// headers, and refuses a replaced function whose
	// assembly definition is in a file this list does not name.
	BlankAsm []string `toml:"blank_asm"`
}

// WholePackage says whether the model replaces every real file.
func (m *ModelConfig) WholePackage() bool {
	return len(m.Replaces) == 1 && m.Replaces[0] == "*"
}

// CheckModel returns the errors of the config's [model] table that the
// config alone shows: no dir, no replaces (an empty list must be written),
// an empty, pattern or repeated replaces entry, "*" together with names, a
// replaced name that is also an exact trusted entry or a skip name, or that
// translate does not include, an added_methods entry that is not `T.m`, and
// an exact trusted entry that translate includes (translate takes
// precedence, so the trusted model would be unused). The errors that need
// the packages are util.BuildModels'.
func (c FilterConfig) CheckModel() []error {
	m := c.Model
	if m == nil {
		return nil
	}
	var errs []error
	if strings.TrimSpace(m.Dir) == "" {
		errs = append(errs, fmt.Errorf("[model] has no dir"))
	}
	if m.Replaces == nil {
		errs = append(errs, fmt.Errorf(`[model] has no replaces: list the replaced declarations `+
			`(replaces = [] for a model that only adds, ["*"] for a whole-package model)`))
	}
	seen := make(map[string]bool)
	skipped := make(map[string]bool)
	for _, e := range c.Skip {
		for _, n := range e.Names {
			skipped[n] = true
		}
	}
	for _, n := range m.Replaces {
		switch {
		case n == "*":
			if len(m.Replaces) != 1 {
				errs = append(errs, fmt.Errorf(`[model] replaces "*" (a whole-package model) together with names`))
			}
		case strings.TrimSpace(n) == "":
			errs = append(errs, fmt.Errorf("[model] replaces an empty name"))
		case isGlob(n):
			errs = append(errs, fmt.Errorf("[model] replaces %q: a pattern; "+
				`replaced names are exact (or a lone "*")`, n))
		case seen[n]:
			errs = append(errs, fmt.Errorf("[model] replaces %q twice", n))
		case slices.Contains(c.Trusted, n):
			errs = append(errs, fmt.Errorf("[model] replaces %q, which is also listed in trusted", n))
		case skipped[n]:
			errs = append(errs, fmt.Errorf("[model] replaces %q, which is also a skip name", n))
		case !MatchesAny(c.translatePatterns(), n):
			errs = append(errs, fmt.Errorf("[model] replaces %q, which translate does not include "+
				"(a replaced declaration is the model's Go, translated)", n))
		}
		seen[n] = true
	}
	for _, n := range c.Trusted {
		if !isGlob(n) && MatchesAny(c.translatePatterns(), n) {
			errs = append(errs, fmt.Errorf("trusted %q, which translate includes "+
				"(translate takes precedence: exclude it with \"!%s\")", n, n))
		}
	}
	for _, p := range m.AddedMethods {
		if t, f, ok := strings.Cut(p, "."); !ok || t == "" || f == "" || strings.Contains(f, ".") {
			errs = append(errs, fmt.Errorf("[model] added_methods %q: not of the form T.m", p))
		}
	}
	seenAsm := make(map[string]bool)
	for _, f := range m.BlankAsm {
		switch {
		case m.WholePackage():
			errs = append(errs, fmt.Errorf(`[model] blank_asm %q with replaces = ["*"]: a whole-package model does not blank assembly`, f))
		case !strings.HasSuffix(f, ".s") || strings.ContainsAny(f, `/\`):
			errs = append(errs, fmt.Errorf("[model] blank_asm %q: not the base name of an assembly (.s) file", f))
		case seenAsm[f]:
			errs = append(errs, fmt.Errorf("[model] blank_asm %q twice", f))
		}
		seenAsm[f] = true
	}
	return errs
}

// translatePatterns is translate with its default: "*" when empty.
func (c FilterConfig) translatePatterns() []string {
	if len(c.ToTranslate) == 0 {
		return []string{"*"}
	}
	return c.ToTranslate
}

// MatchesAny says whether name is in the set the patterns describe (the
// syntax of translate: globs, and "!p" removes).
func MatchesAny(patterns []string, name string) bool {
	return newStringSet(patterns).contains(name)
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
// variable). A blank variable (`var _ = ...`) has no identifier: it is named
// by its position, "_@file.go:L" (BlankName; D4), each with its own entry
// and reason. In a package that skips a blank variable, every blank variable
// must be listed: a blank that a Go upgrade adds, or one that moves, fails
// the translation until its entry is reviewed.
type SkipEntry struct {
	// Exact identifiers of package-level variables (D2: no globs, no "!"),
	// or "_@file.go:L" for a blank variable.
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

// BlankName is the skip name of the blank package variable declared at line
// line of file (the base name of a Go file of the package): "_@file.go:L"
// (D4: a blank variable has no identifier; its position is what review saw).
// Two blank variables on one line share the name.
func BlankName(file string, line int) string {
	return fmt.Sprintf("_@%s:%d", filepath.Base(file), line)
}

var blankNameRx = regexp.MustCompile(`^_@[^/:@]+\.go:[1-9][0-9]*$`)

// IsBlankName says whether a skip name names a blank variable (BlankName).
func IsBlankName(name string) bool {
	return strings.HasPrefix(name, "_@")
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
			case n == "_":
				errs = append(errs, fmt.Errorf(`skip name "_": list each blank variable `+
					`by its position, "_@file.go:L", with its own reason`))
			case IsBlankName(n) && !blankNameRx.MatchString(n):
				errs = append(errs, fmt.Errorf(`skip name %q: a blank variable is named `+
					`"_@file.go:L" (the base name of its Go file and its line)`, n))
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
	toTranslate := c.translatePatterns()

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

// ParseConfig parses a config. A key of the [model] table that ModelConfig
// does not have is an error (a model's config is checked, not ignored).
func ParseConfig(raw []byte) (c FilterConfig, err error) {
	if err = toml.Unmarshal(raw, &c); err != nil || c.Model == nil {
		return
	}
	var doc struct {
		Model map[string]any `toml:"model"`
	}
	if err = toml.Unmarshal(raw, &doc); err != nil {
		return
	}
	model, err := toml.Marshal(doc.Model)
	if err != nil {
		return
	}
	d := toml.NewDecoder(bytes.NewReader(model))
	d.DisallowUnknownFields()
	var m ModelConfig
	if err = d.Decode(&m); err != nil {
		err = fmt.Errorf("[model]: %v", err)
	}
	return
}

func Load(raw []byte) DeclFilter {
	c, err := ParseConfig(raw)
	if err != nil {
		panic(fmt.Sprintf("could not parse config: %s", err))
	}
	return New(c)
}
