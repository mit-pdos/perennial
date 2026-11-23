package goose

// Skipped package variables (the `skip` entries of a package's goose config,
// declfilter.SkipEntry).
//
// A skipped variable is not translated at all: goose emits no Lean name for
// it, no X.init, no GlobalAlloc and no step in initialize'. What remains
// trusted is each entry's reason: that not running the variable's Go
// initializer is unobservable. The design points (D1-D11 of the plan on
// etcd-grove#19) are marked where they are decided, so that each can be
// revised on its own.

import (
	"crypto/sha256"
	"fmt"
	"go/ast"
	"go/printer"
	"go/token"
	"go/types"
	"path/filepath"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/util"
	"golang.org/x/tools/go/packages"
)

// configError is an error in a package's goose config (not at a position in
// the Go source).
func configError(pkgPath string, err error) *ConversionError {
	return &ConversionError{
		Category:    "unsupported",
		Message:     fmt.Sprintf("goose config of %s: %v", pkgPath, err),
		GooseCaller: getCaller(1),
	}
}

// checkSkipConfig returns the errors of the package's skip entries: those the
// config alone shows (declfilter.FilterConfig.CheckSkip) and those that need
// the package: a name that is not one of its package-level variables (a stale
// entry, e.g. after a Go upgrade), a blank-variable name "_@file.go:L" with
// no blank variable there, a blank variable left unlisted in a package that
// skips blank variables (D4: a blank variable that a Go upgrade adds or moves
// fails the translation until its entry is reviewed), and an initializer of
// several variables that is only partly skipped (D5: the initializer, one Go
// evaluation, is the unit).
func (ctx *Ctx) checkSkipConfig(pkg *packages.Package, config declfilter.FilterConfig) (errs []error) {
	for _, err := range config.CheckSkip() {
		errs = append(errs, configError(pkg.PkgPath, err))
	}
	if len(errs) > 0 {
		return
	}
	// the blank package variables, by skip name, in source order
	var blanks []string
	blankSpec := make(map[string]*ast.ValueSpec)
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			if d, ok := d.(*ast.GenDecl); ok && d.Tok == token.VAR {
				for _, s := range d.Specs {
					for _, n := range s.(*ast.ValueSpec).Names {
						if n.Name == "_" {
							b := ctx.blankName(n.Pos())
							if _, ok := blankSpec[b]; !ok {
								blanks = append(blanks, b)
								blankSpec[b] = s.(*ast.ValueSpec)
							}
						}
					}
				}
			}
		}
	}
	skipsBlank := false
	for _, e := range config.Skip {
		for _, n := range e.Names {
			if declfilter.IsBlankName(n) {
				skipsBlank = true
				if _, ok := blankSpec[n]; !ok {
					errs = append(errs, configError(pkg.PkgPath,
						fmt.Errorf("skip name %q: the package has no blank package variable there "+
							"(moved or removed?): review the package's blank variables and list "+
							"each by its current position", n)))
				}
				continue
			}
			if _, ok := pkg.Types.Scope().Lookup(n).(*types.Var); !ok {
				errs = append(errs, configError(pkg.PkgPath,
					fmt.Errorf("skip name %q is not a package-level variable of the package", n)))
			}
		}
	}
	if skipsBlank {
		for _, b := range blanks {
			if _, ok := ctx.filter.SkipReason(b); !ok {
				errs = append(errs, configError(pkg.PkgPath,
					fmt.Errorf("the blank package variable %s (%s) is not listed in a skip entry: "+
						"the package skips blank variables, so each one is listed by its position "+
						"with its own reason; review it and add it (a new or moved blank variable "+
						"needs review)", b, declSource(ctx.fset, blankSpec[b], false))))
			}
		}
	}
	var e errorCatcher
	for _, init := range ctx.info.InitOrder {
		var skipped, kept []string
		for _, v := range init.Lhs {
			if ctx.varAction(v.Name(), v.Pos()) == declfilter.Skip {
				skipped = append(skipped, v.Name())
			} else {
				kept = append(kept, v.Name())
			}
		}
		if len(skipped) > 0 && len(kept) > 0 {
			e.do(func() {
				ctx.unsupported(init.Lhs[0],
					"the initializer of %s is only partly skipped (skipped: %s; not skipped: %s): "+
						"skip all of its variables or none",
					varNames(init.Lhs), strings.Join(skipped, ", "), strings.Join(kept, ", "))
			})
		}
	}
	for _, err := range e.errs {
		errs = append(errs, err)
	}
	ctx.skipsBlank = skipsBlank
	return
}

// blankName is the skip name of a blank package variable declared at pos
// (declfilter.BlankName).
func (ctx *Ctx) blankName(pos token.Pos) string {
	p := ctx.fset.Position(pos)
	return declfilter.BlankName(p.Filename, p.Line)
}

// varAction is how the package variable name, declared at pos, is treated: a
// blank variable is skipped by its position (D4), any other variable by its
// name.
func (ctx *Ctx) varAction(name string, pos token.Pos) declfilter.Action {
	if name == "_" {
		if _, ok := ctx.filter.SkipReason(ctx.blankName(pos)); ok {
			return declfilter.Skip
		}
	}
	return ctx.filter.GetAction(name)
}

// docEscape keeps text from closing or opening a Lean comment.
func docEscape(s string) string {
	return strings.NewReplacer("-/", "- /", "/-", "/ -").Replace(s)
}

// declSource is the Go declaration s, `var X = ...`, on one line. With short,
// a long one is cut to its first maxDeclLen characters and ends with a hash of the
// whole declaration, so that a change to a long initializer still changes
// the text.
func declSource(fset *token.FileSet, s *ast.ValueSpec, short bool) string {
	var b strings.Builder
	if err := printer.Fprint(&b, fset, s); err != nil {
		panic(err)
	}
	src := "var " + strings.Join(strings.Fields(b.String()), " ")
	if r := []rune(src); short && len(r) > maxDeclLen {
		sum := sha256.Sum256([]byte(src))
		src = fmt.Sprintf("%s … [sha256:%x]", string(r[:maxDeclLen]), sum[:8])
	}
	return src
}

const maxDeclLen = 120

func varNames(vs []*types.Var) string {
	var ns []string
	for _, v := range vs {
		ns = append(ns, v.Name())
	}
	return strings.Join(ns, ", ")
}

// A skippedVar is a skipped package variable, as listed in the translation.
type skippedVar struct {
	// pkg.X, or pkg._@file.go:L for a blank variable (D4)
	name   string
	reason string
	// the Go declaration (declSource), so that a change to the initializer
	// changes the entry
	decl string
}

// recordSkipped records the skipped variable name of the declaration s.
func (ctx *Ctx) recordSkipped(s *ast.ValueSpec, name *ast.Ident) {
	key := name.Name
	if key == "_" {
		key = ctx.blankName(name.Pos())
	}
	reason, _ := ctx.filter.SkipReason(key)
	ctx.skipped = append(ctx.skipped, skippedVar{
		name:   ctx.pkgPath + "." + key,
		reason: reason,
		decl:   declSource(ctx.fset, s, true),
	})
}

// skippedDecls is the record of the package's skipped variables,
// `skipped' : List go.SkippedVar`, with a doc comment listing them (D6: an
// informational record, unused by the semantics, from which tools that read
// the Lean environment list the skips in a result's import closure; its
// names are strings, so it gives no handle on the variables). Nothing if the
// package skips nothing.
func (ctx *Ctx) skippedDecls() []glang.Decl {
	if len(ctx.skipped) == 0 {
		return nil
	}
	var b strings.Builder
	b.WriteString("/-- The package variables goose does not translate (the `skip` entries of the package's\n" +
		"goose config): no Lean name, allocation or initialization step, so no translated code names\n" +
		"them. Trusted: not running each one's Go initializer is unobservable (it terminates, cannot\n" +
		"panic, and has no effect beyond the variable), for the reason given.\n\n")
	for _, v := range ctx.skipped {
		fmt.Fprintf(&b, "- `%s` (`%s`): %s\n", strings.TrimPrefix(v.name, ctx.pkgPath+"."),
			docEscape(strings.ReplaceAll(v.decl, "`", "'")), docEscape(v.reason))
	}
	b.WriteString("-/\nnoncomputable def skipped' : List go.SkippedVar := [")
	for i, v := range ctx.skipped {
		if i > 0 {
			b.WriteString(",")
		}
		fmt.Fprintf(&b, "\n  ⟨%s, %s, %s⟩", glang.LeanRawString(v.name), glang.LeanRawString(v.reason),
			glang.LeanRawString(v.decl))
	}
	b.WriteString("]")
	return []glang.Decl{glang.VerbatimDecl{Content: b.String()}}
}

// skipReason returns the reason of a skipped package variable v of this
// package or of one it imports (D7: goose reads the imported package's
// config from the config directory), and whether it is skipped.
func (ctx *Ctx) skipReason(v *types.Var) (string, bool) {
	if v.Pkg().Path() == ctx.pkgPath {
		return ctx.filter.SkipReason(v.Name())
	}
	skips, ok := ctx.depSkips[v.Pkg().Path()]
	if !ok {
		skips = make(map[string]string)
		// an unreadable config is reported by that package's translation
		if c, err := util.ReadConfig(ctx.configDir, v.Pkg().Path()); err == nil {
			for _, e := range c.Skip {
				for _, n := range e.Names {
					skips[n] = e.Reason
				}
			}
		}
		if ctx.depSkips == nil {
			ctx.depSkips = make(map[string]map[string]string)
		}
		ctx.depSkips[v.Pkg().Path()] = skips
	}
	r, ok := skips[v.Name()]
	return r, ok
}

// checkNotSkipped fails if the package variable v, referenced at n, is
// skipped: translated code may not use a skipped variable (D7). Without this
// check the Lean would not elaborate (the variable has no name); the error
// says where and why.
func (ctx *Ctx) checkNotSkipped(n ast.Node, v *types.Var) {
	reason, ok := ctx.skipReason(v)
	if !ok {
		return
	}
	name := v.Name()
	if v.Pkg().Path() != ctx.pkgPath {
		name = v.Pkg().Path() + "." + name
	}
	decl := ctx.curDecl
	if decl == "" {
		decl = "code"
	}
	pos := ctx.fset.Position(n.Pos())
	ctx.unsupported(n, "skipped variable %s (skip: %q) is referenced by translated %s at %s:%d; "+
		"translate %s or do not translate %s",
		name, reason, decl, filepath.Base(pos.Filename), pos.Line, v.Name(), decl)
}

// initAction classifies a package-variable initializer, one Go evaluation
// that may assign several variables (`var a, b = f()`), as a unit: Skip if
// all of its variables are skipped, Translate if all are translated, and
// otherwise (each is trusted or axiomatized) Axiomatize, for an initializer
// that runs the X.init of each of its variables. One initializer is never
// split: an initializer only partly skipped is refused by checkSkipConfig,
// and one whose variables are partly translated is refused here, as goose
// cannot run the translated half of one evaluation (before, goose ran the
// first non-translated variable's X.init only, dropping the others' X.init
// and the translated variables' stores: perennial#657).
func (ctx *Ctx) initAction(init *types.Initializer) declfilter.Action {
	actions := make(map[declfilter.Action][]string)
	for _, v := range init.Lhs {
		a := ctx.varAction(v.Name(), v.Pos())
		if a == declfilter.Trust {
			a = declfilter.Axiomatize
		}
		actions[a] = append(actions[a], v.Name())
	}
	if len(actions) == 1 {
		for a := range actions {
			return a
		}
	}
	if _, ok := actions[declfilter.Skip]; ok {
		// reported by checkSkipConfig
		return declfilter.Skip
	}
	ctx.unsupported(init.Lhs[0],
		"the initializer of %s is only partly translated (translated: %s; trusted or axiomatized: %s): "+
			"translate all of its variables or none",
		varNames(init.Lhs), strings.Join(actions[declfilter.Translate], ", "),
		strings.Join(actions[declfilter.Axiomatize], ", "))
	panic("unreachable")
}
