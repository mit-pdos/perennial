package goose

import (
	"fmt"
	"go/ast"
	"go/token"
	"os"
	"strings"
	"sync"

	"github.com/pkg/errors"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/order"
	"github.com/mit-pdos/perennial/goose/util"
	"golang.org/x/tools/go/packages"
)

type errorCatcher struct {
	errs []error
}

func (e *errorCatcher) do(f func()) {
	defer func() {
		if r := recover(); r != nil {
			if gooseErr, ok := r.(gooseError); ok {
				e.errs = append(e.errs, gooseErr.err)
			} else {
				// r is an error from a non-goose error, indicating a bug
				panic(r)
			}
		}
	}()
	f()
}

// Decls converts an entire package (possibly multiple files) to a list of decls
func (ctx *Ctx) files(fs []*ast.File) (preDecls []glang.Decl, sortedDecls []glang.Decl, errs []error) {
	var e errorCatcher
	// Collect imports from every file before translating declarations. The
	// names of the imports in the Assumptions class are package-wide, so we
	// need the full import set before deciding how to disambiguate packages
	// with the same Go package name.
	for _, f := range fs {
		for _, d := range f.Decls {
			if d, ok := d.(*ast.GenDecl); ok && d.Tok == token.IMPORT {
				e.do(func() { ctx.imports(d.Specs) })
			}
		}
	}
	e.do(func() { ctx.finalizeImports() })
	for _, f := range fs {
		for _, d := range f.Decls {
			e.do(func() { ctx.decl(d) })
		}
	}
	e.do(func() { ctx.finalExtraDecls() })
	return ctx.out.preHeaderDecls(), ctx.out.decls(), e.errs
}

type MultipleErrors []error

func (es MultipleErrors) Error() string {
	var errs []string
	for _, e := range es {
		errs = append(errs, e.Error())
	}
	errs = append(errs, fmt.Sprintf("%d errors", len(es)))
	return strings.Join(errs, "\n\n")
}

func pkgErrors(errors []packages.Error) error {
	var errs []error
	for _, err := range errors {
		errs = append(errs, err)
	}
	return MultipleErrors(errs)
}

// translatePackage translates an entire package to a single Lean file.
//
// If the source directory has multiple source files, these are processed in
// alphabetical order; this must be a topological sort of the definitions or the
// Lean code will be out-of-order. Sorting ensures the results are stable
// and not dependent on map or directory iteration order.
func translatePackage(pkg *packages.Package, config declfilter.FilterConfig) (glang.File, error) {
	if len(pkg.Errors) > 0 {
		return glang.File{}, errors.Errorf(
			"could not load package %v:\n%v", pkg.PkgPath,
			pkgErrors(pkg.Errors))
	}
	ctx := NewPkgCtx(pkg, util.ExtendFilter(pkg, config, declfilter.New(config)))
	f := ctx.initFile(pkg, config)
	preDecls, decls, errs := ctx.files(pkg.Syntax)

	f.PreHeaderDecls = preDecls
	f.Decls = decls
	if len(errs) != 0 {
		return f, errors.Wrap(MultipleErrors(errs),
			"conversion failed")
	}
	return f, nil
}

// initFile starts the Lean file for a package: its header (after the code
// imports) and footer.
func (ctx *Ctx) initFile(pkg *packages.Package, config declfilter.FilterConfig) (f glang.File) {
	f.PkgPath = pkg.PkgPath
	var h strings.Builder
	if config.Bootstrap.Enabled {
		h.WriteString("public import Perennial.Golang.Defn.Pre\n")
		for _, m := range config.Bootstrap.Prelude {
			h.WriteString("public import " + m + "\n")
		}
	} else {
		h.WriteString("public import Perennial.Golang.Defn\n")
	}
	if ctx.filter.HasTrusted() {
		h.WriteString("public import " + glang.LeanModule(glang.LeanRootPrefix(pkg.PkgPath)+"TrustedCode", pkg.PkgPath) + "\n")
	}
	ffi := util.GetFfi(pkg)
	if ffi != "" {
		h.WriteString("public import Perennial." + glang.LeanFfiPrelude(ffi) + "\n")
	}
	h.WriteString("\n@[expose] public section\n")
	h.WriteString("\n" + glang.LeanFileOptions)
	h.WriteString("\nnamespace Perennial\n")
	h.WriteString("noncomputable section\n\n")
	h.WriteString("namespace pkg_id\n")
	fmt.Fprintf(&h, "def %s : GoString := %s\n", glang.LeanNamespace(pkg.PkgPath), glang.LeanStringLit(pkg.PkgPath))
	h.WriteString("end pkg_id\n\n")
	ns := glang.LeanNamespace(pkg.PkgPath)
	fmt.Fprintf(&h, "namespace %s", ns)
	f.Header = h.String()
	f.Footer = fmt.Sprintf("\nend %s\n\nend\nend Perennial\n", ns)
	return
}

// loadOrdered loads the packages matching the patterns in Perennial's
// evaluation order: each file is rewritten by order.Rewrite (as
// cmd/perennial-order does when compiling) and the packages are loaded again
// from the rewritten source, held in memory.
//
// Whatever the rewriter does, goose then checks that every statement it is
// about to translate is in normal form (order.CheckFile), on which every
// evaluation order the Go spec allows agrees: so goose's translation, which
// evaluates in one fixed order, is the behaviour of the compiled code. A
// statement that is not is an error.
func loadOrdered(modDir string, patterns ...string) ([]*packages.Package, error) {
	cfg := util.NewPackageConfig(modDir, true)
	pkgs, err := packages.Load(cfg, patterns...)
	if err != nil {
		return nil, err
	}
	overlay := map[string][]byte{}
	for _, pkg := range pkgs {
		if len(pkg.Errors) > 0 || pkg.TypesInfo == nil {
			continue // reported by translatePackage
		}
		for i, f := range pkg.Syntax {
			name := pkg.CompiledGoFiles[i]
			src, err := os.ReadFile(name)
			if err != nil {
				return nil, err
			}
			out, changed, err := order.Rewrite(pkg.Fset, pkg.Types, pkg.TypesInfo, f, src)
			if err != nil {
				return nil, err
			}
			if changed {
				overlay[name] = out
			}
		}
	}
	if len(overlay) > 0 {
		cfg = util.NewPackageConfig(modDir, true)
		cfg.Overlay = overlay
		if pkgs, err = packages.Load(cfg, patterns...); err != nil {
			return nil, err
		}
	}
	for _, pkg := range pkgs {
		if pkg.TypesInfo == nil {
			continue
		}
		for _, f := range pkg.Syntax {
			for _, v := range order.CheckFile(pkg.TypesInfo, f) {
				pkg.Errors = append(pkg.Errors, packages.Error{
					Pos: pkg.Fset.Position(v.Pos).String(),
					Msg: "statement not in normal form (evaluation order): goose/order did not rewrite it",
				})
			}
		}
	}
	return pkgs, nil
}

// TranslatePackages loads packages by a list of patterns and translates them
// all, producing one file per matched package.
//
// The errs list contains errors corresponding to each package (in parallel with
// the files list). patternErr is only non-nil if the patterns themselves have
// a syntax error.
func TranslatePackages(configDir string, modDir string,
	pkgPattern ...string) (files []glang.File, errs []error, patternErr error) {
	pkgs, patternErr := loadOrdered(modDir, pkgPattern...)

	if patternErr != nil {
		return
	}
	if len(pkgs) == 0 {
		// consider matching nothing to be an error, unlike packages.Load
		return nil, nil,
			errors.New("patterns matched no packages")
	}
	files = make([]glang.File, len(pkgs))
	errs = make([]error, len(pkgs))
	var wg sync.WaitGroup
	wg.Add(len(pkgs))

	// TODO now
	for i, pkg := range pkgs {
		go func() {
			defer wg.Done()
			config, err := util.ReadConfig(configDir, pkg.PkgPath)
			if err != nil {
				errs[i] = err
				return
			}
			files[i], errs[i] = translatePackage(pkg, config)
		}()
	}
	wg.Wait()

	return
}
