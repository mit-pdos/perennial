package goose

import (
	"fmt"
	"go/ast"
	"strings"
	"sync"

	"github.com/pkg/errors"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
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

// translatePackage translates an entire package to a single Coq file.
//
// If the source directory has multiple source files, these are processed in
// alphabetical order; this must be a topological sort of the definitions or the
// Coq code will be out-of-order. Sorting ensures the results are stable
// and not dependent on map or directory iteration order.
func translatePackage(pkg *packages.Package, config declfilter.FilterConfig) (glang.File, error) {
	if len(pkg.Errors) > 0 {
		return glang.File{}, errors.Errorf(
			"could not load package %v:\n%v", pkg.PkgPath,
			pkgErrors(pkg.Errors))
	}
	ctx := NewPkgCtx(pkg, declfilter.New(config))
	coqFile := ctx.initCoqFile(pkg, config)
	preDecls, decls, errs := ctx.files(pkg.Syntax)

	coqFile.PreHeaderDecls = preDecls
	coqFile.Decls = decls
	if len(errs) != 0 {
		return coqFile, errors.Wrap(MultipleErrors(errs),
			"conversion failed")
	}
	return coqFile, nil
}

func (ctx *Ctx) initCoqFile(pkg *packages.Package, config declfilter.FilterConfig) (f glang.File) {
	f.PkgPath = pkg.PkgPath
	if config.Bootstrap.Enabled {
		f.Header = glang.BootstrapHeader + "\n" + strings.Join(config.Bootstrap.Prelude, "\n") + "\n"
	} else {
		f.Header = glang.DefaultHeader + "\n"
	}

	if ctx.filter.HasTrusted() {
		importPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")
		f.Header += fmt.Sprintf("Require Export New.trusted_code.%s.\n", importPath) +
			fmt.Sprintf("Import %s.\n", pkg.Name)
	}

	ffi := util.GetFfi(pkg)
	if ffi != "" {
		f.Header += fmt.Sprintf("From New Require Import %s_prelude.\n", ffi)
	}

	f.Header += "Module pkg_id.\n"
	f.Header += fmt.Sprintf("Definition %s : go_string := \"%s\".\n\n", pkg.Name, pkg.PkgPath)
	f.Header += "End pkg_id.\nExport pkg_id.\n"

	f.Header += fmt.Sprintf("Module %s.", pkg.Name)

	f.Footer = fmt.Sprintf("End %s.\n", pkg.Name)
	return
}

// TranslatePackages loads packages by a list of patterns and translates them
// all, producing one file per matched package.
//
// The errs list contains errors corresponding to each package (in parallel with
// the files list). patternErr is only non-nil if the patterns themselves have
// a syntax error.
func TranslatePackages(configDir string, modDir string,
	pkgPattern ...string) (files []glang.File, errs []error, patternErr error) {
	pkgs, patternErr := packages.Load(util.NewPackageConfig(modDir, true), pkgPattern...)

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
