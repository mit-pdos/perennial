// Command modelcheck reports the Go code in the given packages that goose's
// semantics is known to model incorrectly (package modelcheck). It runs goose's
// translation, with the same Goose configuration and the same decisions about
// what to translate, and prints only modelcheck's findings: other translation
// errors are left to goose. It exits 1 if it finds anything, and 2 if a
// package cannot be loaded.
package main

import (
	"flag"
	"fmt"
	"go/ast"
	"os"
	"strings"

	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"

	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/modelcheck"
	"github.com/mit-pdos/perennial/goose/util"
)

func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: modelcheck [options] <go package patterns>")
		flag.PrintDefaults()
	}
	var modDir string
	flag.StringVar(&modDir, "dir", ".", "directory containing necessary go.mod")
	var configDir string
	flag.StringVar(&configDir, "configdir", ".", "directory containing Goose config files")
	flag.Var(glang.LeanRootFlag{}, "lean-root", glang.LeanRootUsage)
	var all bool
	flag.BoolVar(&all, "all", false,
		"check every statement of every function body, translated or not, without running goose "+
			"(for code goose cannot translate yet; goose stops at the first error in a declaration)")
	flag.Parse()

	if all {
		os.Exit(checkAll(modDir, flag.Args()))
	}

	_, errs, patternErr := goose.TranslatePackages(configDir, modDir, flag.Args()...)
	if patternErr != nil {
		fmt.Fprintln(os.Stderr, patternErr)
		os.Exit(2)
	}
	status := 0
	for _, err := range errs {
		for _, e := range flatten(err) {
			var ce *goose.ConversionError
			switch {
			case errors.As(e, &ce) && strings.HasPrefix(ce.Message, modelcheck.Prefix):
				fmt.Printf("%v: %s\n    %s\n", ce.Position, ce.Message, ce.GoCode)
				status = max(status, 1)
			case errors.As(e, &ce):
				// another translation error: goose reports it
			default:
				fmt.Fprintln(os.Stderr, e) // e.g. a package that does not load
				status = 2
			}
		}
	}
	os.Exit(status)
}

// checkAll checks every assignment and range statement in the packages, and
// returns the exit status.
func checkAll(modDir string, patterns []string) int {
	pkgs, err := packages.Load(util.NewPackageConfig(modDir, false), patterns...)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		return 2
	}
	status := 0
	for _, pkg := range pkgs {
		if len(pkg.Errors) > 0 {
			for _, e := range pkg.Errors {
				fmt.Fprintln(os.Stderr, e)
			}
			status = 2
			continue
		}
		for _, f := range pkg.Syntax {
			ast.Inspect(f, func(n ast.Node) bool {
				var at ast.Node
				var msg string
				var bad bool
				switch s := n.(type) {
				case *ast.AssignStmt:
					at, msg, bad = modelcheck.Assign(pkg.TypesInfo, s)
				case *ast.RangeStmt:
					at, msg, bad = modelcheck.Range(pkg.TypesInfo, s)
				}
				if bad {
					fmt.Printf("%v: %s\n", pkg.Fset.Position(at.Pos()), msg)
					status = max(status, 1)
				}
				return true
			})
		}
	}
	return status
}

// flatten returns the individual errors of a package's translation error.
func flatten(err error) []error {
	if err == nil {
		return nil
	}
	var multi goose.MultipleErrors
	if errors.As(err, &multi) {
		return multi
	}
	return []error{err}
}
