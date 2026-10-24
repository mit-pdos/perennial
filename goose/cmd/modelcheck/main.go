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
	"os"
	"strings"

	"github.com/pkg/errors"

	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/modelcheck"
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
	flag.Parse()

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
