// Command skiplint runs the best-effort lint of goose's skip entries
// (package skiplint) over the given packages, with their goose configs: it
// prints a warning for each skipped initializer that stores to a package
// variable or takes the address of one. It is separate from the translator
// (goose does not run it); etc/update-goose-new.py runs it after translating.
// Warnings do not fail it: it exits 0, or 2 if a package cannot be loaded or
// its config read.
package main

import (
	"flag"
	"fmt"
	"os"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/skiplint"
	"github.com/mit-pdos/perennial/goose/util"
)

func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: skiplint [options] <go package patterns>")
		flag.PrintDefaults()
	}
	var modDir string
	flag.StringVar(&modDir, "dir", ".", "directory containing necessary go.mod")
	var configDir string
	flag.StringVar(&configDir, "configdir", ".", "directory containing Goose config files")
	var load util.LoadFlags
	load.Register(flag.CommandLine, "")
	flag.Parse()

	pkgs, _, err := util.LoadPackages(modDir, configDir, false, load.Options(), flag.Args()...)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	status := 0
	for _, pkg := range pkgs {
		config, err := util.ReadConfig(configDir, pkg.PkgPath)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			status = 2
			continue
		}
		if len(config.Skip) == 0 {
			continue
		}
		if len(pkg.Errors) > 0 {
			for _, e := range pkg.Errors {
				fmt.Fprintln(os.Stderr, e)
			}
			status = 2
			continue
		}
		for _, w := range skiplint.Check(pkg, declfilter.New(config)) {
			fmt.Printf("skiplint: warning: %s: %s\n", pkg.PkgPath, w)
		}
	}
	os.Exit(status)
}
