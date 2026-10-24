// Command modelcheck reports the Go code in the given packages that goose's
// semantics is known to model incorrectly (package modelcheck). It checks the
// declarations goose would translate, under the same Goose configuration, and
// exits 1 if it finds any. goose runs the same check before it emits a
// translation.
package main

import (
	"flag"
	"fmt"
	"os"

	"golang.org/x/tools/go/packages"

	"github.com/mit-pdos/perennial/goose/declfilter"
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
	flag.StringVar(&configDir, "configdir", "",
		"directory containing Goose config files (default: check every declaration)")
	flag.Parse()

	pkgs, err := packages.Load(util.NewPackageConfig(modDir, false), flag.Args()...)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(2)
	}
	if len(pkgs) == 0 {
		fmt.Fprintln(os.Stderr, "patterns matched no packages")
		os.Exit(2)
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
		var config declfilter.FilterConfig
		if configDir != "" {
			config, err = util.ReadConfig(configDir, pkg.PkgPath)
			if err != nil {
				fmt.Fprintln(os.Stderr, err)
				status = 2
				continue
			}
		}
		df := util.ExtendFilter(pkg, config, declfilter.New(config))
		for _, f := range modelcheck.CheckPackage(pkg, df) {
			fmt.Println(f)
			if status == 0 {
				status = 1
			}
		}
	}
	os.Exit(status)
}
