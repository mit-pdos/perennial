package main

import (
	"flag"
	"fmt"
	"os"
	"path"

	"github.com/fatih/color"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/proofsetup"
	"github.com/mit-pdos/perennial/goose/util"
	"golang.org/x/tools/go/packages"
)

func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: proof-setup [options] <package patterns>")

		flag.PrintDefaults()
	}

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	var outRootDir string
	flag.StringVar(&outRootDir, "out", ".",
		"output directory")

	var verbose bool
	flag.BoolVar(&verbose, "verbose", false, "verbosity level")

	flag.Parse()
	pkgPatterns := flag.Args()

	pkgs, err := packages.Load(util.NewPackageConfig(modDir, true), pkgPatterns...)
	if err != nil {
		panic(err)
	} else if len(pkgs) == 0 {
		panic("patterns matched no packages")
	}

	blue := color.New(color.FgBlue).SprintfFunc()
	red := color.New(color.FgRed).SprintFunc()

	for _, pkg := range pkgs {
		pf := proofsetup.New(pkg, verbose)
		fmt.Printf("%s:\n", blue(pf.ProofPath))
		w := pf.SkeletonFile()

		filePath := path.Join(outRootDir, glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath))

		outDir := path.Dir(filePath)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}

		outFile := filePath + ".v"
		_, err = os.Stat(outFile)
		if err == nil {
			pf.UpdateFile(outFile, verbose)
		} else {
			if verbose {
				fmt.Printf("writing new file\n")
			}
			err = os.WriteFile(outFile, []byte(w), 0666)

			if err != nil {
				fmt.Fprintln(os.Stderr, err.Error())
				fmt.Fprintln(os.Stderr, red("could not write output"))
				os.Exit(1)
			}
		}
		if verbose {
			fmt.Println()
		}
	}
}
