package main

import (
	"bytes"
	"flag"
	"fmt"
	"os"
	"path"

	"github.com/fatih/color"

	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/util"
)

func coqFileContents(f glang.File) []byte {
	var b bytes.Buffer
	f.Write(&b)
	return b.Bytes()
}

func translate(pkgPatterns []string, outRootDir string, modDir string,
	ignoreErrors bool) {
	red := color.New(color.FgRed).SprintFunc()
	fs, errs, patternError := goose.TranslatePackages(outRootDir, modDir, pkgPatterns...)
	if patternError != nil {
		fmt.Fprintln(os.Stderr, red(patternError.Error()))
		os.Exit(1)
	}

	someError := false
	for i, f := range fs {
		err := errs[i]
		if err != nil {
			fmt.Fprintln(os.Stderr, red(err.Error()))
			someError = true
			if !ignoreErrors {
				continue
			}
		}
		outFile := path.Join(outRootDir, glang.ImportToPath(f.PkgPath))
		outDir := path.Dir(outFile)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}
		err = util.WriteFileIfChanged(outFile, coqFileContents(f), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
	}
	if someError && !ignoreErrors {
		os.Exit(1)
	}
}

// noinspection GoUnhandledErrorResult
func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: goose [options] <path to go package>")

		flag.PrintDefaults()
	}

	var outRootDir string
	flag.StringVar(&outRootDir, "out", ".",
		"root directory for output (default is current directory)")

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	var ignoreErrors bool
	flag.BoolVar(&ignoreErrors, "ignore-errors", false,
		"output partial translation even if there are errors")

	flag.Parse()

	translate(flag.Args(), outRootDir, modDir, ignoreErrors)
}
