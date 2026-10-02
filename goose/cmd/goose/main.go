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
	if glang.Lean {
		f.WriteLean(&b)
	} else {
		f.Write(&b)
	}
	return b.Bytes()
}

func translate(pkgPatterns []string, outRootDir string, configDir string, modDir string,
	ignoreErrors bool) {
	red := color.New(color.FgRed).SprintFunc()
	fs, errs, patternError := goose.TranslatePackages(configDir, modDir, pkgPatterns...)
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
		if glang.Lean {
			outFile = path.Join(outRootDir, glang.ImportToLeanPath(f.PkgPath))
		}
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

	var configDir string
	flag.StringVar(&configDir, "configdir", "",
		"directory containing Goose config files (default is the output directory)")

	flag.BoolVar(&glang.Lean, "lean", false,
		"emit Lean 4 (Perennial/Code) instead of Rocq")

	flag.Parse()
	if configDir == "" {
		configDir = outRootDir
	}

	translate(flag.Args(), outRootDir, configDir, modDir, ignoreErrors)
}
