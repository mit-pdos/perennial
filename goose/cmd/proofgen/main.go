package main

import (
	"flag"
	"fmt"

	"github.com/mit-pdos/perennial/goose/proofgen"
	"github.com/mit-pdos/perennial/goose/util"
)

func main() {
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: proofgen [options] <path to go package>")
		flag.PrintDefaults()
	}

	var outRootDir string
	flag.StringVar(&outRootDir, "out", ".",
		"root directory for output (default is current directory)")

	var configDir string
	flag.StringVar(&configDir, "configdir", "",
		"directory containing Goose config files")

	var modDir string
	flag.StringVar(&modDir, "dir", ".",
		"directory containing necessary go.mod")

	flag.Parse()
	if configDir == "" {
		flag.Usage()
		panic("bad")
	}

	util.Translate(proofgen.Package, flag.Args(), outRootDir, modDir, configDir)
}
