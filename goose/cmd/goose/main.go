package main

import (
	"bytes"
	"flag"
	"fmt"
	"os"
	"path"
	"strings"

	"github.com/fatih/color"

	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/util"
)

func fileContents(f glang.File) []byte {
	var b bytes.Buffer
	f.Write(&b)
	return b.Bytes()
}

func translate(pkgPatterns []string, outRootDir string, configDir string, modDir string,
	opts util.LoadOptions, ignoreErrors bool) {
	red := color.New(color.FgRed).SprintFunc()
	fs, errs, patternError := goose.TranslatePackages(configDir, modDir, opts, pkgPatterns...)
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
		outFile := path.Join(outRootDir, glang.ImportToLeanPath(f.PkgPath))
		outDir := path.Dir(outFile)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}
		err = util.WriteFileIfChanged(outFile, fileContents(f), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
		chunks := make(map[string]string)
		for name, c := range f.Chunks {
			chunks[name] = string(fileContents(c))
		}
		err = util.WriteChunks(strings.TrimSuffix(outFile, ".lean"), chunks)
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

// modelOverlay is `goose model-overlay`: it writes the overlay of the Go
// models of the packages (util.BuildModels) in the format of go build
// -overlay, and prints the path of its JSON file.
func modelOverlay(args []string) {
	fs := flag.NewFlagSet("goose model-overlay", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintln(fs.Output(), "Usage: goose model-overlay [options] -o <dir> <go package patterns>")
		fmt.Fprintln(fs.Output(), "Writes <dir>/overlay.json (and <dir>/files), for go build/test -overlay: "+
			"the Go models of the [model] tables of the packages' goose configs, with the -overlay given.")
		fs.PrintDefaults()
	}
	modDir := fs.String("dir", ".", "directory containing necessary go.mod")
	configDir := fs.String("configdir", ".", "directory containing Goose config files")
	outDir := fs.String("o", "", "directory to write the overlay to (required)")
	var load util.LoadFlags
	load.Register(fs, "")
	_ = fs.Parse(args)
	if *outDir == "" || fs.NArg() == 0 {
		fs.Usage()
		os.Exit(2)
	}
	opts := load.Options()
	models, err := util.BuildModels(*modDir, *configDir, opts, fs.Args()...)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	out, err := models.WriteGoOverlay(opts, *outDir)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Println(out)
	// the overlay is that of this build configuration (util.NewPackageConfig)
	fmt.Fprintf(os.Stderr, "goose model-overlay: build with GOOS=linux GOARCH=amd64 go build -tags %s -overlay %s\n",
		strings.Join(append([]string{"goose"}, opts.Tags...), ","), out)
}

// layoutModelled is `goose layout-modelled`: it writes the Lean file of the
// types whose layout a model changes (util.LayoutModelledNames), the
// predicate go.layoutModelled.
func layoutModelled(args []string) {
	fs := flag.NewFlagSet("goose layout-modelled", flag.ExitOnError)
	fs.Usage = func() {
		fmt.Fprintln(fs.Output(), "Usage: goose layout-modelled [options] -o <file.lean> <go package patterns>")
		fmt.Fprintln(fs.Output(), "Writes go.layoutModelled: the types of the models of the packages' goose "+
			"configs whose layout the model changes, and the type declarations the configs trust.")
		fs.PrintDefaults()
	}
	modDir := fs.String("dir", ".", "directory containing necessary go.mod")
	configDir := fs.String("configdir", ".", "directory containing Goose config files")
	out := fs.String("o", "", "the Lean file to write (required)")
	uncovered := fs.String("uncovered", "", "comma-separated configs (relative to -configdir) "+
		"with a model or a trusted declaration that no package of the patterns needs to have")
	var load util.LoadFlags
	load.Register(fs, "")
	_ = fs.Parse(args)
	if *out == "" || fs.NArg() == 0 {
		fs.Usage()
		os.Exit(2)
	}
	var unc []string
	if *uncovered != "" {
		unc = strings.Split(*uncovered, ",")
	}
	names, err := util.LayoutModelledNames(*modDir, *configDir, load.Options(), unc, fs.Args()...)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := util.WriteFileIfChanged(*out, util.LayoutModelledLean(names), 0666); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}

// noinspection GoUnhandledErrorResult
func main() {
	if len(os.Args) > 1 && os.Args[1] == "model-overlay" {
		modelOverlay(os.Args[2:])
		return
	}
	if len(os.Args) > 1 && os.Args[1] == "layout-modelled" {
		layoutModelled(os.Args[2:])
		return
	}
	flag.Usage = func() {
		fmt.Fprintln(flag.CommandLine.Output(), "Usage: goose [options] <path to go package>")
		fmt.Fprintln(flag.CommandLine.Output(), "       goose model-overlay [options] -o <dir> <go package patterns>")
		fmt.Fprintln(flag.CommandLine.Output(), "       goose layout-modelled [options] -o <file.lean> <go package patterns>")

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

	flag.Var(glang.LeanRootFlag{}, "lean-root", glang.LeanRootUsage)

	var load util.LoadFlags
	load.Register(flag.CommandLine, "")

	flag.Parse()
	if configDir == "" {
		configDir = outRootDir
	}

	translate(flag.Args(), outRootDir, configDir, modDir, load.Options(), ignoreErrors)
}
