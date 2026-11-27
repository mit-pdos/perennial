package util

import (
	"bytes"
	"encoding/json"
	"flag"
	"fmt"
	"go/token"
	"io"
	"io/fs"
	"os"
	"path"
	"path/filepath"
	"strings"

	"github.com/fatih/color"
	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"
)

// PackageTranslator writes the translation of a package to the writer. It may
// return extra files, as a map from names (without extension) to contents,
// which are written in a directory named after the package file (chunks of
// a large generated proof, see proofgen.Package).
type PackageTranslator func(io.Writer, *packages.Package, bool, declfilter.DeclFilter) map[string]string

// TagsUsage is the help text of -tags.
const TagsUsage = "comma-separated list of additional Go build tags for loading the packages " +
	"(as go build -tags); the goose tag is always set"

// OverlayUsage is the help text of -overlay.
const OverlayUsage = "JSON file in the format of go build -overlay, " +
	`{"Replace": {"<file path>": "<file with its contents>", ...}}: ` +
	"the packages are loaded as if each file path had the contents of its replacement, " +
	"so a file added to a package or replaced in it is type-checked and translated with it, " +
	"under the same build constraints; relative paths are relative to the current directory, " +
	"and deleting a file (an empty replacement) is not supported"

// ParseTags splits the argument of -tags, a comma-separated list of build
// tags, dropping empty entries.
func ParseTags(s string) []string {
	var tags []string
	for _, tag := range strings.Split(s, ",") {
		if tag = strings.TrimSpace(tag); tag != "" {
			tags = append(tags, tag)
		}
	}
	return tags
}

// ReadOverlay reads an overlay file in the format of go build -overlay, a
// JSON object {"Replace": {path: replacement, ...}}, and returns the overlay
// it describes for packages.Config: each path, made absolute, mapped to the
// contents of its replacement. Relative paths, of either side, are relative
// to the current directory, as for the go command. Each replacement is a
// file (not a directory). An empty replacement, which the go command takes as
// deleting the file, is refused: packages.Config cannot express it. Unknown
// fields are refused too (the go command ignores them), to catch a misspelt
// "Replace".
func ReadOverlay(file string) (map[string][]byte, error) {
	data, err := os.ReadFile(file)
	if err != nil {
		return nil, errors.Wrap(err, "could not read the overlay")
	}
	var spec struct{ Replace map[string]string }
	dec := json.NewDecoder(bytes.NewReader(data))
	dec.DisallowUnknownFields()
	if err := dec.Decode(&spec); err != nil {
		return nil, errors.Wrapf(err, "could not parse the overlay %s", file)
	}
	overlay := make(map[string][]byte, len(spec.Replace))
	for from, to := range spec.Replace {
		if from == "" {
			return nil, errors.Errorf("overlay %s: empty path", file)
		}
		if to == "" {
			return nil, errors.Errorf("overlay %s: %s: deleting a file is not supported", file, from)
		}
		absFrom, err := filepath.Abs(from)
		if err != nil {
			return nil, errors.Wrapf(err, "overlay %s", file)
		}
		if _, ok := overlay[absFrom]; ok {
			return nil, errors.Errorf("overlay %s: %s is replaced twice", file, absFrom)
		}
		contents, err := os.ReadFile(to)
		if err != nil {
			return nil, errors.Wrapf(err, "overlay %s: could not read the replacement of %s", file, from)
		}
		overlay[absFrom] = contents
	}
	return overlay, nil
}

// LoadOptions are the options, besides the module, that decide which Go files
// the packages are loaded with, and their contents.
type LoadOptions struct {
	// Tags are the Go build tags, in addition to goose (none if empty).
	Tags []string
	// Overlay maps absolute file paths to file contents, which replace the
	// file on disk or add a file that does not exist (see
	// packages.Config.Overlay, and ReadOverlay).
	Overlay map[string][]byte
	// ModelRoot is the directory the dirs of [model] tables are relative
	// to; if empty, the nearest ancestor of the config directory with a
	// lakefile (RepoRoot).
	ModelRoot string
}

// LoadFlags are the command-line flags that give the LoadOptions: -tags and
// -overlay. Register them before flag.Parse, and call Options after it.
type LoadFlags struct {
	tags      string
	overlay   string
	modelRoot string
}

// Register defines -tags and -overlay on fs; note, if not empty, is added to
// the usage of both (e.g. that two commands must be given the same flags).
func (f *LoadFlags) Register(fs *flag.FlagSet, note string) {
	if note != "" {
		note = " (" + note + ")"
	}
	fs.StringVar(&f.tags, "tags", "", TagsUsage+note)
	fs.StringVar(&f.overlay, "overlay", "", OverlayUsage+note)
	fs.StringVar(&f.modelRoot, "model-root", "", "the directory the dirs of the goose configs' [model] "+
		"tables are relative to (default: the nearest ancestor of the config directory with a "+
		"lakefile.toml or lakefile.lean)"+note)
}

// Options returns the load options the flags give, reading the overlay file
// if there is one; on a bad overlay it prints the error and exits.
func (f *LoadFlags) Options() LoadOptions {
	opts := LoadOptions{Tags: ParseTags(f.tags), ModelRoot: f.modelRoot}
	if f.overlay != "" {
		overlay, err := ReadOverlay(f.overlay)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(2)
		}
		opts.Overlay = overlay
	}
	return opts
}

// NewPackageConfig is the configuration every command loads Go packages with.
// The packages are built with the build tag goose and the additional tags of
// opts (none if empty), which decide the files of a package under build
// constraints, and with the overlay of opts, which adds or replaces files
// (and whose files are subject to the same constraints): goose and proofgen
// must be given the same options, and so must every package of one program
// (build tags are those of a whole Go build).
func NewPackageConfig(modDir string, needDeps bool, opts LoadOptions) *packages.Config {
	mode := packages.NeedName | packages.NeedCompiledGoFiles
	mode |= packages.NeedImports
	mode |= packages.NeedTypes | packages.NeedSyntax | packages.NeedTypesInfo
	if needDeps {
		mode |= packages.NeedDeps
	}
	return &packages.Config{
		Dir:        modDir,
		Env:        append(os.Environ(), "GOOS=linux", "GOARCH=amd64"),
		Mode:       mode,
		BuildFlags: []string{"-tags", strings.Join(append([]string{"goose"}, opts.Tags...), ",")},
		Fset:       token.NewFileSet(),
		Overlay:    opts.Overlay,
	}
}

// fileHasContents returns true if the file at path has data. It returns false
// if any errors are encountered along the way.
func fileHasContents(path string, data []byte) bool {
	f, err := os.Open(path)
	if err != nil {
		return false
	}
	defer f.Close()
	stat, err := f.Stat()
	if stat.Size() != int64(len(data)) {
		return false
	}
	var buf [4096]byte
	for {
		n, err := f.Read(buf[:])
		if err != nil && err != io.EOF {
			return false
		}
		// got to end of file and contents are same
		if n == 0 {
			return true
		}
		if !bytes.Equal(buf[:n], data[:n]) {
			return false
		}
		data = data[n:]
	}
}

// Write data to file name, first checking if it already has those contents
//
// Same interface as [os.WriteFile] - creates name if it doesn't exist with
// perm, but doesn't set perm if the file does exist.
func WriteFileIfChanged(name string, data []byte, perm os.FileMode) error {
	if fileHasContents(name, data) {
		return nil
	}
	return os.WriteFile(name, data, perm)
}

// ReadConfig reads the filter config toml file for a package
func ReadConfig(configDir string, pkgPath string) (declfilter.FilterConfig, error) {
	configPath := path.Join(configDir, glang.GoPathToIdentPath(pkgPath)+".toml")
	configContents, err := os.ReadFile(configPath)
	if errors.Is(err, fs.ErrNotExist) {
		// if config does not exist, treat it as an empty file
		configContents = []byte{}
	} else if err != nil {
		return declfilter.FilterConfig{}, errors.Errorf("config file %s could not be read", configPath)
	}
	config, err := declfilter.ParseConfig(configContents)
	if err != nil {
		return declfilter.FilterConfig{}, errors.Errorf(
			"could not parse package config for %v:\n%v", pkgPath, err,
		)
	}
	return config, nil
}

func Translate(translatePkg PackageTranslator, pkgPatterns []string, outRootDir string, modDir string, configDir string, opts LoadOptions) {
	red := color.New(color.FgRed).SprintFunc()
	pkgs, _, err := LoadPackages(modDir, configDir, true, opts, pkgPatterns...)

	if err != nil {
		fmt.Fprintln(os.Stderr, red(err.Error()))
		os.Exit(1)
	} else if len(pkgs) == 0 {
		panic("patterns matched no packages")
	}

	for _, pkg := range pkgs {
		w := new(strings.Builder)
		config, err := ReadConfig(configDir, pkg.PkgPath)
		if err != nil {
			panic(fmt.Sprintf("could not parse config for %s:\n%v", pkg.PkgPath, err))
		}
		filter := ExtendFilter(pkg, config, declfilter.New(config))

		extra := translatePkg(w, pkg, config.Bootstrap.Enabled, filter)

		filePath := path.Join(outRootDir, glang.GoPathToIdentPath(pkg.PkgPath))
		outDir := path.Dir(filePath)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}

		err = WriteFileIfChanged(filePath+".lean", []byte(w.String()), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
		if err := WriteChunks(filePath, extra); err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
	}
}

// WriteChunks writes the chunk modules of a package to the directory dir and
// removes stale chunk files (named chunk*.lean) there.
func WriteChunks(dir string, files map[string]string) error {
	old, _ := filepath.Glob(path.Join(dir, "chunk*.lean"))
	for _, f := range old {
		name := strings.TrimSuffix(path.Base(f), ".lean")
		if _, ok := files[name]; !ok {
			if err := os.Remove(f); err != nil {
				return err
			}
		}
	}
	if len(files) == 0 {
		return nil
	}
	if err := os.MkdirAll(dir, 0777); err != nil {
		return err
	}
	for name, contents := range files {
		if err := WriteFileIfChanged(path.Join(dir, name+".lean"), []byte(contents), 0666); err != nil {
			return err
		}
	}
	return nil
}
