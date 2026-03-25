package util

import (
	"bytes"
	"fmt"
	"go/token"
	"io"
	"io/fs"
	"os"
	"path"
	"strings"

	"github.com/fatih/color"
	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"
)

type PackageTranslator func(io.Writer, *packages.Package, string, bool, declfilter.DeclFilter)

func NewPackageConfig(modDir string, needDeps bool) *packages.Config {
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
		BuildFlags: []string{"-tags", "goose"},
		Fset:       token.NewFileSet(),
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

var ffiMapping = map[string]string{
	"github.com/mit-pdos/gokv/grove_ffi":         "grove",
	"github.com/goose-lang/primitive/disk":       "disk",
	"github.com/goose-lang/primitive/async_disk": "async_disk",
}

// GetFfi returns the short string corresponding to the FFI used.
//
// Returns an empty string if no FFI is used, and panics if multiple FFIs are
// found.
func GetFfi(pkg *packages.Package) string {
	seenFfis := make(map[string]struct{})
	packages.Visit([]*packages.Package{pkg},
		func(pkg *packages.Package) bool {
			// the dependencies of an FFI are not considered as being used; this
			// allows one FFI to be built on top of another
			if _, ok := ffiMapping[pkg.PkgPath]; ok {
				return false
			}
			return true
		},
		func(pkg *packages.Package) {
			if ffi, ok := ffiMapping[pkg.PkgPath]; ok {
				seenFfis[ffi] = struct{}{}
			}
		},
	)

	if len(seenFfis) > 1 {
		panic(fmt.Sprintf("multiple ffis used %v", seenFfis))
	}
	for ffi := range seenFfis {
		return ffi
	}
	return ""
}

// ReadConfig reads the filter config toml file for a package
func ReadConfig(configDir string, pkgPath string) (declfilter.FilterConfig, error) {
	configPath := path.Join(configDir,
		glang.ImportToPath(pkgPath)+".toml")
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

func Translate(translatePkg PackageTranslator, pkgPatterns []string, outRootDir string, modDir string, configDir string) {
	red := color.New(color.FgRed).SprintFunc()
	pkgs, err := packages.Load(NewPackageConfig(modDir, true), pkgPatterns...)

	if err != nil {
		panic(err)
	} else if len(pkgs) == 0 {
		panic("patterns matched no packages")
	}

	for _, pkg := range pkgs {
		w := new(strings.Builder)
		config, err := ReadConfig(configDir, pkg.PkgPath)
		if err != nil {
			panic(fmt.Sprintf("could not parse config for %s:\n%v", pkg.PkgPath, err))
		}
		filter := declfilter.New(config)

		ffi := GetFfi(pkg)
		translatePkg(w, pkg, ffi, config.Bootstrap.Enabled, filter)

		filePath := path.Join(outRootDir, glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath))
		outDir := path.Dir(filePath)
		err = os.MkdirAll(outDir, 0777)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not create output directory"))
		}

		outFile := filePath + ".v"
		err = WriteFileIfChanged(outFile, []byte(w.String()), 0666)
		if err != nil {
			fmt.Fprintln(os.Stderr, err.Error())
			fmt.Fprintln(os.Stderr, red("could not write output"))
			os.Exit(1)
		}
	}
}
