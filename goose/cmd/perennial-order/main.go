// Command perennial-order compiles the Go code that goose translates in
// Perennial's evaluation order:
//
//	go build -toolexec="perennial-order -code DIR [-code DIR ...]" ./...
//
// Each DIR is a directory goose translated into (its -out, holding each
// package's translation <path>.lean, and its -configdir, holding <path>.toml).
// The go command runs perennial-order in front of every tool it invokes. A
// package with a translation in some DIR is type-checked, and the
// declarations goose translates (util.Translated: the functions, methods and
// package-level variables its configuration's translate list matches) are
// rewritten into normal form (package order), as goose rewrote them before
// translating; the rewritten files go to a temporary directory removed
// afterwards, and the real compiler compiles them. Every other package, and
// every other declaration, is compiled as it is: code that is not verified
// keeps the compiler's own order. The rewritten files carry line directives
// giving every position in the original source, so error messages, panics and
// debug information name the original files; other tools run unchanged.
//
// It adds its own hash and that of the directories' configurations and
// translations to the compiler's version (`compile -V=full`), which the go
// command uses to key its build cache, so builds with other selections are
// cached separately.
package main

import (
	"bufio"
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"go/ast"
	"go/build"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"

	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/order"
	"github.com/mit-pdos/perennial/goose/util"
)

// codeDirs are the directories goose translated into.
var codeDirs []string

func main() {
	args := os.Args[1:]
	for len(args) >= 2 && args[0] == "-code" {
		codeDirs = append(codeDirs, args[1])
		args = args[2:]
	}
	if len(codeDirs) == 0 || len(args) == 0 {
		fmt.Fprintln(os.Stderr, `usage: go build -toolexec="perennial-order -code DIR [-code DIR ...]" ...`)
		os.Exit(2)
	}
	tool, args := args[0], args[1:]
	if strings.TrimSuffix(filepath.Base(tool), ".exe") != "compile" {
		os.Exit(run(tool, args))
	}
	for _, a := range args {
		if strings.HasPrefix(a, "-V") {
			os.Exit(version(tool, args))
		}
	}
	os.Exit(compile(tool, args))
}

func run(tool string, args []string) int {
	cmd := exec.Command(tool, args...)
	cmd.Stdin, cmd.Stdout, cmd.Stderr = os.Stdin, os.Stdout, os.Stderr
	if err := cmd.Run(); err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			return ee.ExitCode()
		}
		fmt.Fprintln(os.Stderr, "perennial-order:", err)
		return 1
	}
	return 0
}

// selfHash identifies this rewriter (its executable) and what it selects:
// the code directories' configurations and the translations they hold.
func selfHash() string {
	exe, err := os.Executable()
	if err != nil {
		fatalf("%v", err)
	}
	f, err := os.Open(exe)
	if err != nil {
		fatalf("%v", err)
	}
	defer f.Close()
	h := sha256.New()
	if _, err := io.Copy(h, f); err != nil {
		fatalf("%v", err)
	}
	for _, dir := range codeDirs {
		abs, _ := filepath.Abs(dir)
		fmt.Fprintf(h, "dir %s\n", abs)
		err := filepath.WalkDir(dir, func(p string, d os.DirEntry, err error) error {
			if err != nil || d.IsDir() {
				return err
			}
			switch filepath.Ext(p) {
			case ".lean":
				fmt.Fprintf(h, "lean %s\n", p)
			case ".toml":
				b, err := os.ReadFile(p)
				if err != nil {
					return err
				}
				fmt.Fprintf(h, "toml %s %d\n%s", p, len(b), b)
			}
			return nil
		})
		if err != nil {
			fatalf("%v", err)
		}
	}
	return hex.EncodeToString(h.Sum(nil))[:16]
}

// selection is what goose translates of the package being compiled, or nil
// if no code directory has a translation of it.
func selection() order.Selection {
	// the import path (the compiler's -p is "main" for a command); a test
	// build adds " [p.test]"
	path, _, _ := strings.Cut(os.Getenv("TOOLEXEC_IMPORTPATH"), " ")
	if path == "" {
		fatalf("TOOLEXEC_IMPORTPATH is not set: run under go build -toolexec")
	}
	var found []string
	for _, dir := range codeDirs {
		if _, err := os.Stat(filepath.Join(dir, glang.GoPathToIdentPath(path)+".lean")); err == nil {
			found = append(found, dir)
		}
	}
	switch len(found) {
	case 0:
		return nil
	case 1:
	default:
		fatalf("%s is translated in more than one code directory: %v", path, found)
	}
	config, err := util.ReadConfig(found[0], path)
	if err != nil {
		fatalf("%v", err)
	}
	return util.Translated(config)
}

// version prints the compiler's version line with this rewriter's hash
// added (to the build ID on a development toolchain, whose cache key it is).
func version(tool string, args []string) int {
	var out bytes.Buffer
	cmd := exec.Command(tool, args...)
	cmd.Stdout, cmd.Stderr = &out, os.Stderr
	if err := cmd.Run(); err != nil {
		if ee, ok := err.(*exec.ExitError); ok {
			return ee.ExitCode()
		}
		fatalf("%v", err)
	}
	line := strings.TrimRight(out.String(), "\n")
	f := strings.Fields(line)
	if n := len(f); n > 0 && strings.HasPrefix(f[n-1], "buildID=") {
		f[n-1] += "+perennial-order-" + selfHash()
	} else {
		f = append(f, "perennial-order="+selfHash())
	}
	fmt.Println(strings.Join(f, " "))
	return 0
}

func fatalf(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "perennial-order: "+format+"\n", args...)
	os.Exit(1)
}

// flagValue is the value of the compiler flag name (-name v or -name=v).
func flagValue(args []string, name string) string {
	for i, a := range args {
		if a == name && i+1 < len(args) {
			return args[i+1]
		}
		if strings.HasPrefix(a, name+"=") {
			return a[len(name)+1:]
		}
	}
	return ""
}

// importConfig reads the packagefile and importmap lines of an importcfg.
func importConfig(file string) (map[string]string, map[string]string) {
	files, maps := map[string]string{}, map[string]string{}
	if file == "" {
		return files, maps
	}
	f, err := os.Open(file)
	if err != nil {
		fatalf("%v", err)
	}
	defer f.Close()
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		line := strings.TrimSpace(sc.Text())
		verb, rest, _ := strings.Cut(line, " ")
		k, v, ok := strings.Cut(rest, "=")
		if !ok {
			continue
		}
		switch verb {
		case "packagefile":
			files[k] = v
		case "importmap":
			maps[k] = v
		}
	}
	return files, maps
}

// applyRewrites is the compiler's -trimpath rewriting of a file name
// (cmd/internal/objabi.ApplyRewrites): the first rule whose prefix matches.
func applyRewrites(file, rewrites string) (string, bool) {
	for _, rw := range strings.Split(rewrites, ";") {
		prefix, replace := rw, ""
		if j := strings.LastIndex(rw, "=>"); j >= 0 {
			prefix, replace = rw[:j], rw[j+len("=>"):]
		}
		if prefix == "" || !hasPathPrefix(file, prefix) {
			continue
		}
		if len(file) == len(prefix) {
			return replace, true
		}
		if replace == "" {
			return file[len(prefix)+1:], true
		}
		return replace + file[len(prefix):], true
	}
	return file, false
}

func hasPathPrefix(s, t string) bool {
	if len(t) > len(s) {
		return false
	}
	for i := 0; i < len(t); i++ {
		cs, ct := s[i], t[i]
		if 'A' <= cs && cs <= 'Z' {
			cs += 'a' - 'A'
		}
		if 'A' <= ct && ct <= 'Z' {
			ct += 'a' - 'A'
		}
		if cs == '\\' {
			cs = '/'
		}
		if ct == '\\' {
			ct = '/'
		}
		if cs != ct {
			return false
		}
	}
	return len(t) >= len(s) || s[len(t)] == '/' || s[len(t)] == '\\'
}

// setFlag sets the compiler flag name to v in args (the flags before the
// files), replacing an existing value.
func setFlag(args []string, name, v string) []string {
	out := append([]string(nil), args...)
	for i, a := range out {
		if a == name && i+1 < len(out) {
			out[i+1] = v
			return out
		}
		if strings.HasPrefix(a, name+"=") {
			out[i] = name + "=" + v
			return out
		}
	}
	return append(out, name, v)
}

func compile(tool string, args []string) int {
	// The files to compile are the trailing .go arguments.
	first := len(args)
	for first > 0 && strings.HasSuffix(args[first-1], ".go") && !strings.HasPrefix(args[first-1], "-") {
		first--
	}
	files := args[first:]
	for _, a := range args {
		if strings.HasPrefix(a, "@") { // a response file could hide the files
			fatalf("response file %s: not supported, refusing to compile it unordered", a)
		}
	}
	if len(files) == 0 {
		return run(tool, args)
	}
	sel := selection()
	if sel == nil {
		return run(tool, args) // not translated: compiled as it is
	}
	pkgPath := flagValue(args, "-p")
	pkgFiles, importMap := importConfig(flagValue(args, "-importcfg"))

	fset := token.NewFileSet()
	var syntax []*ast.File
	var srcs [][]byte
	for _, name := range files {
		src, err := os.ReadFile(name)
		if err != nil {
			fatalf("%v", err)
		}
		f, err := parser.ParseFile(fset, name, src, parser.ParseComments|parser.SkipObjectResolution)
		if err != nil {
			return run(tool, args) // let the compiler report it
		}
		syntax, srcs = append(syntax, f), append(srcs, src)
	}
	lookup := func(path string) (io.ReadCloser, error) {
		if m, ok := importMap[path]; ok {
			path = m
		}
		file, ok := pkgFiles[path]
		if !ok {
			return nil, fmt.Errorf("no export data for %q", path)
		}
		return os.Open(file)
	}
	goarch := os.Getenv("GOARCH")
	if goarch == "" {
		goarch = build.Default.GOARCH
	}
	info := &types.Info{
		Types:      map[ast.Expr]types.TypeAndValue{},
		Defs:       map[*ast.Ident]types.Object{},
		Uses:       map[*ast.Ident]types.Object{},
		Implicits:  map[ast.Node]types.Object{},
		Selections: map[*ast.SelectorExpr]*types.Selection{},
	}
	var typeErr error
	conf := types.Config{
		GoVersion: flagValue(args, "-lang"),
		Importer:  importer.ForCompiler(fset, "gc", lookup),
		Sizes:     types.SizesFor("gc", goarch),
		Error: func(err error) {
			if te, ok := err.(types.Error); typeErr == nil && (!ok || !te.Soft) {
				typeErr = err
			}
		},
	}
	if pkgPath == "" {
		pkgPath = "main"
	}
	pkg, _ := conf.Check(pkgPath, fset, syntax, info)
	if typeErr != nil {
		// If the compiler rejects the package too, its error is the one to
		// report; if it accepts it, refuse to compile it unrewritten.
		if code := run(tool, args); code != 0 {
			return code
		}
		fatalf("cannot type-check %s, refusing to compile it unordered: %v", pkgPath, typeErr)
	}

	dir, err := os.MkdirTemp("", "perennial-order-")
	if err != nil {
		fatalf("%v", err)
	}
	defer os.RemoveAll(dir)
	newArgs := append([]string(nil), args...)
	trim := flagValue(args, "-trimpath")
	var trimRules []string
	for i, f := range syntax {
		out, changed, err := order.Rewrite(fset, pkg, info, f, srcs[i], sel)
		if err != nil {
			fatalf("%v", err)
		}
		if !changed {
			continue
		}
		name := filepath.Join(dir, fmt.Sprintf("%d_%s", i, filepath.Base(files[i])))
		if err := os.WriteFile(name, out, 0o644); err != nil {
			fatalf("%v", err)
		}
		newArgs[first+i] = name
		// The compiler records each file's own path (in export data and
		// debug information); name the rewritten file as the original
		// would be named, so that the output does not depend on the
		// temporary directory.
		orig, _ := applyRewrites(files[i], trim)
		trimRules = append(trimRules, name+"=>"+orig)
	}
	if len(trimRules) > 0 {
		if trim != "" {
			trimRules = append(trimRules, trim)
		}
		newArgs = append(setFlag(newArgs[:first], "-trimpath", strings.Join(trimRules, ";")), newArgs[first:]...)
	}
	return run(tool, newArgs)
}
