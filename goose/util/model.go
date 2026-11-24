package util

import (
	"bytes"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/build"
	"go/parser"
	"go/token"
	"go/types"
	"os"
	"os/exec"
	"path/filepath"
	"slices"
	"sort"
	"strconv"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/pkg/errors"
	"golang.org/x/tools/go/packages"
)

// Go model overlays: the [model] table of a package's goose config
// (declfilter.ModelConfig) names Go model files that replace declarations of
// the real package. BuildModels splices them into the real package and
// returns the result as an overlay of the package's files, which every
// command loads the packages with (LoadPackages), and which `goose
// model-overlay` writes for go build -overlay (WriteGoOverlay).

// ModelFilePrefix starts the name of each file a model adds to its package
// (it sorts after the real files, so their init functions run first).
const ModelFilePrefix = "zz_gomodel_"

// replaceDirective marks a model init function that replaces the real
// package's init.N: //gomodel:replace init.N "<first line of its body>".
const replaceDirective = "//gomodel:replace "

// A PackageModel is the Go model of one package.
type PackageModel struct {
	PkgPath string
	Config  declfilter.ModelConfig
	// Dir is the absolute model directory, Files its model files.
	Dir   string
	Files []string
	// Added is set for a whole-package model of a standard-library
	// package that does not exist.
	Added bool
}

// Models are the Go models of the packages of a load.
type Models struct {
	// Overlay maps absolute file paths to their contents under the models
	// (without the user's -overlay).
	Overlay map[string][]byte
	// Packages are the models, by import path.
	Packages map[string]*PackageModel
	// modelFiles are the absolute paths of all model files.
	modelFiles map[string]bool
}

// ModelErrors are the config errors of the models of a load.
type ModelErrors []error

func (es ModelErrors) Error() string {
	var s []string
	for _, e := range es {
		s = append(s, e.Error())
	}
	return strings.Join(s, "\n")
}

// RepoRoot returns the directory model dirs are relative to: root if not
// empty, else the nearest ancestor of configDir (or configDir itself) with a
// lakefile.toml or lakefile.lean.
func RepoRoot(configDir string, root string) (string, error) {
	if root != "" {
		return filepath.Abs(root)
	}
	dir, err := filepath.Abs(configDir)
	if err != nil {
		return "", err
	}
	for {
		for _, f := range []string{"lakefile.toml", "lakefile.lean"} {
			if _, err := os.Stat(filepath.Join(dir, f)); err == nil {
				return dir, nil
			}
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "", errors.Errorf("no lakefile.toml or lakefile.lean above the config directory %s: "+
				"give the repository root with -model-root", configDir)
		}
		dir = parent
	}
}

// LoadPackages loads the packages matching patterns, as packages.Load with
// NewPackageConfig(modDir, needDeps, opts) does, with the Go models of the
// load (BuildModels) applied.
func LoadPackages(modDir, configDir string, needDeps bool, opts LoadOptions,
	patterns ...string) ([]*packages.Package, *Models, error) {
	models, err := BuildModels(modDir, configDir, opts, patterns...)
	if err != nil {
		return nil, nil, err
	}
	merged, err := models.merge(opts)
	if err != nil {
		return nil, nil, err
	}
	pkgs, err := packages.Load(NewPackageConfig(modDir, needDeps, merged), patterns...)
	return pkgs, models, err
}

// merge returns opts with the models' overlay added to the user's.
func (m *Models) merge(opts LoadOptions) (LoadOptions, error) {
	if len(m.Overlay) == 0 {
		return opts, nil
	}
	o := make(map[string][]byte, len(opts.Overlay)+len(m.Overlay))
	for k, v := range opts.Overlay {
		o[k] = v
	}
	for k, v := range m.Overlay {
		if _, ok := o[k]; ok {
			return opts, errors.Errorf("-overlay replaces %s, which a Go model rewrites", k)
		}
		o[k] = v
	}
	opts.Overlay = o
	return opts, nil
}

// Filter returns df, except that it translates the declarations of the
// package that come from its model, other than the ones df trusts (the
// model's primitive stubs) and the ones names_only matches, which it
// translates names-only.
func (m *Models) Filter(pkg *packages.Package, df declfilter.DeclFilter) declfilter.DeclFilter {
	pm := m.pkgModel(pkg.PkgPath)
	if pm == nil {
		return df
	}
	names := make(map[string]bool)
	namesOnly := make(map[string]bool)
	for n := range modelDeclNames(pkg, m.modelFiles) {
		switch {
		case declfilter.MatchesAny(pm.Config.NamesOnly, n):
			namesOnly[n] = true
		case df.GetAction(n) != declfilter.Trust:
			names[n] = true
		}
	}
	return declfilter.WithNamesOnly(declfilter.WithTranslated(df, names), namesOnly)
}

func (m *Models) pkgModel(path string) *PackageModel {
	if m == nil {
		return nil
	}
	return m.Packages[path]
}

// modelDeclNames returns the names (as the declaration filter sees them) of
// the declarations of pkg whose position is in a model file.
func modelDeclNames(pkg *packages.Package, files map[string]bool) map[string]bool {
	names := make(map[string]bool)
	in := func(p token.Pos) bool { return files[pkg.Fset.Position(p).Filename] }
	inits := 0
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				name := funcDeclName(d)
				if name == "init" {
					name = fmt.Sprintf("init.%d", inits)
					inits++
				}
				if in(d.Name.Pos()) {
					names[name] = true
				}
			case *ast.GenDecl:
				for _, s := range d.Specs {
					switch s := s.(type) {
					case *ast.TypeSpec:
						if in(s.Name.Pos()) {
							names[s.Name.Name] = true
						}
					case *ast.ValueSpec:
						for _, n := range s.Names {
							if in(n.Pos()) && n.Name != "_" {
								names[n.Name] = true
							}
						}
					}
				}
			}
		}
	}
	return names
}

// funcDeclName is the filter name of a function or method declaration
// (`f`, `T.m`; "init" for every init function).
func funcDeclName(d *ast.FuncDecl) string {
	if d.Recv == nil || len(d.Recv.List) == 0 {
		return d.Name.Name
	}
	return recvTypeName(d.Recv.List[0].Type) + "." + d.Name.Name
}

func recvTypeName(t ast.Expr) string {
	for {
		switch e := t.(type) {
		case *ast.StarExpr:
			t = e.X
		case *ast.ParenExpr:
			t = e.X
		case *ast.IndexExpr:
			t = e.X
		case *ast.IndexListExpr:
			t = e.X
		case *ast.Ident:
			return e.Name
		default:
			return "?"
		}
	}
}

// WriteGoOverlay writes the models' overlay, with the user's (opts.Overlay),
// to dir in the format of go build -overlay, and returns the path of its
// JSON file (dir/overlay.json; the contents are in dir/files).
func (m *Models) WriteGoOverlay(opts LoadOptions, dir string) (string, error) {
	merged, err := m.merge(opts)
	if err != nil {
		return "", err
	}
	dir, err = filepath.Abs(dir)
	if err != nil {
		return "", err
	}
	filesDir := filepath.Join(dir, "files")
	if err := os.MkdirAll(filesDir, 0777); err != nil {
		return "", err
	}
	paths := make([]string, 0, len(merged.Overlay))
	for p := range merged.Overlay {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	replace := make(map[string]string, len(paths))
	for i, p := range paths {
		f := filepath.Join(filesDir, fmt.Sprintf("%03d_%s", i, filepath.Base(p)))
		if err := WriteFileIfChanged(f, merged.Overlay[p], 0666); err != nil {
			return "", err
		}
		replace[p] = f
	}
	data, err := json.MarshalIndent(struct{ Replace map[string]string }{replace}, "", "\t")
	if err != nil {
		return "", err
	}
	out := filepath.Join(dir, "overlay.json")
	return out, WriteFileIfChanged(out, append(data, '\n'), 0666)
}

// BuildModels builds the Go models of the packages matching patterns and of
// their dependencies: of every package of the import graph (under opts)
// whose config in configDir has a [model] table. Since a model may import a
// package the real code does not (internal/gomodel, a package only the
// overlay adds), the graph is computed again under the overlay until no new
// model appears. It checks each model (the errors are listed in
// declfilter.ModelConfig and here): the names of replaces both ways, the
// splice, the overlaid package's type-checking, the names_only entries, and
// that the model keeps the real package's API (CheckAPI).
func BuildModels(modDir, configDir string, opts LoadOptions, patterns ...string) (*Models, error) {
	m := &Models{Overlay: make(map[string][]byte), Packages: make(map[string]*PackageModel),
		modelFiles: make(map[string]bool)}
	b := &builder{modDir: modDir, configDir: configDir, opts: opts, models: m,
		real: make(map[string]*packages.Package)}
	for iter := 0; ; iter++ {
		merged, err := m.merge(opts)
		if err != nil {
			return nil, err
		}
		paths, err := b.discover(merged, patterns)
		if err != nil {
			return nil, err
		}
		var newPkgs []*PackageModel
		var errs ModelErrors
		for _, p := range paths {
			if m.Packages[p] != nil {
				continue
			}
			config, err := ReadConfig(configDir, p)
			if err != nil {
				errs = append(errs, err)
				continue
			}
			if config.Model == nil {
				continue
			}
			for _, e := range config.CheckModel() {
				errs = append(errs, errors.Wrapf(e, "model of %s", p))
			}
			df := declfilter.New(config)
			for _, n := range config.Model.Replaces {
				if a := df.GetAction(n); n != "*" && (a == declfilter.Trust || a == declfilter.Skip) {
					errs = append(errs, errors.Errorf("model of %s: replaces %q, which the config "+
						"trusts or skips (a replaced declaration is translated)", p, n))
				}
			}
			pm := &PackageModel{PkgPath: p, Config: *config.Model}
			m.Packages[p] = pm
			newPkgs = append(newPkgs, pm)
		}
		if len(errs) > 0 {
			return nil, errs
		}
		if len(newPkgs) == 0 {
			break
		}
		if iter > 8 {
			return nil, errors.New("Go models: the import graph does not settle")
		}
		if err := b.splice(newPkgs); err != nil {
			return nil, err
		}
	}
	if len(m.Packages) == 0 {
		return m, nil
	}
	return m, b.check()
}

type builder struct {
	modDir, configDir string
	opts              LoadOptions
	models            *Models
	// the real packages, without the models
	real map[string]*packages.Package
	root string
}

func (b *builder) pkgConfig(mode packages.LoadMode, opts LoadOptions) *packages.Config {
	c := NewPackageConfig(b.modDir, false, opts)
	c.Mode = mode
	return c
}

// discover returns the import paths of the import graph of the patterns.
func (b *builder) discover(opts LoadOptions, patterns []string) ([]string, error) {
	pkgs, err := packages.Load(b.pkgConfig(packages.NeedName|packages.NeedImports|packages.NeedDeps, opts),
		patterns...)
	if err != nil {
		return nil, err
	}
	var paths []string
	packages.Visit(pkgs, nil, func(p *packages.Package) {
		path := p.PkgPath
		if path == "" {
			path = p.ID
		}
		paths = append(paths, path)
	})
	sort.Strings(paths)
	return slices.Compact(paths), nil
}

func isStdPath(path string) bool {
	first, _, _ := strings.Cut(path, "/")
	return !strings.Contains(first, ".")
}

func (b *builder) goroot() (string, error) {
	cmd := exec.Command("go", "env", "GOROOT")
	cmd.Dir = b.modDir
	cmd.Env = append(os.Environ(), "GOOS=linux", "GOARCH=amd64")
	out, err := cmd.Output()
	if err != nil {
		return "", errors.Wrap(err, "go env GOROOT")
	}
	return strings.TrimSpace(string(out)), nil
}

// source returns the contents of a real file (under the user's overlay).
func (b *builder) source(path string) ([]byte, error) {
	if c, ok := b.opts.Overlay[path]; ok {
		return c, nil
	}
	return os.ReadFile(path)
}

const realMode = packages.NeedName | packages.NeedFiles | packages.NeedCompiledGoFiles |
	packages.NeedSyntax | packages.NeedTypes | packages.NeedTypesInfo | packages.NeedImports

// splice adds the overlay of each new model.
func (b *builder) splice(pms []*PackageModel) error {
	if b.root == "" {
		root, err := RepoRoot(b.configDir, b.opts.ModelRoot)
		if err != nil {
			return err
		}
		b.root = root
	}
	var paths []string
	for _, pm := range pms {
		paths = append(paths, pm.PkgPath)
	}
	pkgs, err := packages.Load(b.pkgConfig(realMode, b.opts), paths...)
	if err != nil {
		return err
	}
	byPath := make(map[string]*packages.Package)
	for _, p := range pkgs {
		byPath[p.PkgPath] = p
		if p.PkgPath == "" {
			byPath[p.ID] = p
		}
	}
	var errs ModelErrors
	for _, pm := range pms {
		pkg := byPath[pm.PkgPath]
		es := b.splicePackage(pm, pkg)
		for _, e := range es {
			errs = append(errs, errors.Wrapf(e, "model of %s", pm.PkgPath))
		}
	}
	if len(errs) > 0 {
		return errs
	}
	return nil
}

// A modelFile is a parsed model file.
type modelFile struct {
	path string
	src  []byte
	fset *token.FileSet
	file *ast.File
	// local import names -> path
	imports map[string]string
}

func (b *builder) readModel(pm *PackageModel) ([]*modelFile, []error) {
	pm.Dir = filepath.FromSlash(pm.Config.Dir)
	if !filepath.IsAbs(pm.Dir) {
		pm.Dir = filepath.Join(b.root, pm.Dir)
	}
	entries, err := os.ReadDir(pm.Dir)
	if err != nil {
		return nil, []error{errors.Errorf("model directory %s: %v", pm.Dir, err)}
	}
	var mfs []*modelFile
	var errs []error
	for _, e := range entries {
		n := e.Name()
		if e.IsDir() || !strings.HasSuffix(n, ".go") || strings.HasSuffix(n, "_test.go") {
			continue
		}
		path := filepath.Join(pm.Dir, n)
		src, err := os.ReadFile(path)
		if err != nil {
			errs = append(errs, err)
			continue
		}
		fset := token.NewFileSet()
		f, err := parser.ParseFile(fset, path, src, parser.ParseComments)
		if err != nil {
			errs = append(errs, err)
			continue
		}
		for _, cg := range f.Comments {
			for _, c := range cg.List {
				if cg.Pos() < f.Package && (strings.HasPrefix(c.Text, "//go:build") || strings.HasPrefix(c.Text, "// +build")) {
					errs = append(errs, errors.Errorf("%s: a model file has no build constraint "+
						"(it is part of the package exactly when the model is)", path))
				}
				if strings.HasPrefix(c.Text, "//line ") || strings.HasPrefix(c.Text, "/*line ") {
					errs = append(errs, errors.Errorf("%s: a model file has no //line directive "+
						"(the positions of its declarations say which are the model's)", path))
				}
			}
		}
		if constrainedName(n) {
			errs = append(errs, errors.Errorf("%s: a model file's name has no GOOS or GOARCH suffix "+
				"(it is part of the package exactly when the model is)", path))
		}
		mf := &modelFile{path: path, src: src, fset: fset, file: f, imports: make(map[string]string)}
		for _, imp := range f.Imports {
			if p, _ := strconv.Unquote(imp.Path.Value); p == "C" {
				errs = append(errs, errors.Errorf("%s: a model file cannot use cgo", path))
			}
		}
		mfs = append(mfs, mf)
		pm.Files = append(pm.Files, path)
		b.models.modelFiles[path] = true
	}
	if len(mfs) == 0 && len(errs) == 0 {
		errs = append(errs, errors.Errorf("model directory %s has no model files", pm.Dir))
	}
	return mfs, errs
}

// constrainedName says whether a file name has a GOOS or GOARCH suffix
// (go/build's file-name constraints): whether some build configuration
// excludes the file by its name alone.
func constrainedName(name string) bool {
	dir, err := os.MkdirTemp("", "gomodel-name-")
	if err != nil {
		return false
	}
	defer os.RemoveAll(dir)
	if os.WriteFile(filepath.Join(dir, name), []byte("package p\n"), 0666) != nil {
		return false
	}
	matches := func(goos, goarch string) bool {
		ctxt := build.Default
		ctxt.GOOS, ctxt.GOARCH, ctxt.CgoEnabled = goos, goarch, false
		ok, err := ctxt.MatchFile(dir, name)
		return err == nil && ok
	}
	return !matches("linux", "amd64") || !matches("windows", "arm64") || !matches("darwin", "386")
}

// importNames fills in the local names of the model files' imports: the
// name given, or the imported package's name.
func (b *builder) importNames(mfs []*modelFile) error {
	need := make(map[string]bool)
	for _, mf := range mfs {
		for _, imp := range mf.file.Imports {
			if imp.Name == nil {
				p, _ := strconv.Unquote(imp.Path.Value)
				need[p] = true
			}
		}
	}
	names := make(map[string]string)
	if len(need) > 0 {
		var paths []string
		for p := range need {
			paths = append(paths, p)
		}
		merged, err := b.models.merge(b.opts)
		if err != nil {
			return err
		}
		pkgs, err := packages.Load(b.pkgConfig(packages.NeedName, merged), paths...)
		if err != nil {
			return err
		}
		for _, p := range pkgs {
			if p.Name != "" {
				names[p.PkgPath] = p.Name
			}
		}
	}
	for _, mf := range mfs {
		for _, imp := range mf.file.Imports {
			p, _ := strconv.Unquote(imp.Path.Value)
			var n string
			switch {
			case imp.Name != nil:
				n = imp.Name.Name
			case names[p] != "":
				n = names[p]
			default:
				// a package the overlay adds and that is not loaded
				// yet (its model is found in a later round): Go's
				// convention, the last path element
				n = p[strings.LastIndex(p, "/")+1:]
			}
			if n != "_" && n != "." {
				mf.imports[n] = p
			}
		}
	}
	return nil
}

// A decl is one declaration of the real package or of the model: a function
// or method, or one spec of a type or var declaration.
type decl struct {
	name string
	kind string // func, method, init, type, var, const
	file int
	fn   *ast.FuncDecl
	gen  *ast.GenDecl
	spec ast.Spec
	// for an init function of the model: the init.N it replaces (if
	// marked) and the first line of the real body the marker quotes
	replaces  string
	firstLine string
}

// the range of the declaration that is deleted (real) or copied (model)
func (d *decl) span(model bool) (token.Pos, token.Pos) {
	if d.fn != nil {
		start := d.fn.Pos()
		if d.fn.Doc != nil {
			start = d.fn.Doc.Pos()
		}
		return start, d.fn.End()
	}
	if model {
		return d.spec.Pos(), d.spec.End()
	}
	if !d.gen.Lparen.IsValid() {
		start := d.gen.Pos()
		if d.gen.Doc != nil {
			start = d.gen.Doc.Pos()
		}
		return start, d.gen.End()
	}
	start, end := d.spec.Pos(), d.spec.End()
	var doc, comment *ast.CommentGroup
	switch s := d.spec.(type) {
	case *ast.TypeSpec:
		doc, comment = s.Doc, s.Comment
	case *ast.ValueSpec:
		doc, comment = s.Doc, s.Comment
	}
	if doc != nil {
		start = doc.Pos()
	}
	if comment != nil {
		end = comment.End()
	}
	return start, end
}

func (d *decl) specNames() []string {
	if vs, ok := d.spec.(*ast.ValueSpec); ok {
		var ns []string
		for _, n := range vs.Names {
			ns = append(ns, n.Name)
		}
		return ns
	}
	return []string{d.name}
}

// collectDecls returns the declarations of files, by name (a var spec of
// several names under each), in order. Init functions are numbered init.N
// in order; with model set, an init function is numbered only by its
// marker (unmarked ones are additions and get no name).
func collectDecls(files []*ast.File, model bool) (map[string]*decl, []*decl, []error) {
	byName := make(map[string]*decl)
	var all []*decl
	var errs []error
	inits := 0
	markers := make(map[string]bool)
	for i, f := range files {
		for _, d := range f.Decls {
			switch d := d.(type) {
			case *ast.FuncDecl:
				x := &decl{name: funcDeclName(d), kind: "func", file: i, fn: d}
				if d.Recv != nil {
					x.kind = "method"
				} else if d.Name.Name == "init" {
					x.kind = "init"
					if model {
						x.name = ""
						if d.Doc != nil {
							for _, c := range d.Doc.List {
								rest, ok := strings.CutPrefix(c.Text, replaceDirective)
								if !ok {
									continue
								}
								name, quoted, _ := strings.Cut(strings.TrimSpace(rest), " ")
								line, err := strconv.Unquote(strings.TrimSpace(quoted))
								if err != nil || !strings.HasPrefix(name, "init.") {
									errs = append(errs, errors.Errorf("%s: want %sinit.N \"<first line of the real body>\"",
										c.Text, replaceDirective))
									continue
								}
								if markers[name] {
									errs = append(errs, errors.Errorf("%s: a second model init marked as replacing %s", c.Text, name))
								}
								markers[name] = true
								x.name, x.replaces, x.firstLine = name, name, line
							}
						}
					} else {
						x.name = fmt.Sprintf("init.%d", inits)
						inits++
					}
				} else if d.Name.Name == "_" {
					continue
				}
				all = append(all, x)
				if x.name != "" {
					byName[x.name] = x
				}
			case *ast.GenDecl:
				if d.Tok == token.IMPORT {
					continue
				}
				for _, s := range d.Specs {
					x := &decl{file: i, gen: d, spec: s}
					switch s := s.(type) {
					case *ast.TypeSpec:
						x.name, x.kind = s.Name.Name, "type"
						all = append(all, x)
						byName[x.name] = x
					case *ast.ValueSpec:
						x.kind = "var"
						if d.Tok == token.CONST {
							x.kind = "const"
						}
						all = append(all, x)
						for _, n := range s.Names {
							if n.Name != "_" {
								x.name = n.Name
								byName[n.Name] = x
							}
						}
					}
				}
			}
		}
	}
	return byName, all, errs
}

// An edit replaces [start, end) of a file's source.
type edit struct {
	start, end int
	text       string
}

func applyEdits(src []byte, edits []edit) ([]byte, error) {
	sort.SliceStable(edits, func(i, j int) bool { return edits[i].start < edits[j].start })
	var out bytes.Buffer
	at := 0
	for _, e := range edits {
		if e.start < at {
			return nil, errors.New("overlapping edits")
		}
		out.Write(src[at:e.start])
		out.WriteString(e.text)
		at = e.end
	}
	out.Write(src[at:])
	return out.Bytes(), nil
}

func lineDirective(fset *token.FileSet, file string, p token.Pos) string {
	pos := fset.PositionFor(p, false)
	return fmt.Sprintf("//line %s:%d:%d", file, pos.Line, pos.Column)
}

func offset(fset *token.FileSet, p token.Pos) int {
	return fset.File(p).Offset(p)
}

// usedImports returns the local import names that the identifiers under the
// nodes refer to, syntactically: an unresolved identifier (ast.Ident.Obj nil)
// that is the operand of a selector and an import name of the file.
func usedImports(nodes []ast.Node, imports map[string]string) map[string]bool {
	used := make(map[string]bool)
	for _, n := range nodes {
		ast.Inspect(n, func(n ast.Node) bool {
			if s, ok := n.(*ast.SelectorExpr); ok {
				if id, ok := s.X.(*ast.Ident); ok && id.Obj == nil {
					if _, ok := imports[id.Name]; ok {
						used[id.Name] = true
					}
				}
			}
			return true
		})
	}
	return used
}

// blankImports returns the edits that make the imports of f whose names are
// not in used blank (`_`), so the package keeps its imports.
func blankImports(fset *token.FileSet, f *ast.File, name func(*ast.ImportSpec) string, used map[string]bool) []edit {
	var edits []edit
	for _, imp := range f.Imports {
		n := name(imp)
		if n == "" || n == "_" || n == "." || used[n] {
			continue
		}
		if imp.Name == nil {
			at := offset(fset, imp.Path.Pos())
			edits = append(edits, edit{at, at, "_ "})
		} else {
			start, end := offset(fset, imp.Name.Pos()), offset(fset, imp.Name.End())
			edits = append(edits, edit{start, end, "_" + strings.Repeat(" ", end-start-1)})
		}
	}
	return edits
}

func (b *builder) splicePackage(pm *PackageModel, pkg *packages.Package) []error {
	mfs, errs := b.readModel(pm)
	if len(errs) > 0 {
		return errs
	}
	if err := b.importNames(mfs); err != nil {
		return []error{err}
	}
	whole := pm.Config.WholePackage()
	missing := pkg == nil || (len(pkg.GoFiles) == 0 && len(pkg.Errors) > 0)
	var pkgDir, pkgName string
	if missing {
		if !whole || !isStdPath(pm.PkgPath) {
			msg := "the package does not exist"
			if pkg != nil {
				msg = fmt.Sprint(pkg.Errors)
			}
			return []error{errors.Errorf("%s (only a whole-package model, replaces = [\"*\"], "+
				"of a standard-library path may add a package)", msg)}
		}
		goroot, err := b.goroot()
		if err != nil {
			return []error{err}
		}
		pm.Added = true
		pkgDir = filepath.Join(goroot, "src", filepath.FromSlash(pm.PkgPath))
		pkgName = mfs[0].file.Name.Name
	} else {
		if len(pkg.Errors) > 0 {
			return []error{errors.Errorf("the real package does not load: %v", pkg.Errors)}
		}
		if !slices.Equal(pkg.GoFiles, pkg.CompiledGoFiles) {
			return []error{errors.New("the real package uses cgo")}
		}
		b.real[pm.PkgPath] = pkg
		pkgDir = filepath.Dir(pkg.GoFiles[0])
		pkgName = pkg.Name
		for _, f := range pkg.GoFiles {
			if strings.HasPrefix(filepath.Base(f), ModelFilePrefix) {
				errs = append(errs, errors.Errorf("%s: a real file named %s*", f, ModelFilePrefix))
			}
		}
	}
	for _, mf := range mfs {
		if mf.file.Name.Name != pkgName {
			errs = append(errs, errors.Errorf("%s: package %s, not the real package's %s",
				mf.path, mf.file.Name.Name, pkgName))
		}
	}
	if len(errs) > 0 {
		return errs
	}
	ov := b.models.Overlay
	if whole {
		if !missing {
			for _, f := range pkg.GoFiles {
				ov[f] = []byte("package " + pkgName + "\n")
			}
		}
		for _, mf := range mfs {
			ov[filepath.Join(pkgDir, ModelFilePrefix+filepath.Base(mf.path))] =
				append([]byte(fmt.Sprintf("//line %s:1:1\n", mf.path)), mf.src...)
		}
		return nil
	}

	var modelASTs []*ast.File
	for _, mf := range mfs {
		modelASTs = append(modelASTs, mf.file)
	}
	realDecls, _, _ := collectDecls(pkg.Syntax, false)
	modelDecls, modelAll, es := collectDecls(modelASTs, true)
	errs = append(errs, es...)

	// replaces, both ways, and shadowing
	replaced := make(map[string]bool)
	for _, n := range pm.Config.Replaces {
		replaced[n] = true
		r, m := realDecls[n], modelDecls[n]
		switch {
		case r == nil:
			errs = append(errs, errors.Errorf("replaces %q: not a declaration of the real package", n))
		case r.kind == "const":
			errs = append(errs, errors.Errorf("replaces %q: a constant cannot be replaced", n))
		case m == nil:
			errs = append(errs, errors.Errorf("replaces %q: the model does not declare it", n))
		case m.kind != r.kind:
			errs = append(errs, errors.Errorf("replaces %q: a %s, which the model declares as a %s", n, r.kind, m.kind))
		case r.kind == "var" && !slices.Equal(r.specNames(), m.specNames()):
			errs = append(errs, errors.Errorf("replaces %q: the real package declares %s in one spec, the model %s",
				n, strings.Join(r.specNames(), ", "), strings.Join(m.specNames(), ", ")))
		case r.kind == "init":
			if got := firstBodyLine(pkg.Fset, b, r.fn); got != m.firstLine {
				errs = append(errs, errors.Errorf("replaces %q: its first line is %q, the marker says %q "+
					"(did a Go upgrade renumber the package's init functions?)", n, got, m.firstLine))
			}
		}
	}
	for _, rn := range pm.Config.Replaces {
		if r := realDecls[rn]; r != nil && r.kind == "var" {
			for _, n := range r.specNames() {
				if !replaced[n] && n != "_" {
					errs = append(errs, errors.Errorf("replaces %q but not %q, declared in the same spec", rn, n))
				}
			}
		}
	}
	for _, m := range modelAll {
		for _, n := range m.specNames() {
			if n == "" || n == "_" {
				continue
			}
			if m.kind == "init" && !replaced[n] {
				errs = append(errs, errors.Errorf("%s: the model's init is marked as replacing %s, "+
					"which replaces does not list", mfs[m.file].path, n))
				continue
			}
			if realDecls[n] != nil && !replaced[n] {
				errs = append(errs, errors.Errorf("the model declares %q, a real declaration that replaces does not list", n))
			}
			if m.kind != "method" && realDecls[n] == nil && types.Universe.Lookup(n) != nil {
				errs = append(errs, errors.Errorf("the model declares %q, a predeclared identifier "+
					"(it would change the meaning of the real code)", n))
			}
		}
	}
	if len(errs) > 0 {
		return errs
	}

	// the splice into each real file
	type fileEdits struct {
		edits   []edit
		deleted []*decl
		// inserted model declarations
		inserted []*decl
	}
	perFile := make(map[int]*fileEdits)
	modelReplaced := make(map[*decl]bool)
	for _, n := range pm.Config.Replaces {
		r, m := realDecls[n], modelDecls[n]
		if modelReplaced[m] {
			continue // a var spec of several names
		}
		modelReplaced[m] = true
		fe := perFile[r.file]
		if fe == nil {
			fe = &fileEdits{}
			perFile[r.file] = fe
		}
		mf := mfs[m.file]
		rs, re := r.span(false)
		ms, me := m.span(true)
		realPath := pkg.CompiledGoFiles[r.file]
		text := ""
		if r.fn == nil && !r.gen.Lparen.IsValid() {
			text = r.gen.Tok.String()
		}
		text += "\n" + lineDirective(mf.fset, mf.path, ms) + "\n" +
			string(mf.src[offset(mf.fset, ms):offset(mf.fset, me)]) + "\n" +
			lineDirective(pkg.Fset, realPath, re) + "\n"
		fe.edits = append(fe.edits, edit{offset(pkg.Fset, rs), offset(pkg.Fset, re), text})
		fe.deleted = append(fe.deleted, r)
		fe.inserted = append(fe.inserted, m)
	}
	for i, fe := range perFile {
		f := pkg.Syntax[i]
		realPath := pkg.CompiledGoFiles[i]
		src, err := b.source(realPath)
		if err != nil {
			return []error{err}
		}
		deleted := make(map[ast.Node]bool)
		var spans [][2]int
		for _, d := range fe.deleted {
			s, e := d.span(false)
			spans = append(spans, [2]int{offset(pkg.Fset, s), offset(pkg.Fset, e)})
			if d.fn != nil {
				deleted[d.fn] = true
			} else {
				deleted[d.spec] = true
			}
		}
		inSpan := func(p token.Pos) bool {
			o := offset(pkg.Fset, p)
			for _, s := range spans {
				if s[0] <= o && o < s[1] {
					return true
				}
			}
			return false
		}
		// the //go:linkname directives of the deleted declarations
		names := make(map[string]bool)
		for _, d := range fe.deleted {
			if d.fn != nil && d.fn.Recv == nil {
				names[d.fn.Name.Name] = true
			} else if d.kind == "var" {
				for _, n := range d.specNames() {
					names[n] = true
				}
			}
		}
		for _, cg := range f.Comments {
			for _, c := range cg.List {
				fields := strings.Fields(c.Text)
				if len(fields) >= 2 && fields[0] == "//go:linkname" && names[fields[1]] && !inSpan(c.Pos()) {
					s, e := offset(pkg.Fset, c.Pos()), offset(pkg.Fset, c.End())
					fe.edits = append(fe.edits, edit{s, e, strings.Repeat(" ", e-s)})
				}
			}
		}
		// the imports the remaining real code uses (by type information)
		used := make(map[string]bool)
		ast.Inspect(f, func(n ast.Node) bool {
			if n == nil || deleted[n] {
				return false
			}
			if id, ok := n.(*ast.Ident); ok {
				if pn, ok := pkg.TypesInfo.Uses[id].(*types.PkgName); ok {
					used[pn.Name()] = true
				}
			}
			return true
		})
		realName := func(imp *ast.ImportSpec) string {
			if imp.Name != nil {
				return imp.Name.Name
			}
			if pn, ok := pkg.TypesInfo.Implicits[imp].(*types.PkgName); ok {
				return pn.Name()
			}
			return ""
		}
		realImports := make(map[string]string)
		for _, imp := range f.Imports {
			if n := realName(imp); n != "" && n != "_" && n != "." {
				p, _ := strconv.Unquote(imp.Path.Value)
				realImports[n] = p
			}
		}
		// the imports the inserted model code uses
		added := make(map[string]string)
		for _, m := range fe.inserted {
			mf := mfs[m.file]
			var node ast.Node = m.spec
			if m.fn != nil {
				node = m.fn
			}
			for n := range usedImports([]ast.Node{node}, mf.imports) {
				p := mf.imports[n]
				if rp, ok := realImports[n]; ok {
					if rp != p {
						errs = append(errs, errors.Errorf("%s: the model's %s uses %s for %q, which %s imports as %q",
							mf.path, m.name, n, p, filepath.Base(realPath), rp))
					}
					used[n] = true
					continue
				}
				if types.Universe.Lookup(n) != nil {
					errs = append(errs, errors.Errorf("%s: the model's %s imports %q as %s, a predeclared identifier",
						mf.path, m.name, p, n))
				}
				if ap, ok := added[n]; ok && ap != p {
					errs = append(errs, errors.Errorf("%s: the models spliced into %s use %s for both %q and %q",
						mf.path, filepath.Base(realPath), n, ap, p))
				}
				added[n] = p
			}
		}
		fe.edits = append(fe.edits, blankImports(pkg.Fset, f, realName, used)...)
		var addedNames []string
		for n := range added {
			addedNames = append(addedNames, n)
		}
		sort.Strings(addedNames)
		at := offset(pkg.Fset, f.Name.End())
		for _, n := range addedNames {
			fe.edits = append(fe.edits, edit{at, at, fmt.Sprintf("; import %s %q", n, added[n])})
		}
		out, err := applyEdits(src, fe.edits)
		if err != nil {
			return []error{errors.Wrap(err, realPath)}
		}
		b.models.Overlay[realPath] = out
	}
	if len(errs) > 0 {
		return errs
	}

	// the additions of each model file
	for i, mf := range mfs {
		var keep []ast.Node
		var blank [][2]int
		hasAddition := false
		for _, d := range mf.file.Decls {
			gd, ok := d.(*ast.GenDecl)
			if ok && gd.Tok == token.IMPORT {
				continue
			}
			if fd, ok := d.(*ast.FuncDecl); ok {
				x := findDecl(modelAll, i, fd, nil)
				if modelReplaced[x] {
					s, e := x.span(true)
					if fd.Doc != nil {
						s = fd.Doc.Pos()
					}
					blank = append(blank, [2]int{offset(mf.fset, s), offset(mf.fset, e)})
				} else {
					keep = append(keep, fd)
					hasAddition = true
				}
				continue
			}
			allReplaced, anyReplaced := true, false
			for _, s := range gd.Specs {
				if modelReplaced[findDecl(modelAll, i, nil, s)] {
					anyReplaced = true
				} else {
					allReplaced = false
				}
			}
			switch {
			case !anyReplaced:
				keep = append(keep, gd)
				hasAddition = true
			case allReplaced:
				s := gd.Pos()
				if gd.Doc != nil {
					s = gd.Doc.Pos()
				}
				blank = append(blank, [2]int{offset(mf.fset, s), offset(mf.fset, gd.End())})
			default:
				for _, s := range gd.Specs {
					if x := findDecl(modelAll, i, nil, s); modelReplaced[x] {
						blank = append(blank, [2]int{offset(mf.fset, s.Pos()), offset(mf.fset, s.End())})
					} else {
						keep = append(keep, s)
						hasAddition = true
					}
				}
			}
		}
		if !hasAddition {
			continue
		}
		src := slices.Clone(mf.src)
		for _, s := range blank {
			for j := s[0]; j < s[1]; j++ {
				if src[j] != '\n' {
					src[j] = ' '
				}
			}
		}
		used := usedImports(keep, mf.imports)
		edits := blankImports(mf.fset, mf.file, func(imp *ast.ImportSpec) string {
			if imp.Name != nil {
				return imp.Name.Name
			}
			p, _ := strconv.Unquote(imp.Path.Value)
			for n, q := range mf.imports {
				if q == p {
					return n
				}
			}
			return ""
		}, used)
		out, err := applyEdits(src, edits)
		if err != nil {
			return []error{errors.Wrap(err, mf.path)}
		}
		ov[filepath.Join(pkgDir, ModelFilePrefix+filepath.Base(mf.path))] =
			append([]byte(fmt.Sprintf("//line %s:1:1\n", mf.path)), out...)
	}
	return nil
}

func findDecl(all []*decl, file int, fn *ast.FuncDecl, spec ast.Spec) *decl {
	for _, d := range all {
		if d.file == file && ((fn != nil && d.fn == fn) || (spec != nil && d.spec == spec)) {
			return d
		}
	}
	return nil
}

// firstBodyLine is the first line of an init function's body: the text of
// its first statement up to the end of its line (trimmed), empty for an
// empty body.
func firstBodyLine(fset *token.FileSet, b *builder, fn *ast.FuncDecl) string {
	if fn.Body == nil || len(fn.Body.List) == 0 {
		return ""
	}
	st := fn.Body.List[0]
	src, err := b.source(fset.PositionFor(st.Pos(), false).Filename)
	if err != nil {
		return ""
	}
	start, end := offset(fset, st.Pos()), offset(fset, st.End())
	if nl := bytes.IndexByte(src[start:end], '\n'); nl >= 0 {
		end = start + nl
	}
	return strings.TrimSpace(string(src[start:end]))
}

// check type-checks the overlaid model packages, checks that each
// names_only entry matches a model declaration, and checks their API
// against the real packages' (CheckAPI).
func (b *builder) check() error {
	merged, err := b.models.merge(b.opts)
	if err != nil {
		return err
	}
	var paths []string
	for p := range b.models.Packages {
		paths = append(paths, p)
	}
	sort.Strings(paths)
	pkgs, err := packages.Load(b.pkgConfig(packages.NeedName|packages.NeedTypes|packages.NeedSyntax|
		packages.NeedTypesInfo|packages.NeedFiles, merged), paths...)
	if err != nil {
		return err
	}
	var errs ModelErrors
	for _, p := range pkgs {
		if pm := b.models.Packages[p.PkgPath]; pm != nil && pm.Added && len(p.GoFiles) == 0 {
			errs = append(errs, errors.Errorf("model of %s: the Go toolchain does not accept a "+
				"standard-library package added by an overlay (%v); go1.26.0's go list, which "+
				"go/packages runs, finds one only when its overlay files are over 2s old, "+
				"and go1.26.11 and go1.27 accept it", p.PkgPath, p.Errors))
			continue
		}
		if len(p.Errors) > 0 {
			for _, e := range p.Errors {
				errs = append(errs, errors.Errorf("model of %s: %v", p.PkgPath, e))
			}
			continue
		}
		pm := b.models.Packages[p.PkgPath]
		if pm != nil {
			names := modelDeclNames(p, b.models.modelFiles)
			for _, e := range pm.Config.NamesOnly {
				if strings.HasPrefix(e, "!") {
					continue
				}
				matched := false
				for n := range names {
					matched = matched || declfilter.MatchesAny([]string{e}, n)
				}
				if !matched {
					errs = append(errs, errors.Errorf("model of %s: names_only %q matches no model declaration",
						p.PkgPath, e))
				}
			}
		}
		real := b.real[p.PkgPath]
		if pm == nil || real == nil {
			continue
		}
		for _, e := range CheckAPI(real.Types, p.Types, pm.Config) {
			errs = append(errs, errors.Wrapf(e, "model of %s", p.PkgPath))
		}
	}
	if len(errs) > 0 {
		return errs
	}
	return nil
}

func typeString(t types.Type) string {
	return types.TypeString(t, func(p *types.Package) string { return p.Path() })
}

// CheckAPI checks that the overlaid package over keeps the API of the real
// package real (D5): a replaced function, method or variable has an
// identical type (printed with package paths, so type parameters keep their
// names too); a replaced type keeps its exported fields (names, order,
// types, embedding and tags, and the exported fields its embedded fields
// promote), and an exported one also its kind (alias or defined, struct or
// not), its underlying type if it is not a struct, and its comparability;
// every named type of the real package keeps its method sets (of T and *T),
// gaining only methods that added_methods lists, and every pattern there
// matches an added method. For a whole-package model the checks are on the
// names the model declares, and the methods of the real package it does not
// declare may be missing.
func CheckAPI(real, over *types.Package, config declfilter.ModelConfig) []error {
	var errs []error
	whole := config.WholePackage()
	replaced := make(map[string]bool)
	for _, n := range config.Replaces {
		replaced[n] = true
	}
	rs, ovs := real.Scope(), over.Scope()
	for _, name := range rs.Names() {
		r := rs.Lookup(name)
		o := ovs.Lookup(name)
		if !whole && !replaced[name] {
			if _, isType := r.(*types.TypeName); !isType {
				continue
			}
		}
		if o == nil {
			if !whole {
				errs = append(errs, errors.Errorf("%s: missing from the model", name))
			}
			continue
		}
		if fmt.Sprintf("%T", r) != fmt.Sprintf("%T", o) {
			errs = append(errs, errors.Errorf("%s: a %s, which the model declares as a %s",
				name, objKind(r), objKind(o)))
			continue
		}
		switch r := r.(type) {
		case *types.Func, *types.Var:
			if typeString(r.Type()) != typeString(o.Type()) {
				errs = append(errs, errors.Errorf("%s: type %s, which the model changes to %s",
					name, typeString(r.Type()), typeString(o.Type())))
			}
		case *types.Const:
			if whole && r.Exported() && (typeString(r.Type()) != typeString(o.Type()) ||
				r.Val().ExactString() != o.(*types.Const).Val().ExactString()) {
				errs = append(errs, errors.Errorf("%s: the constant %s, which the model changes", name, r.Val()))
			}
		case *types.TypeName:
			if whole || replaced[name] {
				errs = append(errs, checkType(name, r, o.(*types.TypeName))...)
			} else if !r.IsAlias() {
				// a replaced type it embeds or contains may change what it
				// promotes and whether it is comparable
				ot := o.(*types.TypeName).Type()
				if types.Comparable(r.Type()) != types.Comparable(ot) {
					errs = append(errs, errors.Errorf("%s: the model changes whether it is comparable", name))
				}
				if rf, of := exportedFields(r.Type()), exportedFields(ot); !slices.Equal(rf, of) {
					errs = append(errs, errors.Errorf("%s: exported and embedded fields %v, which the model changes to %v",
						name, rf, of))
				}
			}
			errs = append(errs, checkMethods(name, r, o.(*types.TypeName), config, whole)...)
		}
	}
	// replaced methods
	for _, n := range config.Replaces {
		t, m, ok := strings.Cut(n, ".")
		if !ok || strings.HasPrefix(n, "init.") {
			continue
		}
		rt, _ := rs.Lookup(t).(*types.TypeName)
		ot, _ := ovs.Lookup(t).(*types.TypeName)
		if rt == nil || ot == nil {
			continue
		}
		rm, om := method(rt, m), method(ot, m)
		if rm == nil || om == nil {
			continue
		}
		rr, or := typeString(rm.Signature().Recv().Type()), typeString(om.Signature().Recv().Type())
		if rr != or || typeString(rm.Type()) != typeString(om.Type()) {
			errs = append(errs, errors.Errorf("%s: (%s) %s, which the model changes to (%s) %s",
				n, rr, typeString(rm.Type()), or, typeString(om.Type())))
		}
	}
	for _, p := range config.AddedMethods {
		if !addedMethodPatternUsed(p, real, over) {
			errs = append(errs, errors.Errorf("added_methods %q matches no method the model adds", p))
		}
	}
	return errs
}

func objKind(o types.Object) string {
	switch o.(type) {
	case *types.Func:
		return "function"
	case *types.Var:
		return "variable"
	case *types.Const:
		return "constant"
	case *types.TypeName:
		return "type"
	}
	return "declaration"
}

func method(t *types.TypeName, name string) *types.Func {
	if n, ok := t.Type().(*types.Named); ok {
		for i := range n.NumMethods() {
			if n.Method(i).Name() == name {
				return n.Method(i)
			}
		}
	}
	return nil
}

func typeParams(t types.Type) string {
	n, ok := t.(*types.Named)
	if !ok || n.TypeParams().Len() == 0 {
		return ""
	}
	var s []string
	for i := range n.TypeParams().Len() {
		tp := n.TypeParams().At(i)
		s = append(s, tp.Obj().Name()+" "+typeString(tp.Constraint()))
	}
	return "[" + strings.Join(s, ", ") + "]"
}

func checkType(name string, r, o *types.TypeName) []error {
	var errs []error
	{
		if r.IsAlias() != o.IsAlias() {
			return []error{errors.Errorf("%s: the model changes whether it is an alias", name)}
		}
		if r.IsAlias() {
			if typeString(types.Unalias(r.Type())) != typeString(types.Unalias(o.Type())) {
				errs = append(errs, errors.Errorf("%s: the model changes the aliased type", name))
			}
			return errs
		}
		if typeParams(r.Type()) != typeParams(o.Type()) {
			errs = append(errs, errors.Errorf("%s: type parameters %s, which the model changes to %s",
				name, typeParams(r.Type()), typeParams(o.Type())))
		}
		_, rStruct := r.Type().Underlying().(*types.Struct)
		_, oStruct := o.Type().Underlying().(*types.Struct)
		switch {
		case rStruct != oStruct:
			errs = append(errs, errors.Errorf("%s: the model changes whether it is a struct", name))
		case !rStruct && typeString(r.Type().Underlying()) != typeString(o.Type().Underlying()):
			errs = append(errs, errors.Errorf("%s: underlying type %s, which the model changes to %s",
				name, typeString(r.Type().Underlying()), typeString(o.Type().Underlying())))
		}
		if types.Comparable(r.Type()) != types.Comparable(o.Type()) {
			errs = append(errs, errors.Errorf("%s: the model changes whether it is comparable", name))
		}
	}
	rf, of := exportedFields(r.Type()), exportedFields(o.Type())
	if !slices.Equal(rf, of) {
		errs = append(errs, errors.Errorf("%s: exported fields %v, which the model changes to %v "+
			"(only unexported fields may change)", name, rf, of))
	}
	return errs
}

// exportedFields describes the exported fields of a struct type: the direct
// ones in order (with type, embedding and tag), then the exported fields
// promoted through embedded fields (by depth, sorted by name).
func exportedFields(t types.Type) []string {
	st, ok := t.Underlying().(*types.Struct)
	if !ok {
		return nil
	}
	var out []string
	for i := range st.NumFields() {
		f := st.Field(i)
		if f.Exported() || f.Embedded() {
			out = append(out, fmt.Sprintf("%s %s embedded=%v tag=%q", f.Name(), typeString(f.Type()),
				f.Embedded(), st.Tag(i)))
		}
	}
	seen := make(map[string]bool)
	for i := range st.NumFields() {
		seen[st.Field(i).Name()] = true
	}
	level := []*types.Struct{st}
	visited := make(map[types.Type]bool)
	for depth := 1; depth < 8 && len(level) > 0; depth++ {
		var next []*types.Struct
		count := make(map[string]int)
		desc := make(map[string]string)
		for _, s := range level {
			for i := range s.NumFields() {
				f := s.Field(i)
				if !f.Embedded() {
					continue
				}
				ft := f.Type()
				if p, ok := ft.(*types.Pointer); ok {
					ft = p.Elem()
				}
				if visited[ft] {
					continue
				}
				visited[ft] = true
				es, ok := ft.Underlying().(*types.Struct)
				if !ok {
					continue
				}
				next = append(next, es)
				for j := range es.NumFields() {
					g := es.Field(j)
					if !seen[g.Name()] {
						count[g.Name()]++
						desc[g.Name()] = typeString(g.Type())
					}
				}
			}
		}
		var names []string
		for n, c := range count {
			seen[n] = true
			if c == 1 && token.IsExported(n) {
				names = append(names, n)
			}
		}
		sort.Strings(names)
		for _, n := range names {
			out = append(out, fmt.Sprintf("%s %s promoted", n, desc[n]))
		}
		level = next
	}
	return out
}

func methodSet(t types.Type) map[string]string {
	ms := make(map[string]string)
	set := types.NewMethodSet(t)
	for i := range set.Len() {
		sel := set.At(i)
		f := sel.Obj().(*types.Func)
		recv := ""
		if r := f.Signature().Recv(); r != nil {
			recv = typeString(r.Type())
		}
		ms[f.Name()] = fmt.Sprintf("%s (declared on %s, at embedding path %v)", typeString(f.Type()), recv, sel.Index())
	}
	return ms
}

func checkMethods(name string, r, o *types.TypeName, config declfilter.ModelConfig, whole bool) []error {
	if r.IsAlias() || o.IsAlias() {
		return nil
	}
	var errs []error
	for _, ptr := range []bool{false, true} {
		rt, ot := r.Type(), o.Type()
		recv := name
		if ptr {
			if types.IsInterface(rt) {
				continue
			}
			rt, ot = types.NewPointer(rt), types.NewPointer(ot)
			recv = "*" + name
		}
		rm, om := methodSet(rt), methodSet(ot)
		var names []string
		for n := range rm {
			names = append(names, n)
		}
		for n := range om {
			if _, ok := rm[n]; !ok {
				names = append(names, n)
			}
		}
		sort.Strings(names)
		for _, n := range names {
			rs, inR := rm[n]
			ovsig, inO := om[n]
			switch {
			case inR && !inO:
				if !whole {
					errs = append(errs, errors.Errorf("%s: the model removes the method %s from %s", name, n, recv))
				}
			case !inR && inO:
				if (!whole || token.IsExported(n)) && !declfilter.MatchesAny(config.AddedMethods, name+"."+n) {
					errs = append(errs, errors.Errorf("%s: the model adds the method %s to %s, "+
						"which added_methods does not list", name, n, recv))
				}
			case rs != ovsig:
				errs = append(errs, errors.Errorf("%s: method %s of %s has type %s, which the model changes to %s",
					name, n, recv, rs, ovsig))
			}
		}
	}
	return errs
}

// addedMethodPatternUsed says whether some method of a named type of the
// real package that the model adds matches the pattern.
func addedMethodPatternUsed(pattern string, real, over *types.Package) bool {
	for _, name := range real.Scope().Names() {
		r, ok := real.Scope().Lookup(name).(*types.TypeName)
		if !ok || r.IsAlias() {
			continue
		}
		o, ok := over.Scope().Lookup(name).(*types.TypeName)
		if !ok || o.IsAlias() {
			continue
		}
		rm := methodSet(types.NewPointer(r.Type()))
		if types.IsInterface(r.Type()) {
			rm = methodSet(r.Type())
		}
		om := methodSet(types.NewPointer(o.Type()))
		if types.IsInterface(o.Type()) {
			om = methodSet(o.Type())
		}
		for n := range om {
			if _, ok := rm[n]; !ok && declfilter.MatchesAny([]string{pattern}, name+"."+n) {
				return true
			}
		}
	}
	return false
}
