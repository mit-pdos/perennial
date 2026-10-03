package tmpl

import (
	"embed"

	"github.com/mit-pdos/perennial/goose/glang"
	"io"
	"strings"
	"text/template"

	"github.com/pkg/errors"
)

// PackageProof is the data that is passed to the top-level package_proof.v.tmpl
// template.
type PackageProof struct {
	Lean          bool
	FfiPrelude    string
	Name          string
	Ffi           string
	Bootstrap     bool
	ImportPath    string // import path (corresponding to Go PkgPath)
	HasTrusted    bool
	TrustProofGen bool
	Imports       []Import
	Types         []TypeDecl
	// Lean modules to import in addition (chunks of the package's proofs)
	ExtraImports []string
}

type TypeDecl struct {
	PkgName    string
	Name       string
	TypeParams []string
	Fields     []string
	Axiomatize bool

	// Lean backend only
	RawName    string
	ImplName   string
	LeanFields []LeanField
}

// LeanField is a struct field, for the Lean templates.
type LeanField struct {
	// Go field name (or _i for _)
	Name string
	// record projection (quoted if needed)
	Proj string
	// go_string literal for the field name
	GoString string
	// Lean type of the field
	Type string
	// name of the conjunct in typed_pointsto_def
	HypName string
}

type Import struct {
	Name string
	Path string
}

type Variable struct {
	Name    string
	CoqType string
}

type MethodSet struct {
	// a named type
	TypeName string
	TypeId   string
	Methods  []string
}

func indent(n int) string {
	return strings.Repeat(" ", n)
}

//go:embed *.tmpl
var tmplFS embed.FS

// loadTemplates is used once to parse the templates. This happens statically,
// using the embed package to get the template files from the source code.
func loadTemplates() *template.Template {
	tmpl := template.New("proofgen")
	funcs := template.FuncMap{
		"indent": indent,
		"leanq":  leanq,
		"trimgo": func(s string) string { return strings.TrimPrefix(s, "go!") },
	}
	tmpl, err := tmpl.Funcs(funcs).ParseFS(tmplFS, "*.tmpl")
	if err != nil {
		panic(errors.Wrap(err, "internal error: templates does not parse"))
	}
	return tmpl
}

var templates *template.Template = loadTemplates()

func (pf PackageProof) Write(w io.Writer) error {
	name := "package_proof.v.tmpl"
	if pf.Lean {
		name = "package_proof.lean.tmpl"
	}
	if err := templates.ExecuteTemplate(w, name, pf); err != nil {
		return errors.Wrap(err, "could not emit template")
	}
	return nil
}

func leanq(s string) string {
	return glang.LeanQuoteComponent(s)
}
