package tmpl

import (
	"embed"
	"io"
	"strings"
	"text/template"

	"github.com/pkg/errors"
)

// PackageProof is the data that is passed to the top-level package_proof.v.tmpl
// template.
type PackageProof struct {
	Name          string
	Ffi           string
	Bootstrap     bool
	ImportPath    string // import path (corresponding to Go PkgPath)
	HasTrusted    bool
	TrustProofGen bool
	Imports       []Import
	Types         []TypeDecl
}

type TypeDecl struct {
	PkgName    string
	Name       string
	TypeParams []string
	Fields     []string
	Axiomatize bool
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
	}
	tmpl, err := tmpl.Funcs(funcs).ParseFS(tmplFS, "*.tmpl")
	if err != nil {
		panic(errors.Wrap(err, "internal error: templates does not parse"))
	}
	return tmpl
}

var templates *template.Template = loadTemplates()

func (pf PackageProof) Write(w io.Writer) error {
	if err := templates.ExecuteTemplate(w, "package_proof.v.tmpl", pf); err != nil {
		return errors.Wrap(err, "could not emit template")
	}
	return nil
}
