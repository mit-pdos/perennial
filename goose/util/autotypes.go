package util

import (
	"fmt"
	"go/ast"
	"go/token"
	"go/types"
	"os"
	"sort"
	"strings"
	"sync"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"golang.org/x/tools/go/packages"
)

// typeTranslatability determines whether the definition of a named type can
// be translated, given the set of imported packages. It returns the reasons
// it cannot (nil if it can).
type typeTranslatability struct {
	pkgPath  string
	imported map[string]bool
	reasons  map[string]bool
	// same-package aliases referred to
	aliasDeps map[string]bool
}

func (c *typeTranslatability) fail(format string, args ...any) {
	c.reasons[fmt.Sprintf(format, args...)] = true
}

// check walks t. byValue is true if t appears in a position where goose needs
// a Lean/Gallina type modeling its values (a struct field, an array element,
// a type argument, or the underlying type of a non-struct named type), and
// false where only its go.type is needed (under a pointer, slice, map,
// channel, function or interface).
func (c *typeTranslatability) check(t types.Type, byValue bool, top bool) {
	switch t := t.(type) {
	case *types.Basic:
		switch t.Name() {
		case "uint64", "int64", "uint32", "int32", "uint16", "int16",
			"uint8", "int8", "byte", "uint", "int", "float64", "float32",
			"bool", "string", "Pointer":
		case "uintptr":
			// Rocq has no semantics for uintptr values
			if byValue && !glang.Lean {
				c.fail("uintptr value")
			}
		default:
			if byValue {
				c.fail("unsupported basic type %s", t.Name())
			}
		}
	case *types.Alias:
		if p := t.Obj().Pkg(); p != nil && p.Path() == c.pkgPath {
			c.aliasDeps[t.Obj().Name()] = true
		} else if p != nil {
			// we do not know if the alias is translated in its package
			c.fail("alias from another package %s", p.Path())
		}
		c.checkObj(t.Obj())
		if args := t.TypeArgs(); args != nil {
			for i := range args.Len() {
				c.check(args.At(i), byValue, false)
			}
		}
		// the translation unaliases the type (in Lean types) or refers to
		// the alias (in go.types): both need to be supported
		c.check(types.Unalias(t), byValue, false)
	case *types.Named:
		c.checkObj(t.Obj())
		for i := range t.TypeArgs().Len() {
			c.check(t.TypeArgs().At(i), byValue, false)
		}
	case *types.TypeParam:
	case *types.Pointer:
		c.check(t.Elem(), false, false)
	case *types.Slice:
		c.check(t.Elem(), false, false)
	case *types.Array:
		c.check(t.Elem(), byValue, false)
	case *types.Map:
		c.check(t.Key(), false, false)
		c.check(t.Elem(), false, false)
	case *types.Chan:
		c.check(t.Elem(), false, false)
	case *types.Signature:
		if t.TypeParams() != nil && t.TypeParams().Len() > 0 {
			c.fail("generic function type")
		}
		for _, tup := range []*types.Tuple{t.Params(), t.Results()} {
			if tup == nil {
				continue
			}
			for i := range tup.Len() {
				c.check(tup.At(i).Type(), false, false)
			}
		}
	case *types.Interface:
		for i := range t.NumExplicitMethods() {
			c.check(t.ExplicitMethod(i).Type(), false, false)
		}
		for i := range t.NumEmbeddeds() {
			em := t.EmbeddedType(i)
			if u, ok := em.(*types.Union); ok {
				for j := range u.Len() {
					c.check(u.Term(j).Type(), false, false)
				}
			} else {
				c.check(em, false, false)
			}
		}
	case *types.Struct:
		if byValue && !top && t.NumFields() > 0 {
			c.fail("anonymous struct with fields")
		}
		for i := range t.NumFields() {
			c.check(t.Field(i).Type(), true, false)
		}
	default:
		c.fail("unsupported type %T", t)
	}
}

func (c *typeTranslatability) checkObj(obj types.Object) {
	pkg := obj.Pkg()
	if pkg == nil {
		switch obj.Name() {
		case "error", "any", "comparable":
		default:
			c.fail("unsupported predeclared type %s", obj.Name())
		}
		return
	}
	if pkg.Path() == c.pkgPath {
		return
	}
	if !c.imported[pkg.Path()] {
		c.fail("needs import %s", pkg.Path())
	}
}

var typesLogMu sync.Mutex

// ExtendFilter implements the translate_types option: it returns df, extended
// to translate every type declaration that df would axiomatize when goose can
// translate its definition: it uses only supported constructs and refers only
// to the package itself, predeclared types and imported packages. Methods,
// constants and functions are unaffected.
//
// If the environment variable GOOSE_TYPES_LOG is set to a file, a line is
// appended there for every type declaration that df axiomatizes, with the
// decision (and the reasons a type cannot be translated).
func ExtendFilter(pkg *packages.Package, config declfilter.FilterConfig, df declfilter.DeclFilter) declfilter.DeclFilter {
	logFile := os.Getenv("GOOSE_TYPES_LOG")
	if !config.TranslateTypes && logFile == "" {
		return df
	}
	imported := make(map[string]bool)
	for _, f := range pkg.Syntax {
		for _, imp := range f.Imports {
			path := strings.Trim(imp.Path.Value, "\"`")
			if df.ShouldImport(path) {
				imported[path] = true
			}
		}
	}
	type entry struct {
		name      string
		kind      string
		reasons   map[string]bool
		aliasDeps map[string]bool
	}
	var entries []*entry
	aliasPos := make(map[string]int) // source order of (all) aliases
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			d, ok := d.(*ast.GenDecl)
			if !ok || d.Tok != token.TYPE {
				continue
			}
			for _, spec := range d.Specs {
				spec := spec.(*ast.TypeSpec)
				isAlias := spec.Assign != token.NoPos
				if isAlias {
					aliasPos[spec.Name.Name] = len(aliasPos)
				}
				if df.GetAction(spec.Name.Name) != declfilter.Axiomatize {
					continue
				}
				obj := pkg.TypesInfo.Defs[spec.Name]
				c := &typeTranslatability{pkgPath: pkg.PkgPath, imported: imported,
					reasons: make(map[string]bool), aliasDeps: make(map[string]bool)}
				// the definition as written: `type T other.U` refers to other.U
				def := pkg.TypesInfo.TypeOf(spec.Type)
				_, isStruct := def.(*types.Struct)
				var kind string
				if isAlias {
					kind = "Alias"
					if tps := obj.Type().(*types.Alias).TypeParams(); tps != nil && tps.Len() > 0 {
						c.fail("generic alias")
					}
				} else {
					named, ok := obj.Type().(*types.Named)
					if !ok {
						continue
					}
					kind = strings.TrimPrefix(fmt.Sprintf("%T", named.Underlying()), "*types.")
				}
				c.check(def, !isAlias, isStruct)
				if isStruct && config.TranslateTypesExceptStructs {
					c.fail("struct (translate_types_except_structs)")
				}
				if isAlias {
					for a := range c.aliasDeps {
						if aliasPos[a] >= aliasPos[spec.Name.Name] {
							c.fail("refers to a later alias %s", a)
						}
					}
				}
				entries = append(entries, &entry{name: spec.Name.Name, kind: kind,
					reasons: c.reasons, aliasDeps: c.aliasDeps})
			}
		}
	}
	// a type that refers to a same-package alias needs that alias to be
	// translated as well
	names := make(map[string]bool)
	for _, e := range entries {
		if len(e.reasons) == 0 {
			names[e.name] = true
		}
	}
	for changed := true; changed; {
		changed = false
		for _, e := range entries {
			if !names[e.name] {
				continue
			}
			for a := range e.aliasDeps {
				if !names[a] && df.GetAction(a) != declfilter.Translate {
					e.reasons["refers to axiomatized alias "+a] = true
					delete(names, e.name)
					changed = true
					break
				}
			}
		}
	}
	// Translated types are emitted in dependency order (see
	// TypeGetDependencies), so the dependencies through struct fields, arrays
	// and type arguments must be acyclic; keep any type on a cycle
	// axiomatized (e.g., a struct with a field atomic.Pointer[itself]).
	isTranslated := func(n string) bool {
		return names[n] || df.GetAction(n) == declfilter.Translate
	}
	specOf := make(map[string]*ast.TypeSpec)
	for _, f := range pkg.Syntax {
		for _, d := range f.Decls {
			if d, ok := d.(*ast.GenDecl); ok && d.Tok == token.TYPE {
				for _, spec := range d.Specs {
					spec := spec.(*ast.TypeSpec)
					specOf[spec.Name.Name] = spec
				}
			}
		}
	}
	for {
		var onCycle string
		state := make(map[string]int) // 1: on stack, 2: done
		var visit func(n string) bool
		visit = func(n string) bool {
			if !isTranslated(n) || state[n] == 2 {
				return false
			}
			if state[n] == 1 {
				onCycle = n
				return true
			}
			state[n] = 1
			if spec, ok := specOf[n]; ok {
				for m := range TypeGetDependencies(pkg.PkgPath, pkg.TypesInfo.TypeOf(spec.Type)) {
					if visit(m) {
						return true
					}
				}
			}
			state[n] = 2
			return false
		}
		var sorted []string
		for n := range names {
			sorted = append(sorted, n)
		}
		sort.Strings(sorted)
		for _, n := range sorted {
			if visit(n) {
				break
			}
		}
		if onCycle == "" || !names[onCycle] {
			break
		}
		delete(names, onCycle)
		for _, e := range entries {
			if e.name == onCycle {
				e.reasons["cyclic dependency through type arguments"] = true
			}
		}
	}
	var lines []string
	for _, e := range entries {
		var reasons []string
		for r := range e.reasons {
			reasons = append(reasons, r)
		}
		sort.Strings(reasons)
		decision := "translate"
		if len(reasons) > 0 {
			decision = "axiomatize"
		} else if !config.TranslateTypes {
			decision = "translatable"
		}
		lines = append(lines, fmt.Sprintf("%s\t%s\t%s\t%s\t%s\n",
			pkg.PkgPath, e.name, e.kind, decision, strings.Join(reasons, "; ")))
	}
	if !config.TranslateTypes {
		names = nil
	}
	if logFile != "" && len(lines) > 0 {
		typesLogMu.Lock()
		defer typesLogMu.Unlock()
		if f, err := os.OpenFile(logFile, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644); err == nil {
			for _, l := range lines {
				f.WriteString(l)
			}
			f.Close()
		}
	}
	return declfilter.WithTranslated(df, names)
}
