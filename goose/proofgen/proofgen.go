package proofgen

import (
	"fmt"
	"io"
	"sort"
	"strings"

	"github.com/mit-pdos/perennial/goose/declfilter"
	"github.com/mit-pdos/perennial/goose/glang"
	"github.com/mit-pdos/perennial/goose/proofgen/tmpl"
	"golang.org/x/tools/go/packages"
)

func Package(w io.Writer, pkg *packages.Package, ffi string, bootstrap bool, filter declfilter.DeclFilter) map[string]string {
	coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(pkg.PkgPath), "/", ".")

	if glang.Lean {
		coqPath = glang.LeanNamespace(pkg.PkgPath)
	}
	pf := tmpl.PackageProof{
		Lean:          glang.Lean,
		FfiPrelude:    glang.RocqModuleToLean(ffi + "_prelude")[len("Perennial."):],
		Ffi:           ffi,
		Bootstrap:     bootstrap,
		Name:          pkgName(pkg),
		HasTrusted:    filter.HasTrusted(),
		TrustProofGen: filter.TrustProofGen(),
		ImportPath:    coqPath,
	}

	var imports []string
	for path := range pkg.Imports {
		if filter.ShouldImport(path) {
			imports = append(imports, path)
		}
	}
	sort.Strings(imports)

	for _, path := range imports {
		coqPath := strings.ReplaceAll(glang.ThisIsBadAndShouldBeDeprecatedGoPathToCoqPath(path), "/", ".")
		if glang.Lean {
			coqPath = glang.LeanNamespace(path)
		}
		pf.Imports = append(pf.Imports, tmpl.Import{
			Path: coqPath,
		})
	}

	types := translateTypesDeps(pkg, filter)
	var chunks map[string]string
	if glang.Lean {
		chunks = leanChunks(pf, types)
		if chunks != nil {
			// the package module only re-exports the chunks
			var names []string
			for name := range chunks {
				names = append(names, name)
			}
			sort.Strings(names)
			for _, name := range names {
				pf.ExtraImports = append(pf.ExtraImports, "Perennial.GeneratedProof."+pf.ImportPath+"."+name)
			}
			types = nil
		}
	}
	for _, t := range types {
		pf.Types = append(pf.Types, t.decl)
	}

	if err := pf.Write(w); err != nil {
		panic(err)
	}
	return chunks
}

// The generated proofs of a package whose types cost more than this (see
// typeCost) are split into chunks, so that lake can check them in parallel.
const chunkThreshold = 300

// typeCost estimates the cost of checking the generated proofs of a type:
// each struct field has two access instances.
func typeCost(t translatedType) int {
	return 2 + 2*len(t.decl.LeanFields)
}

// leanChunks splits the types of a large package into chunks (returning nil
// for a small package). A chunk only imports the chunks with the types its
// types depend on: types are grouped by their depth in the dependency graph,
// and each depth is split into chunks of about the same cost.
func leanChunks(pf tmpl.PackageProof, types []translatedType) map[string]string {
	total := 0
	for _, t := range types {
		total += typeCost(t)
	}
	if total <= chunkThreshold {
		return nil
	}
	target := max(chunkThreshold/2, total/12)

	depth := make(map[string]int)
	maxDepth := 0
	// types is in dependency order
	for _, t := range types {
		d := 0
		for _, dep := range t.deps {
			d = max(d, depth[dep]+1)
		}
		depth[t.name] = d
		maxDepth = max(maxDepth, d)
	}

	chunkOf := make(map[string]int)
	var chunkTypes [][]translatedType
	for d := 0; d <= maxDepth; d++ {
		cur, cost := -1, 0
		for _, t := range types {
			if depth[t.name] != d {
				continue
			}
			if cur < 0 || cost >= target {
				chunkTypes = append(chunkTypes, nil)
				cur, cost = len(chunkTypes)-1, 0
			}
			chunkTypes[cur] = append(chunkTypes[cur], t)
			chunkOf[t.name] = cur
			cost += typeCost(t)
		}
	}

	files := make(map[string]string)
	for i, ts := range chunkTypes {
		cpf := pf
		cpf.Types = nil
		cpf.ExtraImports = nil
		imports := make(map[int]bool)
		for _, t := range ts {
			cpf.Types = append(cpf.Types, t.decl)
			for _, dep := range t.deps {
				if c := chunkOf[dep]; c != i {
					imports[c] = true
				}
			}
		}
		var cs []int
		for c := range imports {
			cs = append(cs, c)
		}
		sort.Ints(cs)
		for _, c := range cs {
			cpf.ExtraImports = append(cpf.ExtraImports,
				fmt.Sprintf("Perennial.GeneratedProof.%s.chunk%d", pf.ImportPath, c+1))
		}
		w := new(strings.Builder)
		if err := cpf.Write(w); err != nil {
			panic(err)
		}
		files[fmt.Sprintf("chunk%d", i+1)] = w.String()
	}
	return files
}

// pkgName is the Rocq module/Lean namespace of the package
func pkgName(pkg *packages.Package) string {
	if glang.Lean {
		return glang.LeanNamespace(pkg.PkgPath)
	}
	return pkg.Name
}
