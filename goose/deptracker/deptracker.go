package deptracker

import (
	"fmt"
	"iter"
	"slices"
)

// Deps tracks dependencies between identifiers. Gives the dependency structure,
// which is used to produce a topological sort of definitions (though the
// sorting is not handled by this package).
//
// To make this easier to use it maintains a "current name" used as the source
// for added dependencies.
type Deps struct {
	nameToDeps  map[string][]string
	currentName string
}

func (deps *Deps) hasCurrentName() bool {
	return deps.currentName != ""
}

func (dt *Deps) SetCurrentName(s string) {
	if s == "" {
		panic("depTracker: tried to set current name to empty string")
	}
	if dt.hasCurrentName() {
		panic(fmt.Sprintf("depTracker: tried to change current name without "+
			"unsetting it first (currently %s, tried to set to %s)",
			dt.currentName, s,
		))
	}

	dt.currentName = s
}

func (dt *Deps) UnsetCurrentName() {
	if !dt.hasCurrentName() {
		panic("depTracker: tried to unset current name, but none is set")
	}
	dt.currentName = ""
}

func (dt *Deps) Add(s string) {
	if !dt.hasCurrentName() {
		panic("depTracker: tried to add dep without name set")
	}
	dt.nameToDeps[dt.currentName] = append(dt.nameToDeps[dt.currentName], s)
}

func New() *Deps {
	return &Deps{
		nameToDeps:  make(map[string][]string),
		currentName: "",
	}
}

func (deps *Deps) GetDeps(name string) iter.Seq[string] {
	return slices.Values(deps.nameToDeps[name])
}
