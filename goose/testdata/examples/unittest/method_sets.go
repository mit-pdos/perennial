package unittest

// Method sets (go.MethodSetIs in the generated TypeAssumptions).

type msNamer interface {
	Name() string
}

// an interface embedding another and adding an unexported method
type msNamerTagger interface {
	msNamer
	tag() uint64
}

type msLeft struct{}

func (msLeft) Name() string { return "left" }

func (*msLeft) tag() uint64 { return 1 }

type msRight struct{}

func (msRight) Name() string { return "right" }

// Name is promoted from both embedded fields at the same depth: it is in
// neither method set, but tag (only msLeft's) is in *msBoth's
type msBoth struct {
	msLeft
	msRight
}

// a field named Name shadows the method promoted from msLeft
type msShadow struct {
	msLeft
	Name uint64
}

// embedding a pointer: the pointer-receiver methods are in the value's method set
type msPtrEmbed struct {
	*msLeft
}

func msUse() bool {
	var x any = msPtrEmbed{}
	_, ok := x.(msNamerTagger)
	return ok
}

// an exported type with an unexported method, promoted into a type of another
// package (externalglobals.extTagged): the method's id is this package's
// `tag`, which only this package's interfaces (MsTagger) can name
type MsTagged struct{}

func (MsTagged) tag() uint64 { return 2 }

type MsTagger interface {
	tag() uint64
}
