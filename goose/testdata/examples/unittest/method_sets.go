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
