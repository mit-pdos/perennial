// Package proph provides prophecy variables for programs verified with
// Perennial.
//
// A prophecy variable has no runtime effect: [NewProph] returns a [ProphId]{}
// and the resolve methods do nothing. They exist for the proof, where
// Perennial's trusted model (Perennial/TrustedCode/github_com/mit_pdos/perennial/proph.lean)
// gives them their meaning: NewProph creates a prophecy variable that predicts
// the list of values it will be resolved with, and each resolve method
// resolves it with its argument.
package proph

// ProphId is a prophecy variable.
type ProphId struct{}

// NewProph creates a prophecy variable.
func NewProph() ProphId {
	return ProphId{}
}

// ResolveBool resolves p with b.
func (p ProphId) ResolveBool(b bool) {}

// ResolveU64 resolves p with i.
func (p ProphId) ResolveU64(i uint64) {}

// Resolve resolves p with v, as an interface value: its dynamic type and
// value, so a call with an argument of a non-interface type resolves p with
// that type and the argument's value.
func (p ProphId) Resolve(v any) {}
