/-
`wp_testAllocateDistinct` is not stated (TODO: no map alloc?):
the map literal `map[uint64]unit{}` steps to a raw `AllocOp` of `map_empty`,
for which there is no spec. Nothing to state here yet.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

@[expose] public section
