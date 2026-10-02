/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics_proof/allocator.v`.

The Rocq lemma `wp_testAllocateDistinct` ends in `Abort` ("TODO: no map alloc?"):
the map literal `map[uint64]unit{}` steps to a raw `AllocOp` of `map_empty`,
for which there is no spec. Nothing to state here yet.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init
