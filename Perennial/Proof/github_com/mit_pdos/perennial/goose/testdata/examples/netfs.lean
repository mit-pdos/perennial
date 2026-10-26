/-
The proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs`, an
end-to-end example of a crash-safe distributed program: the shared definitions
and the protocols (`Base`), the linked results (`Link`) and the distributed
crash safety of the three-node system (`Results`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Link
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Results

@[expose] public section
