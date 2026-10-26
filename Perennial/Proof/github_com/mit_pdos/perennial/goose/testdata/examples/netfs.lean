/-
The proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/netfs`, an
end-to-end example of a distributed program: the shared definitions and the
protocol (`Base`), the linked results (`Link`) and the distributed adequacy of
the three-node system (`Results`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Link
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.netfs.Results

@[expose] public section
