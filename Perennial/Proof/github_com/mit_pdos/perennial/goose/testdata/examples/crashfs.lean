/-
The proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/crashfs`, an
end-to-end example of crash safety: the shared definitions (`Base`), the linked
results (`Link`) and the crash adequacy of the boot program (`Results`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Link
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.crashfs.Results

@[expose] public section
