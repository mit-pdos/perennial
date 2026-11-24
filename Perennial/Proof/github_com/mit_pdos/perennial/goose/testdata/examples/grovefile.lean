/-
The proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/grovefile`, an
end-to-end example of a program over Grove's `grove_ffi` (a file written and read
back, the TSC read twice): the shared definitions (`Base`), the linked results
(`Link`) and the adequacy of the program on a single Grove node (`Results`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Base
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Link
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.grovefile.Results

@[expose] public section
