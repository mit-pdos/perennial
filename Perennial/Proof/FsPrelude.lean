/-
The proof prelude for code that uses the filesystem extension
(`github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsffi`): its
specs. The proofs assume `[HasExt fsExt]`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.FsPrelude
public import Perennial.GooseLang.Ext.Fs.Specs
