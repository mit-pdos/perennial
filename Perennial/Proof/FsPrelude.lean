/-
The proof prelude for proofs about code that uses the filesystem extension
(`github.com/mit-pdos/perennial/goose/testdata/examples/crashfs/fsext`): its definition and specs. The proofs assume `[HasExt fsExt]`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GooseLang.Ext.Fs.Impl
public import Perennial.GooseLang.Ext.Fs.Specs
