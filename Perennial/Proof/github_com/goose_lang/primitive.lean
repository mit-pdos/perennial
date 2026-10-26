/-
The proofs of `github.com/goose-lang/primitive` (`Assume`, `RandomUint64`, `Mutex`): the
shared definitions (`Base`), the linked results (`Link`),
`github_com.goose_lang.primitive.wp_<F>` for each function `F`, and their corollaries
(`Results`). `primitive/disk` is not translated: there is no disk extension for now.
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Base
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Results

@[expose] public section
