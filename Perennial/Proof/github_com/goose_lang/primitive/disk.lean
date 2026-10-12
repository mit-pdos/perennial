/-
The proofs of the disk FFI wrappers `disk.Read`, `disk.Write` and `disk.Barrier`
(`github.com/goose-lang/primitive/disk`): the shared definitions (`Base`), the linked
results (`Link`), `github_com.goose_lang.primitive.disk.wp_<F>` for each function `F`,
and the further specs of `Write`/`Read`, among them the logically atomic ones (`Results`).
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.disk.Base
public import Perennial.Proof.github_com.goose_lang.primitive.disk.Link
public import Perennial.Proof.github_com.goose_lang.primitive.disk.Results

@[expose] public section
