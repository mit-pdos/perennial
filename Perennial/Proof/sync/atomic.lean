/-
The proofs of the Go `sync/atomic` package: the shared definitions (`Base`), the linked
results (`Link`), `sync.atomic.wp_<F>` for each function or method `F`, and what is derived
from them (`Results`: `wp_AddUint64_receipt`).
-/
module

public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.sync.atomic.Results

@[expose] public section
