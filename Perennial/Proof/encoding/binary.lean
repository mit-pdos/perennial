/-
The proofs of the Go `encoding/binary` package (little- and big-endian
`Uint64`/`PutUint64`/`Uint32`/`PutUint32`): the shared definitions (`Base`, `PtrMethods`), the
linked results (`Link`), `encoding.binary.<T>.wp_<M>` for each method, and what is derived
from them under the old names (`Results`).
-/
module

public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.encoding.binary.PtrMethods
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.encoding.binary.Results

@[expose] public section
