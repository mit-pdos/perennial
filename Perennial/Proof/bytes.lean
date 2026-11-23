/-
The proofs of the Go `bytes` package: the shared definitions (`Base`: `isPkgInit`,
`compareResult`; `BufferBasics`: `ownBuffer`, a `*Buffer` with its content and capacity,
`ownBuffer_new` for a zero `Buffer`, and `bufferGrown`, a buffer `grow` made room in), the linked
results (`Link`), `bytes.wp_<F>` for each function `F` (`Buffer.Write` appends, `Buffer.Bytes`
lends the unread bytes), and `Results` (a `*Buffer` is a reader).
-/
module

public import Perennial.Proof.bytes.Base
public import Perennial.Proof.bytes.BufferBasics
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.bytes.Results

@[expose] public section
