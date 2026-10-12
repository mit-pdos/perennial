/-
The proofs of the Go `sort` package: the shared definitions (`Base`, `FindBasics`,
`SearchBasics`, `SorterBasics`, `PartitionBasics`) and the linked results (`Link`),
`sort.wp_<F>` for each function `F`.
-/
module

public import Perennial.Proof.sort.Base
public import Perennial.Proof.sort.FindBasics
public import Perennial.Proof.sort.SearchBasics
public import Perennial.Proof.sort.SorterBasics
public import Perennial.Proof.sort.PartitionBasics
public import Perennial.Proof.sort.Link

@[expose] public section
