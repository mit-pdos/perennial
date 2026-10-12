/-
The proofs of the Go `slices` package: the shared definitions (`Base`, `SortBasics`, the
`pdqsort` lemmas), the linked results (`Link`), `slices.wp_<F>` for each function `F`, and
`Results`.
-/
module

public import Perennial.Proof.slices.Base
public import Perennial.Proof.slices.SortBasics
public import Perennial.Proof.slices.HeapSortBasics
public import Perennial.Proof.slices.InsertionSortBasics
public import Perennial.Proof.slices.PartitionBasics
public import Perennial.Proof.slices.PdqSortBasics
public import Perennial.Proof.slices.OrderedBasics
public import Perennial.Proof.slices.OrderedInsertionSortBasics
public import Perennial.Proof.slices.OrderedPartitionBasics
public import Perennial.Proof.slices.OrderedPdqSortBasics
public import Perennial.Proof.slices.Link
public import Perennial.Proof.slices.Results

@[expose] public section
