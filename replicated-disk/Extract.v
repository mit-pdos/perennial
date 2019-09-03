Cd "replicated-disk/extract/".

From Coq Require Extraction.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellBasic.

From Perennial Require Import Examples.ReplicatedDisk.ReplicatedDiskImpl.

Extraction Language Haskell.

Separate Extraction impl.

Cd "../../".
