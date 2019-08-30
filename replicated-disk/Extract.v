Cd "replicated-disk/extract/".

From Coq Require Extraction.
Require Import ExtrHaskellNatInt.
Require Import ExtrHaskellBasic.

From Armada Require Import Examples.ReplicatedDisk.ReplicatedDiskImpl.

Extraction Language Haskell.

Separate Extraction impl.

Cd "../../".
