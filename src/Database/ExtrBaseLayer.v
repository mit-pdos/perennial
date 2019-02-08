From Coq Require Extraction.
From RecoveryRefinement Require Import Database.DataStructures.
From RecoveryRefinement Require Import Database.BaseLayer.
From RecoveryRefinement Require Import Spec.InjectOp.

Extraction Language Haskell.

Extract Constant IORef "a" => "Lib.IORef a".
Extract Constant Array "a" => "Lib.Array a".
Extract Constant HashTable "v" => "Lib.HashTable Lib.Word64 v".
Extract Constant LockRef => "Lib.LockRef".

Extraction Inline inject.
Extraction Inline data_inj.
Extraction Inline fs_inj.

(* TODO: extract proc to some monad *)
