From Coq Require Extraction.
From RecoveryRefinement Require Import Database.DataStructures.
From RecoveryRefinement Require Import Database.BaseLayer.

Extraction Language Haskell.

Extract Constant IORef "a" => "Lib.IORef a".
Extract Constant Array "a" => "Lib.Array a".
Extract Constant HashTable "v" => "Lib.HashTable Lib.Word64 v".
Extract Constant LockRef => "Lib.LockRef".

(* TODO: extract proc to some monad *)
