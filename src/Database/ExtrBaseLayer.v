From Coq Require Extraction.
From RecoveryRefinement Require Import Database.DataStructures.
From RecoveryRefinement Require Import Database.BaseLayer.

Extraction Language Haskell.

Extract Constant IORef "a" => "Lib.IORef a".
Extract Constant Array "a" => "Lib.Vector a".
Extract Constant HashTable "k" "v" => "Lib.HashTable k v".

(* TODO: extract proc to some monad *)
