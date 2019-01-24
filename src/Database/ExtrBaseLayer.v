From Coq Require Extraction.
From RecoveryRefinement Require Import Database.DataStructures.
From RecoveryRefinement Require Import Database.BaseLayer.

Extraction Language Haskell.

Extract Constant IORef "a" => "Data.IORef.IORef a".
Extract Constant Array "a" => "Data.Vector.Vector a".
Extract Constant HashTable "k" "v" => "Data.HashTable.IO.BasicHashTable k v".

(* TODO: extract proc to some monad *)
