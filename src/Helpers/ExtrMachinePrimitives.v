From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatInteger.

From RecoveryRefinement Require Import Helpers.MachinePrimitives.

(* TODO: replace fully-qualfied names here with shorter names, and add imports
to a fiximports.py script *)

Extraction Language Haskell.

Extract Inductive uint64 => "Data.Word.Word64" ["fromIntegral"].
(* fromNum might be used by constants, but there shouldn't be any use case for
toNum *)
Extract Inlined Constant toNum => "undefined".

Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(* TODO: need checked versions of these *)
Extract Inlined Constant add => "(+)".
Extract Inlined Constant sub => "(-)".
Extract Inlined Constant compare => "compare".

(* extract these to a real type, but don't provide any constructor *)
Extract Inductive ByteString => "Data.ByteString.ByteString" ["undefined"].

Extract Inlined Constant Fd => "System.Posix.Types.Fd".
