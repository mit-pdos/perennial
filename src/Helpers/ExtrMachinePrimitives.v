From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatInteger.
From Coq Require Import ExtrHaskellString.

From RecoveryRefinement Require Import Helpers.MachinePrimitives.

Extraction Language Haskell.

Extract Inductive uint64 => "Lib.Word64" ["Prelude.fromIntegral"].
(* fromNum might be used by constants, but there shouldn't be any use case for
toNum *)
Extract Inlined Constant toNum => "undefined".

Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

Extract Constant add => "Lib.add".
Extract Constant sub => "Lib.sub".
Extract Constant compare => "Lib.compare".

Extract Constant byte => "Lib.Word8".
(* extract these to a real type, but don't provide any constructor *)
Extract Inductive ByteString => "Lib.ByteString" ["undefined"].

Extract Constant Fd => "Lib.Fd".
