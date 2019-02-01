From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.
From Coq Require Import ExtrHaskellNatInteger.
From Coq Require Import ExtrHaskellString.

From RecoveryRefinement Require Import Helpers.MachinePrimitives.

Extraction Language Haskell.

Extract Inductive uint64 => "Lib.Word64" ["Prelude.fromIntegral"].
(* fromNum might be used by constants, but there shouldn't be any use case for
toNum *)
Extract Inlined Constant toNum => "UNDEFINED_toNum".

Extract Constant uint64_from_le => "Lib.uint64_from_le".
Extract Constant uint64_to_le => "Lib.uint64_to_le".

Extract Constant four_kilobytes => "(4096 :: Lib.Word64)".


Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

Extract Constant add => "Lib.add".
Extract Constant sub => "Lib.sub".
Extract Constant compare => "Lib.compare".

Extract Constant byte => "Lib.Word8".
(* extract these to a real type, but don't provide any constructor *)
Extract Inductive ByteString => "Lib.ByteString" ["UNDEFINED_fromBytes"].
Extract Constant getBytes => "UNDEFINED_getBytes".
Extract Constant BS.toString => "Lib.byteString_to_String".
Extract Constant BS.fromString => "Lib.string_to_ByteString".
Extract Constant BS.append => "Lib.bs_append".
Extract Constant BS.concat => "Lib.bs_concat".
Extract Constant BS.drop => "Lib.bs_drop".
Extract Constant BS.take => "Lib.bs_take".
Extract Constant BS.empty => "Lib.bs_empty".
Extract Constant BS.length => "Lib.bs_length".

Extract Constant Fd => "Lib.Fd".
