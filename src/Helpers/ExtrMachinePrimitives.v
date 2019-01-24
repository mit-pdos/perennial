From Coq Require Import Extraction.
From Coq Require Import ExtrHaskellBasic.

From RecoveryRefinement Require Import Helpers.MachinePrimitives.

(* TODO: replace fully-qualfied names here with shorter names, and add imports
to a fiximports.py script *)

Extraction Language Haskell.

Extract Inlined Constant uint64 => "Data.Word.Word64".
Extract Inlined Constant uint32 => "Data.Word.Word32".
Extract Inlined Constant uint16 => "Data.Word.Word16".
Extract Inlined Constant uint8  => "Data.Word.Word8".

Extract Inductive comparison => "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(* TODO: for now, left toNum/fromNum as undefined, but could theoretically
extract to fromIntegral and convert to Integer (instead of nat) *)
Extract Constant uint64_uint => "Build_UInt undefined undefined (+) (-) compare".
Extract Constant uint32_uint => "Build_UInt undefined undefined (+) (-) compare".
Extract Constant uint16_uint => "Build_UInt undefined undefined (+) (-) compare".
Extract Constant uint8_uint  => "Build_UInt undefined undefined (+) (-) compare".

(* TODO: need to axiomatize conversions in order to extract them to reasonable things, rather than going through Integer *)

(* extract these to a real type, but don't provide any constructor *)
Extract Inductive ByteString => "Data.ByteString.ByteString" ["undefined"].

Extract Inlined Constant Fd => "System.Posix.Types.Fd".
