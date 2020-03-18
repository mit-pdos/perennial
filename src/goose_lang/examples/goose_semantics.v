(* autogenerated from semantics *)
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.

(* comparisons.go *)

Definition testCompareAll: val :=
  rec: "testCompareAll" <> :=
    let: "ok" := ref_to boolT #true in
    let: "nok" := ref_to boolT #false in
    "ok" <-[boolT] ![boolT] "ok" && #1 < #2;;
    "nok" <-[boolT] ![boolT] "ok" && #2 < #1;;
    "ok" <-[boolT] ![boolT] "ok" && #1 ≤ #2;;
    "ok" <-[boolT] ![boolT] "ok" && #2 ≤ #2;;
    "nok" <-[boolT] ![boolT] "ok" && #2 ≤ #1;;
    (if: ![boolT] "nok"
    then #false
    else ![boolT] "ok").

Definition testCompareGT: val :=
  rec: "testCompareGT" <> :=
    let: "x" := ref_to uint64T #4 in
    let: "y" := ref_to uint64T #5 in
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" > #4;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" > ![uint64T] "x";;
    ![boolT] "ok".

Definition testCompareGE: val :=
  rec: "testCompareGE" <> :=
    let: "x" := ref_to uint64T #4 in
    let: "y" := ref_to uint64T #5 in
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≥ #4;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≥ #5;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≥ ![uint64T] "x";;
    (if: ![uint64T] "y" > #5
    then #false
    else ![boolT] "ok").

Definition testCompareLT: val :=
  rec: "testCompareLT" <> :=
    let: "x" := ref_to uint64T #4 in
    let: "y" := ref_to uint64T #5 in
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" < #6;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "x" < ![uint64T] "y";;
    ![boolT] "ok".

Definition testCompareLE: val :=
  rec: "testCompareLE" <> :=
    let: "x" := ref_to uint64T #4 in
    let: "y" := ref_to uint64T #5 in
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≤ #6;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "y" ≤ #5;;
    "ok" <-[boolT] ![boolT] "ok" && ![uint64T] "x" ≤ ![uint64T] "y";;
    (if: ![uint64T] "y" < #5
    then #false
    else ![boolT] "ok").

(* conversions.go *)

Definition literalCast: val :=
  rec: "literalCast" <> :=
    let: "x" := #2 in
    "x" + #2.

Definition stringToByteSlice: val :=
  rec: "stringToByteSlice" "s" :=
    let: "p" := Data.stringToBytes "s" in
    "p".

Definition byteSliceToString: val :=
  rec: "byteSliceToString" "p" :=
    Data.bytesToString "p".

(* tests *)
Definition testByteSliceToString: val :=
  rec: "testByteSliceToString" <> :=
    let: "x" := NewSlice byteT #3 in
    SliceSet byteT "x" #0 (#(U8 65));;
    SliceSet byteT "x" #1 (#(U8 66));;
    SliceSet byteT "x" #2 (#(U8 67));;
    (byteSliceToString "x" = #(str"ABC")).

(* copy.go *)

Definition testCopySimple: val :=
  rec: "testCopySimple" <> :=
    let: "x" := NewSlice byteT #10 in
    SliceSet byteT "x" #3 (#(U8 1));;
    let: "y" := NewSlice byteT #10 in
    SliceCopy byteT "y" "x";;
    (SliceGet byteT "y" #3 = #(U8 1)).

Definition testCopyShorterDst: val :=
  rec: "testCopyShorterDst" <> :=
    let: "x" := NewSlice byteT #15 in
    SliceSet byteT "x" #3 (#(U8 1));;
    SliceSet byteT "x" #12 (#(U8 2));;
    let: "y" := NewSlice byteT #10 in
    let: "n" := SliceCopy byteT "y" "x" in
    ("n" = #10) && (SliceGet byteT "y" #3 = #(U8 1)).

Definition testCopyShorterSrc: val :=
  rec: "testCopyShorterSrc" <> :=
    let: "x" := NewSlice byteT #10 in
    let: "y" := NewSlice byteT #15 in
    SliceSet byteT "x" #3 (#(U8 1));;
    SliceSet byteT "y" #12 (#(U8 2));;
    let: "n" := SliceCopy byteT "y" "x" in
    ("n" = #10) && (SliceGet byteT "y" #3 = #(U8 1)) && (SliceGet byteT "y" #12 = #(U8 2)).

(* encoding.go *)

(* helpers *)
Module Enc.
  Definition S := struct.decl [
    "p" :: slice.T byteT
  ].
End Enc.

Definition Enc__consume: val :=
  rec: "Enc__consume" "e" "n" :=
    let: "b" := SliceTake (struct.loadF Enc.S "p" "e") "n" in
    struct.storeF Enc.S "p" "e" (SliceSkip byteT (struct.loadF Enc.S "p" "e") "n");;
    "b".

Module Dec.
  Definition S := struct.decl [
    "p" :: slice.T byteT
  ].
End Dec.

Definition Dec__consume: val :=
  rec: "Dec__consume" "d" "n" :=
    let: "b" := SliceTake (struct.loadF Dec.S "p" "d") "n" in
    struct.storeF Dec.S "p" "d" (SliceSkip byteT (struct.loadF Dec.S "p" "d") "n");;
    "b".

Definition roundtripEncDec32: val :=
  rec: "roundtripEncDec32" "x" :=
    let: "r" := NewSlice byteT #4 in
    let: "e" := struct.new Enc.S [
      "p" ::= "r"
    ] in
    let: "d" := struct.new Dec.S [
      "p" ::= "r"
    ] in
    UInt32Put (Enc__consume "e" #4) "x";;
    UInt32Get (Dec__consume "d" #4).

Definition roundtripEncDec64: val :=
  rec: "roundtripEncDec64" "x" :=
    let: "r" := NewSlice byteT #8 in
    let: "e" := struct.new Enc.S [
      "p" ::= "r"
    ] in
    let: "d" := struct.new Dec.S [
      "p" ::= "r"
    ] in
    UInt64Put (Enc__consume "e" #8) "x";;
    UInt64Get (Dec__consume "d" #8).

(* tests *)
Definition testEncDec32Simple: val :=
  rec: "testEncDec32Simple" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 0)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 1)) = #(U32 1));;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 1231234)) = #(U32 1231234));;
    ![boolT] "ok".

Definition failing_testEncDec32: val :=
  rec: "failing_testEncDec32" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#(U32 3434807466)) = #(U32 3434807466));;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #20) = #1 ≪ #20);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #18) = #1 ≪ #18);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #10) = #1 ≪ #10);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #0) = #1 ≪ #0);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec32 (#1 ≪ #32 - #1) = #1 ≪ #32 - #1);;
    ![boolT] "ok".

Definition testEncDec64Simple: val :=
  rec: "testEncDec64Simple" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #0 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #1 = #1);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #1231234 = #1231234);;
    ![boolT] "ok".

Definition testEncDec64: val :=
  rec: "testEncDec64" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 #62206846038638762 = #62206846038638762);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #63) = #1 ≪ #63);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #47) = #1 ≪ #47);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #20) = #1 ≪ #20);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #18) = #1 ≪ #18);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #10) = #1 ≪ #10);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #0) = #1 ≪ #0);;
    "ok" <-[boolT] ![boolT] "ok" && (roundtripEncDec64 (#1 ≪ #64 - #1) = #1 ≪ #64 - #1);;
    ![boolT] "ok".

(* function_ordering.go *)

(* helpers *)
Module Editor.
  Definition S := struct.decl [
    "s" :: slice.T uint64T;
    "next_val" :: uint64T
  ].
End Editor.

(* advances the array editor, and returns the value it wrote, storing
   "next" in next_val *)
Definition Editor__AdvanceReturn: val :=
  rec: "Editor__AdvanceReturn" "e" "next" :=
    let: "tmp" := ref_to uint64T (struct.loadF Editor.S "next_val" "e") in
    SliceSet uint64T (struct.loadF Editor.S "s" "e") #0 (![uint64T] "tmp");;
    struct.storeF Editor.S "next_val" "e" "next";;
    struct.storeF Editor.S "s" "e" (SliceSkip uint64T (struct.loadF Editor.S "s" "e") #1);;
    ![uint64T] "tmp".

(* we call this function with side-effectful function calls as arguments,
   its implementation is unimportant *)
Definition addFour64: val :=
  rec: "addFour64" "a" "b" "c" "d" :=
    "a" + "b" + "c" + "d".

Module Pair.
  Definition S := struct.decl [
    "x" :: uint64T;
    "y" :: uint64T
  ].
End Pair.

(* tests *)
Definition failing_testFunctionOrdering: val :=
  rec: "failing_testFunctionOrdering" <> :=
    let: "arr" := ref_to (slice.T uint64T) (NewSlice uint64T #5) in
    let: "e1" := struct.mk Editor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #0;
      "next_val" ::= #1
    ] in
    let: "e2" := struct.mk Editor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #0;
      "next_val" ::= #101
    ] in
    (if: Editor__AdvanceReturn "e1" #2 + Editor__AdvanceReturn "e2" #102 ≠ #102
    then #false
    else
      (if: SliceGet uint64T (![slice.T uint64T] "arr") #0 ≠ #101
      then #false
      else
        (if: addFour64 (Editor__AdvanceReturn "e1" #3) (Editor__AdvanceReturn "e2" #103) (Editor__AdvanceReturn "e2" #104) (Editor__AdvanceReturn "e1" #4) ≠ #210
        then #false
        else
          (if: SliceGet uint64T (![slice.T uint64T] "arr") #1 ≠ #102
          then #false
          else
            (if: SliceGet uint64T (![slice.T uint64T] "arr") #2 ≠ #3
            then #false
            else
              let: "p" := struct.mk Pair.S [
                "x" ::= Editor__AdvanceReturn "e1" #5;
                "y" ::= Editor__AdvanceReturn "e2" #105
              ] in
              (if: SliceGet uint64T (![slice.T uint64T] "arr") #3 ≠ #104
              then #false
              else
                let: "q" := struct.mk Pair.S [
                  "y" ::= Editor__AdvanceReturn "e1" #6;
                  "x" ::= Editor__AdvanceReturn "e2" #106
                ] in
                (if: SliceGet uint64T (![slice.T uint64T] "arr") #4 ≠ #105
                then #false
                else (struct.get Pair.S "x" "p" + struct.get Pair.S "x" "q" = #109)))))))).

(* lock.go *)

(* We can't interpret multithreaded code, so this just checks that
   locks are correctly interpreted *)
Definition testsUseLocks: val :=
  rec: "testsUseLocks" <> :=
    let: "m" := lock.new #() in
    lock.acquire "m";;
    lock.release "m";;
    #true.

(* loops.go *)

(* helpers *)
Definition standardForLoop: val :=
  rec: "standardForLoop" "s" :=
    let: "sumPtr" := ref (zero_val uint64T) in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![uint64T] "i" < slice.len "s"
      then
        let: "sum" := ![uint64T] "sumPtr" in
        let: "x" := SliceGet uint64T "s" (![uint64T] "i") in
        "sumPtr" <-[uint64T] "sum" + "x";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue
      else Break));;
    let: "sum" := ![uint64T] "sumPtr" in
    "sum".

(* based off diskAppendWait loop pattern in logging2 *)
Module LoopStruct.
  Definition S := struct.decl [
    "loopNext" :: refT uint64T
  ].
End LoopStruct.

Definition LoopStruct__forLoopWait: val :=
  rec: "LoopStruct__forLoopWait" "ls" "i" :=
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "nxt" := struct.get LoopStruct.S "loopNext" "ls" in
      (if: "i" < ![uint64T] "nxt"
      then Break
      else
        struct.get LoopStruct.S "loopNext" "ls" <-[uint64T] ![uint64T] (struct.get LoopStruct.S "loopNext" "ls") + #1;;
        Continue)).

(* tests *)
Definition testStandardForLoop: val :=
  rec: "testStandardForLoop" <> :=
    let: "arr" := ref_to (slice.T uint64T) (NewSlice uint64T #4) in
    SliceSet uint64T (![slice.T uint64T] "arr") #0 (SliceGet uint64T (![slice.T uint64T] "arr") #0 + #1);;
    SliceSet uint64T (![slice.T uint64T] "arr") #1 (SliceGet uint64T (![slice.T uint64T] "arr") #1 + #3);;
    SliceSet uint64T (![slice.T uint64T] "arr") #2 (SliceGet uint64T (![slice.T uint64T] "arr") #2 + #5);;
    SliceSet uint64T (![slice.T uint64T] "arr") #3 (SliceGet uint64T (![slice.T uint64T] "arr") #3 + #7);;
    (standardForLoop (![slice.T uint64T] "arr") = #16).

Definition testForLoopWait: val :=
  rec: "testForLoopWait" <> :=
    let: "ls" := struct.mk LoopStruct.S [
      "loopNext" ::= ref (zero_val uint64T)
    ] in
    LoopStruct__forLoopWait "ls" #3;;
    (![uint64T] (struct.get LoopStruct.S "loopNext" "ls") = #4).

Definition testBreakFromLoopWithContinue: val :=
  rec: "testBreakFromLoopWithContinue" <> :=
    let: "i" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: #true
      then
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Break
      else Continue));;
    (![uint64T] "i" = #1).

Definition failing_testBreakFromLoopNoContinue: val :=
  rec: "failing_testBreakFromLoopNoContinue" <> :=
    let: "i" := ref_to uint64T #0 in
    Skip;;
    (for: (λ: <>, ![uint64T] "i" < #20); (λ: <>, Skip) := λ: <>,
      (if: #true
      then
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Break
      else "i" <-[uint64T] ![uint64T] "i" + #2);;
      Continue);;
    (![uint64T] "i" = #1).

Definition testNestedLoops: val :=
  rec: "testNestedLoops" <> :=
    let: "ok1" := ref_to boolT #false in
    let: "ok2" := ref_to boolT #false in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      let: "j" := ref_to uint64T #0 in
      (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
        (if: ![uint64T] "j" > #5
        then Break
        else
          "j" <-[uint64T] ![uint64T] "j" + #1;;
          "ok1" <-[boolT] (![uint64T] "j" = #6);;
          Continue));;
      "i" <-[uint64T] ![uint64T] "i" + #1;;
      "ok2" <-[boolT] (![uint64T] "i" = #1);;
      Break);;
    ![boolT] "ok1" && ![boolT] "ok2".

Definition testNestedGoStyleLoops: val :=
  rec: "testNestedGoStyleLoops" <> :=
    let: "ok" := ref_to boolT #false in
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, ![uint64T] "i" < #10); (λ: <>, "i" <-[uint64T] ![uint64T] "i" + #1) := λ: <>,
      let: "j" := ref_to uint64T #0 in
      (for: (λ: <>, ![uint64T] "j" < ![uint64T] "i"); (λ: <>, "j" <-[uint64T] ![uint64T] "j" + #1) := λ: <>,
        (if: #true
        then Break
        else Continue));;
      "ok" <-[boolT] (![uint64T] "i" = #9);;
      Continue);;
    ![boolT] "ok".

(* maps.go *)

Definition IterateMapKeys: val :=
  rec: "IterateMapKeys" "m" :=
    let: "sum" := ref (zero_val uint64T) in
    MapIter "m" (λ: "k" <>,
      "sum" <-[uint64T] ![uint64T] "sum" + "k");;
    ![uint64T] "sum".

Definition IterateMapValues: val :=
  rec: "IterateMapValues" "m" :=
    let: "sum" := ref (zero_val uint64T) in
    MapIter "m" (λ: <> "v",
      "sum" <-[uint64T] ![uint64T] "sum" + "v");;
    ![uint64T] "sum".

Definition testIterateMap: val :=
  rec: "testIterateMap" <> :=
    let: "ok" := ref_to boolT #true in
    let: "m" := NewMap uint64T in
    MapInsert "m" #0 #1;;
    MapInsert "m" #1 #2;;
    MapInsert "m" #3 #4;;
    "ok" <-[boolT] ![boolT] "ok" && (IterateMapKeys "m" = #4);;
    "ok" <-[boolT] ![boolT] "ok" && (IterateMapValues "m" = #7);;
    ![boolT] "ok".

Definition testMapSize: val :=
  rec: "testMapSize" <> :=
    let: "ok" := ref_to boolT #true in
    let: "m" := NewMap uint64T in
    "ok" <-[boolT] ![boolT] "ok" && (MapLen "m" = #0);;
    MapInsert "m" #0 #1;;
    MapInsert "m" #1 #2;;
    MapInsert "m" #3 #4;;
    "ok" <-[boolT] ![boolT] "ok" && (MapLen "m" = #3);;
    ![boolT] "ok".

(* nil.go *)

Definition failing_testCompareSliceToNil: val :=
  rec: "failing_testCompareSliceToNil" <> :=
    let: "s" := NewSlice byteT #0 in
    "s" ≠ slice.nil.

Definition testComparePointerToNil: val :=
  rec: "testComparePointerToNil" <> :=
    let: "s" := ref (zero_val uint64T) in
    "s" ≠ slice.nil.

(* operations.go *)

(* helpers *)
Definition reverseAssignOps64: val :=
  rec: "reverseAssignOps64" "x" :=
    let: "y" := ref (zero_val uint64T) in
    "y" <-[uint64T] ![uint64T] "y" + "x";;
    "y" <-[uint64T] ![uint64T] "y" - "x";;
    "y" <-[uint64T] ![uint64T] "y" + #1;;
    "y" <-[uint64T] ![uint64T] "y" - #1;;
    ![uint64T] "y".

Definition reverseAssignOps32: val :=
  rec: "reverseAssignOps32" "x" :=
    let: "y" := ref (zero_val uint32T) in
    "y" <-[uint32T] ![uint32T] "y" + "x";;
    "y" <-[uint32T] ![uint32T] "y" - "x";;
    "y" <-[uint32T] ![uint32T] "y" + #1;;
    "y" <-[uint32T] ![uint32T] "y" - #1;;
    ![uint32T] "y".

Definition add64Equals: val :=
  rec: "add64Equals" "x" "y" "z" :=
    ("x" + "y" = "z").

Definition sub64Equals: val :=
  rec: "sub64Equals" "x" "y" "z" :=
    ("x" - "y" = "z").

(* tests *)
Definition testReverseAssignOps64: val :=
  rec: "testReverseAssignOps64" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #0 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #1 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #1231234 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 #62206846038638762 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #63) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #47) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #20) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #18) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #10) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #0) = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps64 (#1 ≪ #64 - #1) = #0);;
    ![boolT] "ok".

Definition failing_testReverseAssignOps32: val :=
  rec: "failing_testReverseAssignOps32" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 0)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 1)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 1231234)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#(U32 3434807466)) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #20) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #18) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #10) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #0) = #(U32 0));;
    "ok" <-[boolT] ![boolT] "ok" && (reverseAssignOps32 (#1 ≪ #32 - #1) = #(U32 0));;
    ![boolT] "ok".

Definition testAdd64Equals: val :=
  rec: "testAdd64Equals" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && add64Equals #2 #3 #5;;
    "ok" <-[boolT] ![boolT] "ok" && add64Equals (#1 ≪ #64 - #1) #1 #0;;
    ![boolT] "ok".

Definition testSub64Equals: val :=
  rec: "testSub64Equals" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && sub64Equals #2 #1 #1;;
    "ok" <-[boolT] ![boolT] "ok" && sub64Equals (#1 ≪ #64 - #1) (#1 ≪ #63) (#1 ≪ #63 - #1);;
    "ok" <-[boolT] ![boolT] "ok" && sub64Equals #2 #8 (#1 ≪ #64 - #6);;
    ![boolT] "ok".

Definition testDivisionPrecedence: val :=
  rec: "testDivisionPrecedence" <> :=
    let: "blockSize" := #4096 in
    let: "hdrmeta" := #8 in
    let: "hdraddrs" := ("blockSize" - "hdrmeta") `quot` #8 in
    ("hdraddrs" = #511).

Definition testModPrecedence: val :=
  rec: "testModPrecedence" <> :=
    let: "x1" := #513 + #12 `rem` #8 in
    let: "x2" := (#513 + #12) `rem` #8 in
    ("x1" = #517) && ("x2" = #5).

Definition testBitwiseOpsPrecedence: val :=
  rec: "testBitwiseOpsPrecedence" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (#222 ∥ #327 = #479);;
    "ok" <-[boolT] ![boolT] "ok" && ((#468 & #1191) = #132);;
    "ok" <-[boolT] ![boolT] "ok" && (#453 ^^ #761 = #828);;
    "ok" <-[boolT] ![boolT] "ok" && (#453 ^^ #761 ∥ #121 = #893);;
    "ok" <-[boolT] ![boolT] "ok" && ((#468 & #1191) ∥ #333 = #461);;
    "ok" <-[boolT] ![boolT] "ok" && #222 ∥ (#327 & #421) ≠ #389;;
    ![boolT] "ok".

Definition testArithmeticShifts: val :=
  rec: "testArithmeticShifts" <> :=
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && (#672 ≪ #3 = #5376);;
    "ok" <-[boolT] ![boolT] "ok" && (#672 ≪ #51 = #1513209474796486656);;
    "ok" <-[boolT] ![boolT] "ok" && (#672 ≫ #4 = #42);;
    "ok" <-[boolT] ![boolT] "ok" && (#672 ≫ #12 = #0);;
    "ok" <-[boolT] ![boolT] "ok" && (#672 ≫ #4 ≪ #4 = #672);;
    ![boolT] "ok".

(* shortcircuiting.go *)

(* helpers *)
Module BoolTest.
  Definition S := struct.decl [
    "t" :: boolT;
    "f" :: boolT;
    "tc" :: uint64T;
    "fc" :: uint64T
  ].
End BoolTest.

Definition CheckTrue: val :=
  rec: "CheckTrue" "b" :=
    struct.storeF BoolTest.S "tc" "b" (struct.loadF BoolTest.S "tc" "b" + #1);;
    struct.loadF BoolTest.S "t" "b".

Definition CheckFalse: val :=
  rec: "CheckFalse" "b" :=
    struct.storeF BoolTest.S "fc" "b" (struct.loadF BoolTest.S "fc" "b" + #1);;
    struct.loadF BoolTest.S "f" "b".

(* tests *)
Definition testShortcircuitAndTF: val :=
  rec: "testShortcircuitAndTF" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckTrue "b" && CheckFalse "b"
    then #false
    else (struct.loadF BoolTest.S "tc" "b" = #1) && (struct.loadF BoolTest.S "fc" "b" = #1)).

Definition testShortcircuitAndFT: val :=
  rec: "testShortcircuitAndFT" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckFalse "b" && CheckTrue "b"
    then #false
    else (struct.loadF BoolTest.S "tc" "b" = #0) && (struct.loadF BoolTest.S "fc" "b" = #1)).

Definition testShortcircuitOrTF: val :=
  rec: "testShortcircuitOrTF" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckTrue "b" || CheckFalse "b"
    then (struct.loadF BoolTest.S "tc" "b" = #1) && (struct.loadF BoolTest.S "fc" "b" = #0)
    else #false).

Definition testShortcircuitOrFT: val :=
  rec: "testShortcircuitOrFT" <> :=
    let: "b" := struct.new BoolTest.S [
      "t" ::= #true;
      "f" ::= #false;
      "tc" ::= #0;
      "fc" ::= #0
    ] in
    (if: CheckFalse "b" || CheckTrue "b"
    then (struct.loadF BoolTest.S "tc" "b" = #1) && (struct.loadF BoolTest.S "fc" "b" = #1)
    else #false).

(* slices.go *)

(* helpers *)
Module ArrayEditor.
  Definition S := struct.decl [
    "s" :: slice.T uint64T;
    "next_val" :: uint64T
  ].
End ArrayEditor.

Definition ArrayEditor__Advance: val :=
  rec: "ArrayEditor__Advance" "ae" "arr" "next" :=
    SliceSet uint64T "arr" #0 (SliceGet uint64T "arr" #0 + #1);;
    SliceSet uint64T (struct.loadF ArrayEditor.S "s" "ae") #0 (struct.loadF ArrayEditor.S "next_val" "ae");;
    struct.storeF ArrayEditor.S "next_val" "ae" "next";;
    struct.storeF ArrayEditor.S "s" "ae" (SliceSkip uint64T (struct.loadF ArrayEditor.S "s" "ae") #1).

(* tests *)
Definition testSliceOps: val :=
  rec: "testSliceOps" <> :=
    let: "x" := NewSlice uint64T #10 in
    SliceSet uint64T "x" #1 #5;;
    SliceSet uint64T "x" #2 #10;;
    SliceSet uint64T "x" #3 #15;;
    SliceSet uint64T "x" #4 #20;;
    let: "v1" := SliceGet uint64T "x" #2 in
    let: "v2" := SliceSubslice uint64T "x" #2 #3 in
    let: "v3" := SliceTake "x" #3 in
    let: "v4" := SliceRef "x" #2 in
    let: "ok" := ref_to boolT #true in
    "ok" <-[boolT] ![boolT] "ok" && ("v1" = #10);;
    "ok" <-[boolT] ![boolT] "ok" && (SliceGet uint64T "v2" #0 = #10);;
    "ok" <-[boolT] ![boolT] "ok" && (slice.len "v2" = #1);;
    "ok" <-[boolT] ![boolT] "ok" && (SliceGet uint64T "v3" #1 = #5);;
    "ok" <-[boolT] ![boolT] "ok" && (SliceGet uint64T "v3" #2 = #10);;
    "ok" <-[boolT] ![boolT] "ok" && (slice.len "v3" = #3);;
    "ok" <-[boolT] ![boolT] "ok" && (![uint64T] "v4" = #10);;
    ![boolT] "ok".

Definition testOverwriteArray: val :=
  rec: "testOverwriteArray" <> :=
    let: "arr" := ref_to (slice.T uint64T) (NewSlice uint64T #4) in
    let: "ae1" := struct.new ArrayEditor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #0;
      "next_val" ::= #1
    ] in
    let: "ae2" := struct.new ArrayEditor.S [
      "s" ::= SliceSkip uint64T (![slice.T uint64T] "arr") #1;
      "next_val" ::= #102
    ] in
    ArrayEditor__Advance "ae2" (![slice.T uint64T] "arr") #103;;
    ArrayEditor__Advance "ae2" (![slice.T uint64T] "arr") #104;;
    ArrayEditor__Advance "ae2" (![slice.T uint64T] "arr") #105;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #2;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #3;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #4;;
    ArrayEditor__Advance "ae1" (![slice.T uint64T] "arr") #5;;
    (if: SliceGet uint64T (![slice.T uint64T] "arr") #0 + SliceGet uint64T (![slice.T uint64T] "arr") #1 + SliceGet uint64T (![slice.T uint64T] "arr") #2 + SliceGet uint64T (![slice.T uint64T] "arr") #3 ≥ #100
    then #false
    else (SliceGet uint64T (![slice.T uint64T] "arr") #3 = #4) && (SliceGet uint64T (![slice.T uint64T] "arr") #0 = #4)).

(* strings.go *)

(* helpers *)
Definition stringAppend: val :=
  rec: "stringAppend" "s" "x" :=
    "s" + uint64_to_string "x".

Definition stringLength: val :=
  rec: "stringLength" "s" :=
    strLen "s".

(* tests *)
Definition failing_testStringAppend: val :=
  rec: "failing_testStringAppend" <> :=
    let: "ok" := ref_to boolT #true in
    let: "s" := ref_to stringT #(str"123") in
    let: "y" := ref_to stringT (stringAppend (![stringT] "s") #45) in
    ![boolT] "ok" && (![stringT] "y" = #(str"12345")).

Definition failing_testStringLength: val :=
  rec: "failing_testStringLength" <> :=
    let: "ok" := ref_to boolT #true in
    let: "s" := ref_to stringT #(str"") in
    "ok" <-[boolT] ![boolT] "ok" && (strLen (![stringT] "s") = #0);;
    "s" <-[stringT] stringAppend (![stringT] "s") #1;;
    "ok" <-[boolT] ![boolT] "ok" && (strLen (![stringT] "s") = #1);;
    "s" <-[stringT] stringAppend (![stringT] "s") #23;;
    ![boolT] "ok" && (strLen (![stringT] "s") = #3).

(* structs.go *)

Module TwoInts.
  Definition S := struct.decl [
    "x" :: uint64T;
    "y" :: uint64T
  ].
End TwoInts.

Module S.
  Definition S := struct.decl [
    "a" :: uint64T;
    "b" :: struct.t TwoInts.S;
    "c" :: boolT
  ].
End S.

Definition NewS: val :=
  rec: "NewS" <> :=
    struct.new S.S [
      "a" ::= #2;
      "b" ::= struct.mk TwoInts.S [
        "x" ::= #1;
        "y" ::= #2
      ];
      "c" ::= #true
    ].

Definition S__readA: val :=
  rec: "S__readA" "s" :=
    struct.loadF S.S "a" "s".

Definition S__readB: val :=
  rec: "S__readB" "s" :=
    struct.loadF S.S "b" "s".

Definition S__readBVal: val :=
  rec: "S__readBVal" "s" :=
    struct.get S.S "b" "s".

Definition S__updateBValX: val :=
  rec: "S__updateBValX" "s" "i" :=
    struct.storeF TwoInts.S "x" (struct.fieldRef S.S "b" "s") "i".

Definition S__negateC: val :=
  rec: "S__negateC" "s" :=
    struct.storeF S.S "c" "s" (~ (struct.loadF S.S "c" "s")).

Definition failing_testStructUpdates: val :=
  rec: "failing_testStructUpdates" <> :=
    let: "ok" := ref_to boolT #true in
    let: "ns" := NewS #() in
    "ok" <-[boolT] ![boolT] "ok" && (S__readA "ns" = #2);;
    let: "b1" := ref_to (struct.t TwoInts.S) (S__readB "ns") in
    "ok" <-[boolT] ![boolT] "ok" && (struct.get TwoInts.S "x" (![struct.t TwoInts.S] "b1") = #1);;
    S__negateC "ns";;
    "ok" <-[boolT] ![boolT] "ok" && (struct.loadF S.S "c" "ns" = #false);;
    struct.storeF TwoInts.S "x" "b1" #3;;
    let: "b2" := ref_to (struct.t TwoInts.S) (S__readB "ns") in
    "ok" <-[boolT] ![boolT] "ok" && (struct.get TwoInts.S "x" (![struct.t TwoInts.S] "b2") = #1);;
    let: "b3" := ref_to (refT (struct.t TwoInts.S)) (struct.fieldRef S.S "b" "ns") in
    "ok" <-[boolT] ![boolT] "ok" && (struct.loadF TwoInts.S "x" (![refT (struct.t TwoInts.S)] "b3") = #1);;
    S__updateBValX "ns" #4;;
    "ok" <-[boolT] ![boolT] "ok" && (struct.get TwoInts.S "x" (S__readBVal "ns") = #4);;
    ![boolT] "ok".

Definition testNestedStructUpdates: val :=
  rec: "testNestedStructUpdates" <> :=
    let: "ok" := ref_to boolT #true in
    let: "ns" := ref_to (refT (struct.t S.S)) (NewS #()) in
    struct.storeF TwoInts.S "x" (struct.fieldRef S.S "b" (![refT (struct.t S.S)] "ns")) #5;;
    "ok" <-[boolT] ![boolT] "ok" && (struct.get TwoInts.S "x" (struct.loadF S.S "b" (![refT (struct.t S.S)] "ns")) = #5);;
    "ns" <-[refT (struct.t S.S)] NewS #();;
    let: "p" := ref_to (refT (struct.t TwoInts.S)) (struct.fieldRef S.S "b" (![refT (struct.t S.S)] "ns")) in
    struct.storeF TwoInts.S "x" (![refT (struct.t TwoInts.S)] "p") #5;;
    "ok" <-[boolT] ![boolT] "ok" && (struct.get TwoInts.S "x" (struct.loadF S.S "b" (![refT (struct.t S.S)] "ns")) = #5);;
    "ns" <-[refT (struct.t S.S)] NewS #();;
    "p" <-[refT (struct.t TwoInts.S)] struct.fieldRef S.S "b" (![refT (struct.t S.S)] "ns");;
    struct.storeF TwoInts.S "x" (struct.fieldRef S.S "b" (![refT (struct.t S.S)] "ns")) #5;;
    "ok" <-[boolT] ![boolT] "ok" && (struct.get TwoInts.S "x" (struct.load TwoInts.S (![refT (struct.t TwoInts.S)] "p")) = #5);;
    "ns" <-[refT (struct.t S.S)] NewS #();;
    "p" <-[refT (struct.t TwoInts.S)] struct.fieldRef S.S "b" (![refT (struct.t S.S)] "ns");;
    struct.storeF TwoInts.S "x" (struct.fieldRef S.S "b" (![refT (struct.t S.S)] "ns")) #5;;
    "ok" <-[boolT] ![boolT] "ok" && (struct.loadF TwoInts.S "x" (![refT (struct.t TwoInts.S)] "p") = #5);;
    ![boolT] "ok".

Definition testStructConstructions: val :=
  rec: "testStructConstructions" <> :=
    let: "ok" := ref_to boolT #true in
    let: "p1" := ref (zero_val (refT (struct.t TwoInts.S))) in
    let: "p2" := ref (zero_val (struct.t TwoInts.S)) in
    let: "p3" := struct.mk TwoInts.S [
      "y" ::= #0;
      "x" ::= #0
    ] in
    let: "p4" := struct.mk TwoInts.S [
      "x" ::= #0;
      "y" ::= #0
    ] in
    "ok" <-[boolT] ![boolT] "ok" && (![refT (struct.t TwoInts.S)] "p1" = slice.nil);;
    "p1" <-[refT (struct.t TwoInts.S)] struct.alloc TwoInts.S (zero_val (struct.t TwoInts.S));;
    "ok" <-[boolT] ![boolT] "ok" && (![struct.t TwoInts.S] "p2" = "p3");;
    "ok" <-[boolT] ![boolT] "ok" && ("p3" = "p4");;
    "ok" <-[boolT] ![boolT] "ok" && ("p4" = struct.load TwoInts.S (![refT (struct.t TwoInts.S)] "p1"));;
    "ok" <-[boolT] ![boolT] "ok" && "p4" ≠ ![refT (struct.t TwoInts.S)] "p1";;
    ![boolT] "ok".

Module StructWrap.
  Definition S := struct.decl [
    "i" :: uint64T
  ].
End StructWrap.

Definition testStoreInStructVar: val :=
  rec: "testStoreInStructVar" <> :=
    let: "p" := ref_to (struct.t StructWrap.S) (struct.mk StructWrap.S [
      "i" ::= #0
    ]) in
    struct.storeF StructWrap.S "i" "p" #5;;
    (struct.get StructWrap.S "i" (![struct.t StructWrap.S] "p") = #5).

Definition testStoreInStructPointerVar: val :=
  rec: "testStoreInStructPointerVar" <> :=
    let: "p" := ref_to (refT (struct.t StructWrap.S)) (struct.alloc StructWrap.S (zero_val (struct.t StructWrap.S))) in
    struct.storeF StructWrap.S "i" (![refT (struct.t StructWrap.S)] "p") #5;;
    (struct.loadF StructWrap.S "i" (![refT (struct.t StructWrap.S)] "p") = #5).

Definition testStoreComposite: val :=
  rec: "testStoreComposite" <> :=
    let: "p" := struct.alloc TwoInts.S (zero_val (struct.t TwoInts.S)) in
    struct.store TwoInts.S "p" (struct.mk TwoInts.S [
      "x" ::= #3;
      "y" ::= #4
    ]);;
    (struct.get TwoInts.S "y" (struct.load TwoInts.S "p") = #4).

Definition testStoreSlice: val :=
  rec: "testStoreSlice" <> :=
    let: "p" := ref (zero_val (slice.T uint64T)) in
    let: "s" := NewSlice uint64T #3 in
    "p" <-[slice.T uint64T] "s";;
    (slice.len (![slice.T uint64T] "p") = #3).

(* wal.go *)

(* 10 is completely arbitrary *)
Definition MaxTxnWrites : expr := #10.

Definition logLength : expr := #1 + #2 * MaxTxnWrites.

Module Log.
  Definition S := struct.decl [
    "d" :: disk.Disk;
    "l" :: lockRefT;
    "cache" :: mapT disk.blockT;
    "length" :: refT uint64T
  ].
End Log.

Definition intToBlock: val :=
  rec: "intToBlock" "a" :=
    let: "b" := NewSlice byteT disk.BlockSize in
    UInt64Put "b" "a";;
    "b".

Definition blockToInt: val :=
  rec: "blockToInt" "v" :=
    let: "a" := UInt64Get "v" in
    "a".

(* New initializes a fresh log *)
Definition New: val :=
  rec: "New" <> :=
    let: "d" := disk.Get #() in
    let: "diskSize" := disk.Size #() in
    (if: "diskSize" ≤ logLength
    then
      Panic ("disk is too small to host log");;
      #()
    else #());;
    let: "cache" := NewMap disk.blockT in
    let: "header" := intToBlock #0 in
    disk.Write #0 "header";;
    let: "lengthPtr" := ref (zero_val uint64T) in
    "lengthPtr" <-[uint64T] #0;;
    let: "l" := lock.new #() in
    struct.mk Log.S [
      "d" ::= "d";
      "cache" ::= "cache";
      "length" ::= "lengthPtr";
      "l" ::= "l"
    ].

Definition Log__lock: val :=
  rec: "Log__lock" "l" :=
    lock.acquire (struct.get Log.S "l" "l").

Definition Log__unlock: val :=
  rec: "Log__unlock" "l" :=
    lock.release (struct.get Log.S "l" "l").

(* BeginTxn allocates space for a new transaction in the log.

   Returns true if the allocation succeeded. *)
Definition Log__BeginTxn: val :=
  rec: "Log__BeginTxn" "l" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log.S "length" "l") in
    (if: ("length" = #0)
    then
      Log__unlock "l";;
      #true
    else
      Log__unlock "l";;
      #false).

(* Read from the logical disk.

   Reads must go through the log to return committed but un-applied writes. *)
Definition Log__Read: val :=
  rec: "Log__Read" "l" "a" :=
    Log__lock "l";;
    let: ("v", "ok") := MapGet (struct.get Log.S "cache" "l") "a" in
    (if: "ok"
    then
      Log__unlock "l";;
      "v"
    else
      Log__unlock "l";;
      let: "dv" := disk.Read (logLength + "a") in
      "dv").

Definition Log__Size: val :=
  rec: "Log__Size" "l" :=
    let: "sz" := disk.Size #() in
    "sz" - logLength.

(* Write to the disk through the log. *)
Definition Log__Write: val :=
  rec: "Log__Write" "l" "a" "v" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log.S "length" "l") in
    (if: "length" ≥ MaxTxnWrites
    then
      Panic ("transaction is at capacity");;
      #()
    else #());;
    let: "aBlock" := intToBlock "a" in
    let: "nextAddr" := #1 + #2 * "length" in
    disk.Write "nextAddr" "aBlock";;
    disk.Write ("nextAddr" + #1) "v";;
    MapInsert (struct.get Log.S "cache" "l") "a" "v";;
    struct.get Log.S "length" "l" <-[uint64T] "length" + #1;;
    Log__unlock "l".

(* Commit the current transaction. *)
Definition Log__Commit: val :=
  rec: "Log__Commit" "l" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log.S "length" "l") in
    Log__unlock "l";;
    let: "header" := intToBlock "length" in
    disk.Write #0 "header".

Definition getLogEntry: val :=
  rec: "getLogEntry" "d" "logOffset" :=
    let: "diskAddr" := #1 + #2 * "logOffset" in
    let: "aBlock" := disk.Read "diskAddr" in
    let: "a" := blockToInt "aBlock" in
    let: "v" := disk.Read ("diskAddr" + #1) in
    ("a", "v").

(* applyLog assumes we are running sequentially *)
Definition applyLog: val :=
  rec: "applyLog" "d" "length" :=
    let: "i" := ref_to uint64T #0 in
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      (if: ![uint64T] "i" < "length"
      then
        let: ("a", "v") := getLogEntry "d" (![uint64T] "i") in
        disk.Write (logLength + "a") "v";;
        "i" <-[uint64T] ![uint64T] "i" + #1;;
        Continue
      else Break)).

Definition clearLog: val :=
  rec: "clearLog" "d" :=
    let: "header" := intToBlock #0 in
    disk.Write #0 "header".

(* Apply all the committed transactions.

   Frees all the space in the log. *)
Definition Log__Apply: val :=
  rec: "Log__Apply" "l" :=
    Log__lock "l";;
    let: "length" := ![uint64T] (struct.get Log.S "length" "l") in
    applyLog (struct.get Log.S "d" "l") "length";;
    clearLog (struct.get Log.S "d" "l");;
    struct.get Log.S "length" "l" <-[uint64T] #0;;
    Log__unlock "l".

(* Open recovers the log following a crash or shutdown *)
Definition Open: val :=
  rec: "Open" <> :=
    let: "d" := disk.Get #() in
    let: "header" := disk.Read #0 in
    let: "length" := blockToInt "header" in
    applyLog "d" "length";;
    clearLog "d";;
    let: "cache" := NewMap disk.blockT in
    let: "lengthPtr" := ref (zero_val uint64T) in
    "lengthPtr" <-[uint64T] #0;;
    let: "l" := lock.new #() in
    struct.mk Log.S [
      "d" ::= "d";
      "cache" ::= "cache";
      "length" ::= "lengthPtr";
      "l" ::= "l"
    ].

(* test *)
Definition testWal: val :=
  rec: "testWal" <> :=
    let: "ok" := ref_to boolT #true in
    let: "lg" := New #() in
    (if: Log__BeginTxn "lg"
    then
      Log__Write "lg" #2 (intToBlock #11);;
      #()
    else #());;
    "ok" <-[boolT] ![boolT] "ok" && (blockToInt (Log__Read "lg" #2) = #11);;
    "ok" <-[boolT] ![boolT] "ok" && (blockToInt (disk.Read #0) = #0);;
    Log__Commit "lg";;
    "ok" <-[boolT] ![boolT] "ok" && (blockToInt (disk.Read #0) = #1);;
    Log__Apply "lg";;
    "ok" <-[boolT] ![boolT] "ok" && (![uint64T] (struct.get Log.S "length" "lg") = #0);;
    ![boolT] "ok".
