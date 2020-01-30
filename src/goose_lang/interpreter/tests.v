From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.interpreter Require Import interpret_types.
From Perennial.goose_lang.interpreter Require Import interpreter.
From Perennial.goose_lang.interpreter Require Import disk_interpreter.

From Perennial.goose_lang.examples Require Import goose_unittest.
From Perennial.goose_lang.ffi Require Import disk.

Definition startstate : state := inhabitant.

Definition testRec : expr :=
  (rec: BAnon BAnon :=
     #3 + #3).

Definition testLiteralCast: expr :=
  λ: <>,
     let: "x" := #2 in
     (Var "x") + #2.

Definition testIfStatement: expr :=
  λ: <>,
     let: "m" := #2 in
     (if: (Var "m") > #3
      then #3
      else #1).

Definition testMatch: val :=
  λ: "x",
  match: (Var "x") with
    InjL "x1" => #3 + (Var "x1")
  | InjR "x1" => #4 + (Var "x1")
  end.

Definition run (p: expr): Error val :=
  fst <$> runStateT (interpret 100 p) startstate.

Notation check_run p := (ltac:(let x := (eval vm_compute in (run p)) in
                               lazymatch x with
                               | Works _ ?v => exact v
                               | Fail _ ?msg => fail "interpreter failed on" p msg
                               end)) (only parsing).

Compute check_run (AllocN #1 (zero_val uint32T)).
Compute check_run (returnTwoWrapper #3).
Compute check_run (testRec #0).

Definition runs_to (p: expr) (v: val) :=
  run p = Works _ v.
Notation "p ~~> v" := (eq_refl : runs_to p v) (at level 70).

Example run_testRec := testRec #0 ~~> #6.

Compute (check_run (testIfStatement #())).
Compute (check_run (testMatch (InjL #2))).
Compute (check_run (testMatch (InjR #2))).
Compute (check_run (testLiteralCast #())).

(* Functions from examples/goose_unittests *)
Compute (check_run ConstWithArith).
Compute (check_run (useMap #())).
Compute (check_run (useSliceIndexing #())).
Compute (check_run (ReassignVars #())).

(* fails because #333 is a uint64 *)
Fail Compute (check_run (EncDec32 #333)).
Example tc1 := testEncDec64 #333 ~~> #true.
Example tc2 := testEncDec32 #(U32 333) ~~> #true.
Example tc3 := testReverseAssignOps64 #333 ~~> #true.
Example tc4 := testShortcircuitAndTF #() ~~> #true.
Example tc5 := testShortcircuitAndFT #() ~~> #true.
Example tc6 := testShortcircuitOrTF #() ~~> #true.
Example tc7 := testShortcircuitOrFT #() ~~> #true.

(* TODO: this fails.
Compute (check_run (testStandardForLoop #())).
Example tc8 := testStandardForLoop #() ~~> #true.
*)


(* Extraction testing:

Require Coq.extraction.Extraction.
Extraction Language Haskell.
Extract Inductive bool => "GHC.Base.Bool" [ "GHC.Base.True" "GHC.Base.False" ].

Extraction "tc1.hs" tc1.

*)
