From Perennial.go_lang Require Import prelude.
From Perennial.go_lang.interpreter Require Import interpret_types.
From Perennial.go_lang.interpreter Require Import interpreter.
From Perennial.go_lang.interpreter Require Import disk_interpreter.

From Perennial.go_lang.examples Require Import goose_unittest.
From Perennial.go_lang.ffi Require Import disk.
Require Import Program.

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

Compute (runStateT (interpret 10 (AllocN #1 (zero_val uint32T))) startstate).
Compute (runStateT (interpret 10 (returnTwoWrapper #3)) startstate).
Compute (runStateT (interpret 10 (testRec #0)) startstate).

Definition run (p: expr): Error val :=
  fst <$> runStateT (interpret 100 p) startstate.

Notation check_run p := (ltac:(let x := (eval vm_compute in (run p)) in
                               lazymatch x with
                               | Works _ ?v => exact v
                               | Fail _ ?msg => fail "interpreter failed on" p msg
                               end)) (only parsing).

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

(* TODO: all currently fail and shouldn't:
Compute (check_run (testShortcircuitAndTF #())).
Compute (check_run (testShortcircuitAndFT #())).
Compute (check_run (testShortcircuitOrTF #())).
Compute (check_run (testShortcircuitOrFT #())).
*)

Definition test_case (p: expr) :=
  match (fst <$> runStateT (interpret 100 p) startstate) with
  | Works _ (LitV (LitBool true)) => true
  | _ => false
  end.

(* fails because #333 is a uint64 *)
Fail Compute (check_run (EncDec32 #333)).
Definition tc1 := (test_case (testEncDec64 #333)).
Definition tc2 := (test_case (testEncDec32 #(U32 333))).
Definition tc3 := (test_case (testReverseAssignOps64 #333)).

Example tc1_ok : tc1 = true := eq_refl.
Example tc2_ok : tc2 = true := eq_refl.
Example tc3_ok : tc3 = true := eq_refl.

(* Extraction testing:

Require Coq.extraction.Extraction.
Extraction Language Haskell.
Extract Inductive bool => "GHC.Base.Bool" [ "GHC.Base.True" "GHC.Base.False" ].

Extraction "tc1.hs" tc1.

*)

