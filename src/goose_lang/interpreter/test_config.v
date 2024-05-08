From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang.interpreter Require Import interpret_types.
From Perennial.goose_lang.interpreter Require Import interpreter.
From Perennial.goose_lang.interpreter Require Import disk_interpreter.
From RecordUpdate Require Import RecordSet.

From Perennial.goose_lang.ffi Require Import disk.

(* there is a right way to do this, and this is definitely not it *)
Definition ffi_is_disk : ffi_state -> disk_state.
Proof.
  eauto.
Defined.

Definition ffi_is_disk' : disk_state -> ffi_state.
Proof.
  eauto.
Defined.

Definition startstate : btstate := let p := inhabitant in
                         ((set world (fun d => ffi_is_disk' $ init_disk (ffi_is_disk d) 30) (fst p), inhabitant), snd p).

(* testing infrastructure *)
Definition run (p: expr): Error val :=
  fst <$> runStateT (interpret 1000 p) startstate.

Tactic Notation "check_run" constr(p) :=
  let x := (eval vm_compute in (run p)) in
  lazymatch x with
  | Works _ ?v => exact v
  | Fail _ ?msg => fail "interpreter failed on" p msg
  end.
Notation check_run p := (ltac:(check_run p)) (only parsing).

Definition runs_to (p: expr) (v: val) :=
  run p = Works _ v.
Notation "p ~~> v" := (runs_to p v) (at level 70).

Inductive outcome_ok (v: val) : val -> Prop := outcome_eq : outcome_ok v v.
Inductive outcome_fail (s: string) : Prop := .

Lemma do_test p v:
  match run p with Works _ w => outcome_ok w v | Fail _ s => outcome_fail s end ->
  runs_to p v.
Proof.
unfold runs_to. destruct run as [v'|e]; intros H.
- apply f_equal. now elim H.
- easy.
Qed.

Ltac test :=
  lazymatch goal with
  | [ |- runs_to ?p _ ] =>
    apply do_test;
    vm_compute;
    lazymatch goal with
    | |- outcome_ok ?v' ?v =>
      reflexivity || fail 0 p "⇝" v' "but expected" v
    | |- outcome_fail ?msg =>
      fail "interpreter failed on" p msg
    | |- ?goal =>
      fail "vm_compute got stuck" goal
    end
  end.
Notation t := ltac:(test) (only parsing).

Definition runWithTrace (e: expr) : Error (val * list string) :=
  (fun p => (fst p, reverse $ snd (snd p))) <$> runStateT (interpret 100 e) startstate.

(* these notations make vm_compute'd values more readable *)
Notation I64_val z := {| i64_car := {| Naive.unsigned := z; Naive._unsigned_in_range := eq_refl |} |}.
Notation I32_val z := {| i32_car := {| Naive.unsigned := z; Naive._unsigned_in_range := eq_refl |} |}.
Notation I8_val z := {| i8_car := {| Naive.unsigned := z; Naive._unsigned_in_range := eq_refl |} |}.

Module Examples.
  Coercion Var' := Var.
  Definition computeSix : val :=
    (rec: <> <> :=
       #3 + #3).
  Definition add2_u32 : val :=
    (λ: "x", "x" + #(I32 2)).

  Definition addRecId : val :=
    (rec: "f" "x" := "x").

  Example run1 : computeSix #() ~~> #6 := t.
  Fail Example run1 : computeSix #() ~~> #5 := t.
  Fail Example run2 : add2_u32 #333 ~~> #(I32 335) := t.

End Examples.
