From Coq Require Import List.

From Perennial.Examples Require Import ExMach.ExMachAPI.
From Perennial Require Export Lib Spec.TypedLayer.


Module DB.

  Definition db := list nat.

  Inductive Op : Type -> Type :=
  | New : Op db
  | Add (d: db) (n:nat) : Op db
  | Avg (d: db) : Op nat.

  Definition State := unit.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | New => pure (nil : list nat)
         | Add db n => pure (n :: db)
         | Avg db => pure (fold_right plus 0 db / length db)
         end;
       crash_step :=
         puts (fun _ => tt);
       finish_step :=
         puts (fun _ => tt);
    |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Inductive OpTy :=
    | dbTy | natTy.

  Inductive has_type : forall T, Op T -> OpTy -> Prop :=
    | NewType : has_type New dbTy
    | AddType db n : has_type (Add db n) dbTy
    | AvgType db: has_type (Avg db) natTy.

  Definition l : TypedLayer Op :=
    {| TypedLayer.OpState := State;
       TypedLayer.OpTy := OpTy;
       op_has_type := has_type;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       finish_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       finish_non_err := crash_non_err_ok;
       initP := fun s => s = tt |}.
End DB.

Definition new : proc ExMach.Op _ := Ret (0, 0).
Definition add db n : proc ExMach.Op _ := (Ret (n + fst db, 1 + snd db))%proc.
Definition avg db : proc ExMach.Op _ := (Ret (fst db / snd db)).

Inductive compile_stat_val : forall T1 T2, T1 -> T2 -> Prop :=
  | compile_val_refl {T} (x : T) : compile_stat_val x x.

Inductive compile_stat_base : forall T1 T2, proc DB.Op T1 -> proc ExMach.Op T2 -> Prop :=
  | new_compile : compile_stat_base (Call DB.New) new
  | add_compile db db' n:
      compile_stat_val db db' ->
      compile_stat_base (Call (DB.Add db n)) (add db' n)
  | avg_compile db db':
      compile_stat_val db db' ->
      compile_stat_base (Call (DB.Avg db)) (avg db').

Definition impl : LayerImplRel ExMach.Op DB.Op :=
  {| compile_rel_base := compile_stat_base;
     compile_rel_val := compile_stat_val;
     recover_rel := Seq_Cons (Ret tt) (Seq_Nil); |}.


(* Check that we can actually translate programs *)

Import DB.
Definition test00 :=
  (db <- Call New; db <- Call (Add db 2); db <- Call (Add db 4); Call (Avg db))%proc.

Lemma test00_compile :
  exists (e': proc _ nat), compile_rel impl test00 e'.
Proof.
  eexists.
  eapply cr_bind; intros.
  { repeat econstructor. }
  eapply cr_bind; intros.
  { repeat econstructor. eauto. }
  eapply cr_bind; intros.
  { repeat econstructor. eauto. }
  repeat econstructor. eauto.
Qed.
