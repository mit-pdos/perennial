From Coq Require Import List.

From RecoveryRefinement Require Export Lib.

Module Var.
  Inductive id := Sum | Count | Lock.
  Inductive Op : Type -> Type :=
  | Read (i:id) : Op nat
  | Write (i:id) (v:nat) : Op unit
  | CAS (i:id) (vold: nat) (vnew:nat) : Op nat .
  Definition State := (nat * nat * nat)%type.

  Definition get (i:id) : State -> nat :=
    match i with
    | Sum => fun '(x, _, _) => x
    | Count => fun '(_, y, _) => y
    | Lock => fun '(_, _, z) => z
    end.

  Definition set (i:id) (v:nat) : State -> State :=
    match i with
    | Sum => fun '(_, y, z) => (v, y, z)
    | Count => fun '(x, _, z) => (x, v, z)
    | Lock => fun '(x, y, _) => (x, y, v)
    end.

  Import RelationNotations.
  Definition cas_rel (i: id) (vold: nat) (vnew: nat): RelationAlgebra.relation State State nat :=
    v <- reads (get i);
    if nat_eq_dec v vold then
        puts (set i vnew);;
        pure v
    else
        pure v.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Read i => reads (get i)
         | Write i v => puts (set i v)
         | CAS i vold vnew => cas_rel i vold vnew
         end;
       crash_step :=
         puts (fun _ => (0, 0, 0)); |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       initP := fun s => s = (0, 0, 0)|}.
End Var.

Module DB.
  Inductive Op : Type -> Type :=
  | Add (n:nat) : Op unit
  | Avg : Op nat.
  Definition State := list nat.

  Definition dynamics : Dynamics Op State :=
    {| step T (op: Op T) :=
         match op with
         | Add n => puts (cons n)
         | Avg => reads (fun l => fold_right plus 0 l / length l)
         end;
       crash_step :=
         puts (fun _ => nil); |}.

  Lemma crash_total_ok (s: State):
    exists s', dynamics.(crash_step) s (Val s' tt).
  Proof. eexists; econstructor. Qed.

  Lemma crash_non_err_ok (s: State) ret:
    dynamics.(crash_step) s ret -> ret ≠ Err.
  Proof. inversion 1; congruence. Qed.

  Definition l : Layer Op :=
    {| Layer.State := State;
       sem := dynamics;
       trace_proj := fun _ => nil;
       crash_preserves_trace := fun _ _ _ => eq_refl;
       crash_total := crash_total_ok;
       crash_non_err := crash_non_err_ok;
       initP := fun s => s = nil |}.
End DB.

Definition read i := Call (Var.Read i).
Definition write i v := Call (Var.Write i v).
Definition cas i vold vnew := Call (Var.CAS i vold vnew).

Definition lock : proc Var.Op unit :=
  Loop (fun (_ : unit) =>
          x <- Call (Var.CAS Var.Lock 0 1);
          Ret (if nat_eq_dec x 0 then
                  DoneWithOutcome tt
                else
                  ContinueOutcome tt)
       )%proc tt.
Definition unlock : proc Var.Op unit := Call (Var.Write Var.Lock 0).

Definition add n :=
  (_ <- lock;
   sum <- read Var.Sum; _ <- write Var.Sum (n + sum)%nat;
   count <- read Var.Count; _ <- write Var.Count (1 + count)%nat;
   unlock)%proc.

Definition avg :=
  (_ <- lock;
   sum <- read Var.Sum; count <- read Var.Count; _ <- unlock; Ret (sum/count)%nat)%proc.

Definition impl : LayerImpl Var.Op DB.Op :=
  {| compile_op T (op: DB.Op T) :=
       match op with
       | DB.Add n => add n
       | DB.Avg => avg
       end;
     recover := Seq_Cons (Ret tt) (Seq_Nil);
     (* init := Ret Initialized; *) |}.
