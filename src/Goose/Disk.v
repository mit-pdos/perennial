From RecordUpdate Require Import RecordSet.
From Tactical Require Import ProofAutomation.

From Perennial Require Import Spec.Proc.
From Perennial Require Import Spec.InjectOp.
From Perennial Require Import Spec.SemanticsHelpers.
From Perennial Require Import Spec.LockDefs.
From Perennial.Goose Require Import Machine.
From Perennial.Goose Require Import GoZeroValues.
From Perennial.Goose Require Import Heap.

From Classes Require Import EqualDec.
From stdpp Require Import fin_maps.

From Transitions Require Import Relations.

Import EqualDecNotation.

Definition BlockSize : uint64 := 4096.
Opaque BlockSize.
Definition Block {model:GoModel} := slice.t byte.

Module Disk.
  Section GoModel.
  Context `{model_wf:GoModelWf}.

  Implicit Types (a:uint64) (v:Block).

  (* the types of the arguments are determined by their name, using the implicit
  types given above *)
  Inductive Op : Type -> Type :=
  | Read a : Op Block
  | Write a v : Op unit
  | Size : Op uint64
  | Barrier : Op unit
  .

  Section OpWrappers.

    Context {Op'} {i:Injectable Op Op'}.
    Notation proc := (proc Op').
    Notation "'Call!' op" := (Call (inject op) : proc _) (at level 0, op at level 200).
    Definition read a : proc _ := Call! Read a.
    Definition write a v : proc _ := Call! Write a v.
    Definition size : proc _ := Call! Size.
    Definition barrier : proc _ := Call! Barrier.

  End OpWrappers.

  Record State :=
    (* TODO: this isn't accurate since a Block is an alias for a slice, whereas
    the state of the disk is the underlying data *)
    mkState { blocks: list Block; }.

  Global Instance _eta : Settable State :=
    settable! mkState <blocks>.

  Import RelationNotations.

  Definition inBounds a : relation State State unit :=
    readSome (fun s => nth_error s.(blocks) a);; pure tt.

  Definition step T (op:Op T) : relation State State T :=
    match op with
    (* TODO: these semantics don't make sense, they need to mediate between the
    heap and the disk *)
    | Read a => inBounds a;;
                        such_that (fun s r => nth_error s.(blocks) a = Some r)
    | Write a v => inBounds a;;
                           puts (set blocks (list_insert a v))
    | Size => reads (fun s => length s.(blocks))
    | Barrier => pure tt (* TODO: track buffers *)
    end.

  Definition crash_step : relation State State unit :=
    pure tt.

  Theorem crash_step_non_err s res :
      crash_step s res ->
      res <> Err.
  Proof.
    destruct res; eauto.
  Qed.

  Global Instance empty_disk : Empty State :=
    {| blocks := nil; |}.

  End GoModel.
End Disk.
