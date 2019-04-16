From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement CSL.NamedDestruct CSL.BigDynOp.
From RecoveryRefinement.Examples.MailServer Require Import MailAPI MailAPILemmas MailTriples.
From RecoveryRefinement.Goose.Examples Require Import MailServer.
From RecoveryRefinement.Goose.Proof Require Import Interp.
Require Import Goose.Proof.RefinementAdequacy.
From RecoveryRefinement Require AtomicPair.Helpers.
From RecoveryRefinement.Goose Require Import Machine GoZeroValues Heap GoLayer.
From RecoveryRefinement.Goose Require Import Machine.
From RecoveryRefinement.Goose Require Import GoZeroValues.

Inductive compile_mail_base {gm: GoModel} : forall {T}, proc Mail.Op T → proc GoLayer.Op T → Prop :=
| cm_open :
    compile_mail_base (Call Mail.Open)
                      (MailServer.Open)
| cm_pickup uid :
    compile_mail_base (Mail.pickup uid)
                      (MailServer.Pickup uid)
| cm_deliver uid msg :
    compile_mail_base (Mail.deliver uid msg)
                      (MailServer.Deliver uid msg)
| cm_delete uid msg :
    compile_mail_base (Call (Mail.Delete uid msg))
                      (MailServer.Delete uid msg)
| cm_unlock uid :
    compile_mail_base (Call (Mail.Unlock uid))
                      (MailServer.Unlock uid)
| cm_dataop {T} (op: Data.Op T) :
    compile_mail_base (Call (Mail.DataOp op))
                      (Call (DataOp op)).

Definition mail_impl {gm: GoModel} :=
  {| compile_rel_base := @compile_mail_base gm;
     recover_rel := rec_singleton (MailServer.Recover) |}.

Import Filesys.FS.
Import GoLayer.Go.
Import Mail.

Definition init_base `{@GoModelWf gm} (s: GoLayer.Go.State) :=
  s.(fs).(FS.heap) = ∅ ∧
  (forall (uid: uint64),
      (uid < 100 -> s.(fs).(dirents) !! (UserDir uid) = Some ∅) ∧
      (uid >= 100 -> s.(fs).(dirents) !! (UserDir uid) = None)) ∧
  s.(fs).(FS.dirents) !! SpoolDir = Some ∅ ∧
  dom (gset string) s.(fs).(FS.dirents) =
  dom (gset string) s.(fs).(FS.dirlocks) ∧
  (∀ dir l, s.(fs).(FS.dirlocks) !! dir = Some l → fst l = Unlocked) ∧
  s.(maillocks) = None.

Definition init_absr `{@GoModelWf gm} sa sc := Mail.initP sa ∧ init_base sc.

Lemma mail_crash_refinement_seq `{@GoModelWf gm} {T} σ1c σ1a esa esc:
  init_absr σ1a σ1c →
  wf_client_seq esa →
  compile_rel_proc_seq mail_impl esa esc →
  ¬ proc_exec_seq Mail.l esa (rec_singleton (Ret ())) (1, σ1a) Err →
  ∀ σ2c (res: T), proc_exec_seq GoLayer.Go.l esc
                                      (rec_singleton MailServer.Recover) (1, σ1c) (Val σ2c res) →
  ∃ σ2a, proc_exec_seq Mail.l esa (rec_singleton (Ret tt)) (1, σ1a) (Val σ2a res).
Proof.
Abort.