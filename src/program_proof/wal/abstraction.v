From RecordUpdate Require Import RecordSet.

From stdpp Require Import gmap.
From iris.algebra Require Import ofe.

From Perennial.Helpers Require Import Tactics Integers.
From Perennial.program_proof Require Import disk_lib.
From Perennial.goose_lang Require Import ffi.disk.

Module update.
  Record t :=
    mk { addr: u64;
         b: Block; }.
  Global Instance _eta: Settable _ := settable! mk <addr; b>.
  Global Instance _witness: Inhabited t := populate!.
End update.

Definition LogSz: Z := 511.
Hint Unfold LogSz : word.

Definition disk := gmap Z Block.
Canonical Structure diskO := leibnizO disk.

Definition txn_upds (txns: list (u64 * list update.t)) : list update.t :=
  concat (snd <$> txns).

Module log_state.
  Record t :=
    mk {
        d: disk;
        txns: list (u64 * list update.t);
        (* installed_lb promises what will be read after a cache miss *)
        installed_lb: nat;
        (* durable_lb promises what will be on-disk after a crash *)
        durable_lb: nat;
      }.
  Global Instance _eta: Settable _ := settable! mk <d; txns; installed_lb; durable_lb>.
  Global Instance _witness: Inhabited t := populate!.

  Definition updates σ : list update.t := txn_upds σ.(txns).
End log_state.

Definition addr_wf (a: u64) (d: disk) :=
  2 + LogSz ≤ int.Z a ∧
  ∃ (b: Block), d !! (int.Z a) = Some b.

Definition addrs_wf (updates: list update.t) (d: disk) :=
  Forall (λ u, addr_wf u.(update.addr) d) updates.

(** * Monotonic lists *)
Section list_mono.
  Context {A} (ltR: A → A → Prop) {Htrans: Transitive ltR}.
  Implicit Types (l: list A).
  Definition list_mono l :=
    ∀ (i1 i2: nat) (x1 x2: A)
      (Hlt: (i1 < i2)%nat)
      (Hx1: l !! i1 = Some x1)
      (Hx2: l !! i2 = Some x2),
      ltR x1 x2.

  Theorem list_mono_app l1 l2 :
    list_mono (l1 ++ l2) <->
    list_mono l1 ∧ list_mono l2 ∧
    (∀ i1 i2 x1 x2
       (Hx1: l1 !! i1 = Some x1)
       (Hx2: l2 !! i2 = Some x2),
        ltR x1 x2).
  Proof.
    split; intros.
    - split_and!.
      + rewrite /list_mono; intros **.
        apply (H i1 i2 x1 x2); auto.
        { rewrite lookup_app_l; auto.
          eapply lookup_lt_Some; eauto. }
        { rewrite lookup_app_l; auto.
          eapply lookup_lt_Some; eauto. }
      + rewrite /list_mono; intros.
        apply (H (length l1 + i1)%nat (length l1 + i2)%nat x1 x2).
        { lia. }
        { rewrite lookup_app_r; auto; try lia.
          replace (length l1 + i1 - length l1)%nat with i1 by lia; auto. }
        { rewrite lookup_app_r; auto; try lia.
          replace (length l1 + i2 - length l1)%nat with i2 by lia; auto. }
      + intros.
        apply (H i1 (length l1 + i2)%nat x1 x2).
        { apply lookup_lt_Some in Hx1.
          lia. }
        { rewrite lookup_app_l; auto.
          eapply lookup_lt_Some; eauto. }
        { rewrite lookup_app_r; auto; try lia.
          replace (length l1 + i2 - length l1)%nat with i2 by lia; auto. }
    - destruct_and! H.
      hnf; intros **.
      apply lookup_app_Some in Hx1.
      apply lookup_app_Some in Hx2.
      intuition idtac.
      + eapply H0; eauto.
      + eapply H2; eauto.
      + apply lookup_lt_Some in H4.
        apply lookup_lt_Some in H1.
        lia.
      + eapply H; [ | eauto | eauto ].
        lia.
  Qed.

  Theorem list_mono_singleton (x:A) :
    list_mono [x].
  Proof.
    hnf; intros.
    apply lookup_lt_Some in Hx1.
    apply lookup_lt_Some in Hx2.
    simpl in *.
    lia.
  Qed.

End list_mono.

Definition wal_wf (s : log_state.t) :=
  addrs_wf (log_state.updates s) s.(log_state.d) ∧
  (* monotonicity of txnids  *)
  list_mono (λ pos1 pos2, int.Z pos1 ≤ int.Z pos2) (fst <$> s.(log_state.txns)) ∧
  s.(log_state.installed_lb) ≤ s.(log_state.durable_lb) < length s.(log_state.txns).

(** * apply_upds: interpret txns on top of disk *)
Definition apply_upds (upds: list update.t) (d: disk): disk :=
  fold_left (fun d '(update.mk a b) => <[int.Z a := b]> d) upds d.

Definition has_updates (log: list update.t) (txns: list (u64 * list update.t)) :=
  forall d, apply_upds log d =
            apply_upds (txn_upds txns) d.

(** * Properties of above definitions *)

Theorem txn_upds_app txn1 txn2:
  txn_upds (txn1 ++ txn2) =
  txn_upds txn1 ++ txn_upds txn2.
Proof.
  rewrite /txn_upds.
  rewrite -concat_app -fmap_app //=.
Qed.

Theorem txn_upds_cons txn txnl:
  txn_upds (txn :: txnl) =
  txn_upds [txn] ++ txn_upds txnl.
Proof.
  rewrite -txn_upds_app //=.
Qed.

Theorem txn_upds_single pos upds :
  txn_upds [(pos, upds)] = upds.
Proof.
  rewrite /txn_upds /=.
  rewrite app_nil_r //.
Qed.

Theorem apply_upds_cons disk u ul :
  apply_upds (u :: ul) disk =
  apply_upds ul (apply_upds [u] disk).
Proof. reflexivity. Qed.

Theorem apply_upds_app upds1 upds2 d :
  apply_upds (upds1 ++ upds2) d =
  apply_upds upds2 (apply_upds upds1 d).
Proof.
  rewrite /apply_upds fold_left_app //.
Qed.

Lemma txn_upds_nils nils :
  Forall (λ x, snd x = nil) nils ->
  txn_upds nils = nil.
Proof.
  rewrite /txn_upds.
  induction nils; simpl in *; intros.
  - done.
  - inversion H; clear H; simpl in *; subst.
    rewrite H2. simpl. eauto.
Qed.

Theorem has_updates_nil :
  has_updates [] [].
Proof. rewrite /has_updates //. Qed.

Theorem has_updates_eq_nil log txns :
  log = [] →
  txns = [] →
  has_updates log txns.
Proof. intros -> ->. rewrite /has_updates //. Qed.

Theorem has_updates_app log1 txns1 log2 txns2 :
  has_updates log1 txns1 ->
  has_updates log2 txns2 ->
  has_updates (log1 ++ log2) (txns1 ++ txns2).
Proof.
  rewrite /has_updates; intros.
  rewrite txn_upds_app !apply_upds_app.
  rewrite H H0 //.
Qed.

Lemma has_updates_app_nils log txns nils :
  Forall (λ x, snd x = nil) nils ->
  has_updates log txns ->
  has_updates log (txns ++ nils).
Proof.
  rewrite /has_updates; intros.
  rewrite txn_upds_app.
  rewrite apply_upds_app.
  rewrite txn_upds_nils; eauto.
Qed.

Lemma has_updates_app_nils_2 log txns nils :
  Forall (λ x, snd x = nil) nils ->
  has_updates log (txns ++ nils) ->
  has_updates log txns.
Proof.
  rewrite /has_updates; intros.
  specialize (H0 d).
  rewrite txn_upds_app in H0.
  rewrite apply_upds_app in H0.
  rewrite (txn_upds_nils nils) /= in H0; eauto.
Qed.

Lemma has_updates_prepend_nils log txns nils :
  Forall (λ x, snd x = nil) nils ->
  has_updates log (nils ++ txns) ->
  has_updates log txns.
Proof.
  rewrite /has_updates; intros.
  specialize (H0 d).
  rewrite txn_upds_app in H0.
  rewrite apply_upds_app in H0.
  rewrite (txn_upds_nils nils) /= in H0; eauto.
Qed.

Lemma has_updates_prepend_nils_2 log txns nils :
  Forall (λ x, snd x = nil) nils ->
  has_updates log txns ->
  has_updates log (nils ++ txns).
Proof.
  rewrite /has_updates; intros.
  specialize (H0 d).
  rewrite txn_upds_app.
  rewrite apply_upds_app.
  rewrite (txn_upds_nils nils) /=; eauto.
Qed.
