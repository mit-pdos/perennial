From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

From Goose.github_com.mit_pdos.go_journal Require Import wal.

From Perennial.Helpers Require Import Transitions.
From Perennial.program_proof Require util_proof.
From Perennial.program_proof Require Import disk_prelude disk_lib.
From Perennial.program_proof Require Import wal.abstraction.

Implicit Types (txn_id:nat) (pos: u64).

Existing Instance r_mbind.
Existing Instance fallback_genPred.

Definition update_durable: transition log_state.t unit :=
  new_durable ← suchThat
              (λ s new_durable,
               (s.(log_state.durable_lb) ≤
                new_durable <
                length s.(log_state.txns))%nat);
  modify (set log_state.durable_lb (λ _, new_durable)).

Definition update_installed: transition log_state.t nat :=
  new_installed ← suchThat
              (λ s new_installed,
                 (s.(log_state.installed_lb) ≤
                  new_installed ≤
                  s.(log_state.durable_lb))%nat);
  modify (set log_state.installed_lb (λ _, new_installed));;
  ret new_installed.

Definition log_crash : transition log_state.t unit :=
  crash_txn ← suchThat
            (λ s (crash_txn: nat),
               (s.(log_state.durable_lb) ≤ crash_txn < length s.(log_state.txns))%nat);
  modify (set log_state.txns (fun txns => take (S crash_txn) txns));;
  modify (set log_state.durable_lb (fun _ => crash_txn));;
  ret tt.

Lemma log_crash_unfold σ σ' :
  relation.denote log_crash σ σ' () ↔
  ∃ (crash_txn:nat),
    (σ.(log_state.durable_lb) ≤ crash_txn < length σ.(log_state.txns))%nat ∧
    σ' = (set log_state.txns (take (S crash_txn)) σ)
           <|log_state.durable_lb := crash_txn|>.
Proof.
  rewrite /log_crash.
  split; simpl; intros.
  - monad_inv.
    eauto.
  - destruct H as (crash_txn & Hbounds & ->).
    eapply (relation.bind_runs _ _ _ _ crash_txn).
    + simpl.
      constructor; eauto.
    + monad_simpl.
Qed.

Definition suchThatMax {Σ} (pred: Σ -> nat -> Prop) : transition Σ nat :=
  suchThat (λ s x, pred s x ∧ ∀ y, pred s y -> y ≤ x).

Definition log_flush (pos:u64) (txn_id: nat) : transition log_state.t unit :=
  assert (λ s, is_txn s.(log_state.txns) txn_id pos);;
  new_durable ← suchThat
              (λ s (new_durable: nat),
                 (Nat.max s.(log_state.durable_lb) txn_id ≤ new_durable < length s.(log_state.txns))%nat);
  modify (set log_state.durable_lb (λ _, (new_durable)));;
  ret tt.

Definition allocPos : transition log_state.t u64 :=
  suchThat (λ s (pos': u64),
            (∀ (pos: u64) txn_id,
                is_txn s.(log_state.txns) txn_id pos ->
                int.Z pos ≤ int.Z pos')).

Definition log_mem_append (txn: list update.t): transition log_state.t u64 :=
  pos ← allocPos;
  modify (set log_state.txns (fun txns => txns ++ [(pos,txn)]));;
  ret pos.

Lemma list_singleton_lookup {A} (i: nat) (x1 x2: A) :
  [x1] !! i = Some x2 ->
  (i = 0%nat) ∧ x1 = x2.
Proof.
  destruct i; simpl.
  - inversion 1; auto.
  - rewrite lookup_nil; inversion 1.
Qed.

Theorem mem_append_preserves_wf σ pos upds :
  addrs_wf upds σ.(log_state.d) ->
  (* pos should be at least as high as any position given out *)
  (∀ (pos': u64) txn_id,
      is_txn σ.(log_state.txns) txn_id pos' ->
      int.Z pos' ≤ int.Z pos) ->
  wal_wf σ ->
  wal_wf (set log_state.txns (λ txns, txns ++ [(pos, upds)]) σ).
Proof.
  simpl.
  intros Haddrwf Hpos_highest Hwf.
  destruct_and! Hwf.
  split_and!; simpl; auto.
  - rewrite /log_state.updates /=.
    rewrite /addrs_wf.
    rewrite txn_upds_app.
    apply Forall_app_2; eauto.
    rewrite txn_upds_single //.
  - rewrite fmap_app.
    simpl.
    apply list_mono_app.
    split_and!; auto.
    { apply list_mono_singleton. }
    intros.
    apply list_singleton_lookup in Hx2 as [-> ->].
    eapply Hpos_highest; eauto.
    rewrite /is_txn.
    rewrite -list_lookup_fmap; eauto.
  - len.
Qed.

Theorem log_mem_append_preserves_wf txn σ σ' pos :
  addrs_wf txn σ.(log_state.d) ->
  wal_wf σ ->
  relation.denote (log_mem_append txn) σ σ' pos ->
  wal_wf σ'.
Proof.
  simpl.
  intros Haddrwf Hwf Htrans; monad_inv.
  eapply mem_append_preserves_wf; eauto.
Qed.

Definition disk_at_txn_id (txn_id: nat) (s:log_state.t): disk :=
  apply_upds (txn_upds (take (S txn_id) (log_state.txns s))) s.(log_state.d).

Definition updates_for_addr (a: u64) (l : list update.t) : list Block :=
  update.b <$> filter (λ u, u.(update.addr) = a) l.

Definition updates_since (txn_id: nat) (a: u64) (s : log_state.t) : list Block :=
  updates_for_addr a (txn_upds (drop (S txn_id) (log_state.txns s))).

Fixpoint latest_update (base: Block) (upds: list Block) : Block :=
  match upds with
  | u :: upds' =>
    latest_update u upds'
  | nil => base
  end.

Definition last_disk (s:log_state.t): disk :=
  disk_at_txn_id (length (log_state.txns s)) s.

Definition no_updates_since σ a txn_id :=
  Forall (λ u, u.(update.addr) ≠ a)
         (txn_upds (drop (S txn_id) (log_state.txns σ))).

Definition log_read_cache (a:u64): transition log_state.t (option Block) :=
  ok ← any bool;
  if (ok:bool)
  then d ← reads last_disk;
       match d !! int.Z a with
       | None => undefined
       | Some b => ret (Some b)
       end
  else
    (* on miss, read makes [installed_to] precise enough so the caller can
    use [log_read_installed] and together get the current value at [a] *)
    update_durable;;
    update_installed;;
    suchThat (fun s (_:unit) =>
                no_updates_since s a s.(log_state.installed_lb));;
    ret None.

Definition installed_disk (s:log_state.t): disk :=
  disk_at_txn_id s.(log_state.installed_lb) s.

Definition log_read_installed (a:u64): transition log_state.t Block :=
  installed_txn_id ← suchThat (fun s txn_id =>
                                 s.(log_state.installed_lb) ≤
                                 txn_id <
                                 length s.(log_state.txns))%nat;
  d ← reads (disk_at_txn_id installed_txn_id);
  unwrap (d !! int.Z a).
