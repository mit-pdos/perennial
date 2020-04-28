From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: list update.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Definition in_bounds γ (a: u64): iProp Σ. Admitted.
Instance in_bounds_persistent γ a : Persistent (in_bounds γ a).
Proof. Admitted.

(* TODO: this will actually require combining in_bounds with some authoritative
resource from the invariant, obviously it can't be for an arbitrary [σ] *)
Theorem in_bounds_valid γ σ a :
  in_bounds γ a -∗ ⌜is_Some (σ.(log_state.d) !! int.val a)⌝.
Proof. Admitted.

(* this is more or less big_sepM_lookup_acc, but with is_installed_read unfolded *)
Theorem is_installed_read_lookup {γ d txns installed_lb} {a: u64} :
  is_Some (d !! int.val a) ->
  is_installed_read γ d txns installed_lb -∗
  ∃ txn_id b,
    ⌜(installed_lb ≤ txn_id)%nat ∧
      apply_upds (txn_upds (take txn_id txns)) d !! int.val a = Some b⌝ ∗
    int.val a d↦ b ∗ (int.val a d↦ b -∗ is_installed_read γ d txns installed_lb).
Proof.
  rewrite /is_installed_read.
  iIntros (Hlookup) "Hbs".
  destruct Hlookup as [b0 Hlookup].
  iDestruct (big_sepM_lookup_acc _ _ _ _ Hlookup with "Hbs") as "[Hb Hbs]".
  iDestruct "Hb" as (b) "(%Hbvalue&Hb&%Ha_bound)".
  destruct Hbvalue as [txn_id (Htxn_id_bound&Htxns_val)].
  iExists txn_id, b.
  iFrame "Hb".
  iSplit; first by auto.
  iIntros "Hb".
  iApply ("Hbs" with "[Hb]").
  { iExists _; iFrame.
    iPureIntro; eauto. }
Qed.

(* simpler read_installed just for experimenting *)
Definition log_read_installed (a:u64): transition log_state.t Block :=
  installed_txn_id ← suchThat (fun s txn_id =>
                                 s.(log_state.installed_lb) ≤
                                 txn_id)%nat;
  d ← reads (disk_at_txn_id installed_txn_id);
  unwrap (d !! int.val a).

Theorem wp_Walog__ReadInstalled (Q: Block -> iProp Σ) l γ a :
  {{{ is_wal P l γ ∗
      in_bounds γ a ∗
       (∀ σ σ' b,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_read_installed a) σ σ' b⌝ -∗
         (P σ ={⊤ ∖↑ N}=∗ P σ' ∗ Q b))
   }}}
    Walog__ReadInstalled #l #a
  {{{ bl, RET slice_val bl; ∃ b, is_block bl b ∗ Q b}}}.
Proof.
  iIntros (Φ) "(#Hwal & #Ha_valid & Hfupd) HΦ".
  wp_call.
  wp_apply (wp_Read_fupd (⊤∖↑walN) (λ b, Q b)%I _ 1 (* q=1 *) with "[Hfupd]").
  { iDestruct "Hwal" as "[Hwal Hcirc]".
    iInv "Hwal" as (σ) "[Hinner HP]" "Hclose".
    iDestruct "Hinner" as "(>? & ? & >? & ? & Hinstalled & ?)"; iNamed.
    iDestruct (is_installed_to_read with "Hinstalled") as "[>Hinstalled_read Hinstalled]".
    iDestruct (in_bounds_valid _ σ with "Ha_valid") as %Hlookup.
    iDestruct (is_installed_read_lookup Hlookup with "Hinstalled_read") as
        (txn_id b [Htxn_id Hbval]) "(Hb&Hinstalled_read)".
    iModIntro.
    iExists b; iFrame "Hb".
    iNext.
    iIntros "Hb".
    iSpecialize ("Hinstalled_read" with "Hb").
    iSpecialize ("Hinstalled" with "Hinstalled_read").
    iMod ("Hfupd" $! σ σ b with "[//] [] HP") as "[HP HQ]".
    { iPureIntro.
      repeat (simpl; monad_simpl).
      exists σ txn_id.
      { econstructor; eauto. }
      repeat (simpl; monad_simpl). }
    iFrame.
    iApply "Hclose".
    iModIntro.
    iExists _; iFrame "HP".
    iFrame.
    auto.
  }
  iIntros (s b) "(HQ&Hs)".
  iApply "HΦ".
  iExists _; iFrame.
  iDestruct (is_slice_to_small with "Hs") as "$".
Qed.

End goose_lang.
