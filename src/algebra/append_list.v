From Perennial.Helpers Require Import List Map.
From Perennial.Helpers Require Import NamedProps.

From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import own.
From Perennial.algebra Require Import auth_map.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Class alistG A Σ :=
  { alist_inG :> mapG nat A Σ; }.

Section list.
Context {A:Type}.
Context `{!alistG A Σ}.
Implicit Types (γ:gname) (l:list A) (i:nat) (x:A).

Definition list_el γ i x := ptsto_ro γ i x.
Definition list_subseq γ start xs: iProp Σ :=
  [∗ list] i↦x ∈ xs, list_el γ (start+i) x.

Definition list_ctx γ l: iProp Σ :=
  "Hctx" ∷ map_ctx γ (list_to_imap l) ∗
  "Hels" ∷ [∗ list] i↦x ∈ l, list_el γ i x.

Global Instance list_ctx_timeless : Timeless (list_ctx γ l).
Proof. apply _. Qed.
Global Instance list_el_timeless : Timeless (list_el γ i x).
Proof. apply _. Qed.
Global Instance list_el_persistent : Persistent (list_el γ i x).
Proof. apply _. Qed.

Lemma lookup_list_to_imap_length l :
  list_to_imap l !! (length l) = None.
Proof.
  rewrite lookup_list_to_imap.
  apply lookup_ge_None_2; lia.
Qed.

Theorem alist_alloc l :
  ⊢ |==> ∃ γ, list_ctx γ l.
Proof.
  (* the proof allocates each element individually to keep track of all of the
  initial [ptsto_ro] facts *)
  induction l as [|x l] using rev_ind.
  - iMod (map_init (list_to_imap [])) as (γ) "Hctx".
    iModIntro.
    iExists _; iFrame.
    rewrite big_sepL_nil //.
  - iMod IHl as (γ) "Hctx".
    iExists γ.
    iNamed "Hctx".
    iMod (map_alloc_ro (length l) x with "Hctx") as "[Hctx Hx]".
    { rewrite lookup_list_to_imap_length //. }
    iModIntro.
    rewrite -list_to_imap_app1.
    iFrame "Hctx".
    rewrite big_sepL_app; iFrame.
    simpl.
    replace (length l + 0) with (length l) by lia.
    iFrame.
Qed.

Theorem alist_lookup_el {γ} l i x :
  l !! i = Some x →
  list_ctx γ l -∗ list_el γ i x.
Proof.
  iIntros (Hlookup) "Hctx"; iNamed "Hctx".
  iDestruct (big_sepL_lookup with "Hels") as "Hx"; eauto.
Qed.

Theorem alist_lookup {γ} l i x :
  list_ctx γ l -∗ list_el γ i x -∗ ⌜l !! i = Some x⌝.
Proof.
  iIntros "Hctx Hel"; iNamed "Hctx".
  iDestruct (map_ro_valid with "Hctx Hel") as %Hlookup.
  rewrite lookup_list_to_imap in Hlookup.
  auto.
Qed.

Theorem alist_app1 {γ l} x :
  list_ctx γ l ==∗
  list_ctx γ (l ++ [x]) ∗ list_el γ (length l) x.
Proof.
  iNamed 1.
  iMod (map_alloc_ro (length l) x with "Hctx") as "[Hctx #Hx]".
  { rewrite lookup_list_to_imap_length //. }
  iModIntro.
  rewrite -list_to_imap_app1.
  iFrame "# ∗".
  simpl.
  rewrite Nat.add_0_r.
  iFrame "Hx".
Qed.

Theorem alist_app {γ} l xs :
  list_ctx γ l ==∗
  list_ctx γ (l ++ xs) ∗ list_subseq γ (length l) xs.
Proof.
  iIntros "Hctx".
  iInduction xs as [|x xs] "IH" using rev_ind.
  - rewrite app_nil_r; iFrame.
    iModIntro.
    rewrite /list_subseq //=.
  - iMod ("IH" with "Hctx") as "[Hctx Hsubseq]".
    iMod (alist_app1 x with "Hctx") as "[Hctx Hx]".
    iModIntro.
    rewrite -app_assoc.
    iFrame.
    simpl.
    rewrite right_id.
    replace (length l + (length xs + 0)) with (length (l ++ xs)).
    { iFrame. }
    rewrite app_length; lia.
Qed.

Theorem alist_subseq_lookup {γ} l start xs :
  list_ctx γ l -∗ list_subseq γ start xs -∗
  ⌜subslice start (start + length xs)%nat l = xs⌝.
Proof.
  iIntros "Hctx Hxs".
  (iInduction xs as [|x xs] "IH" forall (start)).
  - simpl.
    rewrite Nat.add_0_r.
    rewrite subslice_zero_length //.
  - simpl.
    iEval (rewrite /list_subseq big_sepL_cons) in "Hxs".
    iDestruct "Hxs" as "[Hx Hxs]".
    setoid_rewrite <- Nat.add_succ_comm.
    rewrite Nat.add_0_r.
    iDestruct (alist_lookup with "Hctx Hx") as %Hx.
    iDestruct ("IH" with "Hctx Hxs") as %Hxs.
    iPureIntro.
    erewrite subslice_S by (eauto; lia).
    congruence.
Qed.

End list.
