From stdpp Require Import list.
From Perennial.Helpers Require Import List ListLen Map.
From Perennial.Helpers Require Import NamedProps.

From iris.proofmode Require Import tactics.
From iris.bi.lib Require Import fractional.
From Perennial.base_logic.lib Require Import own.
From Perennial.algebra Require Import auth_map.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

Class alistG Σ A :=
  { alist_inG :> mapG Σ nat A; }.

Definition alistΣ A : gFunctors := #[ mapΣ nat A ].

Instance subG_alistΣ Σ A : subG (alistΣ A) Σ → alistG Σ A.
Proof. solve_inG. Qed.

Section list.
Context {A:Type}.
Context `{!alistG Σ A}.
Implicit Types (γ:gname) (l:list A) (i:nat) (x:A).

Definition list_el γ i x := ptsto_ro γ i x.
Definition list_subseq γ start xs: iProp Σ :=
  [∗ list] i↦x ∈ xs, list_el γ (start+i) x.

Definition list_ctx γ q l: iProp Σ :=
  "Hctx" ∷ map_ctx γ q (map_seq 0 l) ∗
  "Hels" ∷ [∗ list] i↦x ∈ l, list_el γ i x.

Global Instance list_ctx_timeless γ q l : Timeless (list_ctx γ q l).
Proof. apply _. Qed.
Global Instance list_el_timeless γ i x : Timeless (list_el γ i x).
Proof. apply _. Qed.
Global Instance list_el_persistent γ i x : Persistent (list_el γ i x).
Proof. apply _. Qed.
Global Instance list_ctx_fractional γ l : Fractional (λ q, list_ctx γ q l).
Proof. apply _. Qed.

Theorem alist_alloc l :
  ⊢ |==> ∃ γ, list_ctx γ 1 l.
Proof.
  (* the proof allocates each element individually to keep track of all of the
  initial [ptsto_ro] facts *)
  induction l as [|x l] using rev_ind.
  - iMod (map_init ∅) as (γ) "Hctx".
    iModIntro.
    iExists _; iFrame.
    rewrite big_sepL_nil //.
  - iMod IHl as (γ) "Hctx".
    iExists γ.
    iNamed "Hctx".
    iMod (map_alloc_ro (length l) x with "Hctx") as "[Hctx Hx]".
    { apply lookup_map_seq_None. right. lia. }
    iModIntro.
    rewrite /list_ctx map_seq_snoc.
    iFrame "Hctx".
    rewrite big_sepL_app; iFrame.
    simpl.
    replace (length l + 0) with (length l) by lia.
    iFrame.
Qed.

Theorem alist_lookup_el {γ l q} i x :
  l !! i = Some x →
  list_ctx γ q l -∗ list_el γ i x.
Proof.
  iIntros (Hlookup) "Hctx"; iNamed "Hctx".
  iDestruct (big_sepL_lookup with "Hels") as "Hx"; eauto.
Qed.

Theorem alist_lookup_subseq {γ q} l (n m: nat) :
  n ≤ m ≤ length l →
  list_ctx γ q l -∗
  list_subseq γ n (subslice n m l).
Proof.
  iIntros (Hbound) "Hctx".
  replace m with (n + (m - n)) by lia.
  remember (m-n) as k.
  assert (n + k ≤ length l) by lia.
  clear dependent m.
  generalize dependent k; intros k ?.
  (iInduction k as [|k] "IH" forall (n H)).
  - rewrite Nat.add_0_r.
    rewrite subslice_zero_length /list_subseq //=.
  - list_elem l n as x.
    iDestruct (alist_lookup_el n with "Hctx") as "#Hx"; eauto.
    replace (n + S k) with (S n + k) by lia.
    erewrite subslice_S; eauto; try lia.
    rewrite /list_subseq /=.
    iDestruct ("IH" $! (S n) with "[%] Hctx") as "Hels".
    { lia. }
    rewrite Nat.add_0_r.
    setoid_rewrite <- Nat.add_succ_comm.
    iFrame "# ∗".
Qed.

Lemma list_subseq_nil {γ} n : ⊢ list_subseq γ n [].
Proof.
  rewrite /list_subseq big_sepL_nil //.
Qed.

Theorem alist_lookup {γ q} l i x :
  list_ctx γ q l -∗ list_el γ i x -∗ ⌜l !! i = Some x⌝.
Proof.
  iIntros "Hctx Hel"; iNamed "Hctx".
  iDestruct (map_ro_valid with "Hctx Hel") as %Hlookup.
  rewrite lookup_map_seq_0 in Hlookup.
  auto.
Qed.

Theorem alist_agree {γ} l i x1 x2 :
  list_el γ i x1 -∗
  list_el γ i x2 -∗
  ⌜x1 = x2⌝.
Proof.
  rewrite /list_el.
  iApply ptsto_ro_agree.
Qed.

Theorem alist_app1 {γ l} x :
  list_ctx γ 1 l ==∗
  list_ctx γ 1 (l ++ [x]) ∗ list_el γ (length l) x.
Proof.
  iNamed 1.
  iMod (map_alloc_ro (length l) x with "Hctx") as "[Hctx #Hx]".
  { rewrite lookup_map_seq_None. right. lia. }
  iModIntro.
  rewrite /list_ctx map_seq_snoc.
  iFrame "# ∗".
  simpl.
  rewrite Nat.add_0_r.
  iFrame "Hx".
Qed.

Theorem alist_app {γ} l xs :
  list_ctx γ 1 l ==∗
  list_ctx γ 1 (l ++ xs) ∗ list_subseq γ (length l) xs.
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
  list_ctx γ 1 l -∗ list_subseq γ start xs -∗
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

Typeclasses Opaque list_ctx.
