From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export lifting.
From Perennial.go_lang Require Import tactics notation.
Set Default Proof Using "Type".

(** This file defines the [array] connective, a version of [mapsto] that works
with lists of values. It also contains array versions of the basic heap
operations of HeapLand. *)

Section go_lang.
  Context `{ffi_semantics: ext_semantics}.
  Context `{!ffi_interp ffi}.

(* technically the definition of array doesn't depend on a state interp, only
the ffiG type; fixing this would require unbundling ffi_interp *)
Definition array `{!heapG Σ} (l : loc) (vs : list val) : iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ i) ↦ v)%I.
Notation "l ↦∗ vs" := (array l vs)
  (at level 20, format "l  ↦∗  vs") : bi_scope.

(** We have no [FromSep] or [IntoSep] instances to remain forwards compatible
with a fractional array assertion, that will split the fraction, not the
list. *)

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l vs : Timeless (array l vs) := _.

Lemma array_nil l : l ↦∗ [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l v : l ↦∗ [v] ⊣⊢ l ↦ v.
Proof. by rewrite /array /= right_id loc_add_0. Qed.

Lemma array_app l vs ws :
  l ↦∗ (vs ++ ws) ⊣⊢ l ↦∗ vs ∗ (l +ₗ length vs) ↦∗ ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  by setoid_rewrite loc_add_assoc.
Qed.

Lemma array_cons l v vs : l ↦∗ (v :: vs) ⊣⊢ l ↦ v ∗ (l +ₗ 1) ↦∗ vs.
Proof.
  rewrite /array big_sepL_cons loc_add_0.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Nat2Z.inj_succ.
  by setoid_rewrite Z.add_1_l.
Qed.

Lemma update_array l vs off v :
  vs !! off = Some v →
  (l ↦∗ vs -∗ ((l +ₗ off) ↦ v ∗ ∀ v', (l +ₗ off) ↦ v' -∗ l ↦∗ <[off:=v']>vs))%I.
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗ X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs)%nat as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗ <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert; last by lia. done.
Qed.

(** Allocation *)
Lemma mapsto_seq_array l v n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ (i : nat)) ↦ v) -∗
  l ↦∗ replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma wp_allocN s E v n :
  (0 < u64_Z n)%Z →
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗ replicate (Word.wordToNat n) v ∗
         [∗ list] i ∈ seq 0 (Word.wordToNat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply wp_allocN_seq; [done..|]. iNext.
  iIntros (l) "Hlm". iApply "HΦ".
  iDestruct (big_sepL_sep with "Hlm") as "[Hl $]".
  by iApply mapsto_seq_array.
Qed.
Lemma twp_allocN s E v n :
  (0 < u64_Z n)%Z →
  [[{ True }]] AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  [[{ l, RET LitV (LitLoc l); l ↦∗ replicate (Word.wordToNat n) v ∗
         [∗ list] i ∈ seq 0 (Word.wordToNat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply twp_allocN_seq; [done..|].
  iIntros (l) "Hlm". iApply "HΦ".
  iDestruct (big_sepL_sep with "Hlm") as "[Hl $]".
  by iApply mapsto_seq_array.
Qed.

Lemma wp_allocN_vec s E v n :
  (0 < u64_Z n)%Z →
  {{{ True }}}
    (* TODO: the coercion from u64 to base_lit doesn't work, which we should probably fix *)
    AllocN #(LitInt n) v @ s ; E
  {{{ l, RET #l; l ↦∗ vreplicate (Word.wordToNat n) v ∗
         [∗ list] i ∈ seq 0 (Word.wordToNat n), meta_token (l +ₗ (i : nat)) ⊤ }}}.
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply wp_allocN; [ lia | done | .. ]. iNext.
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.
Lemma twp_allocN_vec s E v n :
  (0 < u64_Z n)%Z →
  [[{ True }]]
    AllocN #(LitInt n) v @ s ; E
  [[{ l, RET #l; l ↦∗ vreplicate (Word.wordToNat n) v ∗
         [∗ list] i ∈ seq 0 (Word.wordToNat n), meta_token (l +ₗ (i : nat)) ⊤ }]].
Proof.
  iIntros (Hzs Φ) "_ HΦ". iApply twp_allocN; [ lia | done | .. ].
  iIntros (l) "[Hl Hm]". iApply "HΦ". rewrite vec_to_list_replicate. iFrame.
Qed.

(** Access to array elements *)

Lemma wp_load_offset s E l off vs v :
  vs !! off = Some v →
  {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) @ s; E {{{ RET v; l ↦∗ vs }}}.
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_load with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_load_offset_vec s E l sz (off : fin sz) (vs : vec val sz) :
  {{{ ▷ l ↦∗ vs }}} ! #(l +ₗ off) @ s; E {{{ RET vs !!! off; l ↦∗ vs }}}.
Proof. apply wp_load_offset. by apply vlookup_lookup. Qed.

Lemma wp_store_offset s E l off vs v :
  is_Some (vs !! off) →
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_store with "Hl1"). iNext. iIntros "Hl1".
  iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_store_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v :
  {{{ ▷ l ↦∗ vs }}} #(l +ₗ off) <- v @ s; E {{{ RET #(); l ↦∗ vinsert off v vs }}}.
Proof.
  setoid_rewrite vec_to_list_insert. apply wp_store_offset.
  eexists. by apply vlookup_lookup.
Qed.

Lemma wp_cmpxchg_suc_offset s E l off vs v' v1 v2 :
  vs !! off = Some v' →
  v' = v1 →
  vals_compare_safe v' v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v', #true); l ↦∗ <[off:=v2]> vs }}}.
Proof.
  iIntros (Hlookup ?? Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_cmpxchg_suc with "Hl1"); [done..|].
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_cmpxchg_suc_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off = v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #true); l ↦∗ vinsert off v2 vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. eapply wp_cmpxchg_suc_offset=> //.
  by apply vlookup_lookup.
Qed.

Lemma wp_cmpxchg_fail_offset s E l off vs v0 v1 v2 :
  vs !! off = Some v0 →
  v0 ≠ v1 →
  vals_compare_safe v0 v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (v0, #false); l ↦∗ vs }}}.
Proof.
  iIntros (Hlookup HNEq Hcmp Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_cmpxchg_fail with "Hl1"); first done.
  { destruct Hcmp; by [ left | right ]. }
  iIntros "!> Hl1". iApply "HΦ". iDestruct ("Hl2" $! v0) as "Hl2".
  rewrite list_insert_id; last done. iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_cmpxchg_fail_offset_vec s E l sz (off : fin sz) (vs : vec val sz) v1 v2 :
  vs !!! off ≠ v1 →
  vals_compare_safe (vs !!! off) v1 →
  {{{ ▷ l ↦∗ vs }}}
    CmpXchg #(l +ₗ off) v1 v2 @ s; E
  {{{ RET (vs !!! off, #false); l ↦∗ vs }}}.
Proof. intros. eapply wp_cmpxchg_fail_offset=> //. by apply vlookup_lookup. Qed.

(*
Lemma wp_faa_offset s E l off vs (i1 i2 : u64) :
  vs !! off = Some #(LitInt i1) →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #(LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ <[off:=#(LitInt $ Word.wplus i1 i2)]> vs }}}.
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_faa with "Hl1").
  iNext. iIntros "Hl1". iApply "HΦ". iApply "Hl2". iApply "Hl1".
Qed.

Lemma wp_faa_offset_vec s E l sz (off : fin sz) (vs : vec val sz) (i1 i2 : Z) :
  vs !!! off = #i1 →
  {{{ ▷ l ↦∗ vs }}} FAA #(l +ₗ off) #i2 @ s; E
  {{{ RET LitV (LitInt i1); l ↦∗ vinsert off #(i1 + i2) vs }}}.
Proof.
  intros. setoid_rewrite vec_to_list_insert. apply wp_faa_offset=> //.
  by apply vlookup_lookup.
Qed. *)

End lifting.
End go_lang.

Notation "l ↦∗ vs" := (array l vs)
  (at level 20, format "l  ↦∗  vs") : bi_scope.
Typeclasses Opaque array.
