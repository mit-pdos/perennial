From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lifting.
From Perennial.goose_lang Require Import tactics notation typing.
Set Default Proof Using "Type".

(** This file defines the [array] connective, a version of [mapsto] that works
with lists of values. It also contains array versions of the basic heap
operations of HeapLand. *)

Reserved Notation "l ↦∗[ t ] vs" (at level 20, format "l  ↦∗[ t ]  vs").

Section goose_lang.
  Context `{ffi_semantics: ext_semantics}.
  Context {ext_tys:ext_types ext}.
  Context `{!ffi_interp ffi}.

(* technically the definition of array doesn't depend on a state interp, only
the ffiG type; fixing this would require unbundling ffi_interp *)
Definition array `{!heapG Σ} (l : loc) (t:ty) (vs : list val) : iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ[t] i) ↦[t] v)%I.
Notation "l ↦∗[ t ] vs" := (array l t vs) : bi_scope.

(** We have no [FromSep] or [IntoSep] instances to remain forwards compatible
with a fractional array assertion, that will split the fraction, not the
list. *)

Section lifting.
Context `{!heapG Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types σ : state.
Implicit Types v : val.
Implicit Types t : ty.
Implicit Types vs : list val.
Implicit Types l : loc.
Implicit Types sz off : nat.

Global Instance array_timeless l t vs : Timeless (array l t vs) := _.

Lemma array_nil l t : l ↦∗[t] [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l t v : l ↦∗[t] [v] ⊣⊢ l ↦[t] v.
Proof. by rewrite /array /= right_id Z.mul_0_r loc_add_0. Qed.

Lemma array_app l t vs ws :
  l ↦∗[t] (vs ++ ws) ⊣⊢ l ↦∗[t] vs ∗ (l +ₗ[t] length vs) ↦∗[t] ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Z.mul_add_distr_l.
  done.
Qed.

Lemma array_cons l v t vs : l ↦∗[t] (v :: vs) ⊣⊢ l ↦[t] v ∗ (l +ₗ ty_size t) ↦∗[t] vs.
Proof.
  rewrite /array big_sepL_cons Z.mul_0_r loc_add_0.
  f_equiv.
  setoid_rewrite loc_add_assoc.
  assert (forall i, ty_size t * S i = ty_size t + ty_size t * i) as Hoff; [ lia | ].
  by setoid_rewrite Hoff.
Qed.

Lemma update_array l vs off t v :
  vs !! off = Some v →
  (l ↦∗[t] vs -∗ ((l +ₗ[t] off) ↦[t] v ∗ ∀ v', (l +ₗ[t] off) ↦[t] v' -∗ l ↦∗[t] <[off:=v']>vs))%I.
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗[_] X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs)%nat as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗[_] <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert; last by lia. done.
Qed.

(** Allocation *)
Lemma mapsto_seq_array l v t n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ[t] (i : nat)) ↦[t] v) -∗
  l ↦∗[t] replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite Z.mul_add_distr_l.
  setoid_rewrite Z.mul_1_r.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma Zmul_S_r (n: nat) z : z * S n = z + z * n.
Proof.
  lia.
Qed.

Lemma mapsto_seq_struct_array l v t n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ[t] (i:nat)) ↦[t] v) -∗
  l ↦∗[t] replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  rewrite Z.mul_0_r loc_add_0.
  iIntros "[$ Hl]". rewrite -fmap_seq big_sepL_fmap.
  setoid_rewrite Zmul_S_r.
  setoid_rewrite <-loc_add_assoc.
  by iApply "IH".
Qed.

Lemma wp_allocN s E v t (n: u64) :
  (0 < int.val n)%Z →
  val_ty v t ->
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗[t] replicate (int.nat n) v }}}.
Proof.
  iIntros (Hsz Hty Φ) "_ HΦ". iApply wp_allocN_seq; [done..|]. iNext.
  iIntros (l) "Hlm". iApply "HΦ".
  by iApply mapsto_seq_struct_array.
Qed.

(** Access to array elements *)
(* moved to basic_triples *)

(*
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
*)

End lifting.
End goose_lang.

Notation "l  ↦∗[ t ]  vs" := (array l t vs) : bi_scope.
Typeclasses Opaque array.
