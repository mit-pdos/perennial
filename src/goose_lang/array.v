From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics coq_tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lifting.
From Perennial.goose_lang Require Import proofmode tactics.
From Perennial.goose_lang.lib Require Import typed_mem.typed_mem.
Set Default Proof Using "Type".

(** This file defines the [array] connective, a version of [mapsto] that works
with lists of values. It also contains array versions of the basic heap
operations of GooseLang. *)

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

Theorem nat_scaled_offset_to_Z {v t} {i: nat} :
  val_ty v t ->
  Z.of_nat (length (flatten_struct v)) * i =
  ty_size t * Z.of_nat i.
Proof.
  intros Hty.
  rewrite (val_ty_len Hty).
  pose proof (ty_size_ge_0 t).
  lia.
Qed.

Lemma wp_allocN s E v t (n: u64) :
  (0 < int.val n)%Z →
  val_ty v t ->
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗[t] replicate (int.nat n) v }}}.
Proof.
  iIntros (Hsz Hty Φ) "_ HΦ". wp_apply wp_allocN_seq; [done..|].
  iIntros (l) "Hlm". iApply "HΦ".
  iApply mapsto_seq_struct_array.
  iApply (big_sepL_mono with "Hlm").
  iIntros (k y Heq) "Hvals".
  erewrite (nat_scaled_offset_to_Z Hty).
  iSplitL; auto.
Qed.

(** Access to array elements *)
(* moved to basic_triples *)

Lemma wp_load_offset s E l off t vs v :
  vs !! off = Some v →
  {{{ l ↦∗[t] vs }}} load_ty t #(l +ₗ[t] off) @ s; E {{{ RET v; l ↦∗[t] vs ∗ ⌜val_ty v t⌝ }}}.
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_LoadAt with "Hl1"). iIntros "!> Hl1". iApply "HΦ".
  iDestruct ("Hl2" $! v) as "Hl2". rewrite list_insert_id; last done.
  iDestruct (struct_mapsto_ty with "Hl1") as %Hty.
  iSplitL; eauto.
  iApply ("Hl2" with "[$]").
Qed.

Lemma wp_store_offset s E l off vs t v :
  is_Some (vs !! off) →
  val_ty v t ->
  {{{ ▷ l ↦∗[t] vs }}} store_ty t #(l +ₗ[t] off) v @ s; E {{{ RET #(); l ↦∗[t] <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Hty Φ) ">Hl HΦ".
  iDestruct (update_array l _ _ _ _ Hlookup with "Hl") as "[Hl1 Hl2]".
  iApply (wp_StoreAt _ _ _ _ _ _ Hty with "Hl1"). iIntros "!> Hl1".
  iApply "HΦ". iApply ("Hl2" with "Hl1").
Qed.

End lifting.
End goose_lang.

Notation "l  ↦∗[ t ]  vs" := (array l t vs) : bi_scope.
Typeclasses Opaque array.

Ltac iFramePtsTo_core t :=
  match goal with
  | [ |- envs_entails ?Δ ((?l +ₗ ?z) ↦∗[_] ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j ((l +ₗ ?z') ↦∗[_] ?v')] =>
      unify v v';
      replace z with z';
      [ iExact j | t ]
    end
  | [ |- envs_entails ?Δ (?l ↦ ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j (l ↦ ?v')] =>
      replace v with v';
      [ iExact j | t ]
    end
  end.

Tactic Notation "iFramePtsTo" := iFramePtsTo_core ltac:(idtac).
Tactic Notation "iFramePtsTo" "by" tactic(t) := iFramePtsTo_core ltac:(by t).
