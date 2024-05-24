From stdpp Require Import fin_maps.
From iris.proofmode Require Import tactics coq_tactics.
From Perennial.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Export lifting.
From Perennial.goose_lang Require Import proofmode tactics.
From Perennial.goose_lang.lib Require Import typed_mem.typed_mem.
Set Default Proof Using "Type".

(** This file defines the [array] connective, a version of [pointsto] that works
with lists of values. It also contains array versions of the basic heap
operations of GooseLang. *)

Reserved Notation "l ↦∗[ t ] vs" (at level 20,
                                  t at level 50,
                                  format "l  ↦∗[ t ]  vs").
Reserved Notation "l ↦∗[ t ]{# q } vs" (at level 20,
                                       t at level 50, q at level 50,
                                       format "l  ↦∗[ t ]{# q }  vs").
Reserved Notation "l ↦∗[ t ]□ vs" (at level 20,
                                       t at level 50,
                                       format "l  ↦∗[ t ]□  vs").
Reserved Notation "l ↦∗[ t ]{ dq } vs" (at level 20,
                                       t at level 50, dq at level 50,
                                       format "l  ↦∗[ t ]{ dq }  vs").

Section goose_lang.
Context `{ffi_sem: ffi_semantics}.
Context {ext_tys:ext_types ext}.
Context `{!ffi_interp ffi}.

(* technically the definition of array doesn't depend on a state interp, only
the ffiGS type; fixing this would require unbundling ffi_interp *)
Definition array `{!heapGS Σ} (l : loc) (dq:dfrac) (t:ty) (vs : list val) : iProp Σ :=
  ([∗ list] i ↦ v ∈ vs, (l +ₗ[t] i) ↦[t]{dq} v)%I.
Notation "l ↦∗[ t ]{# q } vs" := (array l (DfracOwn q) t vs) : bi_scope.
Notation "l ↦∗[ t ]□ vs" := (array l DfracDiscarded t vs) : bi_scope.
Notation "l ↦∗[ t ]{ dq } vs" := (array l dq t vs) : bi_scope.
Notation "l ↦∗[ t ] vs" := (array l (DfracOwn 1) t vs) : bi_scope.

(** We have no [FromSep] or [IntoSep] instances to remain forwards compatible
with a fractional array assertion, that will split the fraction, not the
list. *)

Section lifting.
Context `{!heapGS Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types (v:val) (t:ty) (l:loc).
Implicit Types (vs : list val).
Implicit Types (sz off : nat).

Global Instance array_timeless l q t vs : Timeless (array l q t vs) := _.

Lemma array_nil l t q : l ↦∗[t]{q} [] ⊣⊢ emp.
Proof. by rewrite /array. Qed.

Lemma array_singleton l t q v : l ↦∗[t]{q} [v] ⊣⊢ l ↦[t]{q} v.
Proof. by rewrite /array /= right_id Z.mul_0_r loc_add_0. Qed.

Lemma array_app l t q vs ws :
  l ↦∗[t]{q} (vs ++ ws) ⊣⊢ l ↦∗[t]{q} vs ∗ (l +ₗ[t] length vs) ↦∗[t]{q} ws.
Proof.
  rewrite /array big_sepL_app.
  setoid_rewrite Nat2Z.inj_add.
  setoid_rewrite loc_add_assoc.
  setoid_rewrite Z.mul_add_distr_l.
  done.
Qed.

Lemma array_cons l v t q vs : l ↦∗[t]{q} (v :: vs) ⊣⊢ l ↦[t]{q} v ∗ (l +ₗ ty_size t) ↦∗[t]{q} vs.
Proof.
  rewrite /array big_sepL_cons Z.mul_0_r loc_add_0.
  f_equiv.
  setoid_rewrite loc_add_assoc.
  assert (forall i, ty_size t * S i = ty_size t + ty_size t * i) as Hoff; [ lia | ].
  by setoid_rewrite Hoff.
Qed.

Lemma array_split (i:Z) l t q vs :
  0 <= i ->
  i <= Z.of_nat (length vs) ->
  l ↦∗[t]{q} vs ⊣⊢
        l ↦∗[t]{q} (take (Z.to_nat i) vs) ∗ (l +ₗ[t] i) ↦∗[t]{q} (drop (Z.to_nat i) vs).
Proof.
  intros Hn Hlength.
  rewrite <- (take_drop (Z.to_nat i) vs) at 1.
  rewrite array_app.
  rewrite take_length.
  rewrite Nat.min_l; last lia.
  rewrite Z2Nat.id; last lia.
  auto.
Qed.

Lemma array_split_nm (n m: nat) {l t q vs} :
  (n + m)%nat = length vs ->
  l ↦∗[t]{q} vs -∗
    ∃ vs1 vs2, ⌜vs = vs1 ++ vs2 ∧ length vs1 = n ∧ length vs2 = m⌝ ∗
               l ↦∗[t]{q} vs1 ∗ (l +ₗ[t] n) ↦∗[t]{q} vs2.
Proof.
  iIntros (Hlen) "Hl".
  rewrite -(take_drop n vs).
  iExists (take n vs), (drop n vs).
  iSplitR.
  { iPureIntro.
    rewrite -> take_length_le by lia.
    rewrite drop_length.
    intuition lia.
  }
  rewrite array_app.
  rewrite -> take_length_le by lia.
  iFrame.
Qed.

Global Instance array_fractional l t vs :
  fractional.Fractional (λ q, array l (DfracOwn q) t vs) := _.

Global Instance array_as_fractional l t q vs :
  fractional.AsFractional (array l (DfracOwn q) t vs) (λ q, array l (DfracOwn q) t vs) q.
Proof. constructor; auto; apply _. Qed.

Theorem loc_add_stride_Sn l t n :
  l +ₗ[t] S n = (l +ₗ ty_size t) +ₗ[t] n.
Proof.
  replace (Z.mul (ty_size t) (S n)) with (ty_size t + Z.mul (ty_size t) n).
  { rewrite loc_add_assoc //. }
  replace (Z.of_nat (S n)) with (1 + Z.of_nat n) by lia.
  rewrite Z.mul_add_distr_l.
  f_equal.
  rewrite Z.mul_1_r //.
Qed.

Lemma array_agree l t q1 q2 vs1 vs2 :
  length vs1 = length vs2 ->
  array l q1 t vs1 -∗ array l q2 t vs2 -∗
  ⌜vs1 = vs2⌝.
Proof.
  rewrite /array; iIntros (Hlen) "Ha1 Ha2".
  (iInduction vs1 as [|v1 vs1] "IH" forall (l vs2 Hlen)).
  { simpl in Hlen.
    destruct vs2; simpl in Hlen; try congruence.
    auto. }
  destruct vs2; simpl in Hlen; first by congruence.
  simpl.
  iDestruct "Ha1" as "[Hx1 Ha1]".
  iDestruct "Ha2" as "[Hx2 Ha2]".
  iDestruct (struct_pointsto_agree with "Hx1 Hx2") as "->".
  setoid_rewrite loc_add_stride_Sn.
  iDestruct ("IH" $! _ vs2 with "[] Ha1 Ha2") as %->; auto.
Qed.

Global Instance array_persistent l t vs : Persistent (array l DfracDiscarded t vs).
Proof. apply _. Qed.

Lemma array_persist l dq t vs:
  array l dq t vs ==∗ array l DfracDiscarded t vs.
Proof.
  rewrite /array.
  iIntros "Ha".
  iDestruct (big_sepL_mono with "Ha") as "Ha".
  2: iMod (big_sepL_bupd with "Ha") as "Ha".
  { iIntros (???) "H".
    iMod (struct_pointsto_persist with "H") as "H". iModIntro. iExact "H". }
  iModIntro. iFrame "Ha".
Qed.

Lemma array_frac_valid l t q vs :
  0 < ty_size t →
  0 < length vs →
  array l (DfracOwn q) t vs -∗ ⌜(q ≤ 1)%Qp⌝.
Proof.
  iIntros (??) "Ha".
  destruct vs; [simpl in H0; lia|].
  rewrite /array /=.
  iDestruct "Ha" as "[Hl _]".
  by iApply (struct_pointsto_frac_valid with "Hl").
Qed.

(* this lemma is just used to prove the update version (with q=1) and read
version (with arbitrary q but no update) below *)
Local Lemma update_array_gen {l vs off t q v} :
  vs !! off = Some v →
  ⊢ l ↦∗[t]{q} vs -∗ ((l +ₗ[t] off) ↦[t]{q} v ∗ ∀ v', (l +ₗ[t] off) ↦[t]{q} v' -∗ l ↦∗[t]{q} <[off:=v']>vs).
Proof.
  iIntros (Hlookup) "Hl".
  rewrite -[X in (l ↦∗[_]{_} X)%I](take_drop_middle _ off v); last done.
  iDestruct (array_app with "Hl") as "[Hl1 Hl]".
  iDestruct (array_cons with "Hl") as "[Hl2 Hl3]".
  assert (off < length vs)%nat as H by (apply lookup_lt_is_Some; by eexists).
  rewrite take_length min_l; last by lia. iFrame "Hl2".
  iIntros (w) "Hl2".
  clear Hlookup. assert (<[off:=w]> vs !! off = Some w) as Hlookup.
  { apply list_lookup_insert. lia. }
  rewrite -[in (l ↦∗[_]{_} <[off:=w]> vs)%I](take_drop_middle (<[off:=w]> vs) off w Hlookup).
  iApply array_app. rewrite take_insert; last by lia. iFrame.
  iApply array_cons. rewrite take_length min_l; last by lia. iFrame.
  rewrite drop_insert_gt; last by lia. done.
Qed.

Lemma update_array {l vs off t v} :
  vs !! off = Some v →
  ⊢ l ↦∗[t] vs -∗ ((l +ₗ[t] off) ↦[t] v ∗ ∀ v', (l +ₗ[t] off) ↦[t] v' -∗ l ↦∗[t] <[off:=v']>vs).
Proof.
  apply update_array_gen.
Qed.

Lemma array_elem_acc {l vs off t q v} :
  vs !! off = Some v →
  l ↦∗[t]{q} vs -∗ (l +ₗ[t] off) ↦[t]{q} v ∗ ((l +ₗ[t] off) ↦[t]{q} v -∗ l ↦∗[t]{q} vs).
Proof.
  iIntros (Hlookup) "Hl".
  iDestruct (update_array_gen Hlookup with "Hl") as "[$ Hupd]".
  iIntros "Hoff".
  iSpecialize ("Hupd" with "Hoff").
  rewrite list_insert_id //.
Qed.

(** Allocation *)
Lemma pointsto_seq_array l v t n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ[t] (i : nat)) ↦[t] v) -∗
  l ↦∗[t] replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Nat2Z.inj_succ. setoid_rewrite <-Z.add_1_l.
  setoid_rewrite Z.mul_add_distr_l.
  setoid_rewrite Z.mul_1_r.
  setoid_rewrite <-loc_add_assoc. iApply "IH". done.
Qed.

Lemma Zmul_S_r (n: nat) z : z * S n = z + z * n.
Proof.
  lia.
Qed.

Lemma pointsto_seq_struct_array l v t n :
  ([∗ list] i ∈ seq 0 n, (l +ₗ[t] (i:nat)) ↦[t] v) -∗
  l ↦∗[t] replicate n v.
Proof.
  rewrite /array. iInduction n as [|n'] "IH" forall (l); simpl.
  { done. }
  rewrite Z.mul_0_r loc_add_0.
  iIntros "[$ Hl]". rewrite -fmap_S_seq big_sepL_fmap.
  setoid_rewrite Zmul_S_r.
  setoid_rewrite <-loc_add_assoc.
  by iApply "IH".
Qed.

Lemma wp_allocN t s E v (n: u64) :
  (0 < uint.Z n)%Z →
  val_ty v t ->
  {{{ True }}} AllocN (Val $ LitV $ LitInt $ n) (Val v) @ s; E
  {{{ l, RET LitV (LitLoc l); l ↦∗[t] replicate (uint.nat n) v }}}.
Proof.
  iIntros (Hsz Hty Φ) "_ HΦ". wp_apply wp_allocN_seq; [done..|].
  iIntros (l) "Hlm". iApply "HΦ".
  iApply pointsto_seq_struct_array.
  iApply (big_sepL_mono with "Hlm").
  iIntros (k y Heq) "Hvals".
  rewrite (nat_scaled_offset_to_Z Hty).
  rewrite struct_pointsto_eq /struct_pointsto_def.
  iSplitL; auto.
Qed.

Lemma wp_load_offset s E l q off t vs v :
  vs !! off = Some v →
  {{{ l ↦∗[t]{q} vs }}} ![t] #(l +ₗ[t] off) @ s; E {{{ RET v; l ↦∗[t]{q} vs ∗ ⌜val_ty v t⌝ }}}.
Proof.
  iIntros (Hlookup Φ) "Hl HΦ".
  iDestruct (array_elem_acc (l:=l) Hlookup with "Hl") as "[Hl1 Hl2]".
  iDestruct (struct_pointsto_ty with "Hl1") as %Hty.
  wp_load.
  iApply "HΦ".
  iSplitL; eauto.
  iApply ("Hl2" with "Hl1").
Qed.

Lemma wp_store_offset s E l off vs t v :
  is_Some (vs !! off) →
  val_ty v t ->
  {{{ ▷ l ↦∗[t] vs }}} (#(l +ₗ[t] off) <-[t] v)%V @ s; E {{{ RET #(); l ↦∗[t] <[off:=v]> vs }}}.
Proof.
  iIntros ([w Hlookup] Hty Φ) ">Hl HΦ".
  iDestruct (update_array (l:=l) Hlookup with "Hl") as "[Hl1 Hl2]".
  wp_store.
  iApply "HΦ". iApply ("Hl2" with "Hl1").
Qed.

End lifting.
End goose_lang.

Notation "l ↦∗[ t ]{# q } vs" := (array l (DfracOwn q) t vs) : bi_scope.
Notation "l ↦∗[ t ]□ vs" := (array l DfracDiscarded t vs) : bi_scope.
Notation "l ↦∗[ t ]{ dq } vs" := (array l dq t vs) : bi_scope.
Notation "l ↦∗[ t ] vs" := (array l (DfracOwn 1) t vs) : bi_scope.
Typeclasses Opaque array.

Ltac iFramePtsTo_core tac :=
  match goal with
  | [ |- envs_entails ?Δ ((?l +ₗ ?z) ↦∗[_] ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j ((l +ₗ ?z') ↦∗[_] ?v')] =>
      unify v v';
      replace z with z';
      [ iExact j | tac ]
    end
  | [ |- envs_entails ?Δ (?l ↦ ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j (l ↦ ?v')] =>
      replace v with v';
      [ iExact j | tac ]
    end
  | [ |- envs_entails ?Δ (?l ↦[?t]{?q} ?v) ] =>
    match Δ with
    | context[Esnoc _ ?j (l ↦[_]{q} ?v')] =>
      replace v with v';
      [ iExact j | tac ]
    end
  end.

Tactic Notation "iFramePtsTo" := iFramePtsTo_core ltac:(idtac).
Tactic Notation "iFramePtsTo" "by" tactic(t) := iFramePtsTo_core ltac:(by t).
