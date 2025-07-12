From iris.algebra Require Import gmap lib.mono_nat.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From iris.algebra Require Import mono_list.
From Perennial.program_proof Require Import proof_prelude.

Section definitions.
Class fmlist_mapG Σ K V `{Countable K} :=
   { #[global] fmlist_map_inG :: inG Σ (gmapR K (mono_listR (leibnizO V))) }.

Definition fmlist_mapΣ K V `{Countable K} := #[GFunctor (gmapUR K (mono_listR (leibnizO V)))].

Global Instance subG_fmlist_mapΣ K V `{Countable K} {Σ} :
  subG (fmlist_mapΣ K V) Σ → fmlist_mapG Σ K V.
Proof. solve_inG. Qed.

Context `{fmlist_mapG Σ K V}.
Definition fmlist_ptsto_def γ (k:K) dq v :=
  own γ {[ k := ●ML{dq} v]}.
Definition fmlist_ptsto_aux : seal (@fmlist_ptsto_def). Proof. by eexists. Qed.
Definition fmlist_ptsto := fmlist_ptsto_aux.(unseal).
Definition fmlist_ptsto_eq : @fmlist_ptsto = @fmlist_ptsto_def := fmlist_ptsto_aux.(seal_eq).

Definition fmlist_ptsto_lb_def γ (k:K) v :=
  own γ {[ k := ◯ML v ]}.
Definition fmlist_ptsto_lb_aux : seal (@fmlist_ptsto_lb_def). Proof. by eexists. Qed.
Definition fmlist_ptsto_lb := fmlist_ptsto_lb_aux.(unseal).
Definition fmlist_ptsto_lb_eq : @fmlist_ptsto_lb = @fmlist_ptsto_lb_def := fmlist_ptsto_lb_aux.(seal_eq).

End definitions.

(** * Notation *)
Notation "k ⤳l[ γ ] dq v " := (fmlist_ptsto γ k dq v)
(at level 20, dq custom dfrac at level 1, format "k  ⤳l[ γ ] dq   v") : bi_scope.
Notation "k ⤳l[ γ ]⪰ v " := (fmlist_ptsto_lb γ k v)
(at level 20, format "k  ⤳l[ γ ]⪰  v") : bi_scope.

Local Ltac unseal := rewrite
  ?fmlist_ptsto_lb_eq /fmlist_ptsto_lb_def
  ?fmlist_ptsto_eq /fmlist_ptsto_def.

Section lemmas.
  Context `{fmlist_mapG Σ K V}.
  Implicit Types (k : K) (l : list V) (dq : dfrac) (q : Qp).

  (** * Instances about the fmlist_ptsto and fmlist_ptsto_lb *)
  Global Instance fmlist_ptsto_timeless k γ dq l : Timeless (k ⤳l[γ]{dq} l).
  Proof. unseal. apply _. Qed.
  Global Instance fmlist_ptsto_persistent k γ l : Persistent (k ⤳l[γ]□ l).
  Proof. unseal. apply _. Qed.
  Global Instance fmlist_ptsto_fractional k γ l : Fractional (λ q, k ⤳l[γ]{#q} l)%I.
  Proof. unseal. intros p q. rewrite -own_op singleton_op -mono_list_auth_dfrac_op. done. Qed.
  Global Instance fmlist_ptsto_as_fractional k γ q v :
    AsFractional (k ⤳l[γ]{#q} v) (λ q, k ⤳l[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Global Instance fmlist_ptsto_lb_timeless k γ l : Timeless (k ⤳l[γ]⪰ l).
  Proof. unseal. apply _. Qed.
  Global Instance fmlist_ptsto_lb_persistent k γ l : Persistent (k ⤳l[γ]⪰ l).
  Proof. unseal. apply _. Qed.

  (** * Lemmas about the fmlist_ptsto and fmlist_ptsto_lb *)
  Lemma fmlist_ptsto_valid k γ dq v : k ⤳l[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Hpoints_to".
    iDestruct (own_valid with "Hpoints_to") as %Hvalid%singleton_valid.
    rewrite mono_list_auth_dfrac_valid in Hvalid. done.
  Qed.

  Lemma fmlist_ptsto_valid_2 k γ dq1 dq2 v1 v2 :
    k ⤳l[γ]{dq1} v1 -∗ k ⤳l[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    rewrite singleton_op singleton_valid mono_list_auth_dfrac_op_valid_L in Hvalid.
    done.
  Qed.

  Lemma fmlist_ptsto_agree k γ dq1 dq2 v1 v2 :
    k ⤳l[γ]{dq1} v1 -∗ k ⤳l[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hpoints_to1 Hpoints_to2".
    iDestruct (fmlist_ptsto_valid_2 with "Hpoints_to1 Hpoints_to2") as %[_ ?].
    done.
  Qed.

  Lemma fmlist_ptsto_combine k γ dq1 dq2 v1 v2 :
    k ⤳l[γ]{dq1} v1 -∗ k ⤳l[γ]{dq2} v2 -∗ k ⤳l[γ]{dq1 ⋅ dq2} v1 ∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (fmlist_ptsto_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl".
    iFrame.
    done.
  Qed.

  Lemma fmlist_ptsto_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ⤳l[γ]{dq1} v1 -∗ k2 ⤳l[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (fmlist_ptsto_valid_2 with "H1 H2") as %[??].
  Qed.

  Lemma fmlist_ptsto_ne γ k1 k2 dq2 v1 v2 :
    k1 ⤳l[γ] v1 -∗ k2 ⤳l[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply fmlist_ptsto_frac_ne. apply: exclusive_l. Qed.

  (** Make an points_toent read-only. *)
  Lemma fmlist_ptsto_persist k γ dq v :
    k ⤳l[γ]{dq} v ==∗ k ⤳l[γ]□ v.
  Proof. unseal. iApply own_update. apply singleton_update.
         apply mono_list_auth_persist. Qed.

  (** * Lemmas about [ghost_map_auth] *)
  Lemma fmlist_map_alloc_strong P (m:gmap K (list V)) :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∗ [∗ map] k ↦ v ∈ m, k ⤳l[γ] v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (A:= (gmapUR K (mono_listR (leibnizO V))))
                              (fmap (λ v, (●ML (v:list (leibnizO V)))) m) P)
      as (γ) "Hauth".
    { done. }
    {
      intros k.
      rewrite lookup_fmap.
      simpl.
      destruct (@lookup _ _ _ _ _).
      { simpl. apply mono_list_auth_valid. }
      { done. }
    }
    iExists γ.
    iDestruct "Hauth" as "[$ Hauth]".
    rewrite -(big_opM_singletons (_ <$> m)).
    rewrite big_opM_own_1.
    rewrite big_sepM_fmap.
    iApply (big_sepM_impl with "Hauth").
    do 2 iModIntro.
    iIntros.
    iFrame.
  Qed.

  Lemma fmlist_map_alloc_fin (l:list V) `{!finite.Finite K} :
    ⊢ |==> ∃ γ, [∗ set] k ∈ (fin_to_set K), k ⤳l[γ] l.
  Proof.
    set (m:=gset_to_gmap (K:=K) (A:=(list V)) l (fin_to_set K)).
    iStartProof.
    iMod (fmlist_map_alloc_strong (λ _, True) m) as (?) "[_ H]".
    { apply pred_infinite_True. }
    iModIntro.
    iExists γ.
    replace (fin_to_set K) with (dom m); last first.
    { apply dom_gset_to_gmap. }
    iDestruct (big_sepM_dom) as "Hm".
    iDestruct "Hm" as "[Hm1 _]".
    iApply ("Hm1" with "[H]").
    iApply (big_sepM_impl with "H").
    iModIntro.
    iIntros.
    apply lookup_gset_to_gmap_Some in H2.
    naive_solver.
  Qed.

  Lemma fmlist_ptsto_update {γ k v} w :
    prefix v w →
    k ⤳l[γ] v ==∗ k ⤳l[γ] w.
  Proof.
    intros.
    unseal. apply bi.entails_wand. apply own_update.
    apply singleton_update.
    apply mono_list_update.
    done.
  Qed.

  Lemma fmlist_ptsto_lb_agree dq γ k l l' :
    k ⤳l[γ]{dq} l -∗
    k ⤳l[γ]⪰ l' -∗
    ⌜prefix l' l⌝.
  Proof.
    unseal.
    iIntros "Hptsto Hlb".
    iDestruct (own_valid_2 with "Hptsto Hlb") as %Hvalid.
    rewrite singleton_op singleton_valid mono_list_both_dfrac_valid_L in Hvalid.
    naive_solver.
  Qed.

  Lemma fmlist_ptsto_lb_comparable γ k l l' :
    k ⤳l[γ]⪰ l -∗
    k ⤳l[γ]⪰ l' -∗
    ⌜prefix l l' ∨ prefix l' l⌝.
  Proof.
    unseal.
    iIntros "Hlb1 Hlb2".
    iDestruct (own_valid_2 with "Hlb1 Hlb2") as %Hvalid.
    by rewrite singleton_op singleton_valid mono_list_lb_op_valid_L in Hvalid.
  Qed.

  Lemma fmlist_ptsto_lb_longer γ k l l' :
    (length l ≤ length l')%nat →
    k ⤳l[γ]⪰ l -∗
    k ⤳l[γ]⪰ l' -∗
    ⌜prefix l l'⌝.
  Proof.
    iIntros (?) "Hlb1 Hlb2".
    iDestruct (fmlist_ptsto_lb_comparable with "Hlb1 Hlb2") as "%Hcases".
    destruct Hcases as [Hbad|Hσ_ineq]; first done.
    enough (l'=l) by naive_solver.
    by apply prefix_length_eq.
  Qed.

  Lemma fmlist_ptsto_lb_len_eq γ k l l' :
    (length l = length l')%nat →
    k ⤳l[γ]⪰ l -∗
    k ⤳l[γ]⪰ l' -∗
    ⌜l = l'⌝.
  Proof.
    iIntros (?) "Hlb1 Hlb2".
    iDestruct (fmlist_ptsto_lb_longer with "Hlb1 Hlb2") as "%Hcases".
    { lia. }
    apply prefix_length_eq in Hcases.
    { done. } lia.
  Qed.

  Lemma fmlist_ptsto_get_lb γ k l dq :
    k ⤳l[γ]{dq} l -∗
    k ⤳l[γ]⪰ l.
  Proof.
    unseal. iApply (own_mono).
    apply singleton_included_mono.
    apply mono_list_included.
  Qed.

  Lemma fmlist_ptsto_lb_mono γ k l l' :
    prefix l' l →
    k ⤳l[γ]⪰ l -∗
    k ⤳l[γ]⪰ l'.
  Proof.
    intros. unseal. iApply (own_mono).
    apply singleton_included_mono.
    by apply mono_list_lb_mono.
  Qed.

End lemmas.
