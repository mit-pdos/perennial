From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl.
From Perennial.algebra Require Import frac_count big_op.
From Perennial.goose_lang Require Import proofmode notation wpc_proofmode.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy spec_assert language_ctx.
From Perennial.goose_lang Require Import typing typed_translate adequacy refinement.
From Perennial.goose_lang Require Export recovery_adequacy spec_assert refinement_adequacy.
From Perennial.goose_lang Require Import metatheory.
From Perennial.Helpers Require Import Qextra.
From Perennial.Helpers Require List.
From Perennial.goose_lang Require Import logical_reln_defns.

Set Default Proof Using "Type".

Section pfs.
Context {ext: ffi_syntax}.
Context {ffi: ffi_model}.
Context {ffi_semantics: ffi_semantics ext ffi}.
Context `{interp: !ffi_interp ffi}.
Context `{interp_adeq: !ffi_interp_adequacy}.
Context (impl_ty: ext_types ext).

Context {spec_ext: spec_ffi_op}.
Context {spec_ffi: spec_ffi_model}.
Context {spec_ffi_semantics: spec_ext_semantics spec_ext spec_ffi}.
Context `{spec_interp: @spec_ffi_interp spec_ffi}.
Context `{spec_adeq: !spec_ffi_interp_adequacy}.
Context (spec_ty: ext_types (@spec_ffi_op_field spec_ext)).

Notation sstate := (@state (@spec_ffi_op_field spec_ext) (spec_ffi_model_field)).
Notation sexpr := (@expr (@spec_ffi_op_field spec_ext)).
Notation sval := (@val (@spec_ffi_op_field spec_ext)).
Notation istate := (@state ext).
Notation iexpr := (@expr ext).
Notation ival := (@val ext).
Notation sty := (@ty (@val_tys _ spec_ty)).
Notation SCtx := (@Ctx (@val_tys _ spec_ty)).

Context `{hsT_model: !specTy_model spec_ty}.
Context (spec_trans: sval → ival → Prop).
Context (spec_atomic_transTy : SCtx -> sexpr -> iexpr -> sty -> sexpr -> iexpr -> sty -> Prop).
Context `{hG: !heapGS Σ} `{hRG: !refinement_heapG Σ} {hS: styG Σ}.
Lemma loc_paired_eq_iff ls l ls' l':
  loc_paired ls l -∗
  loc_paired ls' l' -∗
  ⌜ l = l' ↔ ls = ls' ⌝.
Proof.
  iIntros "(#Hmls&#Hml) (#Hmls'&#Hml')".
  destruct (decide (ls = ls')).
  { subst. iDestruct (meta_agree with "Hmls Hmls'") as %Heq.
    eauto. }
  destruct (decide (l = l')).
  { subst. iDestruct (meta_agree with "Hml Hml'") as %Heq.
    eauto. }
  eauto.
Qed.

Lemma loc_paired_base_eq_iff ls l ls' l':
  addr_offset l = addr_offset ls →
  addr_offset l' = addr_offset ls' →
  loc_paired (addr_base ls) (addr_base l) -∗
  loc_paired (addr_base ls') (addr_base l') -∗
  ⌜ l = l' ↔ ls = ls' ⌝.
Proof.
  iIntros (??) "(#Hmls&#Hml) (#Hmls'&#Hml')".
  destruct (decide (ls = ls')).
  { subst. iDestruct (meta_agree with "Hmls Hmls'") as %Heq.
    iPureIntro.
    apply addr_base_and_offset_eq_iff; eauto; split; eauto.
  }
  destruct (decide (l = l')).
  { subst. iDestruct (meta_agree with "Hml Hml'") as %Heq.
    iPureIntro.
    apply addr_base_and_offset_eq_iff; eauto; split; eauto.
  }
  eauto.
Qed.

Lemma is_loc_loc_paired ls l vTy:
  is_loc ls l vTy -∗ loc_paired ls l.
Proof. iIntros "(?&$)". Qed.

Lemma is_loc_eq_iff ls l ls' l' vTy vTy':
  is_loc ls l vTy -∗
  is_loc ls' l' vTy' -∗
  ⌜ l = l' ↔ ls = ls' ⌝.
Proof.
  iIntros "(?&H1) (?&H2)".
  iApply (loc_paired_eq_iff with "H1 H2").
Qed.

Lemma litv_loc_eq_iff (ls l ls' l': loc):
  (l = l' ↔ ls = ls') →
  ((#l : ival) = #l' ↔ (#ls: sval) = #ls').
Proof.
  intros Heq.
  split; inversion 1; subst; do 2 f_equal; eapply Heq; auto.
Qed.

Lemma arrayT_structRefT_promote vs v t:
    val_interp (hS := hS) (arrayT t) vs v -∗
    val_interp (hS := hS) (structRefT (flatten_ty t)) vs v.
Proof.
  intros. iIntros "Hv".
  intros. rewrite val_interp_array_unfold.
  iDestruct "Hv" as "[Hv|Hnull]".
  - iDestruct "Hv" as (l ls n idx H0lt Hnonempty (->&->&?&?&Heq1&Heq2)) "(Hsz1&Hsz1'&H1)".
    iAssert (loc_paired (addr_base ls) (addr_base l)) with "[H1]" as "#Hpaired".
    {
      destruct n; try lia; [].
      rewrite ?big_sepL_cons.
      iDestruct "H1" as "(H&_)".
      destruct (flatten_ty t); first by congruence.
      rewrite ?big_sepL_cons.
      iDestruct "H" as "(H&_)".
      iApply is_loc_loc_paired; eauto.
    }
    iLeft.
    assert (0 < length (flatten_ty t))%nat.
    { destruct (flatten_ty t); simpl in *; try congruence. lia. }
    unshelve (iExists l, ls, (n * length (flatten_ty t))%nat, _, _).
    { lia. }
    { destruct (flatten_ty t); simpl in *; try congruence. }
    iSplitL "".
    { iPureIntro; split_and!; eauto. lia. }
    rewrite Nat2Z.inj_mul. iFrame.
    iFrame "Hpaired".
    destruct (decide (0 ≤ idx  ∧ idx < n)%Z) as [(Hr1&Hr2)|Hout]; last first.
    { iRight. iPureIntro. rewrite Heq1.
      assert (idx < 0 ∨ n <= idx) as [?|?] by lia.
      - left. rewrite map_length.
        assert (idx * length (flatten_ty t) + length (flatten_ty t) =
                (idx + 1) * length (flatten_ty t)) as -> by ring.
        apply Z.mul_nonpos_nonneg; lia.
      - right.
        apply Z.mul_le_mono_nonneg_r; lia.
    }
    iLeft.
    iDestruct (big_sepL_elem_of _ (seq 0 n) (Z.to_nat idx) with "H1") as "H".
    { apply elem_of_list_In, in_seq. lia. }
    assert (addr_base ls +ₗ length (flatten_ty t) * Z.to_nat idx = ls) as ->.
    { symmetry. rewrite (addr_plus_off_decode ls); f_equal; word. }
    assert (addr_base l +ₗ length (flatten_ty t) * Z.to_nat idx = l) as ->.
    { symmetry. rewrite (addr_plus_off_decode l); f_equal; word. }
    eauto.
  - iRight. eauto.
Qed.
Lemma ctx_has_semTy_subst
      e (es: sexpr) (t: sty) x v vs tx Γ:
      ctx_has_semTy (hS := hS) (<[x:=tx]> Γ) es e t -∗
      val_interp (hS := hS) tx vs v -∗
      ctx_has_semTy (hS := hS) Γ (subst' x vs es) (subst' x v e) t.
Proof.
  rewrite /ctx_has_semTy.
  iIntros "Hhasty Hval".
  iIntros (Γsubst Hproj) "Hsty Hspec Htrace Hctx".
  destruct x as [|x] => //=.
  { iApply ("Hhasty" with "[] [$] [$] [$]").
    * rewrite insert_anon //=.
    * eauto.
  }
  rewrite -?subst_map_insert'.
  iSpecialize ("Hhasty" $! (<[x := {| subst_ty := tx; subst_sval := vs; subst_ival := v |}]> Γsubst)
                 with "[] [$] [$] [$] [Hctx Hval]").
  { iPureIntro. rewrite -Hproj. apply: fmap_insert. }
  { iPoseProof (big_sepM_insert_2 with "[Hval] [Hctx]") as "$".
    * iFrame.
    * eauto.
  }
  rewrite ?fmap_insert //=.
Qed.

Lemma structRefT_comparableTy_val_eq ts vs1 v1 vs2 v2:
  val_interp (hS := hS) (structRefT ts) vs1 v1 -∗
  val_interp (hS := hS) (structRefT ts) vs2 v2 -∗
  ⌜ v1 = v2 ↔ vs1 = vs2 ⌝.
Proof.
  intros.
  iDestruct 1 as "[H1|Hnull1]";
  iDestruct 1 as "[H2|Hnull2]".
  * iDestruct "H1" as (?? n1 ?? (?&?&?&?&Hoffset1)) "(Hpaired1&_)".
    iDestruct "H2" as (?? n2 ?? (?&?&?&?&Hoffset2)) "(Hpaired2&_)".
    subst.
    iDestruct (loc_paired_base_eq_iff with "Hpaired1 Hpaired2") as %Heq; eauto.
    iPureIntro. apply litv_loc_eq_iff. eauto.
  * iDestruct "Hnull2" as %(?&(Hnull2s&Hnull2)). subst.
    iDestruct "H1" as (????? (?&?&?&?&?)) "H".
    iPureIntro.
    split; subst; inversion 1; exfalso; (eapply plus_off_preserves_non_null; [| eassumption]; eauto).
  * iDestruct "Hnull1" as %(?&(Hnull1s&Hnull1)). subst.
    iDestruct "H2" as (????? (?&?&Hnnull1&Hnnull2&?)) "H".
    iPureIntro.
    split; subst; intros Hnulleq; symmetry in Hnulleq; inversion Hnulleq; subst; symmetry.
    ** exfalso. rewrite addr_base_of_plus //= in Hnnull2.
    ** exfalso. rewrite addr_base_of_plus //= in Hnnull1.
  * iDestruct "Hnull1" as %(?&(Hnull1s&Hnull1)). subst.
    iDestruct "Hnull2" as %(?&(Hnull2s&Hnull2)). subst. iPureIntro. split; intros; eauto.
    ** (* this is kind of round about since inversion is behaving oddly on the null offset hypothesis *)
      f_equal. cut (∀ (l l': loc), #l = #l' → LitLoc l = LitLoc l'); eauto.
       inversion 1; eauto.
    ** (* this is kind of round about since inversion is behaving oddly on the null offset hypothesis *)
      f_equal. cut (∀ (l l': loc), (#l = (#l': @val (@spec_ffi_op_field spec_ext))) →
                                     LitLoc l = LitLoc l'); eauto. inversion 1; eauto.
Qed.

Lemma structRefT_unboxed_baseTy ts vs v:
  val_interp (hS := hS) (structRefT ts) vs v -∗
  ⌜ ∃ ls l, vs = LitV ls ∧ v = LitV l ∧ lit_is_unboxed ls ∧ lit_is_unboxed l ⌝.
Proof.
  intros.
  iDestruct 1 as "[H1|Hnull1]".
  * iDestruct "H1" as (?? n1 ?? (?&?&?&?&Hoffset1)) "(Hpaired1&_)".
    subst. iPureIntro. do 2 eexists; split_and!; eauto; simpl; eauto.
  * iDestruct "Hnull1" as %(?&(Hnull1s&Hnull1)).
    subst. iPureIntro. do 2 eexists; split_and!; eauto; simpl; eauto.
Qed.

Lemma structRefT_unboxedTy ts vs v:
  val_interp (hS := hS) (structRefT ts) vs v -∗
  ⌜ val_is_unboxed vs ∧ val_is_unboxed v ⌝.
Proof.
  intros.
  iDestruct 1 as "[H1|Hnull1]".
  * iDestruct "H1" as (?? n1 ?? (?&?&?&?&Hoffset1)) "(Hpaired1&_)".
    subst. eauto.
  * iDestruct "Hnull1" as %(?&(Hnull1s&Hnull1)). subst.
    eauto.
Qed.

Lemma unboxed_baseTy_val_unboxed_lit t vs v:
  is_unboxed_baseTy t = true →
  val_interp (hS := hS) t vs v -∗
  ⌜ ∃ ls l, vs = LitV ls ∧ v = LitV l ∧ lit_is_unboxed ls ∧ lit_is_unboxed l ⌝.
Proof.
  clear spec_trans.
  revert vs v.
  induction t => vs v; try (inversion 1; fail).
  - intros. destruct t; iPureIntro; naive_solver.
  - intros. iIntros "H".
    iDestruct (arrayT_structRefT_promote with "H") as "H".
    iApply (structRefT_unboxed_baseTy); eauto.
  - intros.
    iApply (structRefT_unboxed_baseTy); eauto.
Qed.

Lemma unboxedTy_val_unboxed t vs v:
  is_unboxedTy t = true →
  val_interp (hS := hS) t vs v -∗
  ⌜ val_is_unboxed vs ∧ val_is_unboxed v ⌝.
Proof.
  clear spec_trans.
  revert vs v.
  induction t => vs v; try (inversion 1; fail).
  - intros. destruct t; iPureIntro; naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as "[H|H]".
    * iDestruct "H" as (?? (->&->)) "H".
      iDestruct (unboxed_baseTy_val_unboxed_lit  with "H") as %(?&?&?&?&?&?); subst; eauto.
    * iDestruct "H" as (?? (->&->)) "H".
      iDestruct (unboxed_baseTy_val_unboxed_lit  with "H") as %(?&?&?&?&?&?); subst; eauto.
  - intros. iIntros "H".
    iDestruct (arrayT_structRefT_promote with "H") as "H".
    iApply (structRefT_unboxedTy); eauto.
  - intros.
    iApply (structRefT_unboxedTy); eauto.
Qed.

Lemma comparableTy_val_eq t vs1 v1 vs2 v2:
  is_comparableTy t = true →
  val_interp (hS := hS) t vs1 v1 -∗
  val_interp (hS := hS) t vs2 v2 -∗
  ⌜ v1 = v2 ↔ vs1 = vs2 ⌝.
Proof.
  clear spec_trans.
  revert vs1 v1 vs2 v2.
  induction t => vs1 v1 vs2 v2; try (inversion 1; fail).
  - intros. destruct t; iPureIntro; naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as (?? ?? (->&->)) "(H1&H2)".
    iDestruct 1 as (?? ?? (->&->)) "(H1'&H2')".
    rewrite -/val_interp.
    iPoseProof (IHt1 with "H1 H1'") as "%"; eauto.
    iPoseProof (IHt2 with "H2 H2'") as "%"; eauto.
    iPureIntro. naive_solver.
  - intros (?&?)%andb_prop.
    intros.
    iDestruct 1 as "[H|H]";
    iDestruct 1 as "[H'|H']";
    iDestruct "H" as (?? (->&->)) "H";
    iDestruct "H'" as (?? (->&->)) "H'".
    * iPoseProof (IHt1 with "H H'") as "%"; eauto.
      iPureIntro. split; inversion 1; subst; f_equal; naive_solver.
    * iPureIntro; split; inversion 1.
    * iPureIntro; split; inversion 1.
    * iPoseProof (IHt2 with "H H'") as "%"; eauto.
      iPureIntro. split; inversion 1; subst; f_equal; naive_solver.
  - intros.
    iIntros "H1 H2".
    iDestruct (arrayT_structRefT_promote with "H1") as "H1".
    iDestruct (arrayT_structRefT_promote with "H2") as "H2".
    iApply (structRefT_comparableTy_val_eq with "H1 H2").
  - intros. apply structRefT_comparableTy_val_eq.
Qed.

Global Arguments sty_val_interp {ext ffi interp spec_ext spec_ffi spec_ffi_semantics spec_interp _ specTy_model Σ _ _}.

Lemma sty_val_size:
      forall  τ vs v,
        sty_val_interp hS τ vs v -∗
        ⌜ length (flatten_struct vs) = 1%nat ∧
          length (flatten_struct v) = 1%nat ⌝.
Proof. iIntros. by iDestruct (sty_val_flatten with "[$]") as %[-> ->]. Qed.

Lemma length_flatten_well_typed vs v t:
  storable t →
  val_interp (hS := hS) t vs v -∗
  ⌜ length (flatten_ty t) = length (flatten_struct vs) ∧
    length (flatten_ty t) = length (flatten_struct v) ⌝.
Proof.
  iIntros (Hstore) "Hval".
  iInduction t as [] "IH" forall (vs v).
  - destruct t; iDestruct "Hval" as %Hval;
    repeat destruct Hval as (?&Hval); subst; eauto.
  - iDestruct "Hval" as (???? (?&?)) "(H1&H2)". subst.
    rewrite /= ?app_length.
    destruct Hstore as (?&?).
    iDestruct ("IH" with "[//] [$]") as %[Heq1 Heq2].
    iDestruct ("IH1" with "[//] [$]") as %[Heq1' Heq2'].
    subst. iPureIntro. lia.
  - inversion Hstore.
  - iDestruct "Hval" as "[Hval|Hval]"; iDestruct "Hval" as (?? (?&?)) "Hval";
      subst; eauto.
  - iDestruct "Hval" as (?????? (?&?)) "H1". subst; eauto.
  - iDestruct "Hval" as "[Hval|Hnull]"; last first.
    { iDestruct "Hnull" as (?) "(%&%)"; subst. eauto. }
    iDestruct "Hval" as (?????? (?&?&?&?)) "H1". subst; eauto.
  - iDestruct "Hval" as (?) "(%&%)"; subst. eauto.
  - iDestruct "Hval" as "[Hval|Hnull]"; last first.
    { iDestruct "Hnull" as (?) "(%&%)"; subst. eauto. }
    iDestruct "Hval" as (????? (?&?&?&?)) "H1". subst; eauto.
  - iDestruct "Hval" as %[].
  - iDestruct "Hval" as %[].
  - rewrite /val_interp/=. iDestruct (sty_val_size with "Hval") as "(%&%)"; eauto.
  - rewrite /val_interp/=. done.
Qed.

Lemma flatten_well_typed vs v t i vsi vi ti:
    storable t →
    flatten_ty t !! i = Some ti →
    flatten_struct vs !! i = Some vsi →
    flatten_struct v !! i = Some vi →
    val_interp (hS := hS) t vs v -∗
    val_interp (hS := hS) ti vsi vi.
Proof.
  iIntros (Hstore Hlookup1 Hlookup2 Hlookup3) "Hval".
  iInduction t as [] "IH" forall (vs v i Hlookup1 Hlookup2 Hlookup3).
  - simpl in *.
    destruct t; destruct i; simpl in *; inversion Hlookup1; subst; eauto;
    iDestruct "Hval" as %Hval; repeat destruct Hval as (?&Hval); subst; eauto;
    simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
  - iDestruct "Hval" as (???? (?&?)) "(H1&H2)". subst.
    simpl in Hlookup1, Hlookup2, Hlookup3.
    destruct Hstore as (?&?).
    iDestruct (length_flatten_well_typed with "H1") as %[Hlen1 Hlens1]; first done.
    iDestruct (length_flatten_well_typed with "H2") as %[Hlen2 Hlens2]; first done.
    apply lookup_app_Some in Hlookup1 as [Hleft|Hright].
    { specialize (lookup_lt_Some _ _ _ Hleft) => Hlen.
      rewrite lookup_app_l in Hlookup2; last by lia.
      rewrite lookup_app_l in Hlookup3; last by lia.
      iApply "IH"; eauto.
    }
    { destruct Hright as (?&Hright).
      specialize (lookup_lt_Some _ _ _ Hright) => Hlen.
      rewrite lookup_app_r in Hlookup2; last by lia.
      rewrite lookup_app_r in Hlookup3; last by lia.
      iApply "IH1"; eauto.
      { rewrite Hlen1; eauto. }
      { rewrite Hlens1; eauto. }
    }
  - inversion Hstore.
  - iDestruct "Hval" as "[Hval|Hval]"; iDestruct "Hval" as (?? (?&?)) "Hval";
      subst; eauto.
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iLeft. iExists _, _. iSplitL ""; first done. eauto. }
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iRight. iExists _, _. iSplitL ""; first done. eauto. }
  - iDestruct "Hval" as (?????? (->&->)) "H". subst.
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iExists _,_,_,_,_,_. iFrame. eauto. }
  - iDestruct "Hval" as "[Hval|Hnull]".
    { iDestruct "Hval" as (?????? (?&?&?&?)) "H1". subst; eauto.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iLeft. unshelve (iExists _, _, _, _, _, _; iSplitL ""; first done; eauto); eauto. }
    { iDestruct "Hnull" as (?) "(%&%)"; subst.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iRight. eauto. }
  - iDestruct "Hval" as (?) "(%&%)"; subst.
    simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
    simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
  - iDestruct "Hval" as "[Hval|Hnull]".
    { iDestruct "Hval" as (????? (?&?&?&?)) "H1". subst; eauto.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iLeft. unshelve (iExists _, _, _, _, _; iSplitL ""; first done; eauto); eauto. }
    { iDestruct "Hnull" as (?) "(%&%)"; subst.
      simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
      iRight. eauto. }
  - iDestruct "Hval" as %[].
  - iDestruct "Hval" as %[].
  - rewrite /val_interp/=. iDestruct (sty_val_flatten with "Hval") as %[Heq1 Heq2].
    { simpl in Hlookup1. destruct i; simpl in *; try inversion Hlookup1; subst; eauto.
      rewrite Heq1 in Hlookup2.
      rewrite Heq2 in Hlookup3.
      simpl in *; inversion Hlookup2; inversion Hlookup3; subst; eauto.
    }
  - iDestruct "Hval" as %[].
Qed.

Scheme expr_typing_ind := Induction for expr_transTy Sort Prop with
    val_typing_ind := Induction for val_transTy Sort Prop.

Global Arguments expr_typing_ind spec_op spec_ty impl_op spec_trans
          (* make it possible to supply P and P0 using `with` *)
          spec_atomic_transTy P P0 : rename.

Lemma loc_paired_init l ls:
  meta_token l ⊤ -∗
  meta_token (hG := refinement_na_heapG) ls ⊤ ==∗
  loc_paired ls l.
Proof.
  intros. iIntros "Htok1 Htok2".
  iMod (meta_set ⊤ l ls rlN with "[$]").
  { solve_ndisj. }
  iMod (meta_set (hG := refinement_na_heapG) ⊤ ls l rlN with "[$]").
  { solve_ndisj. }
  by iFrame.
Qed.

Lemma is_loc_init l ls v vs:
  forall  P,
  l ↦ v -∗
  meta_token l ⊤ -∗
  ls s↦ vs -∗
  meta_token (hG := refinement_na_heapG) ls ⊤ -∗
  P vs v -∗
  |={⊤}=> is_loc ls l P.
Proof.
  intros. iIntros "Hl Hltok Hls Hlstok HP".
  iMod (fc_auth_init) as (γ) "Hfc".
  iMod (loc_paired_init with "[$] [$]") as "$".
  iExists γ.
  iMod (inv_alloc locN ⊤ (loc_inv γ ls l P) with "[-]") as "$"; last done.
  { iNext. iExists _, _. iLeft. iFrame. }
Qed.

Lemma logical_reln_prepare_write t ts vs v j K (Hctx: LanguageCtx K):
  {{{ spec_ctx ∗ val_interp (hS := hS) (structRefT (t :: ts)) vs v ∗ j ⤇ K (PrepareWrite vs) }}}
    PrepareWrite v
    {{{ RET #();
        ∃ (ls l: loc) mem_vs mem_v γ,
                       ⌜ vs = #ls ∧ v = #l ⌝ ∗
                       inv locN (loc_inv γ ls l (val_interp (hS := hS) t)) ∗
                       fc_tok γ (1/2)%Qp ∗
                       j ⤇ K #() ∗
                       na_heap_pointsto_st (hG := refinement_na_heapG) WSt ls (DfracOwn (1/2)%Qp) mem_vs ∗
                       (∀ v' : sval, na_heap_pointsto ls (DfracOwn 1) v' -∗ heap_pointsto ls (DfracOwn 1) v') ∗
                       na_heap_pointsto_st (hG := goose_na_heapGS) WSt l (DfracOwn 1) mem_v ∗
                       (∀ v' : ival, na_heap_pointsto l (DfracOwn 1) v' -∗ heap_pointsto l (DfracOwn 1) v')}}}.
Proof.
  intros. iIntros "(#Hctx&Hvl&Hj) HΦ".
  rewrite val_interp_struct_unfold.
  iDestruct "Hvl" as "[Hv|Hnull]".
  * iDestruct "Hv" as (lv lvs n H0lt Hnonemtpy (->&->&?&?&?)) "(Hpaired&Hblock1&Hblocked2&Hloc)".
    iDestruct "Hloc" as "[Hinbound|Hoob]".
    {
      iDestruct "Hinbound" as "(H&_)".
      rewrite /is_loc. iDestruct "H" as "(Hlocinv&Hpaired')".
      iDestruct "Hlocinv" as (γ) "#Hlocinv".
      iInv "Hlocinv" as "Hlocinv_body" "Hclo".
      rewrite /loc_inv. iDestruct "Hlocinv_body" as (mem_vs mem_v) "H".
      iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
      {
        iDestruct "H0readers" as "(>Hfc&>Hspts&>Hpts&#Hval)".
        iApply wp_ncfupd.
        rewrite ?loc_add_0.
        iApply (wp_prepare_write with "[$]"). iIntros "!> Hpts".
        iMod (@ghost_prepare_write _ _ _ _ _ _ _ _ _ _ Hctx with "[$] Hspts Hj") as "(Hspts&Hptsclo&Hj)".
        { solve_ndisj. }
        iDestruct "Hspts" as "(Hspts1&Hspts2)".
        iMod (fc_auth_first_tok with "Hfc") as "(Hfc&Htok)".
        iMod ("Hclo" with "[Hspts1 Hfc Hval]").
        { iNext. iExists mem_vs, mem_v. iRight. iRight. iFrame. }
        iApply "HΦ". iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
        iExists _, _, _, _, _. iFrame "Hlocinv". iFrame.
        eauto.
      }
      {
        iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts&Hspts_clo&>Hpts&#Hval)".
        rewrite ?loc_add_0.
        iMod (ghost_prepare_write_read_stuck with "Hctx Hspts Hj") as %[].
        { lia. }
        { solve_ndisj. }
      }
      {
        (* UB: writer during write *)
        iDestruct "Hwriter" as "(>Hfc&>Hspts)".
        rewrite ?loc_add_0.
        iMod (ghost_prepare_write_write_stuck with "Hctx Hspts Hj") as %[].
        { solve_ndisj. }
      }
    }
    {
      (* UB: oob *)
      iDestruct "Hoob" as %Hoob.
      iMod (ghost_prepare_write_block_oob_stuck with "[$] [$] [$]") as %[].
      { simpl in Hoob. lia. }
      { solve_ndisj. }
    }
  * iDestruct "Hnull" as %(?&->&->).
    (* UB: null *)
    iMod (ghost_prepare_write_null_stuck with "[$] [$]") as %[].
    { rewrite addr_base_of_plus //=. }
    { solve_ndisj. }
Qed.

Lemma logical_reln_finish_store (ls l: loc) (vs vs': sval) (v v': ival) j K (Hctx: LanguageCtx K) (γ: gname):
  forall vTy,
  {{{ spec_ctx ∗ vTy vs v ∗ j ⤇ K (FinishStore #ls vs) ∗ fc_tok γ (1/2)%Qp ∗
      inv locN (loc_inv γ ls l vTy) ∗
      na_heap_pointsto_st (hG := refinement_na_heapG) WSt ls (DfracOwn (1/2)%Qp) vs' ∗
      (∀ v' : sval, na_heap_pointsto ls (DfracOwn 1) v' -∗ heap_pointsto ls (DfracOwn 1) v') ∗
      na_heap_pointsto_st (hG := goose_na_heapGS) WSt l (DfracOwn 1) v' ∗
      (∀ v' : ival, na_heap_pointsto l (DfracOwn 1) v' -∗ heap_pointsto l (DfracOwn 1) v')
 }}}
    FinishStore #l v
 {{{ RET #(); j ⤇ K (of_val #()) }}}.
Proof.
  intros. iIntros "(#Hctx&Hv&Hj&Htok&#Hlocinv&Hspts&Hspts_clo&Hpts&Hpts_clo) HΦ".
  iInv "Hlocinv" as "Hlocinv_body" "Hclo".
  rewrite /loc_inv. iDestruct "Hlocinv_body" as (mem_vs mem_v) "H".
  iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
  {
    iDestruct "H0readers" as "(>Hfc&_&>Hpts'&_)".
    iDestruct (heap_pointsto_na_acc with "Hpts'") as "(Hpts'&_)".
    rewrite ?na_heap_pointsto_eq /na_heap_pointsto_def.
    iDestruct (na_heap_pointsto_st_frac_valid2 with "Hpts Hpts'") as %Hval.
    apply Z2Qc_inj_le in Hval. lia.
  }
  {
    iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts'&Hspts'_clo&>Hpts'&_)".
    iDestruct (heap_pointsto_na_acc with "Hpts'") as "(Hpts'&_)".
    rewrite ?na_heap_pointsto_eq /na_heap_pointsto_def.
    iDestruct (na_heap_pointsto_st_frac_valid2 with "Hpts Hpts'") as %Hval.
    exfalso. eapply Qp.not_add_le_l, Hval.
  }
  {
    iDestruct "Hwriter" as "(>Hfc&>Hspts')".
    iDestruct (na_heap_pointsto_st_agree (hG := refinement_na_heapG) with "[Hspts Hspts']") as %Heq.
    { iFrame. }
    subst.
    iCombine "Hspts Hspts'" as "Hspts".
    iApply wp_ncfupd.
    wp_apply (wp_finish_store with "[$]").
    iIntros "Hl".
    iMod (ghost_finish_store with "Hctx Hspts Hspts_clo Hj") as "(?&Hj)".
    { solve_ndisj. }
    iMod (fc_auth_drop_last with "[$]") as "Hfc".
    iMod ("Hclo" with "[-Hj HΦ]").
    { iNext. iExists _, _. iLeft. iFrame. }
    iApply "HΦ". iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
    eauto.
  }
Qed.

Lemma logical_reln_start_read t ts vs v j K (Hctx: LanguageCtx K):
  {{{ spec_ctx ∗ val_interp (hS := hS) (structRefT (t :: ts)) vs v ∗ j ⤇ K (StartRead vs) }}}
    StartRead v
    {{{ mem_v, RET mem_v;
        ∃ (ls l: loc) (mem_vs: sval) γ q,
                       ⌜ vs = #ls ∧ v = #l ∧ ls ≠ null ∧ l ≠ null ⌝ ∗
                       inv locN (loc_inv γ ls l (val_interp (hS := hS) t)) ∗
                       fc_tok γ q ∗
                       j ⤇ K mem_vs ∗
                       val_interp (hS := hS) t mem_vs mem_v ∗
                       na_heap_pointsto_st (hG := refinement_na_heapG) (RSt O) ls (DfracOwn q) mem_vs ∗
                       na_heap_pointsto_st (hG := goose_na_heapGS) (RSt 1) l (DfracOwn q) mem_v ∗
                       (∀ v' : ival, na_heap_pointsto l (DfracOwn 1) v' -∗ heap_pointsto l (DfracOwn 1) v')}}}.
Proof.
  intros. iIntros "(#Hctx&Hvl&Hj) HΦ".
  rewrite val_interp_struct_unfold.
  iDestruct "Hvl" as "[Hv|Hnull]".
  * iDestruct "Hv" as (lv lvs n H0lt Hnonemtpy (->&->&?&?&?)) "(Hpaired&Hblock1&Hblocked2&Hloc)".
    iDestruct "Hloc" as "[Hinbound|Hoob]".
    {
      iDestruct "Hinbound" as "(H&_)".
      rewrite /is_loc. iDestruct "H" as "(Hlocinv&Hpaired')".
      iDestruct "Hlocinv" as (γ) "#Hlocinv".
      iInv "Hlocinv" as "Hlocinv_body" "Hclo".
      rewrite /loc_inv. iDestruct "Hlocinv_body" as (mem_vs mem_v) "H".
      iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
      {
        iDestruct "H0readers" as "(>Hfc&>Hspts&>Hpts&#Hval)".
        rewrite ?loc_add_0.
        iApply wp_ncfupd.
        iApply (wp_start_read with "[$]"). iIntros "!> (Hpts&Hpts_clo)".
        iDestruct (heap_pointsto_na_acc with "Hspts") as "(Hspts&Hspts_clo)".
        rewrite na_heap_pointsto_eq.
        iMod (@ghost_start_read _ _ _ _ _ _ _ _ _ _ Hctx with "[$] Hspts Hj") as "(Hspts&Hj)".
        { solve_ndisj. }
        replace (RSt 1) with (RSt (1 + O)%nat) by eauto.
        iMod (fc_auth_first_tok with "Hfc") as "(Hfc&Htok)".
        iEval (replace 1%Qp with (1/2 + 1/2)%Qp by apply Qp.half_half) in "Hpts".
        iEval (replace 1%Qp with (1/2 + 1/2)%Qp by apply Qp.half_half) in "Hspts".
        iDestruct (na_heap_pointsto_st_rd_frac _ 1 O with "Hpts") as "(Hpts1&Hpts2)".
        iDestruct (na_heap_pointsto_st_rd_frac _ 1 O with "Hspts") as "(Hspts1&Hspts2)".
        iMod ("Hclo" with "[Hpts2 Hspts1 Hfc Hval]").
        { iNext. iExists mem_vs, mem_v. iRight. iLeft. iExists (1/2)%Qp, (1/2)%Qp, _. iFrame.
          iSplitL "".
          { rewrite Qp.half_half; eauto. }
          iSplitL "".
          { rewrite -na_heap_pointsto_eq. iIntros (?) "H". iApply (na_pointsto_to_heap with "H").
            apply addr_base_non_null; eauto.
          }
          iFrame "Hval".
          iApply (na_pointsto_to_heap with "[Hpts2]").
          { apply addr_base_non_null; eauto. }
          { rewrite na_heap_pointsto_eq /na_heap_pointsto_def. eauto. }
        }
        iApply "HΦ". iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
        iExists _, _, _, _, _. iFrame. iFrame "Hlocinv Hval". iPureIntro; split_and!; eauto;
        eapply addr_base_non_null; eauto.
      }
      {
        iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts&Hspts_clo&>Hpts&#Hval)".
        rewrite ?loc_add_0.
        iApply (wp_ncfupd).
        iApply (wp_start_read with "[$]"). iIntros "!> (Hpts&Hpts_clo)".
        rewrite na_heap_pointsto_eq.
        iMod (@ghost_start_read _ _ _ _ _ _ _ _ _ _ Hctx with "[$] Hspts Hj") as "(Hspts&Hj)".
        { solve_ndisj. }
        replace (S (Pos.to_nat n')) with (S (Pos.to_nat n') + 0)%nat by lia.
        iMod (fc_auth_new_tok _ q q' with "Hfc") as "(Hfc&Htok)"; eauto.
        specialize (Qp.div_2 q') => Hq'.
        rewrite -[x in na_heap_pointsto_st _ lv (DfracOwn x) _]Hq'.
        rewrite -[x in na_heap_pointsto_st (hG := refinement_na_heapG) _ _ (DfracOwn x) mem_vs]Hq'.
        iDestruct (na_heap_pointsto_st_rd_frac _ 1 O with "Hpts") as "(Hpts1&Hpts2)".
        iDestruct (na_heap_pointsto_st_rd_frac _ _ _ with "Hspts") as "(Hspts1&Hspts2)".
        iMod ("Hclo" with "[Hpts2 Hspts1 Hfc Hval]").
        { iNext. iExists mem_vs, mem_v. iRight. iLeft. iExists (q + q'/2)%Qp, (q'/2)%Qp, _. iFrame.
          iSplitL "".
          { iPureIntro. rewrite -assoc Hq'. eauto. }
          replace (S (Pos.to_nat n')) with ((Pos.to_nat (n' + 1)))%nat by lia. iFrame.
          iSplitL "".
          { rewrite -na_heap_pointsto_eq. iIntros (?) "H". iApply (na_pointsto_to_heap with "H").
            apply addr_base_non_null; eauto.
          }
          iFrame "Hval".
          iApply (na_pointsto_to_heap with "[Hpts2]").
          { apply addr_base_non_null; eauto. }
          { rewrite na_heap_pointsto_eq /na_heap_pointsto_def. eauto. }
        }
        iApply "HΦ". iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
        iExists _, _, _, _, _. iFrame. iFrame "#".
        iSplitL "".
        { iPureIntro; split_and!; eauto; eapply addr_base_non_null; eauto. }
        { rewrite -na_heap_pointsto_eq. iIntros (?) "H". iApply (na_pointsto_to_heap with "H").
          apply addr_base_non_null; eauto. }
      }
      {
        (* UB: writer during read *)
        iDestruct "Hwriter" as "(>Hfc&>Hspts)".
        rewrite ?loc_add_0.
        iMod (ghost_start_read_write_stuck with "Hctx Hspts Hj") as %[].
        { solve_ndisj. }
      }
    }
    {
      (* UB: oob *)
      iDestruct "Hoob" as %Hoob.
      iMod (ghost_start_read_block_oob_stuck with "[$] [$] [$]") as %[].
      { simpl in Hoob. lia. }
      { solve_ndisj. }
    }
  * iDestruct "Hnull" as %(?&->&->).
    (* UB: null *)
    iMod (ghost_start_read_null_stuck with "[$] [$]") as %[].
    { rewrite addr_base_of_plus //=. }
    { solve_ndisj. }
Qed.

Lemma logical_reln_finish_read (ls l: loc) (vs': sval) (v': ival) j K (Hctx: LanguageCtx K) (γ: gname) q
  (Hnonnull: l ≠ null):
  forall vTy,
 {{{ spec_ctx ∗ j ⤇ K (FinishRead #ls) ∗ fc_tok γ q ∗
      inv locN (loc_inv γ ls l vTy) ∗
      na_heap_pointsto_st (hG := refinement_na_heapG) (RSt O) ls (DfracOwn q) vs' ∗
      na_heap_pointsto_st (hG := goose_na_heapGS) (RSt 1) l (DfracOwn q) v' ∗
      (∀ v' : ival, na_heap_pointsto l (DfracOwn 1) v' -∗ heap_pointsto l (DfracOwn 1) v')
 }}}
    FinishRead #l
 {{{ RET #(); j ⤇ K (of_val #()) }}}.
Proof.
  intros. iIntros "(#Hctx&Hj&Htok&#Hlocinv&Hspts&Hpts&Hpts_clo) HΦ".
  iInv "Hlocinv" as "Hlocinv_body" "Hclo".
  rewrite /loc_inv. iDestruct "Hlocinv_body" as (mem_vs mem_v) "H".
  iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
  {
    iDestruct "H0readers" as "(>Hfc&_&>Hpts'&_)".
    iDestruct (heap_pointsto_na_acc with "Hpts'") as "(Hpts'&_)".
    rewrite ?na_heap_pointsto_eq /na_heap_pointsto_def.
    iDestruct (na_heap_pointsto_st_frac_valid2 with "Hpts Hpts'") as %Hval.
    exfalso. revert Hval; rewrite (comm _ q 1%Qp). eapply Qp.not_add_le_l.
  }
  {
    iDestruct "Hreaders" as (q1 q2 n') "(>Hq_sum&>Hfc&>Hspts'&Hspts'_clo&>Hpts'&Hvty)".
    iDestruct "Hq_sum" as %Hq_sum.
    iDestruct (heap_pointsto_na_acc with "Hpts'") as "(Hpts'&_)".
    iApply wp_ncfupd.
    wp_apply (wp_finish_read with "[Hpts]").
    { iFrame. iIntros (?). iApply na_pointsto_to_heap; eauto. }
    iIntros "Hpts".
    iDestruct (heap_pointsto_na_acc with "Hpts") as "(Hpts&_)".
    rewrite ?na_heap_pointsto_eq /na_heap_pointsto_def.

    assert (n' = 1 ∨ ∃ n'', n' = 1 + n'')%positive as [H1reader|Hmore].
    { induction n' using Pos.peano_ind; eauto.
      right. exists n'. lia.
    }
    - subst. iDestruct (fc_auth_last_agree with "Hfc Htok") as %Hq. subst.
      iDestruct (na_heap_pointsto_st_agree with "[Hpts Hpts']") as %Heq.
      { iFrame. } subst.
      iDestruct (na_heap_pointsto_st_rd_frac with "[$]") as "Hpts".
      rewrite Hq_sum Nat.add_0_r.
      iMod (ghost_finish_read with "Hctx Hspts' Hj") as "(Hspts'&Hj)".
      { solve_ndisj. }
      iDestruct (na_heap_pointsto_st_agree (hG := refinement_na_heapG) with "[Hspts Hspts']") as %Heq.
      { iFrame. } subst.
      iDestruct (na_heap_pointsto_st_rd_frac (hG := refinement_na_heapG) with "[Hspts Hspts']") as "Hspts".
      { iFrame. }
      iMod (fc_auth_drop_last with "[$]") as "Hfc".
      iMod ("Hclo" with "[- Hj HΦ]").
      {
        iNext. iExists _, _. iLeft. iFrame.
        iDestruct ("Hpts_clo" with "[$]") as "$".
        rewrite Nat.add_0_r.
        iApply "Hspts'_clo".
        iEval (rewrite comm Hq_sum) in "Hspts".
        eauto.
      }
      iApply "HΦ". iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
      eauto.
    - destruct Hmore as (n''&->).
      iDestruct (fc_auth_non_last_agree with "[$] [$]") as %(q'&Hq).
      iDestruct (na_heap_pointsto_st_agree with "[Hpts Hpts']") as %Heq.
      { iFrame. } subst.
      iDestruct (na_heap_pointsto_st_rd_frac with "[$]") as "Hpts".
      replace (Pos.to_nat (1 + n'')) with (S (Pos.to_nat n'')) by lia.
      iMod (ghost_finish_read with "Hctx Hspts' Hj") as "(Hspts'&Hj)".
      { solve_ndisj. }
      iDestruct (na_heap_pointsto_st_agree (hG := refinement_na_heapG) with "[Hspts Hspts']") as %Heq.
      { iFrame. } subst.
      iDestruct (na_heap_pointsto_st_rd_frac (hG := refinement_na_heapG) with "[Hspts Hspts']") as "Hspts".
      { iFrame. }
      iMod (fc_auth_drop with "[$]") as "Hfc".
      iMod ("Hclo" with "[- Hj HΦ]").
      {
        iNext. iExists _, _. iRight. iLeft. iFrame.
        iExists _.
        rewrite ?Nat.add_0_r.
        iFrame.
        iSplitL "".
        { iPureIntro. rewrite -Hq_sum. rewrite -assoc {1}(comm _ q2). eauto. }
        rewrite (comm _ q2).
        iApply na_pointsto_to_heap; auto.
        rewrite na_heap_pointsto_eq. iFrame.
      }
      iApply "HΦ". iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
      eauto.
  }
  {
    iDestruct "Hwriter" as "(>Hfc&>Hspts')".
    iDestruct (na_heap_pointsto_st_WSt_agree (hG := refinement_na_heapG) with "[Hspts Hspts']") as %Heq.
    { iFrame. }
    congruence.
  }
Qed.

Existing Instances sty_inv_persistent.

Lemma val_interp_structRefT_is_loc ts vs v :
  val_interp (hS:=hS) (structRefT ts) vs v -∗
  ⌜∃ l1 l2, vs = LitV (LitLoc l1) ∧ v = LitV (LitLoc l2)⌝.
Proof.
  iDestruct 1 as "[H|Hnull]".
  + iDestruct "H" as (?? n ?? (?&?&?&?&Hoffset)) "(Hpaired&_)".
    subst.
    eauto.
  + iDestruct "Hnull" as %(?&(Hnulls&Hnull)). subst.
    eauto.
Qed.

Lemma is_comparableTy_is_comparable t vs v :
  is_comparableTy t = true →
  val_interp (hS:=hS) t vs v -∗
  ⌜is_comparable vs ∧ is_comparable v⌝.
Proof.
  clear spec_trans.
  generalize dependent vs.
  generalize dependent v.
  induction t; simpl; intros ?? Hcompare; try congruence.
  - destruct t; cbn [base_ty_interp]; iPureIntro; naive_solver.
  - cbn [val_interp]. rewrite /prodT_interp.
    iDestruct 1 as (???? [-> ->]) "[? ?]".
    apply andb_true_iff in Hcompare as [? ?].
    iDestruct (IHt1 with "[$]") as %[? ?]; auto.
    iDestruct (IHt2 with "[$]") as %[? ?]; auto.
  - cbn [val_interp]. rewrite /sumT_interp.
    apply andb_true_iff in Hcompare as [? ?].
    iDestruct 1 as "[ (%&%&%Heq&?) | (%&%&%Heq&?) ]".
    + destruct Heq as [-> ->].
      iDestruct (IHt1 with "[$]") as %?; auto.
    + destruct Heq as [-> ->].
      iDestruct (IHt2 with "[$]") as %?; auto.
  - iIntros "H".
    iDestruct (arrayT_structRefT_promote with "H") as "H".
    iDestruct (val_interp_structRefT_is_loc with "H") as (??) "[-> ->]".
    done.
  - iIntros "H".
    iDestruct (val_interp_structRefT_is_loc with "H") as (??) "[-> ->]".
    done.
Qed.

Lemma sty_fundamental_lemma:
  sty_rules_obligation spec_trans →
  sty_atomic_obligation spec_atomic_transTy →
  ∀ Γ es e τ, expr_transTy _ _ _ spec_trans spec_atomic_transTy Γ es e τ →
    ⊢ ctx_has_semTy (hS := hS) Γ es e τ.
Proof using spec_trans.
  iIntros (Hrules Hatomic ???? Htyping).
  induction Htyping using @expr_typing_ind with
      (spec_trans := spec_trans)
      (P := (λ Γ es e τ
             (HTYPE: expr_transTy _ _ _ spec_trans spec_atomic_transTy Γ es e τ),
               ⊢ ctx_has_semTy (hS := hS) Γ es e τ))
      (P0 := (λ Γ vs v τ
             (HTYPE: val_transTy _ _ _ spec_trans spec_atomic_transTy Γ vs v τ),
               ⊢ sty_inv hS -∗ spec_ctx -∗ trace_ctx -∗ val_interp (hS := hS) τ vs v));
    try (intros; iIntros (Γsubst HPROJ) "#Hinv #Hspec #Htrace #Hctx");
    try (intros; iIntros "#Hinv #Hspec #Htrace").


  (* Variables *)
  - subst.
    rewrite lookup_fmap in e.
    apply fmap_Some_1 in e as (t'&?&?). subst.
    iDestruct (big_sepM_lookup with "Hctx") as "H"; first eauto.
    rewrite /= ?lookup_fmap H //=.
    iIntros (j K Hctx) "Hj". iApply wpc_value; iSplit.
    * iModIntro. iExists _; iFrame "H"; iFrame.
    * by iModIntro.
  (* Function app. *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) x2).
    spec_bind (subst_map ((subst_sval <$> Γsubst)) x1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    wpc_bind (subst_map _ f2).
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppLCtx (vs2)] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv2] [] H"); last by eauto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
    iSpecialize ("Hinterp" $! _ _ with "Hv2").
    iApply ("Hinterp" with "Hj").
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc. iApply wp_value. iExists _. iFrame.
    iApply (IHHtyping with "[$] [$] [$]").
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. econstructor; eauto.
      { simpl. econstructor; eauto. }
      { econstructor; eauto. }
    }
    wp_pures; eauto. iModIntro.
    iExists _; iFrame.
    iExists _, _, _, _, _, _; iSplit; first eauto.
    iLöb as "IH".
    iModIntro. iIntros (v vs) "Hval".
    clear j K Hctx.
    iIntros (j K Hctx) "Hj".
    wpc_pures; first by eauto.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
      (* TODO: make spec_ctx auto frame source_ctx *)
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. econstructor; eauto.
    }
    iPoseProof (ctx_has_semTy_subst with "[] []") as "H1".
    { iApply IHHtyping. }
    { simpl. iExists _, _, _, _, _, _. iFrame "IH"; eauto. }
    iPoseProof (ctx_has_semTy_subst with "[] Hval") as "H2".
    { iApply "H1". }
    iSpecialize ("H2" with "[//] [$] [$] [$] [$] [//] [Hj]").
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite (binder_delete_commute f x)). iFrame. }
    { do 2 (rewrite -subst_map_binder_insert' subst_map_binder_insert).
      iEval (rewrite {2}binder_delete_commute). iApply wpc_wp. iFrame. }
  (* Fork *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. econstructor; eauto.
    }
    iEval (simpl; rewrite right_id) in "Hchild".
    iDestruct "Hchild" as (j') "Hj'".
    iApply wpc_wp.
    iApply (wpc_fork with "[Hj']").
    { iNext. iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
      iSpecialize ("H" $! j' (λ x, x) with "[] [$]"); first by (iPureIntro; apply language_ctx_id).
      iApply (wpc_mono with "H"); eauto.
    }

    iSplit; first (iApply "Hj"). iNext. iExists _; iFrame; eauto.
  - iApply (Hatomic _ _ _ _ _ _ _ _ _ _ Γsubst with "[$] [$] [$] [$]").
    { intros. rewrite HPROJ. eauto. }
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) cond').
    spec_bind (_ _ cond) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last auto.

    iIntros (vcond) "H". iDestruct "H" as (vscond) "(Hj&Hvcond)".
    (* split on the value of the bool *)
    iDestruct "Hvcond" as %(b&->&->).
    destruct b.
    * wpc_pures; first by auto. simpl.
      iApply wp_wpc.
      iMod (ghost_step_lifting_puredet _ _ K with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. econstructor; eauto.
      }
      iApply wpc_wp.
      iApply (IHHtyping2 with "[//] [$] [$] [$] [$]"). eauto.
    * wpc_pures; first by auto. simpl.
      iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. econstructor; eauto.
      }
      iApply wpc_wp.
      iApply (IHHtyping3 with "[//] [$] [$] [$] [$]"). eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc.
    iMod (ghost_step_stuck_det with "Hj []") as %[]; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros; eapply stuck_Panic. }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iApply wp_wpc.
    iApply wp_ncfupd.
    iApply wp_ArbitraryInt; auto.
    iNext.
    iIntros. iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    iModIntro. iExists _. iFrame. iExists _. iPureIntro; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u64), ⌜ un_op_eval UToW64Op v1 = Some #vres ∧
                            un_op_eval UToW64Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [UnOpCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u64), ⌜ un_op_eval SToW64Op v1 = Some #vres ∧
                            un_op_eval SToW64Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u32), ⌜ un_op_eval UToW32Op v1 = Some #vres ∧
                            un_op_eval UToW32Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u32), ⌜ un_op_eval SToW32Op v1 = Some #vres ∧
                            un_op_eval SToW32Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u8), ⌜ un_op_eval UToW8Op v1 = Some #vres ∧
                            un_op_eval UToW8Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: u8), ⌜ un_op_eval SToW8Op v1 = Some #vres ∧
                            un_op_eval SToW8Op vs1 = Some #vres ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iAssert (∃ (vres: string), ⌜ un_op_eval ToStringOp v1 = Some #(LitString vres) ∧
                            un_op_eval ToStringOp vs1 = Some #(LitString vres) ⌝)%I with "[Hv1]" as %Hres.
    {
      destruct t; try inversion e;
      destruct t; try congruence;
      rewrite /val_interp//=;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iPureIntro; eexists; eauto.
    }
    destruct Hres as (x&Heq1&Heq2).
    iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
        rewrite Heq2; eauto. econstructor; eauto.
      }
      wp_pures.
      by eauto 10 with iFrame.
  - destruct op; try inversion e; subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e2).
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    iDestruct "Hv1" as (?) "(%&%)"; subst.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures.
    by eauto 10 with iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    simpl. spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iApply wp_wpc.

    iDestruct (is_comparableTy_is_comparable with "Hv1")
      as %[Hcomparevs1 Hcomparev1]; auto.
    iDestruct (is_comparableTy_is_comparable with "Hv2")
      as %[Hcomparevs2 Hcomparev2]; auto.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
      rewrite /bin_op_eval /bin_op_eval_eq /=.
      rewrite decide_True //.
    }
    (* need to solve is_comparable side condition *)
    wp_pure1; [ done | ].
    iExists _. iFrame. iExists (bool_decide (vs1 = vs2)); eauto.
    iDestruct (comparableTy_val_eq with "Hv1 Hv2") as %Heq; auto.
    iPureIntro. split; first auto. do 2 f_equal.
    by apply bool_decide_ext.
  (* bin op *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl.

    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.

    iDestruct "Hspec" as "(#Hsrc&#Hstate)".
    (* Be patient, this is handling a bunch of cases. *)
    iApply wp_wpc.
    destruct op; inversion e; subst;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iDestruct "Hv2" as (?) "(%&%)"; subst;
      (iMod (ghost_step_lifting_puredet with "[$]") as "(Hj&Hchild)";
       [ intros; eexists; apply base_prim_step_trans; repeat econstructor; eauto
        | set_solver+ | wp_pures; eauto; iExists _; iFrame; eauto]).

  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl.

    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.

    iDestruct "Hspec" as "(#Hsrc&#Hstate)".
    (* Be patient this is handling a bunch of cases. *)
    iApply wp_wpc.
    destruct op; inversion e; subst;
      iDestruct "Hv1" as (?) "(%&%)"; subst;
      iDestruct "Hv2" as (?) "(%&%)"; subst;
      (iMod (ghost_step_lifting_puredet with "[$]") as "(Hj&Hchild)";
       [ intros; eexists; apply base_prim_step_trans; repeat econstructor; eauto
        | set_solver+ | wp_pures; eauto; iExists _; iFrame; eauto]).
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map _ e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    simpl.

    wpc_bind (subst_map _ e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (_ _ e2) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.

    iDestruct "Hspec" as "(#Hsrc&#Hstate)".
    iApply wp_wpc.
    iDestruct "Hv1" as (?) "(%&%)"; subst;
    iDestruct "Hv2" as (?) "(%&%)"; subst;
    (iMod (ghost_step_lifting_puredet with "[$]") as "(Hj&Hchild)";
     [ intros; eexists; apply base_prim_step_trans; repeat econstructor; eauto
      | set_solver+ | wp_pures; eauto; iExists _; iFrame; eauto]).

  (* data *)
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map _ e2').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e2) as Hctx'.
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    iSpecialize ("H" $! j _ Hctx'  with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    simpl.
    clear Hctx'.

    spec_bind (_ ,_)%E as Hctx'.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v) "H". iDestruct "H" as (vs) "(Hj&Hv)".
    clear Hctx'.
    simpl.
    iDestruct "Hv" as (???? (->&->)) "(?&?)".

    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v) "H". iDestruct "H" as (vs) "(Hj&Hv)".
    clear Hctx'.
    simpl.
    iDestruct "Hv" as (???? (->&->)) "(?&?)".

    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures; eauto.
  - subst.
    Opaque val_interp.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H1"; eauto.
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H2"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) ehd').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) ehd) as Hctx'.
    iSpecialize ("H1" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[H2] [] H1"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) etl').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) etl) as Hctx'.
    iSpecialize ("H2" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hv1] [] H2"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    clear Hctx'.
    simpl.

    spec_bind (vs1, vs2)%E as Hctx'.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame.
    rewrite val_interp_list_unfold /listT_interp.
    iDestruct "Hv2" as (lvs lv (->&->)) "H". iModIntro.
    iExists (vs1 :: lvs), (v1 :: lv). iSplit; first by eauto.
    simpl. iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H1"; eauto.
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H2"; eauto.
    iPoseProof (IHHtyping3 with "[//] [$] [$] [$] [$]") as "H3"; eauto.
    rewrite /impl.ListMatch.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) consfun').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) consfun) as Hctx'.
    iSpecialize ("H3" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[H1 H2] [] H3"); last by auto.
    iIntros (vconsfun) "H". iDestruct "H" as (vsconsfun) "(Hj&Hvconsfun)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) nilfun').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) nilfun) as Hctx'.
    iSpecialize ("H2" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[H1 Hvconsfun] [] H2"); last by auto.
    iIntros (vnilfun) "H". iDestruct "H" as (vsnilfun) "(Hj&Hvnilfun)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) el').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) el) as Hctx'.
    iSpecialize ("H1" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hvnilfun Hvconsfun] [] H1"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvsl)".
    clear Hctx'.
    simpl.
    iApply wp_wpc.

    spec_bind (App _ vsl)%E as Hctx'.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    spec_bind (λ: _, _)%E as Hctx'.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    simpl.

    spec_bind (App _ vsnilfun)%E as Hctx'.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    spec_bind (λ: _, _)%E as Hctx'.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    spec_bind (App _ vsconsfun)%E as Hctx'.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    clear Hctx'0.
    rewrite val_interp_list_unfold.
    iDestruct "Hvsl" as (lvs lv (->&->)) "H".
    destruct lvs as [|vs lvs];
    destruct lv as [|v lv]; try (iDestruct "H" as %[]; done).

    * simpl.

      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }

      spec_bind (Rec _ _ _)%E as Hctx'.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }
      simpl.
      clear Hctx'.

      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }

      simpl.

      Transparent val_interp.
      wp_pures.
      rewrite /val_interp -/val_interp.
      rewrite /arrowT_interp.
      iDestruct "Hvnilfun" as (f x e fs xs es (->&->)) "#Hwand".
      iSpecialize ("Hwand" $! #() #() with "[] Hj").
      { eauto. }
      iApply (wpc_wp _ _ _ _ True%I).
      iApply (wpc_mono' with "[] [] Hwand"); last by auto.
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      iExists _. iFrame.
    * simpl.

      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }

      spec_bind (Rec _ _ _)%E as Hctx'.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }
      simpl.
      clear Hctx'.

      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }

      simpl.

      wp_pures.
      rewrite /val_interp -/val_interp.
      rewrite /arrowT_interp.
      iDestruct "Hvconsfun" as (f x e fs xs es (->&->)) "#Hwand".
      iSpecialize ("Hwand" $! (v, list.val_of_list lv)%V (vs, list.val_of_list lvs)%V with "[H] Hj").
      { rewrite /val_interp -/val_interp. iExists _, _, _, _. iSplit; first by eauto.
        rewrite val_interp_list_unfold /listT_interp.
        iDestruct "H" as "($&H)".
        iExists _, _. iSplit; first eauto. iFrame.
      }
      iApply (wpc_wp _ _ _ _ True%I).
      iApply (wpc_mono' with "[] [] Hwand"); last by auto.
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      iExists _. iFrame.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    simpl.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame. iLeft. iExists _, _; iFrame; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) e) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    simpl.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    wp_pures; auto.
    iExists _. iFrame. iRight. iExists _, _; iFrame; eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) cond').
    spec_bind (subst_map ((subst_sval <$> Γsubst)) cond) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    iDestruct "Hv1" as "[Hleft|Hright]".
    {
      iDestruct "Hleft" as (?? (->&->)) "Hv".
      wpc_pures; first auto.
      iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }
      iApply wpc_wp.
      wpc_bind (subst_map _ e1').
      iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H"; eauto.
      spec_bind (subst_map _ e1) as Hctx'.
      iSpecialize ("H" $! j _ Hctx' with "Hj").
      iApply (wpc_mono' with "[Hv] [] H"); last first.
      { iIntros "H". iExact "H". }
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
      iSpecialize ("Hinterp" with "[$]").
      iSpecialize ("Hinterp" $! j _ Hctx with "Hj").
      iApply (wpc_mono' with "[] [] Hinterp"); last first.
      { iIntros "H". iExact "H". }
      { iIntros (v'') "H". iDestruct "H" as (vs'') "(Hj&Hv')".
        iExists _. iFrame. }
    }
    {
      iDestruct "Hright" as (?? (->&->)) "Hv".
      wpc_pures; first auto.
      iApply wp_wpc.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&Hchild)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { set_solver+. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }
      iApply (wpc_wp _).
      wpc_bind (subst_map _ e2').
      iPoseProof (IHHtyping3 with "[//] [$] [$] [$] [$]") as "H"; eauto.
      spec_bind (subst_map _ e2) as Hctx'.
      iSpecialize ("H" $! j _ Hctx' with "Hj").
      iApply (wpc_mono' with "[Hv] [] H"); last first.
      { iIntros "H". iExact "H". }
      iIntros (v1) "H". iDestruct "H" as (vs1) "(Hj&Hv1)".
      simpl. iDestruct "Hv1" as (?????? (Heq1&Heq2)) "#Hinterp".
      iSpecialize ("Hinterp" with "[$]").
      iSpecialize ("Hinterp" $! j _ Hctx with "Hj").
      iApply (wpc_mono' with "[] [] Hinterp"); last by auto.
      iIntros (v'') "H". iDestruct "H" as (vs'') "(Hj&Hv')".
      iExists _. iFrame.
    }
  (* pointers *)
  - subst.
    Opaque val_interp.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) n').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [Primitive2LCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last by auto. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [Primitive2RCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last by auto. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iApply wp_wpc.
    iApply wp_fupd.
    Transparent val_interp.
    iDestruct "Hv1" as (nint) "(->&->)".
    destruct (decide (0 < uint.Z nint)) as [Hnonneg|]; last first.
    {
      iMod (ghost_allocN_non_pos_stuck with "[$] [$]") as %[].
      { eauto. }
      { solve_ndisj. }
    }
    iDestruct (length_flatten_well_typed with "Hv2") as %(Hspecsize&Hsize); first done.
    iApply wp_ncfupd.
    iApply wp_allocN_seq_sized_meta.
    { rewrite -Hsize. destruct (flatten_ty t) as [|]; try congruence; simpl; try lia. }
    { auto. }
    { auto. }
    iNext. iIntros (l) "(%&Hsize&Hpts)".
    iMod (ghost_allocN_seq_sized_meta with "[] Hj") as (ls) "(Hj&%&Hssize&Hspts)".
    { rewrite -Hspecsize. destruct (flatten_ty t) as [|]; try congruence; simpl; try lia. }
    { eassumption. }
    { solve_ndisj. }
    { iApply "Hspec". }
    iExists _. iFrame "Hj".
    rewrite val_interp_array_unfold /arrayT_interp.
    iLeft. unshelve (iExists l, ls, (uint.nat nint), 0, _, _); eauto.
    { lia. }
    rewrite -Hsize -Hspecsize.
    iFrame. replace ((uint.nat nint * length (flatten_ty t)))%Z with
                   (Z.of_nat (uint.nat nint * length (flatten_ty t)))%nat by lia.
    iFrame.
    iSplitL "".
    { iPureIntro. split_and!; eauto.
      * apply addr_base_non_null_offset; eauto; naive_solver.
      * apply addr_base_non_null_offset; eauto; naive_solver.
      * naive_solver congruence.
      * lia.
    }
    rewrite (addr_offset_0_is_base l); last naive_solver.
    rewrite (addr_offset_0_is_base ls); last naive_solver.
    iCombine "Hpts Hspts" as "Hpts".
    rewrite -big_sepL_sep.
    iDestruct "Hv2" as "#Hv".
    iFrame.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hpts").
    { iIntros "!> !>" (k x Hlookup) "(Hmtoks&Hsmtoks)".
      iDestruct (big_sepL2_sepL_2 with "Hmtoks Hsmtoks") as "Hmtoks"; first lia.
      iApply big_sepL_fupd.
      iApply (big_sepL2_elim_big_sepL with "[] Hmtoks").
      { rewrite map_length //=. }
      { iModIntro. iIntros (i vi vsi vty Hlookup1 Hlookup2 Hlookup3) "((Hpts&Hm)&(Hspts&Hsm))".
        rewrite list_lookup_fmap in Hlookup3.
        apply fmap_Some_1 in Hlookup3 as (sty&Hlookup3&Heq). subst.
        iDestruct (flatten_well_typed with "Hv") as "Hvali"; eauto.
        iMod (is_loc_init with "Hpts Hm Hspts Hsm Hvali") as "$".
        eauto.
      }
    }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpLCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last by auto. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e2').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpRCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last by auto. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[Hv1] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iApply wp_wpc.
    iApply wp_ncfupd.
    iDestruct "Hv2" as (off) "H". iDestruct "H" as %[Heq1 Heq2]. subst.
    iDestruct "Hv1" as "[Hv1|Hnull]"; last first.
    { iDestruct "Hnull" as %(off'&Heq1'&Heq2'). subst.
      wp_pures.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { solve_ndisj. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }
      iModIntro. iExists _. iFrame. iRight.
      iExists _. rewrite /loc_add. rewrite addr_plus_plus. eauto.
    }
    iDestruct "Hv1" as (l ls n idx Hgtzero Hnonempty Hpeq) "(Hblock1&Hblock2&Hlist)".
    destruct Hpeq as (->&->&?&?&Hoff&Hoffs).
    wp_pures.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { solve_ndisj. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    iModIntro.
    iExists _. iFrame. iLeft.
    unshelve (iExists (addr_plus_off l (ty_size t * uint.Z off)),
                                      (addr_plus_off ls (ty_size t * uint.Z off)), _, (idx + uint.Z off), _, _; iFrame); eauto.
    rewrite ?addr_base_of_plus ?addr_offset_of_plus. iPureIntro; split_and!; eauto.
    * rewrite Hoff. rewrite -ty_size_length.
      specialize (ty_size_ge_0 t). intros.
      rewrite Z2Nat.id //=. lia.
    * rewrite Hoffs. rewrite -ty_size_length.
      specialize (ty_size_ge_0 t). intros.
      rewrite Z2Nat.id //=. lia.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j K with "[] Hj"); first auto.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".
    iExists _. iFrame "Hj". iApply arrayT_structRefT_promote. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) e1').
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [BinOpLCtx _ _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last by auto. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    iApply wp_wpc.
    iApply wp_ncfupd.
    iDestruct "Hv1" as "[Hv1|Hnull]"; last first.
    { iDestruct "Hnull" as %(off'&Heq1'&Heq2'). subst.
      wp_pures.
      iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
      { iFrame. iDestruct "Hspec" as "($&?)". }
      { solve_ndisj. }
      { intros ?. eexists. simpl.
        apply base_prim_step_trans. repeat econstructor; eauto.
      }
      iModIntro. iExists _. iFrame. iRight.
      iExists _. rewrite /loc_add. rewrite addr_plus_plus. eauto.
    }
    iDestruct "Hv1" as (l' ls' n Hgtzero Hnonempty Hpeq) "(Hpaired&Hblock1&Hblock2&Hlist)".
    destruct Hpeq as (->&->&?&?&Hoff).
    wp_pures.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { solve_ndisj. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. repeat econstructor; eauto.
    }
    iModIntro.
    iExists _. iFrame.
    replace (k * uint.Z 1) with k by word.
    iLeft.
    rewrite ?map_length.
    unshelve (iExists (l' +ₗ k), (ls' +ₗ k), _, _, _; iFrame).
    { eauto. }
    {
      apply List.map_neq_nil, List.drop_lt. lia.
    }
    iSplitL "".
    { iPureIntro. split_and!; eauto. rewrite ?addr_offset_of_plus Hoff //. }
    iFrame.
    iDestruct "Hlist" as "[Hinb|Hoob]".
    {
      iLeft. setoid_rewrite loc_add_assoc.
      rewrite -?List.list_fmap_map fmap_drop.
      iDestruct (big_sepL_drop _ _ (Z.to_nat k) with "Hinb") as "H".
      iApply (big_sepL_mono with "H").
      iIntros (k' ? _) "H".
      replace (Z.of_nat (Z.to_nat k + k')%nat) with (k + k'); eauto. lia.
    }
    {
      iRight.
      iDestruct "Hoob" as %Hoob. iPureIntro.
      rewrite ?addr_offset_of_plus drop_length. lia.
    }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) l').
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [Primitive1Ctx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last done. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vn1) "H". iDestruct "H" as (vsn1) "(Hj&Hv1)".

    iApply wp_wpc.
    iApply wp_fupd.

    rewrite val_interp_struct_unfold.
    iDestruct "Hv1" as "[Hv|Hnull]".
    * iDestruct "Hv" as (lv lvs n H0lt Hnonemtpy (->&->&?&?&?)) "(Hpaired&Hblock1&Hblocked2&Hloc)".
      iDestruct "Hloc" as "[Hinbound|Hoob]".
      {
        iDestruct "Hinbound" as "(H&_)".
        rewrite /is_loc. iDestruct "H" as "(Hlocinv&Hpaired')".
        iDestruct "Hlocinv" as (γ) "Hlocinv".
        iInv "Hlocinv" as "Hlocinv_body" "Hclo".
        rewrite /loc_inv. iDestruct "Hlocinv_body" as (??) "H".
        iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
        {
          iDestruct "H0readers" as "(>Hfc&>Hspts&>Hpts&#Hval)".
          rewrite ?loc_add_0.
          wp_step.
          iApply wp_ncfupd.
          iApply (wp_load with "[$]"). iIntros "!> Hpts".
          iMod (ghost_load with "[$] Hspts Hj") as "(Hspts&Hj)".
          { solve_ndisj. }
          iMod ("Hclo" with "[Hpts Hspts Hfc Hval]").
          { iNext. iExists _, _. iLeft. iFrame. iFrame "Hval". }
          iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
          iIntros " !>". iExists _. iFrame. iFrame "Hval".
        }
        {
          iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts&Hspts_clo&>Hpts&#Hval)".
          rewrite ?loc_add_0.
          wp_step.
          iApply wp_ncfupd.
          iApply (wp_load with "[$]"). iIntros "!> Hpts".
          iMod (ghost_load_rd with "[$] Hspts Hj") as "(Hspts&Hj)".
          { solve_ndisj. }
          iMod ("Hclo" with "[Hpts Hspts Hspts_clo Hfc Hval]").
          { iNext. iExists _, _. iRight. iLeft. iExists _, _, _. iFrame. iFrame "Hval". eauto. }
          iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
          iIntros " !>". iExists _. iFrame. iFrame "Hval".
        }
        {
          iDestruct "Hwriter" as "(>Hfc&>Hspts)".
          rewrite ?loc_add_0.
          iMod (ghost_load_write_stuck with "[$] [$] [$]") as %[].
          { solve_ndisj. }
        }
      }
      {
        iDestruct "Hoob" as %Hoob.
        iMod (ghost_load_block_oob_stuck with "[$] [$] [$]") as %[].
        { simpl in Hoob. lia. }
        { solve_ndisj. }
      }
    * iDestruct "Hnull" as %(?&->&->).
      iMod (ghost_load_null_stuck with "[$] [$]") as %[].
      { rewrite addr_base_of_plus //=. }
      { solve_ndisj. }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ v) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (varg) "H". iDestruct "H" as (vsarg) "(Hj&Hvarg)".

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) l').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    simpl. spec_bind (subst_map _ l) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[Hvarg] [] H"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvl)".

    iApply wp_wpc.
    iApply wp_ncfupd.
    rewrite /Store. wp_pures.
    wp_bind (PrepareWrite _).

    (* XXX need tactic to do these pure det reductions ... *)
    simpl.
    spec_bind (App _ vsl) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (App _ vsl) with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. econstructor. eauto.
    }
    simpl.
    clear Hctx'.


    spec_bind (Rec _ _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (Rec _ _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { simpl. iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. econstructor; eauto.
      * simpl. econstructor. econstructor.
      * econstructor. eauto.
    }
    clear Hctx'.

    spec_bind (App _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ _
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { simpl. iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. econstructor; eauto.
    }
    clear Hctx'.

    simpl.
    spec_bind (PrepareWrite vsl) as Hctx'.
    wp_apply (logical_reln_prepare_write _ _ _ _ _ _ (Hctx') with "[Hvl Hj]").
    { iFrame "Hspec Hvl". iFrame "Hj". }
    clear Hctx'.

    iDestruct 1 as (lsval lval ?? γ (->&->)) "(#Hlocinv&Htok&Hj&Hspts&Hspts_clo&Hpts&Hpts_clo)".

    simpl.
    spec_bind (Rec _ _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (Rec _ _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. repeat econstructor; eauto.
    }
    clear Hctx'.

    simpl.
    spec_bind (App _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (App _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    wp_pures.
    wp_apply (logical_reln_finish_store with "[-]").
    { iFrame. iFrame "#". eauto. }
    iIntros "Hj".
    iModIntro. iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) l').
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    simpl. spec_bind (subst_map _ l) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj"); clear Hctx'.
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvl)".

    iApply wp_wpc.
    iApply wp_fupd.
    rewrite /Read. wp_pures.
    wp_bind (StartRead _).

    (* XXX need tactic to do these pure det reductions ... *)
    simpl.
    spec_bind (App _ vsl) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (App _ vsl) with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. econstructor. eauto.
    }
    simpl.
    clear Hctx'.

    spec_bind (StartRead vsl) as Hctx'.
    wp_apply (logical_reln_start_read _ _ _ _ _ _ (Hctx') with "[Hvl Hj]").
    { iFrame "Hspec Hvl". iFrame "Hj". }
    clear Hctx'.

    iIntros (mem_v).
    iDestruct 1 as (lsval lval ? γ q (->&->&?&?)) "(#Hlocinv&Htok&Hj&#Hval&Hspts&Hpts&Hpts_clo)".

    simpl.
    spec_bind (Rec _ _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (Rec _ _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. repeat econstructor; eauto.
    }
    clear Hctx'.

    simpl.
    spec_bind (App _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (App _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. repeat econstructor; eauto.
    }
    clear Hctx'.
    simpl.

    wp_pures.
    spec_bind (FinishRead _) as Hctx'.
    wp_apply (logical_reln_finish_read with "[-]").
    { eauto. }
    { iFrame. iFrame "#". }
    iIntros "Hj".
    clear Hctx'.

    simpl.
    spec_bind (Rec _ _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (Rec _ _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. repeat econstructor; eauto.
    }
    clear Hctx'.

    simpl.
    spec_bind (App _ _) as Hctx'.
    iMod (ghost_step_lifting_puredet _ _ _ (App _ _)
            with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)". }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. simpl. repeat econstructor; eauto.
    }
    wp_pures.
    iModIntro. iExists _. simpl. iFrame. eauto.
  - subst.
    Opaque val_interp.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) l').
    iPoseProof (IHHtyping1 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ l) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvl)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v1').
    iPoseProof (IHHtyping2 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ v1) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hvl] [] H"); last by auto.
    iIntros (v1_done) "H". iDestruct "H" as (vs1_done) "(Hj&Hv1)".
    clear Hctx'.
    simpl.

    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v2').
    iPoseProof (IHHtyping3 with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ v2) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[Hvl Hv1] [] H"); last by auto.
    iIntros (v2_done) "H". iDestruct "H" as (vs2_done) "(Hj&Hvs2_done)".
    clear Hctx'.
    simpl.

    Transparent val_interp.
    iApply wp_wpc.
    iApply wp_fupd.

    rewrite val_interp_struct_unfold.
    iDestruct "Hvl" as "[Hv|Hnull]".
    * iDestruct "Hv" as (lv lvs n H0lt Hnonemtpy (->&->&?&?&?)) "(Hpaired&Hblock1&Hblocked2&Hloc)".
      iDestruct "Hloc" as "[Hinbound|Hoob]".
      {
        iDestruct "Hinbound" as "(H&_)".
        rewrite /is_loc. iDestruct "H" as "(Hlocinv&Hpaired')".
        iDestruct "Hlocinv" as (γ) "Hlocinv".
        iInv "Hlocinv" as "Hlocinv_body" "Hclo".
        rewrite /loc_inv. iDestruct "Hlocinv_body" as (mem_vs mem_v) "H".
        iDestruct (unboxedTy_val_unboxed with "Hv1") as %(Hsunboxed&Hunboxed).
        { eauto. }
        iDestruct "H" as "[H0readers|[Hreaders|Hwriter]]".
        {
          iDestruct "H0readers" as "(>Hfc&>Hspts&>Hpts&#Hval)".
          rewrite ?loc_add_0.
          iDestruct (comparableTy_val_eq with "Hv1 Hval") as ">Heq".
          { apply unboxedTy_comparable. eauto. }
          iDestruct "Heq" as %Heq_iff.
          destruct (decide (mem_v = v1_done)).
          * iApply wp_ncfupd.
            wp_apply (wp_cmpxchg_suc with "Hpts"); first eauto.
            { right. eauto. }
            iIntros "Hpts".
            iMod (ghost_cmpxchg_suc with "[$] Hspts Hj") as "(Hspts&Hj)".
            { symmetry. eapply Heq_iff; eauto. }
            { right; eauto. }
            { solve_ndisj. }
            iMod ("Hclo" with "[Hpts Hspts Hfc Hval Hvs2_done]").
            { iNext. iExists _, _. iLeft. iFrame. }
            iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
            iIntros "!>". iExists _. iFrame. iExists _, _, _, _. iFrame. iSplitL ""; first eauto.
            iFrame "Hval". eauto.
          * iApply wp_ncfupd.
            wp_apply (wp_cmpxchg_fail with "Hpts"); first eauto.
            { right. eauto. }
            iIntros "Hpts".
            iMod (ghost_cmpxchg_fail with "[$] Hspts Hj") as "(Hspts&Hj)".
            { naive_solver. }
            { right; eauto. }
            { solve_ndisj. }
            iMod ("Hclo" with "[Hpts Hspts Hfc Hval]").
            { iNext. iExists _, _. iLeft. iFrame. eauto. }
            iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
            iIntros "!>". iExists _. iClear "Hvs2_done". iFrame. iExists _, _, _, _.
            iSplitL ""; first eauto. iFrame "Hval". eauto.
        }
        {
          iDestruct "Hreaders" as (q q' n') "(>%&>Hfc&>Hspts&Hspts_clo&>Hpts&#Hval)".
          rewrite ?loc_add_0.
          iDestruct (comparableTy_val_eq with "Hv1 Hval") as ">Heq".
          { apply unboxedTy_comparable. eauto. }
          iDestruct "Heq" as %Heq_iff.
          destruct (decide (mem_v = v1_done)).
          * iMod (ghost_cmpxchg_suc_read_stuck with "[$] Hspts Hj") as %[].
            { symmetry. eapply Heq_iff; eauto. }
            { lia. }
            { solve_ndisj. }
          * iApply wp_ncfupd. wp_apply (wp_cmpxchg_fail with "Hpts"); first eauto.
            { right. eauto. }
            iIntros "Hpts".
            iMod (ghost_cmpxchg_fail_rd with "[$] Hspts Hj") as "(Hspts&Hj)".
            { naive_solver. }
            { right; eauto. }
            { solve_ndisj. }
            iMod ("Hclo" with "[Hpts Hspts Hfc Hval Hspts_clo]").
            { iNext. iExists _, _. iRight. iLeft. iExists _, _, _. iFrame. iFrame "%". eauto. }
            iApply fupd_ncfupd. iApply fupd_mask_intro_subseteq; first by set_solver+.
            iIntros "!>". iExists _. iClear "Hvs2_done". iFrame. iExists _, _, _, _.
            iSplitL ""; first eauto. iFrame "Hval". eauto.
        }
        {
          iDestruct "Hwriter" as "(>Hfc&>Hspts)".
          rewrite ?loc_add_0.
          iMod (ghost_cmpxchg_write_stuck with "[$] [$] [$]") as %[].
          { solve_ndisj. }
        }
      }
      {
        iDestruct "Hoob" as %Hoob.
        iMod (ghost_cmpxchg_block_oob_stuck with "[$] [$] [$]") as %[].
        { simpl in Hoob. lia. }
        { solve_ndisj. }
      }
    * iDestruct "Hnull" as %(?&->&->).
      iMod (ghost_cmpxchg_null_stuck with "[$] [$]") as %[].
      { rewrite addr_base_of_plus //=. }
      { solve_ndisj. }
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) sel').
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ sel) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvl)".
    clear Hctx'.
    simpl.

    iApply wp_wpc.
    iApply wp_fupd.
    iInv "Htrace" as (????) ">(He1&He2&Htr1&Htr2&Hor1&Hor2)" "Hclo".
    iDestruct "He1" as %->.
    iDestruct "He2" as %->.
    iDestruct "Hvl" as (?) "(%&%)". subst.
    wp_apply (wp_input with "[$]").
    iIntros "(Htr1&Hor1)".
    iMod (ghost_input with "[$] [$] [$] [$]") as "(Hj&?&?)".
    { solve_ndisj. }
    { solve_ndisj. }
    iMod ("Hclo" with "[-Hj]").
    { iNext. iExists _, _, _, _. iFrame. eauto. }
    iIntros "!> !>". iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) v').
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H".
    spec_bind (subst_map _ v) as Hctx'.
    iSpecialize ("H" $! j _ Hctx' with "Hj").
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (vl) "H". iDestruct "H" as (vsl) "(Hj&Hvl)".
    clear Hctx'.
    simpl.

    iApply wp_wpc.
    iApply wp_ncfupd.
    iInv "Htrace" as (????) ">(He1&He2&Htr1&Htr2&Hor1&Hor2)" "Hclo".
    iDestruct "He1" as %->.
    iDestruct "He2" as %->.
    iDestruct "Hvl" as (?) "(%&%)". subst.
    wp_apply (wp_output with "[$]").
    iIntros "Htr1".
    iMod (ghost_output with "[$] [$] [$]") as "(Hj&?)".
    { solve_ndisj. }
    { solve_ndisj. }
    iMod ("Hclo" with "[-Hj]").
    { iNext. iExists _, _, _, _. iFrame. eauto. }
    iIntros "!> !>". iExists _. iFrame. eauto.
  - subst.
    iIntros (j K Hctx) "Hj". simpl.
    iPoseProof (IHHtyping with "[//] [$] [$] [$] [$]") as "H"; eauto.
    wpc_bind (subst_map ((subst_ival <$> Γsubst)) _).
    iSpecialize ("H" $! j (λ x, K (ectx_language.fill [AppRCtx _] x)) with "[] Hj").
    { iPureIntro. apply comp_ctx; last by auto. apply ectx_lang_ctx. }
    iApply (wpc_mono' with "[] [] H"); last by auto.
    iIntros (v2) "H". iDestruct "H" as (vs2) "(Hj&Hv2)".
    iPoseProof (Hrules with "[$] [$] [$] [] Hj") as "H"; eauto.
  (* Values *)
  - inversion b; subst; eauto.
    * iRight. iExists O. rewrite loc_add_0 //=.
    * iRight. iExists O. rewrite loc_add_0 //=.
  - iPoseProof (IHHtyping with "[$] [$] [$]") as "Hv1"; eauto.
    iPoseProof (IHHtyping0 with "[$] [$] [$]") as "Hv2"; eauto.
    iExists _, _, _, _. iSplitL ""; first by eauto. iFrame.
  - iExists [], []. simpl. eauto.
  - iPoseProof (IHHtyping with "[$] [$] [$]") as "Hv1"; eauto.
    iPoseProof (IHHtyping0 with "[$] [$] [$]") as "Hv2"; eauto.
    rewrite val_interp_list_unfold.
    iDestruct "Hv2" as (l l' (->&->)) "H".
    iExists (vhd :: l), (vhd' :: l').
    iSplit; first eauto. iFrame.
  - iLeft. iExists _, _.
    iSplitL ""; first by eauto. iApply (IHHtyping with "[$] [$] [$]").
  - iRight. iExists _, _.
    iSplitR ""; first by eauto. iApply (IHHtyping with "[$] [$] [$]").
  - iLöb as "IH".
    iExists _, _, _, _, _, _.
    iSplitL ""; first by eauto. iModIntro.
    iIntros (varg vsarg) "Hvarg".
    iIntros (j K Hctx) "Hj". simpl.
    wpc_pures; first auto.
    iApply wp_wpc.
    iMod (ghost_step_lifting_puredet with "[Hj]") as "(Hj&_)"; swap 1 3.
    { iFrame. iDestruct "Hspec" as "($&?)".
    }
    { set_solver+. }
    { intros ?. eexists. simpl.
      apply base_prim_step_trans. econstructor; eauto.
    }

    iPoseProof (ctx_has_semTy_subst with "[] []") as "H1".
    { iApply IHHtyping. }
    { simpl. iApply "IH". }
    iPoseProof (ctx_has_semTy_subst with "[] Hvarg") as "H2".
    { iApply "H1". }
    iSpecialize ("H2" $! ∅ with "[] [$] [$] [$] [] [//] [Hj]").
    { iPureIntro. apply: fmap_empty. }
    { iApply big_sepM_empty. eauto. }
    { rewrite fmap_empty subst_map_empty. iFrame. }
    rewrite fmap_empty subst_map_empty. iApply wpc_wp. eauto.
Qed.
End pfs.
