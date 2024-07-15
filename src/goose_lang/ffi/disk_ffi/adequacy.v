From stdpp Require Import gmap.
From stdpp Require Import vector fin_maps.

From Perennial.goose_lang Require Import lang lifting.
From Perennial.goose_lang.lib Require Import slice.

From Perennial.goose_lang.ffi.disk_ffi Require Import impl specs.

From Perennial.program_logic Require Import ectx_lifting.
From Perennial.algebra Require Import gen_heap_names.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang Require Import adequacy.

#[global]
Program Instance disk_interp_adequacy:
  @ffi_interp_adequacy disk_model disk_interp disk_op disk_semantics :=
  {| ffiGpreS := disk_preG;
     ffiΣ := diskΣ;
     subG_ffiPreG := subG_diskG;
     ffi_initgP := λ _, True;
     ffi_initP := λ _ _, True;
  |}.
Next Obligation. rewrite //=. iIntros (Σ hPre g). eauto. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ?) "_".
  iMod (gen_heap_init σ) as (?) "(Hctx & Hpts & _)".
  iExists (DiskGS _ _). by iFrame.
Qed.
Next Obligation.
  iIntros (Σ σ σ' Hcrash Hold) "Hinterp".
  iExists Hold.
  inversion Hcrash; subst.
  iFrame. iPureIntro; split_and!; auto.
Qed.

Section crash.
  Existing Instances disk_op disk_model disk_ty.
  Existing Instances disk_semantics disk_interp.
  Existing Instance goose_diskGS.

  Lemma disk_pointsto_post_crash `{!heapGS Σ} l q v:
    l d↦{q} v ⊢@{_} post_crash (λ _, l d↦{q} v).
  Proof.
    iIntros "H". iIntros (???) "#Hrel".
    rewrite /ffi_crash_rel.
    iDestruct "Hrel" as %(Heq1&Heq2).
    rewrite /goose_diskGS. rewrite Heq1. eauto.
  Qed.

  Global Instance disk_pointsto_into_crash `{!heapGS Σ} l q v:
    IntoCrash (l d↦{q} v)%I (λ hG, l d↦{q} v)%I.
  Proof. apply disk_pointsto_post_crash. Qed.

  Global Instance disk_array_into_crash `{!heapGS Σ} l vs:
    IntoCrash (l d↦∗ vs)%I (λ _, l d↦∗ vs)%I.
  Proof. apply _. Qed.
End crash.
