(** Iris reasoning principles for core Grove FFI *)
From iris.base_logic Require Export lib.mono_nat.
From stdpp Require Import gmap vector fin_maps.
From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import gen_heap_names.
From iris.proofmode Require Import proofmode.
From Perennial.base_logic Require Import ghost_map.
From Perennial.program_logic Require Import ectx_lifting atomic.

From Perennial.Helpers Require Import CountableTactics Transitions Integers.
From Perennial.goose_lang Require Import lang lifting.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang.ffi.grove_ffi Require Export impl.

Set Default Proof Using "Type".
(* this is purely cosmetic but it makes printing line up with how the code is
   usually written *)
Set Printing Projections.

(** * Grove semantic interpretation and lifting lemmas *)
Class groveGS Σ : Set := GroveGS {
  #[global] groveG_net_heapG :: gen_heap.gen_heapGS endpoint (gset message) Σ;
  grove_time_name : gname;
  #[global] groveG_timeG :: mono_natG Σ;
}.

Class groveGpreS Σ : Set := {
  #[global] grove_preG_net_heapG :: gen_heap.gen_heapGpreS endpoint (gset message) Σ;
  #[global] grove_preG_files_heapG :: gen_heap.gen_heapGpreS byte_string (list byte) Σ;
  #[global] grove_preG_tscG :: mono_natG Σ;
}.
Class groveNodeGS Σ : Set := GroveNodeGS {
  #[global] groveG_preS :: groveGpreS Σ;
  grove_tsc_name : gname;
  #[global] groveG_files_heapG :: gen_heap.gen_heapGS byte_string (list byte) Σ;
}.

Definition groveΣ : gFunctors :=
  #[gen_heapΣ endpoint (gset message); gen_heapΣ byte_string (list byte); mono_natΣ].

#[global]
Instance subG_groveGpreS Σ : subG groveΣ Σ → groveGpreS Σ.
Proof. solve_inG. Qed.

Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  Existing Instances grove_op grove_model.
  Context {go_gctx : GoGlobalContext}.

  Definition data_vals (data : list u8) : list val :=
    ((λ b, #b) <$> data).

  Local Program Instance grove_interp: ffi_interp grove_model :=
    {| ffiGlobalGS := groveGS;
       ffiLocalGS := groveNodeGS;
       ffi_local_ctx _ _ σ :=
         (mono_nat_auth_own grove_tsc_name 1 (uint.nat σ.(grove_node_tsc)) ∗
          gen_heap_interp σ.(grove_node_files))%I;
       ffi_global_ctx _ _ g :=
         (gen_heap_interp g.(grove_net) ∗ mono_nat_auth_own grove_time_name 1 (uint.nat g.(grove_global_time))
         )%I;
       ffi_local_start _ _ σ :=
         ([∗ map] f↦c ∈ σ.(grove_node_files), (pointsto (L:=byte_string) (V:=list byte) f (DfracOwn 1) c))%I;
       ffi_global_start _ _ g :=
         ([∗ map] e↦ms ∈ g.(grove_net), (pointsto (L:=endpoint) (V:=gset message) e (DfracOwn 1) ms))%I;
       ffi_restart _ _ _ := True%I;
      ffi_crash_rel Σ hF1 σ1 hF2 σ2 :=
        (* TODO: you could also assume the tsc is non-decreasing across a crash *)
       ⌜ hF1 = hF2 ∧ σ1.(grove_node_files) = σ2.(grove_node_files) ⌝%I;
    |}.
End grove.

Notation "c c↦ ms" := (pointsto (L:=endpoint) (V:=gset message) c (DfracOwn 1) ms)
                       (at level 20, format "c  c↦  ms") : bi_scope.

Notation "s f↦{ q } c" := (pointsto (L:=byte_string) (V:=list byte) s q c)
                            (at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{DfracOwn 1} c)%I
                       (at level 20, format "s  f↦ c") : bi_scope.

Section lifting.
  Existing Instances grove_op grove_model grove_semantics grove_interp.
  Context `{!gooseGlobalGS Σ, !gooseLocalGS Σ} {go_gctx : GoGlobalContext}.
  Local Instance goose_groveGS : groveGS Σ := goose_ffiGlobalGS.
  Local Instance goose_groveNodeGS : groveNodeGS Σ := goose_ffiLocalGS.

  Definition chan_meta_token (c : endpoint) (E: coPset) : iProp Σ :=
    gen_heap.meta_token (hG := groveG_net_heapG) c E.
  Definition chan_meta `{Countable A} (c : endpoint) N (x : A) : iProp Σ :=
    gen_heap.meta (hG := groveG_net_heapG) c N x.

  (** "The TSC is at least" *)
  Definition tsc_lb (time : nat) : iProp Σ :=
    mono_nat_lb_own grove_tsc_name time.

  (* FIXME: have to manually put some of this stuff here because of two mono_natG's in context *)
  Definition is_time_lb (t:u64) := @mono_nat_lb_own Σ (goose_groveGS.(groveG_timeG)) grove_time_name (uint.nat t).
  Definition own_time (t:u64) := @mono_nat_auth_own Σ (goose_groveGS.(groveG_timeG)) grove_time_name 1 (uint.nat t).

  Lemma own_time_get_lb t :
    own_time t -∗ is_time_lb t.
  Proof.
    rewrite /own_time /is_time_lb. destruct goose_groveGS.
    iApply mono_nat_lb_own_get.
  Qed.

  Lemma is_time_lb_mono t t':
    uint.nat t <= uint.nat t' →
    is_time_lb t' -∗ is_time_lb t.
  Proof.
    rewrite /own_time /is_time_lb. destruct goose_groveGS.
    intros.
    iApply mono_nat_lb_own_le.
    word.
  Qed.

  Definition connection_socket (c_l : endpoint) (c_r : endpoint) : val :=
    ExtV (ConnectionSocketV c_l c_r).
  Definition listen_socket (c : endpoint) : val :=
    ExtV (ListenSocketV c).
  Definition bad_socket : val :=
    ExtV BadSocketV.

  (* Lifting automation *)
  Local Hint Extern 0 (base_reducible _ _ _) => eexists _, _, _, _, _; simpl : core.
  Local Hint Extern 0 (base_reducible_no_obs _ _ _) => eexists _, _, _, _; simpl : core.
  (** The tactic [inv_base_step] performs inversion on hypotheses of the shape
[base_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
  Ltac inv_base_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : base_step ?e _ _ _ _ _ _ _ |- _ =>
          rewrite /base_step /= in H;
          monad_inv; repeat (simpl in H; monad_inv)
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | H : prod _ _ |- _ => destruct H
        | H : and _ _ |- _ => destruct H
        | H : ex _ |- _ => destruct H
        | H : ∀ _, (_ = _) → _ |- _ => specialize (H _ ltac:(done))
        | H : ∀ _ _, (_ = _) → _ |- _ => specialize (H _ _ ltac:(done))
        | H : ∀ _ _ _ , (_ = _) → _ |- _ => specialize (H _ _ _ ltac:(done))
        | _ => progress subst
        end.

  Local Lemma wp_GroveOp op (v : val) s E Φ :
    ▷ (∀ σ1 g1 e2 σ2 g2 (Hstep : is_grove_ffi_step op v e2 σ1 σ2 g1 g2),
       ffi_local_ctx goose_ffiLocalGS  σ1 -∗
       ffi_global_ctx goose_ffiGlobalGS g1 -∗ |NC={E}=>
       (ffi_local_ctx goose_ffiLocalGS σ2 ∗
        ffi_global_ctx goose_ffiGlobalGS g2 ∗
        WP e2 @ s; E {{ Φ }})) -∗
    WP ExternalOp op v @ s; E {{ v, Φ v }}.
  Proof.
    iLöb as "IH".
    iIntros "HΦ".
    Search lc "wp_".
    iApply wp_lift_step_ncfupd; first by auto.
    iIntros (σ1 g1 ns mj D κ κs nt) "@ Hg".
    iApply ncfupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
    iSplit.
    { iPureIntro. destruct s; try done. apply base_prim_reducible.
      repeat econstructor; simpl.
      { instantiate (1:=(_, _, _)). repeat econstructor. }
      repeat econstructor. }
    iIntros "!>" (v2 σ2 g2 efs Hstep).
    iMod (global_state_interp_le with "Hg") as "Hg".
    { apply step_count_next_incr. }
    apply base_reducible_prim_step in Hstep.
    2:{ repeat econstructor; simpl.
        { instantiate (1:=(_, _, _)). repeat econstructor. }
        repeat econstructor. }
    inv Hstep. simpl in *.
    inv_base_step. monad_inv. simpl in *.
    inv_base_step. monad_inv. destruct H0; inv_base_step.
    { iFrame "∗#%". iMod "Hmask" as "_". iIntros "Hlc". iModIntro.
      iSplitL; last done. by iApply "IH". }
    iMod "Hmask" as "_".
    iDestruct "Hg" as "[Hffi_global Hg]".
    iMod ("HΦ" with "[//] [$] [$]") as "H".
    iDestruct "H" as "(? & ? & ?)".
    iIntros "Hlc". iFrame "∗#%". done.
  Qed.

  Lemma wp_ListenOp (c : w64) s E :
    {{{ True }}}
      ExternalOp ListenOp #c @ s; E
    {{{ RET listen_socket c; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". iModIntro. inv_base_step.
    iFrame "∗#". iApply wp_value. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_ConnectOp c_r s E :
    {{{ True }}}
      ExternalOp ConnectOp #c_r @ s; E
    {{{ (err : bool) (c_l : endpoint),
      RET (#err, if err then bad_socket else connection_socket c_l c_r);
      if err then True else c_l c↦ ∅
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg".
    inv_base_step. monad_inv.
    destruct x; inv_base_step.
    - iFrame "∗#%".
      iDestruct "Hg" as "(? & ?)".
      iMod (@gen_heap_alloc with "[$]") as "[? [? ?]]"; first done.
      iFrame "∗#%". iModIntro. iApply wp_value. iApply ("HΦ" $! false). iFrame.
    - iFrame "∗#". iApply wp_value. by iApply ("HΦ" $! true (W64 0)).
  Qed.

  Lemma wp_AcceptOp c_l s E :
    {{{ True }}}
      ExternalOp AcceptOp (listen_socket c_l) @ s; E
    {{{ c_r, RET connection_socket c_l c_r; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". iModIntro. inv_base_step.
    iFrame "∗#". iApply wp_value. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_SendOp c_l c_r ms (l : loc) (data : list u8) s E :
    {{{ c_r c↦ ms }}}
      ExternalOp SendOp (connection_socket c_l c_r, #data)%V @ s; E
    {{{ (err_early err_late : bool), RET #(err_early || err_late);
       c_r c↦ (if err_early then ms else ms ∪ {[Message c_l data]}) }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step. iFrame "∗#".
    iDestruct "Hg" as "(Hg & ?)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Heq.
    rewrite Heq in H0. inv_base_step.
    iMod (@gen_heap_update with "Hg Hc") as "[$ Hc]".
    iFrame. iModIntro. iApply wp_value. by iApply ("HΦ" $! false).
  Qed.

  Lemma wp_RecvOp c_l c_r ms s E :
    {{{ c_l c↦ ms }}}
      ExternalOp RecvOp (connection_socket c_l c_r) @ s; E
    {{{ (err : bool) (data : list u8),
        RET (#err, #data);
        ⌜if err then True else Message c_r data ∈ ms ⌝ ∗
        c_l c↦ ms
    }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step.
    iDestruct "Hg" as "(Hg & ?)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Heq.
    iFrame "∗#%". rewrite Heq in H. iModIntro. destruct x; inv_base_step.
    { iApply wp_value. iApply "HΦ". by iFrame. }
    { iApply wp_value. iApply ("HΦ" $! false). by iFrame. }
  Qed.

  Lemma wp_FileReadOp (f : go_string) q c E :
    {{{ f f↦{q} c }}}
      ExternalOp FileReadOp #f @ E
    {{{ RET #c; f f↦{q} c }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step.
    iDestruct "Hl" as "(? & %Hl & Hl)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Heq.
    iFrame "∗#%". rewrite Heq in H0. inv_base_step. iModIntro.
    iApply wp_value. by iApply "HΦ".
  Qed.

  Lemma wp_FileWriteOp f old new E :
    {{{ f f↦ old }}}
      ExternalOp FileWriteOp (#f, #new)%V @ E
    {{{ RET #(); f f↦ new }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step.
    iDestruct "Hl" as "(? & %Hfilebound & Hl)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Heq.
    iFrame "∗#%". iMod (@gen_heap_update with "[$] [$]") as "[? ?]".
    iModIntro. iFrame. iApply wp_value; by iApply "HΦ".
  Qed.

  Lemma wp_FileAppendOp f old new E :
    {{{ f f↦ old  }}}
      ExternalOp FileAppendOp (#f, #new)%V @ E
    {{{ RET #(); f f↦ (old ++ new) }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step.
    iDestruct "Hl" as "(? & Hl)".
    iDestruct (@gen_heap_valid with "[$] [$]") as %Heq.
    rewrite Heq in H0. inv_base_step.
    iFrame "∗#%". iMod (@gen_heap_update with "[$] [$]") as "[? ?]".
    iModIntro. iFrame. iApply wp_value; by iApply "HΦ".
  Qed.

  Lemma wp_GetTscOp prev_time s E :
    {{{ tsc_lb prev_time }}}
      ExternalOp GetTscOp #() @ s; E
    {{{ (new_time: u64), RET #new_time;
      ⌜prev_time ≤ uint.nat new_time⌝ ∗ tsc_lb (uint.nat new_time)
    }}}.
  Proof.
    iIntros (Φ) "Hc HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step.
    iDestruct "Hl" as "(? & Hl)".
    iDestruct (mono_nat_lb_own_valid with "[$] [$]") as %[_ Hlb].
    iMod (mono_nat_own_update (uint.nat x) with "[$]") as "[? ?]"; first lia.
    iFrame "∗#%". iModIntro. iApply wp_value. iApply "HΦ". iFrame. word.
  Qed.

  Lemma wp_GetTimeRangeOp s E :
   ∀ Φ, (∀ (l h t:u64), ⌜uint.nat t <= uint.nat h⌝ -∗ ⌜uint.nat l <= uint.nat t⌝ -∗
                  own_time t -∗ |NC={E}=> (own_time t ∗ Φ (#l, #h)%V)) -∗
   WP ExternalOp GetTimeRangeOp #() @ s; E {{ Φ }}.
  Proof.
    iIntros (Φ) "HΦ". iApply (wp_GroveOp with "[-]").
    iIntros "!> * Hl Hg". inv_base_step.
    iDestruct "Hg" as "(? & Hg)".
    iMod (@mono_nat_own_update with "[$]") as "[H _]"; first shelve.
    iSpecialize ("HΦ" with "[] [] [$]"); [shelve..|].
    iMod "HΦ" as "[? HΦ]".
    iFrame. iModIntro. iApply wp_value. iFrame.
    Unshelve. all: word.
  Qed.

  Lemma wp_time_acc e s E Φ:
  goose_lang.(language.to_val) e = None →
   (∀ t, own_time t ={E}=∗ own_time t ∗ WP e @ s; E {{ Φ }}) -∗
   WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "Hacc_wp".
    iApply wp_acc_global_state_interp.
    { rewrite H. done. }
    iIntros (?????) "[(? & Ht) ?]".
    unfold own_time.
    iMod ("Hacc_wp" with "Ht") as "[Ht Hacc_wp]".
    by iFrame.
  Qed.

End lifting.

(** * Some generally helpful lemmas *)
Section grove.
  (* these are local instances on purpose, so that importing this files doesn't
  suddenly cause all FFI parameters to be inferred as the grove model *)
  (* FIXME: figure out which of these clients need to set *)
  Existing Instances grove_op grove_model grove_semantics grove_interp goose_groveGS goose_groveNodeGS.
  Context `{!heapGS Σ}.

  Lemma tsc_lb_0 :
    ⊢ |==> tsc_lb 0.
  Proof. iApply mono_nat_lb_own_0. Qed.

  Lemma tsc_lb_weaken t1 t2 :
    (t1 ≤ t2)%nat →
    tsc_lb t2 -∗ tsc_lb t1.
  Proof. intros. apply mono_nat_lb_own_le. done. Qed.
End grove.

From Perennial.goose_lang Require Import adequacy.

#[global]
Program Instance grove_interp_adequacy {go_gctx : GoGlobalContext} :
  @ffi_interp_adequacy grove_model grove_interp grove_op grove_semantics :=
  {| ffiGpreS := groveGpreS;
     ffiΣ := groveΣ;
     subG_ffiPreG := subG_groveGpreS;
     ffi_initgP := λ g, True;
     ffi_initP := λ σ g, True;
  |}.
Next Obligation.
  rewrite //=. iIntros (_ Σ hPre g _). eauto.
  iMod (gen_heap_init g.(grove_net)) as (names) "(H1&H2&H3)".
  iMod (mono_nat_own_alloc (uint.nat g.(grove_global_time))) as (?) "[Ht _]".
  iExists (GroveGS _ names _ _). iFrame. eauto.
Qed.
Next Obligation.
  rewrite //=.
  iIntros (_ Σ hPre σ ??).
  iMod (mono_nat_own_alloc (uint.nat σ.(grove_node_tsc))) as (tsc_name) "[Htsc _]".
  iMod (gen_heap_init σ.(grove_node_files)) as (names) "(H1&H2&_)".
  iExists (GroveNodeGS _ _ tsc_name _). eauto with iFrame.
Qed.
Next Obligation.
  intros ?. iIntros (Σ σ σ' Hcrash Hold) "(Htsc_old & Hfiles_old)".
  simpl in Hold. destruct Hcrash.
  iExists Hold. iFrame. iPureIntro. done.
Qed.

Section crash.
  Existing Instances grove_op grove_model.
  Existing Instances grove_semantics grove_interp.
  Existing Instance goose_groveNodeGS.

  Lemma file_pointsto_post_crash `{!heapGS Σ} f q v:
    f f↦{q} v ⊢@{_} post_crash (λ _, f f↦{q} v).
  Proof.
    iIntros "H". iIntros (???) "#Hrel".
    iDestruct "Hrel" as %(Heq1&Heq2).
    rewrite /goose_groveNodeGS.
    rewrite Heq1. eauto.
  Qed.

  Global Instance file_pointsto_crash `{!heapGS Σ} fname data q:
    IntoCrash (fname f↦{q} data)%I (λ hG, fname f↦{q} data)%I.
  Proof.
    apply file_pointsto_post_crash.
  Qed.
End crash.
