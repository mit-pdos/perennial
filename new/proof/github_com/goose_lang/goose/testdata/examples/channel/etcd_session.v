From New.proof Require Import proof_prelude.

From New.proof Require Import sync.atomic strings fmt sync time
  chan_proof.closeable.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples.channel
  Require Import etcd_session.

From New.proof.github_com.goose_lang.goose.model.channel Require Import idioms.
Import bag.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : etcd_session.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Definition is_inv : iProp Σ :=
  "#Hmu" ∷ is_Mutex (global_addr etcd_session.mu) (
      ∃ ch γch,
        "sessionc" ∷ (global_addr etcd_session.sessionc) ↦{#1/2} ch ∗
        "#Hsessionc" ∷ own_closeable_chan ch γch True closeable.Unknown ∗
        "#Hsessionc_is" ∷ is_chan ch γch unit
    )
.

#[global] Instance : IsPkgInit (iProp Σ) etcd_session := define_is_pkg_init is_inv%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) etcd_session := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop etcd_session get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    etcd_session.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init etcd_session }}}.
Proof.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ").
  { destruct Hinit as (-> & ?). reflexivity. }
  iIntros "Hown". wp_auto.
  wp_apply wp_GlobalAlloc as "mu".
  wp_apply wp_GlobalAlloc as "sessionc".
  wp_apply (primitive.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (time.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (sync.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }
  wp_apply (errors.wp_initialize' with "[$Hown]") as "(Hown & #?)".
  { naive_solver. }

  iApply wp_fupd.
  wp_apply chan.wp_make1 as "* (#? & % & ?)".
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".
  iMod (alloc_closeable_chan with "[$] [$]") as "Hown".
  iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".
  iDestruct "sessionc" as "[H ?]".
  iMod (init_Mutex with "[$] [H]") as "#$".
  { iFrame "∗#". }
  done.
Qed.

Lemma wp_newSession :
  {{{ is_pkg_init etcd_session }}}
    @! etcd_session.newSession #()
  {{{ (err : error.t), RET #err; True }}}.
Proof.
  wp_start. wp_apply primitive.wp_RandomUint64 as "% _". wp_if_destruct.
  { wp_apply errors.wp_New as "% _". wp_end. }
  { wp_end. }
Qed.

Lemma wp_waitForSessionExpiration :
  {{{ is_pkg_init etcd_session }}}
    @! etcd_session.waitForSessionExpiration #()
  {{{ RET #(); True }}}.
Proof. wp_start. wp_end. Qed.

Lemma wp_monitorSession ch γch :
  {{{ is_pkg_init etcd_session ∗
      "sessionc" ∷ (global_addr etcd_session.sessionc) ↦{#1/2} (ch : chan.t) ∗
      "Hsessionc" ∷ own_closeable_chan ch γch True closeable.Open ∗
      "#Hsessionc_is" ∷ is_chan ch γch unit
(* TODO now: reduce the frequency with which [is_chan] has to be manually written. Do this by:
   1) putting is_chan inside the `recv_au`, `send_au`, etc. so it isn't a
   separate precond on the send/recv/select WPs.
   2) in the case of the closeable spec, put is_chan inside `own_closeable_chan`
   3) commit changes with a concise commit message.
 *)
  }}}
    @! etcd_session.monitorSession #()
  {{{ RET #(); True }}}.
Proof.
  wp_start as "@".
  iAssert (
      ∃ ch γch cst,
        "sessionc" ∷ global_addr etcd_session.sessionc ↦{#1 / 2} ch ∗
        "Hsessionc" ∷ (own_closeable_chan ch γch True cst) ∗
        "#Hsessionc_is" ∷ is_chan ch γch unit ∗
        "%Hcst" ∷ ⌜ cst ≠ closeable.Unknown ⌝
    )%I with "[sessionc Hsessionc]" as "HH".
  { iFrame "∗#". done. }
  iClear "Hsessionc_is".
  wp_for "HH".
  wp_apply wp_waitForSessionExpiration.
  iDestruct (is_pkg_init_access with "[$]") as "#Hinv".
  simpl. rewrite /is_inv. iNamed "Hinv".
  wp_apply (wp_Mutex__Lock with "[]").
  { iFrame "#". }
  iIntros "[Hlocked Hown]". iNamedSuffix "Hown" "_inv".
  wp_auto.
  wp_bind.
  iCombine "sessionc sessionc_inv" gives %Heq. subst.
  iCombine "sessionc sessionc_inv" as "sessionc".
  iApply (wp_wand _ _ _
              (λ v,
                 ⌜ v = execute_val ⌝ ∗
                 ∃ ch γch,
                   "sessionc" ∷ global_addr etcd_session.sessionc ↦ ch ∗
                   "Hsessionc" ∷ own_closeable_chan ch γch True closeable.Open ∗
                   "#Hsessionc_is" ∷ is_chan ch γch unit
              )%I with "[sessionc Hsessionc]").
  {
    - wp_apply (chan.wp_select_nonblocking_alt [⌜ cst = closeable.Open ⌝%I] with "[] [-]").
      2:{ iNamedAccu. }
      { rewrite big_sepL2_cons. iSplit.
        + iNamed 1. repeat iExists _; iSplitR; first done.
          iFrame "Hsessionc_is".
          iApply (own_closeable_chan_nonblocking_receive with "[$]").
          iSplit.
          { destruct cst; try done.
            iIntros "#Hclosed". wp_auto. iApply wp_fupd.
            wp_apply chan.wp_make1 as "* (#? & % & ?)".
            iMod (alloc_closeable_chan with "[$] [$]") as "Hown".
            iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".
            iSplitR; first done. iFrame "∗#%". done. }
          destruct cst; try done. iIntros. iFrame. done.
        + rewrite big_sepL2_nil //. }
      { simpl. iIntros "@ [%H _]". wp_auto. subst.
        iSplitR; first done.
        iFrame "∗#%". }
  }
  iClear "Hsessionc_is".
  iIntros "% [% @]". subst. wp_auto.
  iDestruct "sessionc" as "[sessionc sessionc_inv]".
  iCombineNamed "*_inv" as "Hinv".
  iDestruct (own_closeable_chan_Unknown with "[$]") as "#?".
  wp_apply (wp_Mutex__Unlock with "[$Hlocked Hinv]").
  { iFrame "#". iNamed "Hinv". iFrame "∗#". }
  wp_apply wp_newSession as "% _". destruct err.
  - wp_auto. wp_for_post. iFrame "∗#%". done.
  - wp_auto. wp_apply (wp_Mutex__Lock with "[]"); first iFrame "#".
    iIntros "[Hlocked H]". iNamedSuffix "H" "_inv2". wp_auto.
    iCombine "sessionc sessionc_inv2" gives %Heq. subst.
    wp_apply (wp_closeable_chan_close with "[$Hsessionc]").
    { done. }
    iIntros "#?". wp_auto.
    iCombineNamed "*_inv2" as "Hinv".
    wp_apply (wp_Mutex__Unlock with "[$Hlocked Hinv]").
    { iFrame "#". iNamed "Hinv". iFrame "∗#". }
    wp_for_post.
    iFrame "∗#%". done.
Qed.

Lemma waitSession A A' `{!ZeroVal A'} `{!TypedPointsto A'} `{!IntoValTyped A' A}
  cancel γcancel (Pcancel : A' → _) :
  {{{ is_pkg_init etcd_session ∗
      "#Hcancel" ∷ is_chan_bag γcancel cancel Pcancel }}}
    #(functions etcd_session.waitSession [A]) #cancel
  {{{ (err : error.t), RET #err;
      match err with
      | interface.nil => True
      | _ => (∃ a, Pcancel a)
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iDestruct (is_pkg_init_access with "[$]") as "#Hinv".
  simpl. rewrite /is_inv. iNamed "Hinv".
  wp_apply (wp_Mutex__Lock with "[]").
  { iFrame "#". }
  iIntros "[Hlocked Hown]". iNamedSuffix "Hown" "_inv".
  wp_auto.
  iCombineNamed "*_inv" as "Hinv".
  wp_apply (wp_Mutex__Unlock with "[$Hlocked Hinv]") --no-auto.
  { iFrame "Hmu". iNamed "Hinv". iFrame "∗#". }
  wp_auto_lc 2.
  wp_apply chan.wp_select_blocking.
  rewrite big_andL_cons. iSplit.
  { repeat iExists _; iSplitR; first done.
    iFrame "#".
    iApply (closeable_chan_receive with "[$]").
    iIntros "[_ #?]". wp_auto. wp_end. }
  rewrite big_andL_cons. iSplit.
  { repeat iExists _; iSplitR; first done.
    iDestruct (is_bag_is_chan with "[$]") as "#?".
    iFrame "#". iApply (bag_recv_au with "[$] [$]").
    iIntros "!> % ?". wp_auto. wp_apply errors.wp_New as "% _".
    wp_end. }
  rewrite big_andL_nil //.
Qed.

End wps.
