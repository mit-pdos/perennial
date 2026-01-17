(* TODO: there should be a directory for this Go package. *)

From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base idiom.base.
From New.proof Require Import sync strings time.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.
From iris.base_logic.lib Require Import token.

Class locked_stackG Σ :=
  {
    #[local] ls_var_inG :: ghost_varG Σ (list go_string);
  }.

Section locked_stack_proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

(* FIXME: duplication *)
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Context `{!locked_stackG Σ}.

Definition own_LockedStack γ (σ : list go_string) : iProp Σ :=
  ghost_var γ (1/2) σ.
#[global] Opaque own_LockedStack.
#[local] Transparent own_LockedStack.

Definition is_LockedStack s γ : iProp Σ :=
  "#Hmu" ∷ (is_Mutex (struct.field_ref_f chan_spec_raw_examples.LockedStack "mu" s)
              (∃ stack_sl (stack : list go_string),
                  "stack" ∷ s ↦s[chan_spec_raw_examples.LockedStack :: "stack"] stack_sl ∗
                  "Hsl" ∷ stack_sl ↦* stack ∗
                  "Hcap" ∷ own_slice_cap go_string stack_sl (DfracOwn 1) ∗
                  "Hauth" ∷ ghost_var γ (1/2) (reverse stack)
    )) ∗
  "_" ∷ True.
#[global] Opaque is_LockedStack.
#[local] Transparent is_LockedStack.
#[global] Instance is_LockedStack_persistent s γ : Persistent (is_LockedStack s γ).
Proof. apply _. Qed.

Lemma wp_NewLockedStack :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.NewLockedStack #()
  {{{ s γ, RET #s; is_LockedStack s γ ∗ own_LockedStack γ [] }}}.
Proof.
  wp_start. unshelve wp_apply wp_slice_make2; try tc_solve; first word.
  iIntros (stack_sl) "[stack_sl cap]". rewrite replicate_0.
  wp_auto. wp_alloc s as "Hs".
  iApply wp_fupd. wp_auto.
  iMod (ghost_var_alloc []) as (γ) "[Hstack_auth Hstack_frag]".
  iApply "HΦ". iDestruct (struct_fields_split with "Hs") as "H". iNamed "H".
  simpl. iMod (init_Mutex with "[$] [-Hstack_frag]") as "$"; by iFrame.
Qed.

Lemma wp_LockedStack__Push v γ s :
  ∀ Φ,
  is_pkg_init chan_spec_raw_examples ∗ is_LockedStack s γ -∗
  (|={⊤,∅}=> ∃ σ, own_LockedStack γ σ ∗ (own_LockedStack γ (v :: σ) ={∅,⊤}=∗ Φ #())) -∗
  WP s @ (ptrT.id chan_spec_raw_examples.LockedStack.id) @ "Push" #v {{ Φ }}.
Proof.
  wp_start as "#His". wp_auto. iNamed "His".
  wp_apply (wp_Mutex__Lock with "[$Hmu]"). iIntros "[Hlocked Hi]".
  iNamedSuffix "Hi" "_inv". wp_auto.
  wp_apply wp_slice_literal. iIntros "% [Htmp _]". wp_auto.
  wp_apply (wp_slice_append with "[$Hsl_inv $Hcap_inv $Htmp]").
  iIntros (stack_sl') "(Hsl_inv & Hcap_inv & _)". wp_auto.
  iApply fupd_wp. iMod "HΦ" as "(% & Hl & HΦ)". iCombine "Hl Hauth_inv" gives %[_ ->].
  iMod (ghost_var_update_2 with "Hl Hauth_inv") as "[Hl Hauth_inv]".
  { compute_done. }
  iMod ("HΦ" with "Hl") as "HΦ". iModIntro.
  iCombineNamed "*_inv" as "Hi".
  wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hi]").
  { iNamed "Hi". iFrame. rewrite reverse_app. iFrame. }
  iFrame.
Qed.

Lemma wp_LockedStack__Pop γ s :
  ∀ Φ,
  is_pkg_init chan_spec_raw_examples ∗ is_LockedStack s γ -∗
  (|={⊤,∅}=> ∃ σ, own_LockedStack γ σ ∗
                 (match σ with
                  | [] => own_LockedStack γ [] ={∅,⊤}=∗ Φ (#"", #false)%V
                  | v :: σ => own_LockedStack γ σ ={∅,⊤}=∗ Φ (#v, #true)%V
                  end)
  ) -∗
  WP s @ (ptrT.id chan_spec_raw_examples.LockedStack.id) @ "Pop" #() {{ Φ }}.
Proof.
  wp_start as "#His". wp_auto. iNamed "His".
  wp_apply (wp_Mutex__Lock with "[$Hmu]"). iIntros "[Hlocked Hi]".
  iNamedSuffix "Hi" "_inv". wp_auto.
  iDestruct (own_slice_len with "[$]") as %Hlen.
  iDestruct (own_slice_cap_wf with "[$]") as %Hcap.
  iApply fupd_wp. iMod "HΦ" as "(% & Hl & HΦ)".
  iCombine "Hl Hauth_inv" gives %[_ Heq].
  apply (f_equal reverse) in Heq. rewrite reverse_involutive in Heq.
  subst. destruct σ; simpl in *.
  - iMod ("HΦ" with "Hl") as "HΦ".
    iModIntro. rewrite bool_decide_true.
    2:{ revert Hlen; by len. }
    wp_auto. iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hi]").
    { iNamed "Hi". iFrame. }
    iFrame.
  - iMod (ghost_var_update_2 with "Hl Hauth_inv") as "[Hl Hauth_inv]".
    { compute_done. }
    iMod ("HΦ" with "Hl") as "HΦ". iModIntro.
    rewrite bool_decide_false; last (revert Hlen; by len).
    wp_auto. wp_pure; first (revert Hlen; by len).
    rewrite reverse_cons.
    wp_apply (wp_load_slice_elem with "[$Hsl_inv]") as "Hsl_inv".
    { revert Hlen; by len. }
    { iPureIntro. rewrite lookup_app_r; last (revert Hlen; by len).
      replace (_) with O by (revert Hlen; by len). done. }
    (* NOTE: there are too many choices here... would be better to have at least
       one "canonical" proof approach. *)
    wp_apply (wp_slice_slice_with_cap with "[$Hsl_inv $Hcap_inv]").
    { iPureIntro. revert Hlen Hcap; by len. }
    iIntros "(_ & Hsl_inv & Hcap_inv)".
    wp_auto.
    iCombineNamed "*_inv" as "Hi".
    wp_apply (wp_Mutex__Unlock with "[$Hmu $Hlocked Hi]").
    { iNamed "Hi". iFrame. rewrite /subslice.
      rewrite take_app_le; last (revert Hlen Hcap; by len).
      rewrite take_ge; last (revert Hlen Hcap; by len).
      rewrite drop_0 reverse_involutive. iFrame. }
    iFrame.
Qed.

End locked_stack_proof.

Section elimination_stack_proof.

Record EliminationStack_names :=
  {
    spec_gn : gname;
    ls_gn : gname;
    ch_gn : chan_names;
    s_gn : gname;
    r_gn : gname;
  }.

Class elimination_stackG {ext : ffi_syntax} Σ :=
  {
    #[local] es_ls_inG :: locked_stackG Σ;
    #[local] es_var_inG :: ghost_varG Σ (list go_string);
    #[local] es_chan_inG :: chanG Σ go_string;
    #[local] es_afterChan_inG :: chanG Σ unit;
    #[local] es_time_inG :: chan_idiomG Σ time.Time.t;
    #[local] es_token_pointer_inG :: ghost_varG Σ gname;
    #[local] es_send_token_inG :: tokenG Σ;
    #[local] es_reply_token_inG :: ghost_varG Σ go_string;
  }.

Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Context `{!elimination_stackG Σ}.

Definition own_EliminationStack γ (σ : list go_string) : iProp Σ :=
  ghost_var γ.(spec_gn) (1/2) σ.
#[global] Opaque own_EliminationStack.
#[local] Transparent own_EliminationStack.

(** Supports atomic updates for Pop and Push that are allowd to access [⊤∖N]. *)

Local Notation "⟦ σ ⟧ " := (own_EliminationStack ltac2:(Control.refine (fun () => &γ)) σ) (only parsing).
Local Notation "⟦ σ ⟧" :=
  (own_EliminationStack _ σ) (only printing, format "⟦ σ ⟧").
Local Notation "½r γr"
  := (ghost_var ltac2:(Control.refine (fun () => '(&γ.(r_gn)))) (1/2) γr) (only parsing, at level 1).
Local Notation "½r γr" := (ghost_var _.(r_gn) (1/2) γr) (only printing, format "½r  γr").
Local Notation "½s γs"
  := (ghost_var ltac2:(Control.refine (fun () => '(&γ.(s_gn)))) (1/2) γs) (only parsing, at level 1).
Local Notation "½s γs" := (ghost_var _.(s_gn) (1/2) γs ) (only printing, format "½s  γs").

Local Definition own_exchanger_inv γ N exstate : iProp Σ :=
  ∃ γs γr,
  "Hs●" ∷ ½s γs ∗ "Hr●" ∷ ½r γr ∗
  "Hexchanger" ∷ (
      match exstate with
      | chan_rep.Idle =>
          "Hs◯" ∷ ½s γs ∗ "Hr◯" ∷ ½r γr
      | chan_rep.SndPending v =>
          "Hpush_au" ∷ (|={⊤∖↑N,∅}=> ∃ σ, ⟦σ⟧ ∗ (⟦v :: σ⟧ ={∅,⊤∖↑N}=∗ token γs)) ∗
          "Hr◯" ∷ ½r γr
      | chan_rep.RcvPending =>
          "Hpop_au" ∷ (|={⊤∖↑N,∅}=> ∃ σ, ⟦σ⟧ ∗ (∀ v σ', ⌜ σ = v :: σ' ⌝ → ⟦σ'⟧ ={∅,⊤∖↑N}=∗
                                                        ghost_var γr (3/4) v)) ∗
          "Hs◯" ∷ ½s γs
      | chan_rep.SndCommit v =>
          "Hpop_wit" ∷ ghost_var γr (3/4) v ∗ "Hs◯" ∷ ½s γs
      | chan_rep.RcvCommit =>
          "Hpush_wit" ∷ token γs ∗ "Hr◯" ∷ ½r γr
      | _ => False
      end
    ).

Definition is_EliminationStack s γ N : iProp Σ :=
  ∃ st,
    "#s" ∷ s ↦□ st ∗
    "#Hbase" ∷ is_LockedStack st.(chan_spec_raw_examples.EliminationStack.base') γ.(ls_gn) ∗
    "#Hch" ∷ is_chan (t:=stringT) st.(chan_spec_raw_examples.EliminationStack.exchanger') γ.(ch_gn) ∗
    "#Hinv" ∷ inv (N.@"inv") (
        ∃ stack (exstate : chan_rep.t go_string),
          "Hls" ∷ own_LockedStack γ.(ls_gn) stack ∗
          "Hauth" ∷ ghost_var γ.(spec_gn) (1/2) stack ∗
          "exchanger" ∷ own_chan st.(chan_spec_raw_examples.EliminationStack.exchanger') exstate γ.(ch_gn) ∗
          "Hexchanger" ∷ own_exchanger_inv γ (N.@"inv") exstate
      ).

#[global] Opaque own_EliminationStack.
#[local] Transparent own_EliminationStack.

Lemma wp_NewEliminationStack N :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.NewEliminationStack #()
  {{{ s γ, RET #s; is_EliminationStack s γ N ∗ ⟦[]⟧ }}}.
Proof.
  wp_start. wp_apply wp_NewLockedStack as "%base %γbase (#Hbase & Hls)".
  wp_apply (chan.wp_make (t:=stringT)); first lia.
  iIntros "* (#? & _ & Hc)". simpl.
  wp_auto. wp_alloc s as "Hs".
  iApply wp_fupd. wp_auto.
  iMod (ghost_var_alloc []) as (γspec) "[Hauth Hes]".
  iMod (ghost_var_alloc γspec) as (γs) "[Hs● Hs◯]".
  iMod (ghost_var_alloc γs) as (γr) "[Hr● Hr◯]".
  iPersist "Hs". iApply "HΦ". iMod (inv_alloc with "[-Hes]") as "#Hinv".
  2:{ iModIntro. instantiate (1:=ltac:(econstructor)). iFrame "∗#". }
  iFrame "Hs● Hr●". simpl. iFrame. iFrame.
Qed.

Lemma alloc_push_help_token {E} N P :
  ⊢ |={E}=> ∃ γs, (token γs ={↑N}=∗ ▷ P) ∗
                 (▷ P ={↑N}=∗ token γs).
Proof.
  iMod (token_alloc) as "[%γs Htok]".
  iMod (token_alloc) as "[%γs2 Htok2]".
  iMod (inv_alloc N _ (P ∗ token γs2 ∨ token γs)%I with "[$Htok]") as "#Hescrow".
  iExists γs. iModIntro.
  iSplitR.
  - iIntros "Ht". iInv "Hescrow" as "[[HP _]| >Hbad]"; first by iFrame.
    iCombine "Ht Hbad" gives %[].
  - iIntros "HP". iInv "Hescrow" as "[[_ >Hbad] | >Htok]".
    + iCombine "Htok2 Hbad" gives %[].
    + iModIntro. iSplitR "Htok"; last by iFrame. iNext. iLeft. iFrame.
Qed.

Lemma alloc_pop_help_token {E} N P :
  ⊢ |={E}=> ∃ γr, (∀ (v : go_string), ghost_var γr (3/4) v ={↑N}=∗ ▷ P v) ∗
                 (∀ v, ▷ P v ={↑N}=∗ ghost_var γr (3/4) v).
Proof.
  iMod (ghost_var_alloc ""%go) as "[%γr Htok]".
  iMod (token_alloc) as "[%γdone Hdone]".
  iMod (inv_alloc N _ (∃ v, P v ∗ token γdone ∗ ghost_var γr (1/4) v ∨ ghost_var γr 1 v)%I with
    "[$Htok]") as "#Hescrow".
  iExists γr. iModIntro.
  iSplitR.
  - iIntros "% Ht". iInv "Hescrow" as "[% [(HP & _ & >Ht2)| >Hbad]]".
    + iCombine "Ht Ht2" gives %[_ Heq]. subst. iFrame. iSplitL; last done.
      iModIntro. iNext. iCombine "Ht Ht2" as "Ht".
      replace (3/4 + 1/4)%Qp with 1%Qp by compute_done. iFrame.
    + iCombine "Ht Hbad" gives %[Hbad _]. done.
  - iIntros "% HP". iInv "Hescrow" as "[% [(_ & >Hbad & _)| >Ht]]".
    + iCombine "Hdone Hbad" gives %[].
    + iMod (ghost_var_update with "Ht") as "Ht". iModIntro.
      iEval (replace (1)%Qp with (3/4 + 1/4)%Qp by compute_done) in "Ht".
      iDestruct "Ht" as "[Ht Ht2]". iFrame. iSplitL; last done.
      iNext. iExists v. iLeft. iFrame.
Qed.

(* FIXME *)
Transparent handoff.is_chan_handoff.

Lemma wp_EliminationStack__Push v γ s N :
  ∀ Φ,
  is_pkg_init chan_spec_raw_examples ∗ is_EliminationStack s γ N -∗
  (|={⊤∖↑N,∅}=> ∃ σ, ⟦σ⟧ ∗ (⟦(v :: σ)⟧ ={∅,⊤∖↑N}=∗ Φ #())) -∗
  WP s @ (ptrT.id chan_spec_raw_examples.EliminationStack.id) @ "Push" #v {{ Φ }}.
Proof.
  wp_start as "#His". iNamed "His".
  iRename "s" into "s1". wp_auto.
  wp_apply time.wp_After. iIntros (after_ch γafter) "#Hafter".
  wp_auto_lc 2.
  wp_apply chan.wp_select_blocking.
  simpl. iSplit.
  - (* elimination occurs *)
    iFrame "#". iExists _; iSplitR; first done.
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iNamedSuffix "Hi" "_inv". iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hmask". iNext. iFrame.
    destruct exstate; iNamedSuffix "Hexchanger_inv" "_inv"; try by iExFalso.
    + (* idle *)
      iNamedSuffix "Hexchanger_inv" "_inv";
      iIntros "exchanger_inv". iMod "Hmask" as "_".
      iRename "Hs◯_inv" into "Hs◯".
      rename γs into γs_old.
      iRename "HΦ" into "Hau_inv".
      iMod (alloc_push_help_token (N.@"escrow") (Φ #())) as (γs) "[HΦ Htok_inv]".
      iMod (ghost_var_update_2 with "Hs◯ Hs●_inv") as "[Hs●_inv Hs◯]".
      { compute_done. }
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. iFrame. iNext.
        iMod (fupd_mask_subseteq _) as "Hmask";
          last iMod "Hau_inv" as "(% & ? & Hau)"; first solve_ndisj.
        iModIntro. iFrame.
        iIntros "H". iMod ("Hau" with "[$]") as "H".
        iMod "Hmask" as "_".
        iMod (fupd_mask_subseteq _) as "Hmask";
          last iMod ("Htok_inv" with "[$]") as "Htok"; first solve_ndisj.
        iMod "Hmask". iFrame. done. }
      iModIntro.
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
      iNamedSuffix "Hi" "_inv". iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hmask". iNext. iFrame.
      destruct exstate; iNamedSuffix "Hexchanger_inv" "_inv"; try by done.
      iIntros "exchanger_inv". iMod "Hmask" as "_".
      iCombine "Hs●_inv Hs◯" gives %[_ ->]. iRename "Hs◯" into "Hs◯_inv".
      iNamed "Hexchanger_inv". iRename "Hr◯" into "Hr◯_inv".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. iFrame. }
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod ("HΦ" with "[$]") as "HΦ";
        first solve_ndisj.
      iMod "Hmask" as "_". iModIntro. wp_auto. iFrame.
    + done.
    + iIntros "exchanger_inv". iMod "Hmask" as "_". iNamedSuffix "Hexchanger_inv" "_inv".
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as "(% & Hfrag & HΦ)"; first solve_ndisj.
      iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst stack.
      iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
      { compute_done. }
      iMod ("HΦ" with "Hfrag") as "HΦ". iMod "Hmask" as "_".
      iMod "Hpop_au_inv" as "(% & Hfrag & Hpop)".
      iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst σ0.
      iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
      { compute_done. }
      iMod ("Hpop" with "[//] Hfrag") as "Hpop_inv".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. iFrame. }
      iModIntro. wp_auto. iFrame.
    + done.
    + done.
  - iSplit; last done.
    iFrame "#".
    iPoseProof "Hafter" as "[$ _]".
    iApply (handoff.handoff_rcv_au (V:=time.Time.t) with "[$Hafter] [$]").
    iIntros (t) "_ !>". wp_auto_lc 1.
    wp_apply wp_LockedStack__Push.
    { iFrame "#". }
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iNamedSuffix "Hi" "_inv".
    iFrame. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    iIntros "Hlc_inv". iMod "Hmask" as "_".
    iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as "(% & Hfrag & HΦ)";
      first solve_ndisj.
    iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst stack.
    iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
    { compute_done. }
    iMod ("HΦ" with "Hfrag") as "HΦ". iMod "Hmask" as "_".
    iCombineNamed "*_inv" as "Hi".
    iMod ("Hclose" with "[Hi]") as "_".
    { iNamed "Hi". iFrame. }
    iModIntro. wp_auto. iFrame.
Qed.

Lemma wp_EliminationStack__Pop γ s N :
  ∀ Φ,
  is_pkg_init chan_spec_raw_examples ∗ is_EliminationStack s γ N -∗
  (|={⊤∖↑N,∅}=> ∃ σ, ⟦σ⟧ ∗
                 (match σ with
                  | [] => ⟦[]⟧ ={∅,⊤∖↑N}=∗ Φ (#"", #false)%V
                  | v :: σ => ⟦σ⟧ ={∅,⊤∖↑N}=∗ Φ (#v, #true)%V
                  end)) -∗
  WP s @ (ptrT.id chan_spec_raw_examples.EliminationStack.id) @ "Pop" #() {{ Φ }}.
Proof.
  wp_start as "#His". iNamed "His".
  iRename "s" into "s1". wp_auto.
  wp_apply time.wp_After. iIntros (after_ch γafter) "#Hafter".
  wp_auto_lc 2.
  wp_apply chan.wp_select_blocking.
  simpl. iSplit.
  - (* elimination occurs *)
    iFrame "#".
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iNamedSuffix "Hi" "_inv". iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hmask". iNext. iFrame.
    destruct exstate; iNamedSuffix "Hexchanger_inv" "_inv"; try by iExFalso.
    + (* idle *)
      iNamedSuffix "Hexchanger_inv" "_inv";
      iIntros "exchanger_inv". iMod "Hmask" as "_".
      iRename "Hr◯_inv" into "Hr◯".
      rename γs into γs_old.
      iRename "HΦ" into "Hau_inv".
      iMod (alloc_pop_help_token (N.@"escrow") (λ v, Φ (#v, #true)%V)) as (γs) "[HΦ Htok_inv]".
      iMod (ghost_var_update_2 with "Hr◯ Hr●_inv") as "[Hr●_inv Hr◯]".
      { compute_done. }
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. iFrame. iNext.
        iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "Hau_inv" as "(% & ? & Hau)";
          first solve_ndisj.
        iModIntro. iFrame.
        iIntros "* -> H". iMod ("Hau" with "[$]") as "H".
        iMod "Hmask" as "_".
        iMod (fupd_mask_subseteq _) as "Hmask";
          last iMod ("Htok_inv" with "[$]") as "Htok"; first solve_ndisj.
        iMod "Hmask". iFrame. done. }
      iModIntro.
      iInv "Hinv" as "Hi" "Hclose".
      iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
      iNamedSuffix "Hi" "_inv". iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hmask". iNext. iFrame.
      destruct exstate; iNamedSuffix "Hexchanger_inv" "_inv"; try by done.
      iIntros "exchanger_inv". iMod "Hmask" as "_".
      iCombine "Hr●_inv Hr◯" gives %[_ ->]. iRename "Hr◯" into "Hr◯_inv".
      iNamed "Hexchanger_inv". iRename "Hs◯" into "Hs◯_inv".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. iFrame. }
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod ("HΦ" with "[$]") as "HΦ";
        first solve_ndisj.
      iMod "Hmask" as "_". iModIntro. wp_auto. iFrame.
    + iIntros "exchanger_inv". iMod "Hmask" as "_". iNamedSuffix "Hexchanger_inv" "_inv".
      iMod "Hpush_au_inv" as "(% & Hfrag & Hpush)".
      iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst.
      iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
      { compute_done. }
      iMod ("Hpush" with "Hfrag") as "Hpush_inv".
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as "(% & Hfrag & HΦ)"; first solve_ndisj.
      iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst.
      iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
      { compute_done. }
      iMod ("HΦ" with "Hfrag") as "HΦ". iMod "Hmask".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. iFrame. }
      iModIntro. wp_auto. iFrame.
    + done.
    + done.
    + done.
  - iSplit; last done.
    iFrame "#".
    (* FIXME: need to break is_handoff to get is_chan *)
    iPoseProof "Hafter" as "[$ _]".
    iApply (handoff.handoff_rcv_au (V:=time.Time.t) with "[$Hafter] [$]").
    iIntros (t) "_ !>". wp_auto_lc 1.
    wp_apply wp_LockedStack__Pop.
    { iFrame "#". }
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iNamedSuffix "Hi" "_inv".
    iFrame. iApply fupd_mask_intro; first solve_ndisj. iIntros "Hmask".
    destruct stack.
    * iIntros "Hlc_inv". iMod "Hmask" as "_".
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as "(% & Hfrag & HΦ)";
        first solve_ndisj.
      iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst.
      iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
      { compute_done. }
      iMod ("HΦ" with "Hfrag") as "HΦ". iMod "Hmask" as "_".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. }
      iModIntro. wp_auto. iFrame.
    * iIntros "Hlc_inv". iMod "Hmask" as "_".
      iMod (fupd_mask_subseteq _) as "Hmask"; last iMod "HΦ" as "(% & Hfrag & HΦ)";
        first solve_ndisj.
      iCombine "Hfrag Hauth_inv" gives %[_ Heq]. subst.
      iMod (ghost_var_update_2 with "Hfrag Hauth_inv") as "[Hfrag Hauth_inv]".
      { compute_done. }
      iMod ("HΦ" with "Hfrag") as "HΦ". iMod "Hmask" as "_".
      iCombineNamed "*_inv" as "Hi".
      iMod ("Hclose" with "[Hi]") as "_".
      { iNamed "Hi". iFrame. }
      iModIntro. wp_auto. iFrame.
Qed.

End elimination_stack_proof.
