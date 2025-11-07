(* TODO: there should be a directory for this Go package. *)

From New.proof Require Export proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import chan_au_base.
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
  wp_apply wp_slice_literal. iIntros "% Htmp". wp_auto.
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
    #[local] es_chan_inG :: chanGhostStateG Σ go_string;
    #[local] es_token_pointer_inG :: ghost_varG Σ gname;
    #[local] es_send_token_inG :: tokenG Σ;
    #[local] es_reply_token_inG :: ghost_varG Σ val;
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
          "Hsend_au" ∷ (|={⊤∖↑N,∅}=> ∃ σ, ⟦σ⟧ ∗ (⟦v :: σ⟧ ={∅,⊤∖↑N}=∗ token γs)) ∗
          "Hr◯" ∷ ½r γr
      | chan_rep.RcvPending =>
          "Hrecv_au" ∷ (|={⊤∖↑N,∅}=> ∃ σ, ⟦σ⟧ ∗ (∀ v σ', ⌜ σ = v :: σ' ⌝ → ⟦σ⟧ ={∅,⊤∖↑N}=∗
                                                        ghost_var γr (3/4) (#v, #true)%V)) ∗
          "Hs◯" ∷ ½s γs
      | chan_rep.SndCommit v =>
          "Hrecv_wit" ∷ ghost_var γr (3/4) (#v, #true)%V ∗ "Hs◯" ∷ ½s γs
      | chan_rep.RcvCommit =>
          "Hrecv_wit" ∷ token γs ∗ "Hr◯" ∷ ½r γr
      | _ => False
      end
    ).

Definition is_EliminationStack s γ N : iProp Σ :=
  ∃ st,
    "#s" ∷ s ↦□ st ∗
    "#Hbase" ∷ is_LockedStack st.(chan_spec_raw_examples.EliminationStack.base') γ.(ls_gn) ∗
    "#Hch" ∷ is_channel st.(chan_spec_raw_examples.EliminationStack.exchanger') 0 γ.(ch_gn) ∗
    "#Hinv" ∷ inv N (
        ∃ stack (exstate : chan_rep.t go_string),
          "Hls" ∷ own_LockedStack γ.(ls_gn) stack ∗
          "Hauth" ∷ ghost_var γ.(spec_gn) (1/2) stack ∗
          "exchanger" ∷ own_channel st.(chan_spec_raw_examples.EliminationStack.exchanger') 0 exstate γ.(ch_gn) ∗
          "exch_inv" ∷ own_exchanger_inv γ N exstate
      ).

#[global] Opaque own_EliminationStack.
#[local] Transparent own_EliminationStack.

End elimination_stack_proof.
