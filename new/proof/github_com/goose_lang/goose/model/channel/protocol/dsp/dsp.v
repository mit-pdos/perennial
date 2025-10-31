Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export chan_au_base.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export dsp_ghost_theory.
From iris.base_logic.lib Require Export token.

(** * Dependent Separation Protocols (DSP) over Go Channels

    This file implements dependent separation protocols using bidirectional Go channels.

    Key concepts:
    - Protocol endpoints communicate via two Go channels
    - LR channel: left endpoint sends values to right endpoint
    - RL channel: right endpoint sends values to left endpoint
    - Protocol state is tracked using Actris iProto with sum types
    - Channel closure is protocol-aware - only allowed when protocol permits
*)

(* Include [chanGhostStateG Σ V] etc. here or not? *)
Class dspG Σ V := {
  chanG_tokenG :: tokenG Σ;
  chanG_protoG :: protoG Σ V;
}.

Record dsp_names := DSPNames {
  token_lr_name : gname;            (* Token for excluding closed state of lr channel  *)
  token_rl_name : gname;            (* Token for excluding closed state of rl channel*)
  dsp_lr_name : gname;              (* Protocol ownership for lr channel *)
  dsp_rl_name : gname;              (* Protocol ownership for rl channel *)
}.

Definition flip_dsp_names (γdsp_names : dsp_names) : dsp_names :=
  DSPNames 
    γdsp_names.(token_rl_name)
    γdsp_names.(token_lr_name)
    γdsp_names.(dsp_rl_name)
    γdsp_names.(dsp_lr_name).

Section dsp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanGhostStateG Σ V} `{!IntoVal V} `{!IntoValTyped V tV}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!dspG Σ V}.

Let N := nroot .@ "dsp_chan".

(** ** Buffer Matching Predicates *)

(** Defines when Go channel state matches expected message queue *)
Definition buffer_matches {V}
    (state : chan_rep.t V) (vs : list V) : Prop :=
  match state with
  | chan_rep.Buffered queue => vs = queue
  | chan_rep.SndPending v | chan_rep.SndCommit v => vs = [v]
  | chan_rep.Closed draining => vs = draining
  | _ => vs = []
  end.

(** ** DSP Session Context *)

(** DSP session invariant - owns both channels and maintains protocol state *)
Definition dsp_session_inv
    (γdsp_names : dsp_names)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) : iProp Σ :=
  ∃ lr_state rl_state (vsl vsr : list V),
    ⌜buffer_matches lr_state vsl⌝ ∗
    ⌜buffer_matches rl_state vsr⌝ ∗
    own_channel lr_chan lrcap lr_state γlr_names ∗
    own_channel rl_chan rlcap rl_state γrl_names ∗
    match lr_state with
    | chan_rep.Closed _ => iProto_own (γdsp_names.(dsp_lr_name)) END
    | _ => token (γdsp_names.(token_lr_name))
    end ∗
    match rl_state with
    | chan_rep.Closed _ => iProto_own (γdsp_names.(dsp_rl_name)) END
    | _ => token (γdsp_names.(token_rl_name))
    end ∗
    iProto_ctx (γdsp_names.(dsp_lr_name)) (γdsp_names.(dsp_rl_name)) vsl vsr.

Lemma dsp_session_inv_sym
    γdsp_names lr_chan rl_chan γlr_names γrl_names lrcap rlcap :
   dsp_session_inv γdsp_names lr_chan rl_chan γlr_names γrl_names lrcap rlcap ⊣⊢
   dsp_session_inv (flip_dsp_names γdsp_names) rl_chan lr_chan γrl_names γlr_names rlcap lrcap.
Proof.
  iSplit.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. by iApply iProto_ctx_sym.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. by iApply iProto_ctx_sym.
Qed.

(** DSP session context - public interface with persistent channel handles *)
Definition dsp_session
             (γdsp_names : dsp_names)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) : iProp Σ :=
  is_channel lr_chan lrcap γlr_names ∗
  is_channel rl_chan rlcap γrl_names ∗
  inv N (dsp_session_inv γdsp_names lr_chan rl_chan γlr_names γrl_names lrcap rlcap).

(** ** DSP Endpoints *)

(** Left endpoint - can send V_LR via lr_chan, receive V_RL via rl_chan *)
Definition dsp_endpoint
    (v : val)
    (p : option $ iProto Σ V) : iProp Σ :=
  ∃ (γdsp_names : dsp_names) (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z),
    ⌜v = #(lr_chan,rl_chan)⌝ ∗
    dsp_session γdsp_names lr_chan rl_chan γlr_names γrl_names lrcap rlcap ∗
    match p with
    | None => token γdsp_names.(token_lr_name)
    | Some p => iProto_own γdsp_names.(dsp_lr_name) p
    end.

Notation "c ↣ p" := (dsp_endpoint c (Some p)) (at level 20, format "c  ↣  p").
Notation "↯ c" := (dsp_endpoint c None) (at level 20, format "↯  c").


Global Instance dsp_endpoint_ne c : NonExpansive (dsp_endpoint c).
Proof. solve_proper. Qed.
Global Instance dsp_endpoint_proper c : Proper ((≡) ==> (≡)) (dsp_endpoint c).
Proof. apply (ne_proper _). Qed.

Lemma iProto_pointsto_le c p1 p2 : c ↣ p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣ p2.
Proof.
  iDestruct 1 as (γdsp_names lr_chan rl_chan γlr_names γrl_names lr_cap rl_cap ->) "[Hc Hp]".
  iIntros "Hle'". iExists _,_,_,_,_,_,_. iSplit; [done|]. iFrame "Hc".
  by iApply (iProto_own_le with "Hp").
Qed.

(** ** Initialization *)

(** Initialize a new DSP session from basic channels *)
Lemma dsp_session_init
    E (lr_chan rl_chan : loc) (lr_state rl_state : chan_rep.t V)
    (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (p : iProto Σ V) :
  (lr_state = chan_rep.Idle ∨ lr_state = chan_rep.Buffered []) →
  (rl_state = chan_rep.Idle ∨ rl_state = chan_rep.Buffered []) →
  is_channel lr_chan lrcap γlr_names -∗
  is_channel rl_chan rlcap γrl_names -∗
  own_channel lr_chan lrcap lr_state γlr_names -∗
  own_channel rl_chan rlcap rl_state γrl_names ={E}=∗
  #(lr_chan,rl_chan) ↣ p ∗ #(rl_chan,lr_chan) ↣ iProto_dual p.
Proof.
  iIntros (Hlr Hrl) "#Hcl_is #Hcr_is Hcl_own Hcr_own".
  iMod (iProto_init) as (γl γr) "(Hctx & Hpl & Hpr)".
  iMod (token_alloc) as (γtl) "Htl".
  iMod (token_alloc) as (γtr) "Htr".
  set γdsp_names := (DSPNames γtl γtr γl γr).
  iMod (inv_alloc N _ (dsp_session_inv γdsp_names lr_chan rl_chan γlr_names γrl_names lrcap rlcap) with "[Hcl_own Hcr_own Htl Htr Hctx]")
    as "#Hinv".
  { iExists lr_state,rl_state,[],[]. iIntros "!>". iFrame.
    by destruct Hlr,Hrl; simplify_eq; do 2 (iSplit; [done|]); iFrame. }
  iModIntro.
  iSplitL "Hpl".
  - iExists γdsp_names,_,_,_,_,_,_. iSplit; [done|].    
    iFrame "Hpl Hinv". iFrame "∗#".
  - iExists (flip_dsp_names γdsp_names),_,_,_,_,_,_. iSplit; [done|].
    rewrite dsp_session_inv_sym. iFrame "Hinv".
    iFrame "∗#".
Qed.

(** ** Endpoint Operations *)

(** Endpoint sends value *)
Lemma dsp_send (lr_chan rl_chan : loc) (v : V) (p : iProto Σ V) :
  is_pkg_init channel -∗
  {{{ #(lr_chan,rl_chan) ↣ <!> MSG v; p }}}
    chan.send #tV #lr_chan #v
  {{{ RET #(); #(lr_chan,rl_chan) ↣ p }}}.
Proof.
  iIntros "#Hinit !>" (Φ) "Hc HΦ".
  iDestruct "Hc" as (??????? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_send lr_chan lrcap v γlr_names with "[$Hcl]").
  iIntros "H£".
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
  iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
  iApply fupd_mask_intro; [solve_ndisj|]. 
  iIntros "Hclose'".
  iModIntro.
  iExists _. iFrame.
  destruct lr_state.
  - destruct (length buff <? lrcap)%Z; [|done].
    iIntros "Hownl".
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx Hp []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hp Hown]". iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hp]").
    { iIntros "!>". iExists _,_,_,_. iFrame. inversion H. iFrame. done. }
    iApply "HΦ". by iFrame "#∗".
  - iIntros "Hownl".
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx Hp []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hctx Hown]". iMod "Hclose'" as "_". 
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]").
    { iIntros "!>". iExists _,_,_,_. iFrame. inversion H. iFrame. done. }
    iModIntro.
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hclose'".
    iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
    iFrame.
    iIntros "!>".
    destruct lr_state; try done.
    + iIntros "Hownl". iMod "Hclose'".
      iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]").
      { iIntros "!>". iExists _,_,_,_. iFrame. iFrame. done. }
      iApply "HΦ". iFrame "#∗". done.
    + iDestruct (iProto_own_excl with "Hown Hclosel") as "[]".
  - done.
  - iIntros "Hownl".
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx Hp []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hp Hown]". iMod "Hclose'".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hp]").
    { iIntros "!>". iExists _,_,_,_. iFrame. inversion H. iFrame. done. }
    iApply "HΦ". by iFrame "#∗".
  - done.
  - done.
  - iDestruct (iProto_own_excl with "Hp Hclosel") as "[]".
Qed.

(** Endpoint receives value *)
Lemma dsp_recv {TT:tele}
    (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  is_pkg_init channel -∗
  {{{ #(lr_chan,rl_chan) ↣ <?.. x> MSG (v x) {{ P x }}; p x }}}
    chan.receive #tV #rl_chan
  {{{ x, RET (#(v x), #true); #(lr_chan,rl_chan) ↣ p x ∗ P x }}}.
Proof.
  iIntros "#Hinit !>" (Φ) "Hc HΦ".
  iDestruct "Hc" as (??????? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_receive rl_chan rlcap γrl_names with "[$Hcr]").
  iIntros "H£s".
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
  iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hclose'".
  iModIntro.
  iExists _. iFrame.
  destruct rl_state.
  - destruct buff; [done|].
    destruct vsr; [done|].
    iIntros "Hownr".
    iDestruct (iProto_recv with "Hctx Hp") as "Hp".
    iMod "Hp" as (xs) "(Hctx & Hown & Hm)". iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iDestruct "H£s" as "[H£ H£s]".
    iCombine "Hown Hm" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[Hown Hm]".
    rewrite iMsg_base_eq.
    iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
    simpl in *. simplify_eq.
    iApply "HΦ".
    iDestruct "H£s" as "[H£ H£s]".
    rewrite later_equivI_1.
    iMod (lc_fupd_elim_later with "H£ Hp") as "Hp".
    iModIntro. iRewrite "Hp". by iFrame "#∗".
  - iIntros "Hownr".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame. iFrame. done. }
    iModIntro.
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hclose'". iModIntro.
    iExists _. iFrame.
    destruct rl_state; try done.
    + iIntros "Hownr".
      simpl in *. simplify_eq.
      iDestruct (iProto_recv with "Hctx Hp") as "Hp".
      iMod "Hp" as (xs) "(Hctx & Hown & Hm)". iMod "Hclose'" as "_".
      iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
      { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
        iPureIntro. simpl in *. by simplify_eq. }
      iCombine "Hown Hm" as "H".
      iDestruct "H£s" as "[H£ H£s]".
      iMod (lc_fupd_elim_later with "H£ H") as "[Hown Hm]".
      rewrite iMsg_base_eq.
      iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
      simpl in *. simplify_eq.
      iApply "HΦ".
      iDestruct "H£s" as "[H£ H£s]".
      rewrite later_equivI_1.
      iMod (lc_fupd_elim_later with "H£ Hp") as "Hp".
      iModIntro. iRewrite "Hp". by iFrame "#∗".
    + simpl in *. simplify_eq.
      destruct draining; [|done].
      iDestruct (iProto_recv_end_inv_l with "Hctx Hp Hcloser") as "H".
      iDestruct "H£s" as "[H£ H£s]".
      iMod (lc_fupd_elim_later with "H£ H") as "[]".
  - iIntros "Hownr".
    simpl in *. simplify_eq.
    iDestruct (iProto_recv with "Hctx Hp") as "Hp".
    iMod "Hp" as (xs) "(Hctx & Hown & Hm)". iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iDestruct "H£s" as "[H£ H£s]".
    iCombine "Hown Hm" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[Hown Hm]".
    rewrite iMsg_base_eq.
    iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
    simpl in *. simplify_eq.
    iApply "HΦ".
    iDestruct "H£s" as "[H£ H£s]".
    rewrite later_equivI_1.
    iMod (lc_fupd_elim_later with "H£ Hp") as "Hp".
    iModIntro. iRewrite "Hp". by iFrame "#∗".
  - done.
  - done.
  - done.
  - destruct draining.
    { simpl in *. simplify_eq.
      iDestruct (iProto_recv_end_inv_l with "Hctx Hp Hcloser") as "H".
      iDestruct "H£s" as "[H£ H£s]".
      iMod (lc_fupd_elim_later with "H£ H") as "[]". }
    simpl in *. simplify_eq.
    iIntros "Hownr".
    iDestruct (iProto_recv with "Hctx Hp") as "Hp".
    iMod "Hp" as (xs) "(Hctx & Hown & Hm)". iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iDestruct "H£s" as "[H£ H£s]".
    iCombine "Hown Hm" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[Hown Hm]".
    rewrite iMsg_base_eq.
    iDestruct (iMsg_texist_exist with "Hm") as (x <-) "[Hp HP]".
    simpl in *. simplify_eq.
    iApply "HΦ".
    iDestruct "H£s" as "[H£ H£s]".
    rewrite later_equivI_1.
    iMod (lc_fupd_elim_later with "H£ Hp") as "Hp".
    iModIntro. iRewrite "Hp". by iFrame "#∗".
Qed.

(** Endpoint closes (stops sending val) *)
Lemma dsp_close (lr_chan rl_chan : loc) (p : iProto Σ V) :
  is_pkg_init channel -∗
  {{{ #(lr_chan,rl_chan) ↣ END }}}
    chan.close #tV #lr_chan
  {{{ RET #(); ↯ #(lr_chan,rl_chan) }}}.
Proof.
  iIntros "#Hinit !>" (Φ) "Hc HΦ".
  iDestruct "Hc" as (??????? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_close lr_chan lrcap γlr_names with "[$Hcl]").
  iIntros "H£".
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
  iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hclose'".
  iModIntro.
  iExists _. iFrame.
  destruct lr_state; try done.
  - iIntros "Hownl".
    iMod "Hclose'".
    iMod ("Hclose" with "[Hownl Hownr Hcloser Hctx Hp]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iFrame "Hp". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iApply "HΦ". by iFrame "#∗".
  - iIntros "Hownl".
    iMod "Hclose'".
    iMod ("Hclose" with "[Hownl Hownr Hcloser Hctx Hp]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iFrame "Hp". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iApply "HΦ". by iFrame "#∗".
  - iDestruct (iProto_own_excl with "Hp Hclosel") as "[]".   
Qed.

(** Endpoint receives on a closed or ended channel *)
Lemma dsp_recv_end (lr_chan rl_chan : loc) :
  is_pkg_init channel -∗
  {{{ #(lr_chan,rl_chan) ↣ END }}}
    chan.receive #tV #rl_chan
  {{{ RET (#(default_val V), #false); #(lr_chan,rl_chan) ↣ END }}}.
Proof.
  iIntros "#Hinit !>" (Φ) "Hc HΦ".
  iDestruct "Hc" as (??????? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_receive rl_chan rlcap γrl_names with "[$Hcr]").
  iIntros "H£s".
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
  iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hclose'".
  iModIntro.
  iExists _. iFrame.
  destruct rl_state; try done.
  - destruct buff; [done|].
    destruct vsr; [done|].
    iIntros "Hownr".
    iDestruct (iProto_end_inv_l with "Hctx Hp") as "H".
    iDestruct "H£s" as "[H£ H£s]".
    iMod (lc_fupd_elim_later with "H£ H") as %?.
    by simplify_eq.
  - iIntros "Hownr".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iModIntro.
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
    iDestruct "H£s" as "[H£ H£s]".
    iMod (lc_fupd_elim_later with "H£ Hctx") as "Hctx".
    iApply fupd_mask_intro; [solve_ndisj|].
    iIntros "Hclose'".
    iFrame.
    destruct rl_state; try done.
    + iIntros "!> Hownr".
      simpl in *. simplify_eq.
      iDestruct (iProto_end_inv_l with "Hctx Hp") as "H".
      iDestruct "H£s" as "[H£ H£s]".
      iMod (lc_fupd_elim_later with "H£ H") as %?.
      by simplify_eq.
    + destruct draining; last first.
      { simpl in *. simplify_eq.
        iDestruct (iProto_end_inv_l with "Hctx Hp") as "H".
        iDestruct "H£s" as "[H£ H£s]".
        iIntros "!>". eauto. }
      iIntros "!> Hownr".
      iMod "Hclose'".
      iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
      { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
        iPureIntro. simpl in *. by simplify_eq. }
      iApply "HΦ". by iFrame "#∗".      
  - iIntros "Hownr".
    simpl in *.
    simplify_eq.
    iDestruct (iProto_end_inv_l with "Hctx Hp") as "H".
    iDestruct "H£s" as "[H£ H£s]".
    iMod (lc_fupd_elim_later with "H£ H") as %?.
    by simplify_eq.
  - destruct draining; last first.
    { simpl in *.
      simplify_eq.
      iDestruct (iProto_end_inv_l with "Hctx Hp") as "H".
      iDestruct "H£s" as "[H£ H£s]".
      iMod (lc_fupd_elim_later with "H£ H") as %?.
      by simplify_eq. }
    simpl in *. simplify_eq.
    iIntros "Hownr".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|].
      iPureIntro. simpl in *. by simplify_eq. }
    iApply "HΦ". by iFrame "#∗".
Qed.

(** Endpoint receives on a closed or ended channel *)
Lemma dsp_recv_closed (lr_chan rl_chan : loc) :
  is_pkg_init channel -∗
  {{{  ↯ #(lr_chan,rl_chan) }}}
    chan.receive #tV #rl_chan
  {{{ RET (#(default_val V), #false); ↯ #(lr_chan,rl_chan) }}}.
Proof.
  iIntros "#Hinit !>" (Φ) "Hc HΦ".
  iDestruct "Hc" as (??????? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_receive rl_chan rlcap γrl_names with "[$Hcr]").
  iIntros "H£s".
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
  iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
  iCombine "Hctx Hclosel" as "H".
  iDestruct "H£s" as "[H£ H£s]".
  iMod (lc_fupd_elim_later with "H£ H") as "[Hctx Hclosel]".
  destruct lr_state; try by iDestruct (token_exclusive with "Hp Hclosel") as "[]".  
  iDestruct (iProto_end_inv_l with "Hctx Hclosel") as "#>%".
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hclose'".
  iModIntro.
  iExists _. iFrame.
  destruct rl_state; try done.
  - simpl in *. simplify_eq. iFrame. done.
  - simpl in *. simplify_eq.
    iIntros "Hownr".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|]. by iFrame. }
    iModIntro.
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
    iDestruct "H£s" as "[H£ H£s]".
    iCombine "Hctx Hclosel" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[Hctx Hclosel]".
    iApply fupd_mask_intro; [solve_ndisj|].
    iIntros "Hclose'".
    iFrame.
    destruct lr_state; try by iDestruct (token_exclusive with "Hp Hclosel") as "[]".  
    iDestruct (iProto_end_inv_l with "Hctx Hclosel") as "#>->".
    destruct rl_state; try done.
    simpl in *. simplify_eq.
    iIntros "!> Hownr".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|]. by iFrame. }
    iApply "HΦ". by iFrame "#∗".
  - simpl in *. by simplify_eq.
  - simpl in *. simplify_eq.
    iIntros "Hownr".
    iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]") as "_".
    { iIntros "!>". iExists _,_,_,_. iFrame "Hownr ∗". iSplit; [done|]. by iFrame. }
    iApply "HΦ". by iFrame "#∗".
Qed.

Lemma dsp_recv_false (b : bool) (lr_chan rl_chan : loc) :
  is_pkg_init channel -∗
  {{{ (if b then #(lr_chan,rl_chan) ↣ END else  ↯ #(lr_chan,rl_chan)) }}}
    chan.receive #tV #rl_chan
  {{{ RET (#(default_val V), #false); (if b then #(lr_chan,rl_chan) ↣ END else  ↯ #(lr_chan,rl_chan)) }}}.
Proof. destruct b; [apply dsp_recv_end|apply dsp_recv_closed]. Qed.

End dsp.

Notation "c ↣ p" := (dsp_endpoint c (Some p)) (at level 20, format "c  ↣  p").
Notation "↯ c" := (dsp_endpoint c None) (at level 20, format "↯  c").
