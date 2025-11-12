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

(* Include [chanG Σ V] etc. here or not? *)
Class dspG Σ V := {
  chanG_tokenG :: tokenG Σ;
  chanG_protoG :: protoG Σ V;
}.

Record dsp_names := DSPNames {
  chan_lr_name : chan_names;
  chan_rl_name : chan_names;
  token_lr_name : gname;            (* Token for excluding closed state of lr channel  *)
  token_rl_name : gname;            (* Token for excluding closed state of rl channel*)
  dsp_lr_name : gname;              (* Protocol ownership for lr channel *)
  dsp_rl_name : gname;              (* Protocol ownership for rl channel *)
}.

Definition flip_dsp_names (γdsp_names : dsp_names) : dsp_names :=
  DSPNames
    γdsp_names.(chan_rl_name)
    γdsp_names.(chan_lr_name)
    γdsp_names.(token_rl_name)
    γdsp_names.(token_lr_name)
    γdsp_names.(dsp_rl_name)
    γdsp_names.(dsp_lr_name).

Section dsp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chanG Σ V} `{!IntoVal V} `{!IntoValTyped V tV}.
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
    (lr_chan rl_chan : loc)
     : iProp Σ :=
  ∃ lr_state rl_state (vsl vsr : list V),
    ⌜buffer_matches lr_state vsl⌝ ∗
    ⌜buffer_matches rl_state vsr⌝ ∗
    own_channel lr_chan lr_state (γdsp_names.(chan_lr_name)) ∗
    own_channel rl_chan rl_state (γdsp_names.(chan_rl_name)) ∗
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
    γdsp_names lr_chan rl_chan :
   dsp_session_inv γdsp_names lr_chan rl_chan ⊣⊢
   dsp_session_inv (flip_dsp_names γdsp_names) rl_chan lr_chan .
Proof.
  iSplit.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. simpl. iFrame. by iApply iProto_ctx_sym.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. by iApply iProto_ctx_sym.
Qed.

(** DSP session context - public interface with persistent channel handles *)
Definition dsp_session
             (γdsp_names : dsp_names)
    (lr_chan rl_chan : loc)
     : iProp Σ :=
  is_channel lr_chan γdsp_names.(chan_lr_name) ∗
  is_channel rl_chan γdsp_names.(chan_rl_name) ∗
  inv N (dsp_session_inv γdsp_names lr_chan rl_chan).

(** ** DSP Endpoints *)

(** Left endpoint - can send V_LR via lr_chan, receive V_RL via rl_chan *)
Definition dsp_endpoint
  (γdsp_names : dsp_names)
    (v : val)
    (p : option $ iProto Σ V) : iProp Σ :=
  ∃ (lr_chan rl_chan : loc),
    ⌜v = #(lr_chan,rl_chan)⌝ ∗
    dsp_session γdsp_names lr_chan rl_chan ∗
    match p with
    | None => token γdsp_names.(token_lr_name)
    | Some p => iProto_own γdsp_names.(dsp_lr_name) p
    end.

Notation "c ↣{ γ } p" := (dsp_endpoint γ c (Some p)) (at level 20, format "c  ↣{  γ  }  p").
Notation "↯{ γ } c" := (dsp_endpoint γ c None) (at level 20, format "↯{  γ  }  c").

Global Instance dsp_endpoint_ne γ c : NonExpansive (dsp_endpoint γ c).
Proof. solve_proper. Qed.
Global Instance dsp_endpoint_proper γ c : Proper ((≡) ==> (≡)) (dsp_endpoint γ c).
Proof. apply (ne_proper _). Qed.

Lemma iProto_pointsto_le γ c p1 p2 : c ↣{γ}  p1 ⊢ ▷ (p1 ⊑ p2) -∗ c ↣{γ}  p2.
Proof.
  iDestruct 1 as (lr_chan rl_chan ->) "[Hc Hp]".
  iIntros "Hle'". iExists _,_. iSplit; [done|]. iFrame "Hc".
  by iApply (iProto_own_le with "Hp").
Qed.

(** ** Initialization *)

(** Initialize a new DSP session from basic channels *)
Lemma dsp_session_init
    E (lr_chan rl_chan : loc) (lr_state rl_state : chan_rep.t V)
    (γlr_names γrl_names : chan_names)
    (p : iProto Σ V) :
  (lr_state = chan_rep.Idle ∨ lr_state = chan_rep.Buffered []) →
  (rl_state = chan_rep.Idle ∨ rl_state = chan_rep.Buffered []) →
  is_channel lr_chan γlr_names -∗
  is_channel rl_chan γrl_names -∗
  own_channel lr_chan lr_state γlr_names -∗
  own_channel rl_chan rl_state γrl_names ={E}=∗
  ∃ γdsp1 γdsp2,
  #(lr_chan,rl_chan) ↣{γdsp1}  p ∗ #(rl_chan,lr_chan) ↣{γdsp2} iProto_dual p.
Proof.
  iIntros (Hlr Hrl) "#Hcl_is #Hcr_is Hcl_own Hcr_own".
  iMod (iProto_init) as (γl γr) "(Hctx & Hpl & Hpr)".
  iMod (token_alloc) as (γtl) "Htl".
  iMod (token_alloc) as (γtr) "Htr".
  set γdsp_names := (DSPNames γlr_names γrl_names γtl γtr γl γr).
  iMod (inv_alloc N _ (dsp_session_inv γdsp_names lr_chan rl_chan) with "[Hcl_own Hcr_own Htl Htr Hctx]")
    as "#Hinv".
  { iExists lr_state,rl_state,[],[]. iIntros "!>". iFrame.
    by destruct Hlr,Hrl; simplify_eq; do 2 (iSplit; [done|]); iFrame. }
  iModIntro.
  iExists γdsp_names, (flip_dsp_names γdsp_names).
  iSplitL "Hpl".
  - iExists _,_. iSplit; [done|].
    iFrame "Hpl Hinv". iFrame "∗#".
  - iExists _,_. iSplit; [done|].
    rewrite dsp_session_inv_sym. iFrame "Hinv".
    iFrame "∗#".
Qed.

(** ** Endpoint Operations *)

 (* is_mpmc γ ch n_prod n_cons P R -∗ *)
 (*  £1 ∗ £1 -∗ *)
 (*  mpmc_producer γ sent ∗ P v -∗ *)
 (*  ▷(mpmc_producer γ (sent ⊎ {[+ v +]}) -∗ Φ) -∗ *)
 (*  send_au_slow ch v γ.(mpmc_chan_name) Φ. *)

(** Endpoint sends value *)
Lemma dsp_send_au γ (lr_chan rl_chan : loc) (v : V) (p : iProto Σ V) Φ :
  £1 -∗
  #(lr_chan,rl_chan) ↣{γ} (<!> MSG v; p)%proto -∗
  ▷(#(lr_chan,rl_chan) ↣{γ} p -∗ Φ) -∗
  send_au_slow lr_chan v γ.(chan_lr_name) Φ.
Proof.
  iIntros "H£ Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
  iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
  iApply fupd_mask_intro; [solve_ndisj|].
  iIntros "Hclose'".
  iModIntro.
  iExists _. iFrame.
  destruct lr_state.
  - iIntros "Hownl".
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

Lemma wp_dsp_send (lr_chan rl_chan : loc) γ (v : V) (p : iProto Σ V) :
  {{{ #(lr_chan,rl_chan) ↣{γ} <!> MSG v; p }}}
    chan.send #tV #lr_chan #v
  {{{ RET #(); #(lr_chan,rl_chan) ↣{γ} p }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_send lr_chan v _ with "[$Hcl]").
  iIntros "(Hlc1 & Hlc2 & _)".
  iApply (dsp_send_au with "[$] [$Hp]").
  { iFrame "#". done. }
  done.
Qed.

Lemma dsp_send_tele_au
  {TT : tele} (tt:TT)
  γ (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) Φ :
  £1 -∗
  #(lr_chan,rl_chan) ↣{γ} ((<!.. x> MSG (v x) {{ P x }}; p x))%proto -∗
  P tt -∗
  (#(lr_chan,rl_chan) ↣{γ} p tt -∗ Φ) -∗
  send_au_slow lr_chan (v tt) γ.(chan_lr_name) Φ.
Proof.
  iIntros "H£ Hc HP HΦ".
  iDestruct (iProto_pointsto_le _ _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
    as "Hc".
  { iIntros "!>".
    iApply iProto_le_trans;
      [iApply iProto_le_texist_intro_l|].
    by iFrame "HP". }  
  iApply (dsp_send_au with "H£ Hc HΦ").
Qed.

Lemma wp_dsp_send_tele
  {TT : tele} (tt:TT)
  (lr_chan rl_chan : loc) γ (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  {{{ #(lr_chan,rl_chan) ↣{γ} (<!.. x> MSG (v x) {{ P x }}; p x) ∗ P tt }}}
    chan.send #tV #lr_chan #(v tt)
  {{{ RET #(); #(lr_chan,rl_chan) ↣{γ} p tt }}}.
Proof.
  iIntros (Φ) "[Hc HP] HΦ".
  iDestruct (iProto_pointsto_le _ _ _ (<!> MSG v tt; p tt)%proto with "Hc [HP]")
    as "Hc".
  { iIntros "!>".
    iApply iProto_le_trans;
      [iApply iProto_le_texist_intro_l|].
    by iFrame "HP". }
  by iApply (wp_dsp_send with "Hc").
Qed.

(** Endpoint receives value *)
Lemma dsp_recv_au {TT:tele}
    γ (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) Φ :
  (£1 ∗ £1) -∗
  #(lr_chan,rl_chan) ↣{γ} (<?.. x> MSG (v x) {{ ▷ P x }}; p x)%proto -∗
   ▷(∀ x, #(lr_chan,rl_chan) ↣{γ} p x ∗ P x -∗ Φ (v x) true) -∗
  rcv_au_slow rl_chan γ.(chan_rl_name) Φ.
Proof.
  iIntros "H£s Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
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
    iCombine "HP Hp" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[HP Hp]".
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
      iCombine "HP Hp" as "H".
      iMod (lc_fupd_elim_later with "H£ H") as "[HP Hp]".
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
    iCombine "HP Hp" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[HP Hp]".
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
    iCombine "HP Hp" as "H".
    iMod (lc_fupd_elim_later with "H£ H") as "[HP Hp]".
    iModIntro. iRewrite "Hp". by iFrame "#∗".
Qed.

Lemma wp_dsp_recv {TT:tele}
    γ (lr_chan rl_chan : loc) (v : TT → V) (P : TT → iProp Σ) (p : TT → iProto Σ V) :
  {{{ #(lr_chan,rl_chan) ↣{γ} <?.. x> MSG (v x) {{ ▷ P x }}; p x }}}
    chan.receive #tV #rl_chan
  {{{ x, RET (#(v x), #true); #(lr_chan,rl_chan) ↣{γ} p x ∗ P x }}}.
Proof.
  iIntros (Φ) "Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
  iApply (chan.wp_receive _ _ with "[$Hcr]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iApply (dsp_recv_au with "[$] [$Hp]").
  { iFrame "#". eauto. }
  done.
Qed.

(** Endpoint closes (stops sending val) *)
Lemma wp_dsp_close γ (lr_chan rl_chan : loc) (p : iProto Σ V) Φ :
  #(lr_chan,rl_chan) ↣{γ} END -∗
  (↯{γ} #(lr_chan,rl_chan) -∗ Φ) -∗
  close_au lr_chan γ.(chan_lr_name) Φ.
Proof.
  iIntros "Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
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
Lemma wp_dsp_recv_end γ (lr_chan rl_chan : loc) Φ :
  (£1 ∗ £1) -∗
  #(lr_chan,rl_chan) ↣{γ} END-∗
  (#(lr_chan,rl_chan) ↣{γ} END -∗ Φ (default_val V) false) -∗
  rcv_au_slow rl_chan γ.(chan_rl_name) Φ.
Proof.
  iIntros "H£s Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
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
Lemma wp_dsp_recv_closed γ (lr_chan rl_chan : loc) Φ :
  (£1 ∗ £1) -∗
  ↯{γ} #(lr_chan,rl_chan) -∗
  (↯{γ} #(lr_chan,rl_chan) -∗ Φ (default_val V) false) -∗
  rcv_au_slow rl_chan γ.(chan_rl_name) Φ.
Proof.
  iIntros "H£s Hc HΦ".
  iDestruct "Hc" as (?? Heq) "(#(Hcl&Hcr&HI)&Hp)".
  rewrite to_val_unseal in Heq. simplify_eq.
  rename lr_chan0 into lr_chan.
  rename rl_chan0 into rl_chan.
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

Lemma wp_dsp_recv_false (b : bool) γ (lr_chan rl_chan : loc) Φ :
  (£1 ∗ £1) -∗
  (if b then #(lr_chan,rl_chan) ↣{γ} END else ↯{γ} #(lr_chan,rl_chan)) -∗
  ((if b then #(lr_chan,rl_chan) ↣{γ} END else ↯{γ} #(lr_chan,rl_chan)) -∗ Φ (default_val V) false) -∗
  rcv_au_slow rl_chan γ.(chan_rl_name) Φ.
Proof. destruct b; [apply wp_dsp_recv_end|apply wp_dsp_recv_closed]. Qed.

End dsp.

Notation "c ↣{ γ } p" := (dsp_endpoint γ c (Some p)) (at level 20, format "c  ↣{  γ  }  p").
Notation "↯{ γ } c" := (dsp_endpoint γ c None) (at level 20, format "↯{  γ  }  c").
