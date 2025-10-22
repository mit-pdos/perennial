Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export chan_au_send chan_au_recv chan_au_base chan_init.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export dsp_ghost_theory.

(** * Dependent Separation Protocols (DSP) over Go Channels

    This file implements dependent separation protocols using bidirectional Go channels.

    Key concepts:
    - Protocol endpoints communicate via two Go channels
    - LR channel: left endpoint sends values to right endpoint
    - RL channel: right endpoint sends values to left endpoint
    - Protocol state is tracked using Actris iProto with sum types
    - Channel closure is protocol-aware - only allowed when protocol permits
*)

(** ** Sum Type for Bidirectional Communication *)

#[export] Instance eqdec_sum `{EqDecision A} `{EqDecision B}
  : EqDecision (A + B) := _.
#[export] Instance countable_sum `{Countable A} `{Countable B}
  : Countable (A + B) := _.

Section dsp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!ghost_varG Σ ()}.
Context `{!chanGhostStateG Σ val}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!protoG Σ val}.

#[export] Instance into_val_val : IntoVal val := { to_val_def := id }.
Instance into_val_typed_val : IntoValTyped val atomic.Value.
Proof. Admitted.

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
    (γl γr : gname)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) : iProp Σ :=
  ∃ lr_state rl_state vsl vsr,
    ⌜buffer_matches lr_state vsl⌝ ∗
    ⌜buffer_matches rl_state vsr⌝ ∗
    own_channel lr_chan lrcap lr_state γlr_names ∗
    own_channel rl_chan rlcap rl_state γrl_names ∗
    match lr_state with
    | chan_rep.Closed _ => iProto_own γl END
    | _ => True
    end ∗
    match rl_state with
    | chan_rep.Closed _ => iProto_own γr END
    | _ => True
    end ∗
    iProto_ctx γl γr vsl vsr.

Lemma dsp_session_inv_sym
    γl γr lr_chan rl_chan γlr_names γrl_names lrcap rlcap :
   dsp_session_inv γl γr lr_chan rl_chan γlr_names γrl_names lrcap rlcap ⊣⊢
   dsp_session_inv γr γl rl_chan lr_chan γrl_names γlr_names rlcap lrcap.
Proof.
  iSplit.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. by iApply iProto_ctx_sym.
  - iDestruct 1 as (????) "(Hcl&Hcr&?&?&?&?&Hp)". iFrame. by iApply iProto_ctx_sym.
Qed.

(** DSP session context - public interface with persistent channel handles *)
Definition dsp_session
    (γl γr : gname)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) : iProp Σ :=
  is_channel lr_chan lrcap γlr_names ∗
  is_channel rl_chan rlcap γrl_names ∗
  inv N (dsp_session_inv γl γr lr_chan rl_chan γlr_names γrl_names lrcap rlcap).

(** ** DSP Endpoints *)

(** Left endpoint - can send V_LR via lr_chan, receive V_RL via rl_chan *)
Definition dsp_endpoint
    (v:val)
    (p : option $ iProto Σ val) : iProp Σ :=
  ∃ (γl γr : gname) (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z),
    ⌜v = #lr_chan⌝ ∗
    dsp_session γl γr lr_chan rl_chan γlr_names γrl_names lrcap rlcap ∗
    match p with
    | None => True
    | Some p => iProto_own γl p
    end.

Notation "c ↣ p" := (dsp_endpoint c (Some p)) (at level 20, format "c  ↣  p").
Notation "↯ c" := (dsp_endpoint c None) (at level 20, format "↯  c").

(** ** Initialization *)

(** Initialize a new DSP session from basic channels *)
Lemma dsp_session_init
    E (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (p : iProto Σ val) :
  is_channel lr_chan lrcap γlr_names -∗
  is_channel rl_chan rlcap γrl_names -∗
  own_channel lr_chan lrcap chan_rep.Idle γlr_names -∗
  own_channel rl_chan rlcap chan_rep.Idle γrl_names ={E}=∗
  #lr_chan ↣ p ∗ #rl_chan ↣ iProto_dual p.
Proof.
  iIntros "#Hcl_is #Hcr_is Hcl_own Hcr_own".
  iMod (iProto_init) as (γl γr) "(Hctx & Hpl & Hpr)".
  iMod (inv_alloc N _ (dsp_session_inv γl γr lr_chan rl_chan γlr_names γrl_names lrcap rlcap) with "[Hcl_own Hcr_own Hctx]")
    as "#Hinv".
  { iExists chan_rep.Idle,chan_rep.Idle,[],[]. by iFrame. }
  iModIntro.
  iSplitL "Hpl".
  - iExists _,_,_,_,_,_,_,_. iSplit; [done|].    
    iFrame "Hpl Hinv". iFrame "∗#".
  - iExists _,_,_,_,_,_,_,_. iSplit; [done|].
    rewrite dsp_session_inv_sym. iFrame "Hinv".
    iFrame "∗#".
Qed.

(** ** Endpoint Operations *)

Lemma into_val_val_unfold (v : val) : #v = v.
Proof. by rewrite to_val_unseal /to_val_def /=. Qed.

(** Endpoint sends value *)
Lemma dsp_send (c : val) (v : val) (p : iProto Σ val) :
  {{{ is_pkg_init channel ∗ c ↣ <!> MSG v; p }}}
    c @ (ptrT.id channel.Channel.id) @ "Send" #atomic.Value #v
  {{{ RET #(); c ↣ p }}}.
Proof.
  iIntros (Φ) "(#Hinit&Hc) HΦ".
  iDestruct "Hc" as (????????->) "(#(Hcl&Hcr&HI)&Hp)".
  replace (# (# lr_chan)) with (# lr_chan); last first.
  { by rewrite into_val_val_unfold. }
  iApply (wp_Send lr_chan lrcap v γlr_names with "[$Hinit $Hcl]").
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
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx [$Hp] []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hp Hown]". iMod "Hclose'" as "_".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hp]").
    { iIntros "!>". iExists _,_,_,_. iFrame. do 2 (iSplit; [done|]).
      iFrame. inversion H. subst. admit. }    
    iApply "HΦ". by iFrame "#∗".
  - iIntros "Hownl".
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx [$Hp] []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hctx Hown]". iMod "Hclose'" as "_". 
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]").
    { iIntros "!>". iExists _,_,_,_. iFrame. do 2 (iSplit; [done|]).
      iFrame. inversion H. subst. admit. }
    iModIntro.
    iMod (inv_acc with "HI") as "[IH Hclose]"; [solve_ndisj|].
    iApply fupd_mask_intro; [solve_ndisj|]. iIntros "Hclose'".
    iDestruct "IH" as (????) "(>%&>%&Hownl&Hownr&Hclosel&Hcloser&Hctx)".
    iFrame.
    iIntros "!>".
    destruct lr_state; try done.
    + iIntros "Hownl". iMod "Hclose'".
      iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hctx]").
      { iIntros "!>". iExists _,_,_,_. iFrame. done. }
      iApply "HΦ". iFrame "#∗". done.
    + iDestruct (iProto_own_excl with "Hown Hclosel") as "[]".
  - done.
  - iIntros "Hownl".
    iDestruct (iProto_send _ _ _ _ _ v p with "Hctx [$Hp] []") as "Hp".
    { by rewrite iMsg_base_eq. }
    iMod "Hp" as "[Hp Hown]". iMod "Hclose'".
    iMod ("Hclose" with "[Hownl Hownr Hclosel Hcloser Hp]").
    { iIntros "!>". iExists _,_,_,_. iFrame. do 2 (iSplit; [done|]).
      iFrame. inversion H. subst. admit. }
    iApply "HΦ". by iFrame "#∗".
  - done.
  - done.
  - iDestruct (iProto_own_excl with "Hp Hclosel") as "[]".
Admitted.

(** Endpoint receives value *)
Lemma dsp_recv {TT:tele}
    (c: val) (v : TT → val) (P : TT → iProp Σ) (p : TT → iProto Σ val) :
  {{{ is_pkg_init channel ∗ c ↣ <?.. x> MSG (v x) {{ ▷ P x }}; p x }}}
    c @ (ptrT.id channel.Channel.id) @ "Receive" #atomic.Value #()
  {{{ x, RET (#(v x), #true); c ↣ p x ∗ P x }}}.
Proof.
Admitted.

(** Endpoint receives on a closed or ended channel *)
Lemma dsp_recv_closed {TT:tele} (c : val) :
  {{{ is_pkg_init channel ∗ (c ↣ END ∨ ↯ c) }}}
    c @ (ptrT.id channel.Channel.id) @ "Receive" #atomic.Value #()
  {{{ RET (#(), #false);
      dsp_endpoint c None }}}.
Proof.
Admitted.

(** Endpoint closes (stops sending val) *)
Lemma dsp_close  (c : val) (p : iProto Σ val) :
  {{{ is_pkg_init channel ∗ c ↣ END }}}
    c @ (ptrT.id channel.Channel.id) @ "Close" #atomic.Value #()
  {{{ RET #(); ↯ c }}}.
Proof.
Admitted.

End dsp.
