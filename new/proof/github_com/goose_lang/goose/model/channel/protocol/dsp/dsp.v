Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export chan_au_send chan_au_recv chan_au_base chan_init.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export dsp_ghost_theory.

(** * Dependent Separation Protocols (DSP) over Go Channels

    This file implements dependent separation protocols using bidirectional Go channels.

    Key concepts:
    - Two protocol endpoints (left and right) communicate via two Go channels
    - LR channel: left endpoint sends V_LR values to right endpoint
    - RL channel: right endpoint sends V_RL values to left endpoint
    - Protocol state is tracked using Actris iProto with sum types
    - Channel closure is protocol-aware - only allowed when protocol permits
*)

(** ** Sum Type for Bidirectional Communication *)

Definition DspV (V_LR V_RL : Type) := sum V_LR V_RL.

#[export] Instance eqdec_sum `{EqDecision A} `{EqDecision B}
  : EqDecision (A + B) := _.
#[export] Instance countable_sum `{Countable A} `{Countable B}
  : Countable (A + B) := _.

Section dsp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!ghost_varG Σ ()}.
Context `{!chanGhostStateG Σ ()}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

(** ** Buffer Matching Predicates *)

(** Defines when Go channel state matches expected message queue *)
Definition lr_buffer_matches {V_LR}
    (lr_state : chan_rep.t V_LR) (vsl : list V_LR) : Prop :=
  match lr_state with
  | chan_rep.Buffered queue => vsl = queue
  | chan_rep.SndPending v | chan_rep.SndCommit v => vsl = [v]
  | chan_rep.Closed draining => vsl = draining
  | _ => vsl = []
  end.

Definition rl_buffer_matches {V_RL}
    (rl_state : chan_rep.t V_RL) (vsr : list V_RL) : Prop :=
  match rl_state with
  | chan_rep.Buffered queue => vsr = queue
  | chan_rep.SndPending v | chan_rep.SndCommit v => vsr = [v]
  | chan_rep.Closed draining => vsr = draining
  | _ => vsr = []
  end.

(** ** Protocol Value Lifting *)

(** Lift left-to-right values into sum type for protocol *)
Definition lift_lr {V_LR V_RL} (vsl : list V_LR)
  : list (DspV V_LR V_RL) := List.map (@inl V_LR V_RL) vsl.

(** Lift right-to-left values into sum type for protocol *)
Definition lift_rl {V_LR V_RL} (vsr : list V_RL)
  : list (DspV V_LR V_RL) := List.map (@inr V_LR V_RL) vsr.

(** ** DSP Session Context *)

(** DSP session invariant - owns both channels and maintains protocol state *)
Definition dsp_session_inv {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) : iProp Σ :=
  ∃ lr_state rl_state vsl vsr,
    own_channel lr_chan lrcap lr_state γlr_names ∗
    own_channel rl_chan rlcap rl_state γrl_names ∗
    ⌜lr_buffer_matches lr_state vsl⌝ ∗
    ⌜rl_buffer_matches rl_state vsr⌝ ∗
    iProto_ctx γl γr (lift_lr vsl) (lift_rl vsr).

(** DSP session context - public interface with persistent channel handles *)
Definition dsp_session {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) : iProp Σ :=
  is_channel lr_chan lrcap γlr_names ∗
  is_channel rl_chan rlcap γrl_names ∗
  inv N (dsp_session_inv γl γr lr_chan rl_chan γlr_names γrl_names lrcap rlcap).

(** ** DSP Endpoints *)

(** Left endpoint - can send V_LR via lr_chan, receive V_RL via rl_chan *)
Definition dsp_left_endpoint {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z)
    (p : iProto Σ (DspV V_LR V_RL)) : iProp Σ :=
  dsp_session γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap ∗
  iProto_own γl p.

(** Right endpoint - can send V_RL via rl_chan, receive V_LR via lr_chan *)
Definition dsp_right_endpoint {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z)
    (p : iProto Σ (DspV V_LR V_RL)) : iProp Σ :=
  dsp_session γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap ∗
  iProto_own γr p.

(** ** Initialization *)

(** Initialize a new DSP session from basic channels *)
Lemma dsp_session_init {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (N : namespace) (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (p : iProto Σ (DspV V_LR V_RL)) :
  is_channel lr_chan lrcap γlr_names -∗
  is_channel rl_chan rlcap γrl_names -∗
  own_channel lr_chan lrcap chan_rep.Idle γlr_names -∗
  own_channel rl_chan rlcap chan_rep.Idle γrl_names ==∗
  ∃ γl γr,
    dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p ∗
    dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap (iProto_dual p).
Proof.
Admitted.

(** ** Left Endpoint Operations *)

(** Left endpoint sends V_LR value via lr_chan *)
Lemma dsp_left_send {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (v : V_LR) (m : iMsg Σ (DspV V_LR V_RL)) :
  {{{ is_pkg_init channel ∗
      dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap (<!> m) ∗
      ∃ p', iMsg_car m (inl v) (Next p') }}}
    lr_chan @ (ptrT.id channel.Channel.id) @ "Send" #tL #v
  {{{ p', RET #();
      iMsg_car m (inl v) (Next p') ∗
      dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p' }}}.
Proof.
Admitted.

(** Left endpoint receives V_RL value via rl_chan *)
Lemma dsp_left_recv {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (m : iMsg Σ (DspV V_LR V_RL)) :
  {{{ is_pkg_init channel ∗
      dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap (<?> m) }}}
    rl_chan @ (ptrT.id channel.Channel.id) @ "Receive" #tR #()
  {{{ (v : V_RL) (ok : bool), RET (#v, #ok);
      if ok then ∃ p', iMsg_car m (inr v) (Next p') ∗
                      dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p'
      else (* Channel closed - only valid if protocol allows termination *)
           iProto_le (<?> m) END ∗
           dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap END }}}.
Proof.
Admitted.


(** Left endpoint closes lr_chan (stops sending V_LR) *)
Lemma dsp_left_close_lr {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (p : iProto Σ (DspV V_LR V_RL)) :
  {{{ is_pkg_init channel ∗
      dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p ∗
      (* Only allow closure when protocol permits it *)
      p ⊑ END }}}
    lr_chan @ (ptrT.id channel.Channel.id) @ "Close" #tL #()
  {{{ RET #(); dsp_left_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap END }}}.
Proof.
Admitted.

(** ** Right Endpoint Operations *)

(** Right endpoint sends V_RL value via rl_chan *)
Lemma dsp_right_send {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (v : V_RL) (m : iMsg Σ (DspV V_LR V_RL)) :
  {{{ is_pkg_init channel ∗
      dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap (<!> m) ∗
      ∃ p', iMsg_car m (inr v) (Next p') }}}
    rl_chan @ (ptrT.id channel.Channel.id) @ "Send" #tR #v
  {{{ p', RET #();
      iMsg_car m (inr v) (Next p') ∗
      dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p' }}}.
Proof.
Admitted.

(** Right endpoint receives V_LR value via lr_chan *)
Lemma dsp_right_recv {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (m : iMsg Σ (DspV V_LR V_RL)) :
  {{{ is_pkg_init channel ∗
      dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap (<?> m) }}}
    lr_chan @ (ptrT.id channel.Channel.id) @ "Receive" #tL #()
  {{{ (v : V_LR) (ok : bool), RET (#v, #ok);
      if ok then ∃ p', iMsg_car m (inl v) (Next p') ∗
                      dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p'
      else (* Channel closed - only valid if protocol allows termination *)
           (<?> m) ⊑ END ∗
           dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap END }}}.
Proof.
Admitted.

(** Right endpoint closes rl_chan (stops sending V_RL) *)
Lemma dsp_right_close_rl {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname) (N : namespace)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (lrcap rlcap: Z) (p : iProto Σ (DspV V_LR V_RL)) :
  {{{ is_pkg_init channel ∗
      dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap p ∗
      (* Only allow closure when protocol permits it *)
      p ⊑ END }}}
    rl_chan @ (ptrT.id channel.Channel.id) @ "Close" #tR #()
  {{{ RET #(); dsp_right_endpoint γl γr N lr_chan rl_chan γlr_names γrl_names lrcap rlcap END }}}.
Proof.
Admitted.

End dsp.
