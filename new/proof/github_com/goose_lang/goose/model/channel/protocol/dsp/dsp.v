Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export chan_au_send chan_au_recv chan_au_base chan_init.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export dsp_ghost_theory.

Definition DspV (V_LR V_RL : Type) := sum V_LR V_RL.

#[export] Instance eqdec_sum `{EqDecision A} `{EqDecision B}
  : EqDecision (A + B) := _.
#[export] Instance countable_sum `{Countable A} `{Countable B}
  : Countable (A + B) := _.

  (*------------------------------------------------------------------------------
  Dependent Separation Protocols (DSP) over Go channels

  - This file encodes dependent separation protocols on Go channels.
  - There are two protocol endpoints (goroutines), and two Go channels:
    one for traffic left→right and one for the opposite (right→left).
------------------------------------------------------------------------------*)
Section dsp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!ghost_varG Σ ()}.
Context `{!chanGhostStateG Σ ()}.          (* not used below; fine to keep *)
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Definition lr_buffer_matches {V_LR}
    (lr_state : chan_rep.t V_LR) (vsl : list V_LR) : Prop :=
  match lr_state with
  | chan_rep.Buffered queue => vsl = queue
  | chan_rep.SndWait v | chan_rep.SndDone v => vsl = [v]
  | chan_rep.Closed draining => vsl = draining
  | _ => vsl = []
  end.

Definition rl_buffer_matches {V_RL}
    (rl_state : chan_rep.t V_RL) (vsr : list V_RL) : Prop :=
  match rl_state with
  | chan_rep.Buffered queue => vsr = queue
  | chan_rep.SndWait v | chan_rep.SndDone v => vsr = [v]
  | chan_rep.Closed draining => vsr = draining
  | _ => vsr = []
  end.

Definition lift_lr {V_LR V_RL} (vsl : list V_LR)
  : list (DspV V_LR V_RL) := List.map (@inl V_LR V_RL) vsl.

Definition lift_rl {V_LR V_RL} (vsr : list V_RL)
  : list (DspV V_LR V_RL) := List.map (@inr V_LR V_RL) vsr.

Definition dsp_chan_ctx
    {V_LR V_RL}
    `{!protoG Σ (DspV V_LR V_RL)}
    `{!chanGhostStateG Σ V_LR} `{!IntoVal V_LR} `{!IntoValTyped V_LR tL}
    `{!chanGhostStateG Σ V_RL} `{!IntoVal V_RL} `{!IntoValTyped V_RL tR}
    (γl γr : gname)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (vsl : list V_LR) (vsr : list V_RL) (lrcap rlcap: w64) : iProp Σ :=
  ∃ lr_state rl_state,
      is_channel (V:=V_LR) lr_chan lrcap γlr_names
  ∗   is_channel (V:=V_RL) rl_chan rlcap γrl_names
  ∗   ⌜lr_buffer_matches lr_state vsl⌝
  ∗   ⌜rl_buffer_matches rl_state vsr⌝
  ∗   (* iProto_ctx needs both queues as the same V: lift into the sum *)
      iProto_ctx γl γr (lift_lr vsl) (lift_rl vsr).

End dsp.