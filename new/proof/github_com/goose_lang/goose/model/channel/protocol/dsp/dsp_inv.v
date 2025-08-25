
(* WIP proof of concept for DSP on top of Go channels *)
(*
(* The shared message type for DSP/Actris *)
Definition DspV (V_LR V_RL : Type) := V_LR + V_RL.

#[export] Instance eqdec_sum `{EqDecision A} `{EqDecision B}
  : EqDecision (A + B) := _.
#[export] Instance countable_sum `{Countable A} `{Countable B}
  : Countable (A + B) := _.

Definition lr_buffer_matches {V_LR}
    (lr_state : chan_state.Channel V_LR) (vsl : list V_LR) : Prop :=
  match lr_state with
  | chan_state.Open (chan_state.Buffered (chan_state.Buffer queue _)) => vsl = queue
  | chan_state.Open (chan_state.Unbuffered ub_state) =>
      match ub_state with
      | chan_state.Idle      => vsl = []
      | chan_state.SndWait v => vsl = [v]  (* logically buffered on send-wait *)
      | chan_state.RcvWait   => vsl = []
      | chan_state.SndDone _ => vsl = []
      | chan_state.RcvDone   => vsl = []
      end
  | chan_state.Closed => vsl = []
  end.

(* Symmetric matcher for the RL side *)
Definition rl_buffer_matches {V_RL}
    (rl_state : chan_state.Channel V_RL) (vsr : list V_RL) : Prop :=
  match rl_state with
  | chan_state.Open (chan_state.Buffered (chan_state.Buffer queue _)) => vsr = queue
  | chan_state.Open (chan_state.Unbuffered ub_state) =>
      match ub_state with
      | chan_state.Idle      => vsr = []
      | chan_state.SndWait v => vsr = [v]
      | chan_state.RcvWait   => vsr = []
      | chan_state.SndDone _ => vsr = []
      | chan_state.RcvDone   => vsr = []
      end
  | chan_state.Closed => vsr = []
  end.


Definition lift_lr {V_LR V_RL} (vsl : list V_LR)
  : list (DspV V_LR V_RL) := List.map (@inl V_LR V_RL) vsl.

Definition lift_rl {V_LR V_RL} (vsr : list V_RL)
  : list (DspV V_LR V_RL) := List.map (@inr V_LR V_RL) vsr.

(* DSP-Go channel connection context using the single universe V_LR + V_RL *)
Definition dsp_chan_ctx {Σ V_LR V_RL} `{!protoG Σ (DspV V_LR V_RL)}
    (γl γr : gname)
    (lr_chan rl_chan : loc) (γlr_names γrl_names : chan_names)
    (vsl : list V_LR) (vsr : list V_RL) : iProp Σ :=
  ∃ lr_state rl_state,
    is_channel lr_chan γlr_names ∗
    is_channel rl_chan γrl_names ∗
    ⌜lr_buffer_matches lr_state vsl⌝ ∗
    ⌜rl_buffer_matches rl_state vsr⌝ ∗
    (* iProto_ctx needs both queues as the SAME V: lift into the sum *)
    iProto_ctx γl γr (lift_lr vsl) (lift_rl vsr).
*)