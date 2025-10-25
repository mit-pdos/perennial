From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_init.
From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

(** The mathematical model of channel states. This represents the logical
    behavior of channels independent of the implementation details. *)
Module chan_rep.
Inductive t (V : Type) : Type :=
| Buffered (buff: list V)     (* Buffered channel with pending messages *)
| Idle                        (* Empty unbuffered channel, ready for operations *)
| SndPending (v: V)          (* Unbuffered channel with sender waiting *)
| RcvPending                 (* Unbuffered channel with receiver waiting *)
| SndCommit (v: V)           (* Sender committed, waiting for receiver to complete *)
| RcvCommit                  (* Receiver committed, waiting for sender to complete *)
| Closed (draining: list V)  (* Closed channel, possibly draining remaining messages *)
.
#[global] Instance witness V : Inhabited (t V) := populate!.


Global Arguments Buffered {V}.
Global Arguments Idle {V}.
Global Arguments SndPending {V}.
Global Arguments RcvPending {V}.
Global Arguments SndCommit {V}.
Global Arguments RcvCommit {V}.
Global Arguments Closed {V}.

End chan_rep.

(** The state machine representation matching the model implementation.
    This is slightly different from the mathematical representation
    in that we don't go to the SndWait state logically until an offer 
    is about to be accepted. *)
Inductive chan_phys_state (V : Type) : Type :=
| Buffered (buff: list V)     (* Channel with buffered messages *)
| Idle                        (* Ready for operations *)
| SndWait (v : V)            (* Sender offers *)
| RcvWait                    (* Receiver offers *)
| SndDone (v : V)            (* Sender operation completed, handshake in progress *)
| RcvDone (v : V)            (* Receiver operation completed, handshake in progress *)
| Closed (draining: list V)  (* Closed channel *)
.

  Global Arguments Idle {V}.
  Global Arguments SndWait {V}.
  Global Arguments RcvWait {V}.
  Global Arguments SndDone {V}.
  Global Arguments RcvDone {V}.
  Global Arguments Closed {V}.
  Global Arguments Buffered {V}.

(** The offer protocol coordinates handshakes between senders and receivers
    in unbuffered channels. An "offer" represents a pending operation that
    can be accepted by the other party. This ghost state ensures that 
    an outstanding offer can only be accepted or left as-is for when we lock
    the channel to check the status. *)
Inductive offer_lock (V : Type) : Type :=
| Snd (v : V)                (* Sender has made an offer *)
| Rcv                        (* Receiver has made an offer *)
.

  Global Arguments Snd {V}.
  Global Arguments Rcv {V}.

(** Ghost names for tracking various aspects of channel state in the logic *)
Record chan_names := {
  state_name : gname;                    (* Main channel state *)
  offer_lock_name : gname;               (* Offer protocol lock *)
  offer_parked_prop_name : gname;        (* The saved prop that we can leave with the channel to support select *)
  offer_parked_pred_name : gname;        (* The saved continuation for receive, which is a predicate on v, ok *)
  offer_continuation_name : gname;       (* The continuation for send *)
}.

(** Type class for ghost state associated with channels *)
Class chanGhostStateG Σ V := ChanGhostStateG {
  offerG :: ghost_varG Σ (chan_rep.t V);
  offer_lockG :: ghost_varG Σ (option (offer_lock V));
  offer_parked_propG :: savedPropG Σ;
  offer_parked_predG :: savedPredG Σ (V * bool);
}.

Definition chanGhostStateΣ V : gFunctors :=
  #[ ghost_varΣ (chan_rep.t V); ghost_varΣ (option (offer_lock V));
     savedPropΣ; savedPredΣ  (V * bool) ].

#[global] Instance subG_chanGhostStateG Σ V :
  subG (chanGhostStateΣ V) Σ → chanGhostStateG Σ V.
Proof. solve_inG. Qed.

Section base.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.

(* Remove the later from a saved prop if we have later credits. *)
Lemma saved_prop_lc_agree γ dq1 dq2 P Q :
   £ 1 -∗ saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ |={⊤}=> (P ≡ Q).
Proof.
  iIntros "Hlc HP HQ".
  iDestruct (saved_prop_agree with "HP HQ") as "Heq".
  iMod (lc_fupd_elim_later with "Hlc Heq") as "H3".
  iModIntro. done.
Qed.

(** Maps physical channel states to their heap representations.
    Each state corresponds to specific field values in the Go struct. *)
Definition chan_phys (ch: loc) (s: chan_phys_state V) : iProp Σ :=
  match s with
    | Closed [] =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 6) ∗
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | Closed draining =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 6) ∗
        "slice" ∷ own_slice slice_val (DfracOwn 1) draining ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | Buffered buff =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 0) ∗
        "slice" ∷ own_slice slice_val (DfracOwn 1) buff ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | Idle =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 1) ∗
        "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | SndWait v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 2) ∗
        "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗  
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | RcvWait =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 3) ∗
        "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | SndDone v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 4) ∗
        "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗  
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | RcvDone v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 5) ∗ 
        "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    end.

(** Bundles together offer-related ghost state for atomic operations *)
Definition saved_offer (γ : chan_names) (q : Qp)
  (lock_val : option (offer_lock V))
  (parked_prop continuation_prop : iProp Σ) : iProp Σ :=
  ghost_var γ.(offer_lock_name) q lock_val ∗
  saved_prop_own γ.(offer_parked_prop_name) (DfracOwn q) parked_prop ∗
  saved_prop_own γ.(offer_continuation_name) (DfracOwn q) continuation_prop.

Notation offer_bundle_full γ := (saved_offer γ 1%Qp).
Notation offer_bundle_half γ := (saved_offer γ (1/2)%Qp).

Definition offer_bundle_empty (γ : chan_names) : iProp Σ :=
  offer_bundle_full γ None True True.

Lemma offer_idle_to_send γ v parked_prop cont :
  offer_bundle_empty γ ==∗
  offer_bundle_half γ (Some (Snd v)) parked_prop cont ∗
  offer_bundle_half γ (Some (Snd v)) parked_prop cont.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update (Some (Snd v)) with "Hlock") as "[Hlock1 Hlock2]".
  iMod (saved_prop_update cont with "Hcont") as "[Hcont1 Hcont2]".
  iMod (saved_prop_update parked_prop with "Hoffer") as "[Hoffer1 Hoffer2]".
  iModIntro. iFrame.
Qed.

Lemma offer_send_to_idle γ v parked_prop cont :
  offer_bundle_half γ (Some (Snd v)) parked_prop cont -∗
   offer_bundle_half γ (Some (Snd v)) parked_prop cont ==∗
  offer_bundle_empty γ.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iIntros "[Hlock2 [Hoffer2 Hcont2]]".
  iCombine "Hlock Hlock2" as "Hlock".
  iMod (saved_prop_update_halves True with "Hoffer Hoffer2") as "[Hoffer Hoffer2]".
  iMod (saved_prop_update_halves True with "Hcont Hcont2") as "[Hcont Hcont2]".
  iCombine "Hcont Hcont2" as "Hcont".
  iCombine "Hoffer Hoffer2" as "Hoffer".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iModIntro. unfold offer_bundle_empty. unfold offer_bundle_full. iFrame.
  unfold saved_prop_own.
  rewrite dfrac_op_own.
  rewrite Qp.half_half.
  iFrame.
Qed.

Lemma offer_idle_to_recv γ parked_prop cont:
  offer_bundle_empty γ ==∗
  offer_bundle_half γ (Some Rcv) parked_prop cont ∗
  offer_bundle_half γ (Some Rcv) parked_prop cont.
Proof.
   iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update (Some (Rcv)) with "Hlock") as "[Hlock1 Hlock2]".
  iMod (saved_prop_update cont with "Hcont") as "[Hcont1 Hcont2]".
  iMod (saved_prop_update parked_prop with "Hoffer") as "[Hoffer1 Hoffer2]".
  iModIntro. iFrame.
Qed.

Lemma offer_recv_to_idle γ parked_prop cont :
  offer_bundle_half γ (Some Rcv) parked_prop cont -∗
   offer_bundle_half γ (Some Rcv) parked_prop cont ==∗
  offer_bundle_empty γ.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iIntros "[Hlock2 [Hoffer2 Hcont2]]".
  iCombine "Hlock Hlock2" as "Hlock".
  iMod (saved_prop_update_halves True with "Hoffer Hoffer2") as "[Hoffer Hoffer2]".
  iMod (saved_prop_update_halves True with "Hcont Hcont2") as "[Hcont Hcont2]".
  iCombine "Hcont Hcont2" as "Hcont".
  iCombine "Hoffer Hoffer2" as "Hoffer".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iModIntro. unfold offer_bundle_empty. unfold offer_bundle_full. iFrame.
  unfold saved_prop_own.
  rewrite dfrac_op_own.
  rewrite Qp.half_half.
  iFrame.
Qed.

Lemma offer_reset γ :
  ∀ parked_prop cont state,
   offer_bundle_full γ state parked_prop cont ==∗
  offer_bundle_empty γ.
Proof.
  intros parked_prop cont state.
  iIntros "[Hlock [Hoffer Hcont]]".
  iMod (ghost_var_update None with "Hlock") as "Hlock".
  iMod (saved_prop_update True with "Hcont") as "Hcont".
  iMod (saved_prop_update True with "Hoffer") as "Hoffer".
  iModIntro.
  iFrame.
Qed.

Lemma offer_bundle_agree γ q1 q2
  lock1 parked1 cont1 lock2 parked2 cont2 :
  saved_offer γ q1 lock1 parked1 cont1 ∗
  saved_offer γ q2 lock2 parked2 cont2 ⊢
  ⌜lock1 = lock2⌝ ∗
  ▷(parked1 ≡ parked2) ∗ ▷(cont1 ≡ cont2).
Proof.
  iIntros "[[Hl1 [Hp1 Hc1]] [Hl2 [Hp2 Hc2]]]".
  iDestruct (ghost_var_agree with "Hl1 Hl2") as %->.
  iDestruct (saved_prop_agree with "Hp1 Hp2") as "Hp_eq".
  iDestruct (saved_prop_agree with "Hc1 Hc2") as "Hc_eq".
  auto.
Qed.

Lemma offer_bundle_lc_agree γ
  lock1 parked1 cont1 lock2 parked2 cont2 :
  £ 1 -∗ £ 1 -∗
  saved_offer γ (1/2) lock1 parked1 cont1 -∗
  saved_offer γ (1/2) lock2 parked2 cont2 -∗
  |={⊤}=> ⌜lock1 = lock2⌝ ∗
         (parked1 ≡ parked2) ∗ (cont1 ≡ cont2) ∗
         offer_bundle_empty γ.
Proof.
  iIntros "Hlc1".
  iIntros "Hlc2".
  iIntros "[Hl1 [Hp1 Hc1]]".
  iIntros "[Hl2 [Hp2 Hc2]]".
   iDestruct (ghost_var_agree with "[$Hl1] [$Hl2]") as %->.
  iDestruct (saved_prop_agree with "[$Hp1] [$Hp2]") as "#Hp_eq".
  iDestruct (saved_prop_agree with "[$Hc1] [$Hc2]") as "#Hc_eq".

  iMod (lc_fupd_elim_later with "Hlc1 Hp_eq") as "Hp_eq1".
  iMod (lc_fupd_elim_later with "Hlc2 Hc_eq") as "Hc_eq1".
  unfold offer_bundle_empty. unfold offer_bundle_full.
  iFrame.
  iSplitR; first done.  (* ⌜lock2 = lock2⌝ is trivial *)

(* Combine and update ghost variable *)
iCombine "Hl1 Hl2" as "Hlock".
iMod ((ghost_var_update None) with "Hlock") as "Hlock".

(* Update saved propositions using halves lemmas *)
iMod (saved_prop_update_halves True with "Hp1 Hp2") as "[Hp1 Hp2]".
iMod (saved_prop_update_halves True with "Hc1 Hc2") as "[Hc1 Hc2]".

(* Combine the updated halves to get full ownership *)
iCombine "Hp1 Hp2" as "Hparked".
iCombine "Hc1 Hc2" as "Hcont".

(* Simplify the combined fractions *)
rewrite dfrac_op_own Qp.half_half.

iFrame.
  auto.
Qed.

Lemma saved_offer_fractional_invalid γ q1 q2 lock1 parked1 cont1 lock2 parked2 cont2 :
  (1 < q1 + q2)%Qp →
  saved_offer γ q1 lock1 parked1 cont1 -∗
  saved_offer γ q2 lock2 parked2 cont2 -∗
  False.
Proof.
  iIntros (Hq) "[Hlock1 [Hp1 Hc1]] [Hlock2 [Hp2 Hc2]]".
  iDestruct (ghost_var_valid_2 with "Hlock1 Hlock2") as "[%Hvalid _]".
  iPureIntro.
apply Qp.lt_nge in Hq.
contradiction.
Qed.

Lemma saved_offer_half_full_invalid γ lock1 parked1 cont1 lock2 parked2 cont2 :
  saved_offer γ (1/2) lock1 parked1 cont1 -∗
  saved_offer γ 1 lock2 parked2 cont2 -∗
  False.
Proof.
  iApply saved_offer_fractional_invalid.
  compute_done. (* 1/2 + 1 = 3/2 > 1 *)
Qed.

Definition chan_rep (γ : gname) (q : Qp) (s : chan_rep.t V) : iProp Σ :=
  ghost_var γ q s.

Notation chan_rep_full γ s := (chan_rep γ 1 s).
Notation chan_rep_half γ s := (chan_rep γ (1/2)%Qp s).
Notation chan_rep_auth γ s := (chan_rep_half γ s).
Notation chan_rep_frag γ s := (chan_rep_half γ s).

Lemma chan_rep_update γ s s' :
  chan_rep_full γ s ==∗ chan_rep_full γ s'.
Proof.
  iApply (ghost_var_update s' γ s). 
Qed.

Lemma chan_rep_agree γ q1 q2 s s' :
  chan_rep γ q1 s -∗ chan_rep γ q2 s' -∗ ⌜s = s'⌝.
Proof. 
  iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2"). 
Qed.

Lemma chan_rep_combine γ s s' :
  chan_rep_half γ s -∗ chan_rep_half γ s' -∗ ⌜s = s'⌝ -∗ chan_rep_full γ s.
Proof.
  iIntros "H1 H2 %H3". iDestruct (chan_rep_agree with "H1 H2") as %->.
  iCombine "H1" "H2" as "H". done.
Qed.

Lemma chan_rep_halves_update γ s1 s2 s' :
  chan_rep_half γ s1 -∗ chan_rep_half γ s2 ==∗
     chan_rep_half γ s' ∗ chan_rep_half γ s'.
Proof.
  rewrite /chan_rep.
  apply ghost_var_update_halves.
Qed.

Definition chan_cap_valid (s : chan_rep.t V) (cap: Z) : Prop :=
  match s with
  | chan_rep.Buffered _ => (0 < cap)%Z     
  | chan_rep.Closed [] => True              (* Empty closed channels might have been unbuffered, doesn't matter *)
  | chan_rep.Closed _ => (0 < cap)%Z (* Draining closed channels are buffered channels *)
  | _ => cap = 0                            (* All other states are unbuffered *)
  end.

(** ** Channel Ownership Predicate *)

(** Represents ownership of a channel with its logical state *)
Definition own_channel (ch: loc) (cap: Z) (s: chan_rep.t V) (γ: chan_names) : iProp Σ :=
  "Hchanrepfrag" ∷ chan_rep_half γ.(state_name) s ∗
  "%Hcapvalid" ∷ ⌜chan_cap_valid s cap⌝.

Lemma own_channel_agree ch cap cap' s s' γ :
   own_channel ch cap s γ -∗ own_channel ch cap' s' γ -∗ ⌜s = s'⌝.
Proof. 
  iIntros "H1 H2". iNamed "H1". iDestruct "H2" as "[Hoc %Hcap]".
  iDestruct (ghost_var_agree with "[$Hchanrepfrag] [$Hoc]") as "%Hag".
  unfold chan_cap_valid in *.
  by iApply (ghost_var_agree with "Hchanrepfrag Hoc"). 
Qed.

Lemma own_channel_halves_update ch cap s s' s'' γ :
  chan_cap_valid s'' cap →
  own_channel ch cap s γ -∗ own_channel ch cap s' γ ==∗
  own_channel ch cap s'' γ ∗ own_channel ch cap s'' γ.
Proof.
  iIntros (Hvalid) "[Hv1 %] [Hv2 %]". rewrite /named.
  iMod (chan_rep_halves_update with "Hv1 Hv2") as "[$ $]".
  iPureIntro.
  auto.
Qed.

(** Type alias for convenience: converts postcondition to predicate format *)
Definition K (Φ : V → bool → iProp Σ) : (V * bool) → iProp Σ :=
  λ '(v,b), Φ v b.

(** Inner atomic update for receive completion (second phase of handshake) *)
Definition rcv_au_inner ch (cap: Z) (γ: chan_names) (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_channel ch cap s γ ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Sender has committed, complete the exchange *)
    | chan_rep.SndCommit v => own_channel ch cap chan_rep.Idle γ ={∅,⊤}=∗ Φ v true
    (* Case: Channel is closed with no messages *)
    | chan_rep.Closed [] => own_channel ch cap s γ ={∅,⊤}=∗ Φ (default_val V) false
    | _ => True
    end).

(** Slow path receive: may need to block and wait *)
Definition rcv_au_slow ch (cap: Z) (γ: chan_names) (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch cap s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Sender is waiting, can complete immediately *)
    | chan_rep.SndPending v =>
          own_channel ch cap chan_rep.RcvCommit γ ={∅,⊤}=∗ Φ v true
    (* Case: Channel is idle, need to wait for sender *)
    | chan_rep.Idle =>
          own_channel ch cap (chan_rep.RcvPending) γ ={∅,⊤}=∗
              rcv_au_inner ch cap γ Φ
    (* Case: Channel is closed *)
    | chan_rep.Closed [] => own_channel ch cap s γ ={∅,⊤}=∗ Φ (default_val V) false
    (* Case: Closed but still have values to drain *)
    | chan_rep.Closed (v::rest) => (own_channel ch cap (chan_rep.Closed rest) γ ={∅,⊤}=∗ Φ v true)
    (* Case: Buffered channel with values in buffer *)
    | chan_rep.Buffered (v::rest) => (own_channel ch cap (chan_rep.Buffered rest) γ ={∅,⊤}=∗ Φ v true)
    | _ => True
    end).

(** Fast path receive: immediate completion when possible *)
Definition rcv_au_fast ch (cap: Z) (γ: chan_names) (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch cap s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Sender is waiting, can complete immediately *)
    | chan_rep.SndPending v =>
          own_channel ch cap chan_rep.RcvCommit γ ={∅,⊤}=∗ Φ v true
    (* Case: Channel is closed *)
    | chan_rep.Closed [] => own_channel ch cap s γ ={∅,⊤}=∗ Φ (default_val V) false
    (* Case: Channel is closed but still has values to drain *)
    | chan_rep.Closed (v::rest) => (own_channel ch cap (chan_rep.Closed rest) γ ={∅,⊤}=∗ Φ v true)
    (* Case: Buffered channel with values *)
    | chan_rep.Buffered (v::rest) => (own_channel ch cap (chan_rep.Buffered rest) γ ={∅,⊤}=∗ Φ v true)
    | _ => True
    end).

(** Inner atomic update for send completion (second phase of handshake) *)
Definition send_au_inner ch (cap: Z) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_channel ch cap s γ ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Receiver has committed, complete the exchange *)
    | chan_rep.RcvCommit =>
           own_channel ch cap chan_rep.Idle γ ={∅,⊤}=∗ Φ
    (* Case: Channel is closed, operation fails *)
    | chan_rep.Closed draining => False
    | _ => True
    end).

(** Slow path send: may need to block and wait *)
Definition send_au_slow ch (cap: Z) (v : V) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch cap s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Receiver is waiting, can complete immediately *)
    | chan_rep.RcvPending =>
        own_channel ch cap (chan_rep.SndCommit v) γ ={∅,⊤}=∗ Φ
    (* Case: Channel is idle, need to wait for receiver *)
    | chan_rep.Idle =>
          own_channel ch cap (chan_rep.SndPending v) γ ={∅,⊤}=∗
              send_au_inner ch cap γ Φ
    (* Case: Channel is closed, client must rule this out *)
    | chan_rep.Closed draining => False
    (* Case: Buffered channel with space available *)
    | chan_rep.Buffered buff => 
        if (length buff <? cap) 
        then (own_channel ch cap (chan_rep.Buffered (buff ++ [v])) γ ={∅,⊤}=∗ Φ)
        else True
    | _ => True
    end).

(** Fast path send: immediate completion when possible *)
Definition send_au_fast ch (cap: Z) (v : V) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch cap s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Receiver is waiting, can complete immediately *)
    | chan_rep.RcvPending =>
        own_channel ch cap (chan_rep.SndCommit v) γ ={∅,⊤}=∗ Φ
    (* Case: Channel is closed, client must rule this out *)
    | chan_rep.Closed draining => False
    (* Case: Buffered channel with space available *)
    | chan_rep.Buffered buff => 
        if (length buff <? cap) 
        then (own_channel ch cap (chan_rep.Buffered (buff ++ [v])) γ ={∅,⊤}=∗ Φ)
        else True
    | _ => True
    end).


Definition close_au ch (cap: Z) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_channel ch cap s γ ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Ready to close unbuffered *)
    | chan_rep.Idle =>
           own_channel ch cap (chan_rep.Closed []) γ ={∅,⊤}=∗ Φ
    (* Case: Buffered, go to draining *)
    | chan_rep.Buffered buff => 
          own_channel ch cap (chan_rep.Closed buff) γ ={∅,⊤}=∗ Φ
    (* Case: Channel is closed already, panic *)
    | chan_rep.Closed draining => False 
    | _ => True
    end).


(** Maps physical states to their logical representations with ghost state.
    This is the key invariant that connects the physical implementation
    to the logical specifications. *)
Definition chan_logical (ch: loc) (cap: Z) (γ : chan_names) (s : chan_phys_state V): iProp Σ :=
  match s with
  | Idle =>
       ∃ (Φr: V → bool → iProp Σ),
           "Hoffer" ∷ offer_bundle_empty γ ∗
           "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (K Φr) ∗
            own_channel ch cap chan_rep.Idle γ

  | SndWait v =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ),
          "Hoffer" ∷ offer_bundle_half γ (Some (Snd v)) P Φ ∗
          "HP" ∷ P ∗
          "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (K Φr) ∗
          "Hau" ∷ (P -∗ send_au_slow ch cap v γ Φ) ∗
           own_channel ch cap chan_rep.Idle γ

  | RcvWait =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
         "Hoffer" ∷ offer_bundle_half γ (Some Rcv) P True ∗
         "HP" ∷ P ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (K Φr) ∗
         "Hau" ∷ (P -∗ rcv_au_slow ch cap γ Φr) ∗
         own_channel ch cap chan_rep.Idle γ

  | SndDone v =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
       "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (K Φr) ∗
       "Hoffer" ∷ offer_bundle_half γ (Some Rcv) P True ∗
       "Hau" ∷ rcv_au_inner ch cap γ Φr ∗
       own_channel ch cap (chan_rep.SndCommit v) γ

  | RcvDone v =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ),
         "Hoffer" ∷ offer_bundle_half γ (Some (Snd v)) P Φ ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (K Φr) ∗
         "Hau" ∷ send_au_inner ch cap γ Φ ∗
       own_channel ch cap chan_rep.RcvCommit γ

  | Closed [] =>
          own_channel ch cap (chan_rep.Closed []) γ ∗ 
           "Hoffer" ∷ if (cap =? 0) then offer_bundle_empty γ else True

  | Closed draining =>
          own_channel ch cap (chan_rep.Closed draining) γ

  | Buffered buff =>
          own_channel ch cap (chan_rep.Buffered buff) γ
  end.

(** The main invariant protected by the channel's mutex.
    This connects the physical heap state with the logical state. *)
Definition chan_inv_inner (ch: loc) (cap: Z) (γ: chan_names) : iProp Σ :=
  ∃ (s : chan_phys_state V),
    "phys" ∷ chan_phys ch s ∗
    "offer" ∷ chan_logical ch cap γ s.

(** The public predicate that clients use to interact with channels.
    This is persistent and provides access to the channel's capabilities. *)
Definition is_channel (ch: loc) (cap: Z) (γ: chan_names) : iProp Σ :=
  ∃ (mu_loc: loc),
    "#cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ (W64 cap) ∗
    "#mu" ∷ ch ↦s[(channel.Channel.ty t) :: "mu"]□ mu_loc ∗
    "#lock" ∷ primitive.is_Mutex mu_loc (chan_inv_inner ch cap γ).

Global Instance is_channel_pers ch cap γ : Persistent (is_channel cap ch γ).
Proof. apply _. Qed.

Global Instance own_channel_timeless ch cap s γ : Timeless (own_channel ch cap s γ).
Proof. apply _. Qed.

Lemma is_channel_not_null ch cap γ:
  is_channel ch cap γ -∗ ⌜ch ≠ null⌝.
Proof.
  iNamed 1.
  iDestruct (field_pointsto_not_null with "cap") as %Hnn; auto.
  done.
Qed.

End base.
