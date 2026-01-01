From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.

(* NOTE: must shadow iris ghost_var *)
From Perennial.algebra Require Import ghost_var.

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
  chan_cap : Z;                          (* The channel capacity *)
  chan_cap_bound : 0 ≤ chan_cap < 2^63;
}.

(** Type class for ghost state associated with channels *)
Class chanG Σ V := ChanG {
  offerG :: ghost_varG Σ (chan_rep.t V);
  offer_lockG :: ghost_varG Σ (option (offer_lock V));
  offer_parked_propG :: savedPropG Σ;
  offer_parked_predG :: savedPredG Σ (V * bool);
}.

Definition chanΣ V : gFunctors :=
  #[ ghost_varΣ (chan_rep.t V); ghost_varΣ (option (offer_lock V));
     savedPropΣ; savedPredΣ  (V * bool) ].

#[global] Instance subG_chanG Σ V :
  subG (chanΣ V) Σ → chanG Σ V.
Proof. solve_inG. Qed.

Section base.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context
  {core_sem : go.CoreSemantics} {pre_sem : go.PredeclaredSemantics}
  {array_sem : go.ArraySemantics} {slice_sem : go.SliceSemantics}.
Local Set Default Proof Using "Type core_sem pre_sem array_sem slice_sem".

Context `{!chanG Σ V}.
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.


(* Remove the later from a saved prop if we have later credits. *)
Lemma saved_prop_lc_agree γ dq1 dq2 P Q :
   £ 1 -∗ saved_prop_own γ dq1 P -∗ saved_prop_own γ dq2 Q -∗ |={⊤}=> (P ≡ Q).
Proof.
  iIntros "Hlc HP HQ".
  iDestruct (saved_prop_agree with "HP HQ") as "Heq".
  iMod (lc_fupd_elim_later with "Hlc Heq") as "H3".
  iModIntro. done.
Qed.

(* FIXME: move higher level. *)
Notation "ptr .[ t , field ]" := (struct_field_ref t field ptr)
  (at level 1, format "ptr .[ t ,  field ]").

(** Maps physical channel states to their heap representations.
    Each state corresponds to specific field values in the Go struct. *)
(* TODO gemini change
        `ch.[channel.Channel t, "XXX"] YYY` into
        `ch.[channel.Channel.ty t :: "XXX"] YYY` into
 *)
Definition chan_phys (ch: loc) (s: chan_phys_state V) : iProp Σ :=
  match s with
    | Closed [] =>
        (∃ (slice_val: slice.t),
            "state" ∷ (ch.[channel.Channel t , "state"] ↦ (W64 6)) ∗
            "slice" ∷ own_slice t slice_val (DfracOwn 1) [] ∗
            "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
            "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val)
    | Closed draining =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 6) ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) draining ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    | Buffered buff =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 0) ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) buff ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    | Idle =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 1) ∗
        "v" ∷ ch.[channel.Channel t, "v"] ↦ v ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    | SndWait v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 2) ∗
        "v" ∷ ch.[channel.Channel t, "v"] ↦ v ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    | RcvWait =>
        ∃ (v:V) (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 3) ∗
        "v" ∷ ch.[channel.Channel t, "v"] ↦ v ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    | SndDone v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 4) ∗
        "v" ∷ ch.[channel.Channel t, "v"] ↦ v ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    | RcvDone v =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch.[channel.Channel t, "state"] ↦ (W64 5) ∗
        "v" ∷ ch.[channel.Channel t, "v"] ↦ v ∗
        "slice" ∷ own_slice t slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap t slice_val (DfracOwn 1) ∗
        "buffer" ∷ ch.[channel.Channel t, "buffer"] ↦ slice_val
    end.

(** Bundles together offer-related ghost state for atomic operations *)
Definition saved_offer (γ : chan_names) (q : Qp)
  (lock_val : option (offer_lock V))
  (parked_prop continuation_prop : iProp Σ) : iProp Σ :=
  ghost_var γ.(offer_lock_name) (DfracOwn q) lock_val ∗
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

Lemma offer_halves_to_idle γ x y parked_prop cont :
  offer_bundle_half γ (Some x) parked_prop cont -∗
   offer_bundle_half γ (Some y) parked_prop cont ==∗
  offer_bundle_empty γ.
Proof.
  iIntros "[Hlock [Hoffer Hcont]]".
  iIntros "[Hlock2 [Hoffer2 Hcont2]]".
  iCombine "Hlock Hlock2" gives %Heq.
  assert (x = y) by (destruct_and!; congruence); subst.
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
  £ 1 -∗
  saved_offer γ (1/2) lock1 parked1 cont1 -∗
  saved_offer γ (1/2) lock2 parked2 cont2 -∗
  |={⊤}=> ⌜lock1 = lock2⌝ ∗
         (parked1 ≡ parked2) ∗ (cont1 ≡ cont2) ∗
         offer_bundle_empty γ.
Proof.
  iIntros "Hlc1".
  iIntros "[Hl1 [Hp1 Hc1]]".
  iIntros "[Hl2 [Hp2 Hc2]]".
  iDestruct (ghost_var_agree with "[$Hl1] [$Hl2]") as %->.
  iDestruct (saved_prop_agree with "[$Hp1] [$Hp2]") as "#Hp_eq".
  iDestruct (saved_prop_agree with "[$Hc1] [$Hc2]") as "#Hc_eq".

  iCombine "Hp_eq Hc_eq" as "Heq".
  iClear "Hp_eq Hc_eq".
  iMod (lc_fupd_elim_later with "Hlc1 Heq") as "[Hp_eq Hc_eq]".
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
  ghost_var γ (DfracOwn q) s.

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

(* NOTE: unused *)
#[local] Lemma chan_rep_combine γ s s' :
  chan_rep_half γ s -∗ chan_rep_half γ s' -∗ chan_rep_full γ s.
Proof.
  iIntros "H1 H2". iDestruct (chan_rep_agree with "H1 H2") as %->.
  iCombine "H1 H2" as "H". done.
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
  | chan_rep.Buffered buf =>
      (* Buffered is only used for buffered channels, and buffer size is bounded
      by capacity *)
      (Z.of_nat (length buf) ≤ cap)%Z ∧ (0 < cap)
  | chan_rep.Closed [] => True              (* Empty closed channels might have been unbuffered, doesn't matter *)
  | chan_rep.Closed draining =>
      (* Draining closed channels are buffered channels, and draining elements
      are bounded by capacity *)
      (Z.of_nat (length draining) ≤ cap) ∧ (0 < cap)
  | _ => cap = 0                            (* All other states are unbuffered *)
  end.

(** ** Channel Ownership Predicate *)

(* chan_cap is directly user accessible *)

(** Represents ownership of a channel with its logical state *)
Definition own_channel (ch: loc) (s: chan_rep.t V) (γ: chan_names) : iProp Σ :=
  "Hchanrepfrag" ∷ chan_rep_half γ.(state_name) s ∗
  "%Hcapvalid" ∷ ⌜chan_cap_valid s (chan_cap γ)⌝.

Lemma own_channel_agree ch s s' γ :
   own_channel ch s γ -∗ own_channel ch s' γ -∗ ⌜s = s'⌝.
Proof.
  iIntros "H1 H2". iNamedSuffix "H1" "1". iNamedSuffix "H2" "2".
  iDestruct (ghost_var_agree with "[$Hchanrepfrag1] [$Hchanrepfrag2]") as "%Hag".
  unfold chan_cap_valid in *.
  by iApply (ghost_var_agree with "Hchanrepfrag1 Hchanrepfrag2").
Qed.

(* Needs [chan_cap_valid s'' cap] as precondition? *)
Lemma own_channel_halves_update s'' ch s s' γ :
  chan_cap_valid s'' (chan_cap γ) →
  own_channel ch s γ -∗ own_channel ch s' γ ==∗
  own_channel ch s'' γ ∗ own_channel ch s'' γ.
Proof.
  intros Hvalid.
  iIntros "(Hv1 & %) (Hv2 & %)". rewrite /named.
  iMod (chan_rep_halves_update with "Hv1 Hv2") as "[$ $]".
  iFrame "#∗".
  iPureIntro.
  auto.
Qed.

Lemma own_channel_buffer_size ch γ buf :
  own_channel ch (chan_rep.Buffered buf) γ -∗
  ⌜Z.of_nat (length buf) ≤ chan_cap γ⌝.
Proof.
  iNamed 1.
  simpl in Hcapvalid.
  iPureIntro. lia.
Qed.

Lemma own_channel_drain_size ch γ draining :
  own_channel ch (chan_rep.Closed draining) γ -∗
  ⌜Z.of_nat (length draining) ≤ chan_cap γ⌝.
Proof.
  iNamed 1.
  pose proof (chan_cap_bound γ).
  simpl in Hcapvalid.
  destruct draining.
  { simpl. iPureIntro; lia. }
  iPureIntro. lia.
Qed.

(** uncurry *)
Definition K (Φ : V → bool → iProp Σ) : (V * bool) → iProp Σ :=
  λ '(v,b), Φ v b.

(* TODO: rename this; no need to save characters by writing just constants in
   `rcv` (we would've done snd otherwise) *)

(** Inner atomic update for receive completion (second phase of handshake) *)
Definition rcv_au_inner ch (γ: chan_names) (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_channel ch s γ ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Sender has committed, complete the exchange *)
    | chan_rep.SndCommit v => own_channel ch chan_rep.Idle γ ={∅,⊤}=∗ Φ v true
    (* Case: Channel is closed with no messages *)
    | chan_rep.Closed [] => own_channel ch s γ ={∅,⊤}=∗ Φ (zero_val V) false
    | _ => True
    end).

(** Slow path receive: may need to block and wait *)
Definition rcv_au_slow ch (γ: chan_names) (Φ : V → bool → iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Sender is waiting, can complete immediately *)
    | chan_rep.SndPending v =>
          own_channel ch chan_rep.RcvCommit γ ={∅,⊤}=∗ Φ v true
    (* Case: Channel is idle, need to wait for sender *)
    | chan_rep.Idle =>
          own_channel ch (chan_rep.RcvPending) γ ={∅,⊤}=∗
              rcv_au_inner ch γ Φ
    (* Case: Channel is closed *)
    | chan_rep.Closed [] => own_channel ch s γ ={∅,⊤}=∗ Φ (zero_val V) false
    (* Case: Closed but still have values to drain *)
    | chan_rep.Closed (v::rest) => (own_channel ch (chan_rep.Closed rest) γ ={∅,⊤}=∗ Φ v true)
    (* Case: Buffered channel with values in buffer *)
    | chan_rep.Buffered (v::rest) => (own_channel ch (chan_rep.Buffered rest) γ ={∅,⊤}=∗ Φ v true)
    | _ => True
    end).

(** Fast path receive: immediate completion when possible *)
Definition rcv_au_fast ch γ (Φ : V → bool → iProp Σ) Φnotready : iProp Σ :=
  (|={⊤,∅}=>
     ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
           "Hcont" ∷
             match s with
             (* Case: Sender is waiting, can complete immediately *)
             | chan_rep.SndPending v =>
                 own_channel ch chan_rep.RcvCommit γ ={∅,⊤}=∗ Φ v true
             (* Case: Channel is closed *)
             | chan_rep.Closed [] => own_channel ch s γ ={∅,⊤}=∗ Φ (zero_val V) false
             (* Case: Channel is closed but still has values to drain *)
             | chan_rep.Closed (v::rest) => (own_channel ch (chan_rep.Closed rest) γ ={∅,⊤}=∗ Φ v true)
             (* Case: Buffered channel with values *)
             | chan_rep.Buffered (v::rest) => (own_channel ch (chan_rep.Buffered rest) γ ={∅,⊤}=∗ Φ v true)
             | _ => True
             end) ∧
  Φnotready.

(** See [send_au_fast_alt] documentation below.  *)
Definition rcv_au_fast_alt ch γ (Φ : V → bool → iProp Σ) Φnotready : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Sender is waiting, can complete immediately *)
    | chan_rep.SndPending v =>
          own_channel ch chan_rep.RcvCommit γ ={∅,⊤}=∗ Φ v true
    (* Case: Channel is closed *)
    | chan_rep.Closed [] => own_channel ch s γ ={∅,⊤}=∗ Φ (zero_val V) false
    (* Case: Channel is closed but still has values to drain *)
    | chan_rep.Closed (v::rest) => (own_channel ch (chan_rep.Closed rest) γ ={∅,⊤}=∗ Φ v true)
    (* Case: Buffered channel with values *)
    | chan_rep.Buffered (v::rest) => (own_channel ch (chan_rep.Buffered rest) γ ={∅,⊤}=∗ Φ v true)
    | _ => (own_channel ch s γ ={∅,⊤}=∗ Φnotready)
    end).

Lemma blocking_rcv_implies_nonblocking ch γ (Φ : V → bool → iProp Σ) :
  rcv_au_slow ch γ Φ -∗
  rcv_au_fast ch γ Φ True.
Proof.
  iIntros "Hau".
  iSplitL; last done. iMod "Hau" as (s) "[Hoc Hcont]".
  iModIntro. iExists s. iFrame "Hoc".
  destruct s; try done.
Qed.

(** Inner atomic update for send completion (second phase of handshake) *)
Definition send_au_inner ch (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_channel ch s γ ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Receiver has committed, complete the exchange *)
    | chan_rep.RcvCommit =>
           own_channel ch chan_rep.Idle γ ={∅,⊤}=∗ Φ
    (* Case: Channel is closed, operation fails *)
    | chan_rep.Closed draining => False
    | _ => True
    end).

(** Slow path send: may need to block and wait *)
Definition send_au_slow ch (v : V) (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
     "Hcont" ∷
    (match s with
    (* Case: Receiver is waiting, can complete immediately *)
    | chan_rep.RcvPending =>
        own_channel ch (chan_rep.SndCommit v) γ ={∅,⊤}=∗ Φ
    (* Case: Channel is idle, need to wait for receiver *)
    | chan_rep.Idle =>
          own_channel ch (chan_rep.SndPending v) γ ={∅,⊤}=∗
              send_au_inner ch γ Φ
    (* Case: Channel is closed, client must rule this out *)
    | chan_rep.Closed draining => False
    (* Case: Buffered channel *)
    | chan_rep.Buffered buff =>
        (* own_channel implies new buffer size is <= cap, so the whole update is
        equivalent to True if no space is available *)
        (own_channel ch (chan_rep.Buffered (buff ++ [v])) γ ={∅,⊤}=∗ Φ)
    | _ => True
    end).

(** Fast path send: immediate completion when possible *)
Definition send_au_fast ch (v : V) γ Φ Φnotready : iProp Σ :=
  (|={⊤,∅}=>
     ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
           "Hcont" ∷
             match s with
             (* Case: Receiver is waiting, can complete immediately *)
             | chan_rep.RcvPending =>
                 own_channel ch (chan_rep.SndCommit v) γ ={∅,⊤}=∗ Φ
             (* Case: Channel is closed, client must rule this out *)
             | chan_rep.Closed draining => False
             (* Case: Buffered channel *)
             | chan_rep.Buffered buff =>
                   (own_channel ch (chan_rep.Buffered (buff ++ [v])) γ ={∅,⊤}=∗ Φ)
             | _ => True
             end) ∧
  Φnotready.

(* Special case update that only works if the channel is known to be buffered. *)
Definition buffered_send_au ch (v : V) γ Φ : iProp Σ :=
  |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
          "Hcont" ∷
            match s with
            | chan_rep.Buffered buf => own_channel ch (chan_rep.Buffered (buf ++ [v])) γ ={∅,⊤}=∗ Φ
            | chan_rep.Closed _ => False
            | _ => True
            end.

(** This is an alternate specification for nonblocking chan send that allows for
    proving a caller-chosen [Φnotready] in case the send does not occur. If no
    cases are ready in the containing select statement, the [Φnotready]s will be
    passed as a precondition to the default handler, allowing for reasoning
    about programs in which it should be _impossible_ to reach the default.

    This is not implied by nor does it imply [send_au_fast].
    - [send_au_fast -∗ send_au_fast_alt]: the default spec does not provide
      [|={∅,⊤}=>] in the notready case, but it's necessary to somehow close all
      invariants in [send_au_fast_alt].
    - [send_au_fast_alt -∗ send_au_fast]: under [send_au_fast_alt], the notready
      predicate is only known to be true if the channel is _actually_ not ready,
      whereas [send_au_fast] requires proving it's always OK to skip a case.

    The writer of this spec does not know a different au which is weaker than
    both [send_au_fast] and [send_au_fast_alt] and which is provable with
    [TrySend]. If such a thing exists, it may enable having a canonical spec for
    nonblocking channel operations. To be worth it, it would also require having
    a canonical version of the select spec, for which there are currently two
    (see [golang/theory/chan.v]). *)
Definition send_au_fast_alt ch (v : V) γ Φ Φnotready : iProp Σ :=
  |={⊤,∅}=>
    ▷∃ s, "Hoc" ∷ own_channel ch s γ ∗
          "Hcont" ∷
            match s with
            (* Case: Receiver is waiting, can complete immediately *)
            | chan_rep.RcvPending =>
                own_channel ch (chan_rep.SndCommit v) γ ={∅,⊤}=∗ Φ
            (* Case: Channel is closed, client must rule this out *)
            | chan_rep.Closed draining => False
            (* Case: Buffered channel *)
            | chan_rep.Buffered buff =>
                if decide (length buff < chan_cap γ) then
                  (own_channel ch (chan_rep.Buffered (buff ++ [v])) γ ={∅,⊤}=∗ Φ)
                else
                  (own_channel ch s γ ={∅,⊤}=∗ Φnotready)
            | _ => (own_channel ch s γ ={∅,⊤}=∗ Φnotready)
            end.

Lemma blocking_send_implies_nonblocking ch v γ (Φ : iProp Σ) :
  send_au_slow ch v γ Φ -∗
  send_au_fast ch v γ Φ True.
Proof.
  iIntros "Hchan".
  iSplitL; last done.
  iMod "Hchan" as (s) "[Hoc Hcont]".
  iModIntro. iExists s. iFrame "Hoc".
  destruct s; try done.
Qed.

Definition close_au ch (γ: chan_names) (Φ : iProp Σ) : iProp Σ :=
   |={⊤,∅}=>
    ▷∃ s, "Hocinner" ∷ own_channel ch s γ ∗
     "Hcontinner" ∷
    (match s with
    (* Case: Ready to close unbuffered *)
    | chan_rep.Idle =>
           own_channel ch (chan_rep.Closed []) γ ={∅,⊤}=∗ Φ
    (* Case: Buffered, go to draining *)
    | chan_rep.Buffered buff =>
          own_channel ch (chan_rep.Closed buff) γ ={∅,⊤}=∗ Φ
    (* Case: Channel is closed already, panic *)
    | chan_rep.Closed draining => False
    | _ => True
    end).


(** Maps physical states to their logical representations with ghost state.
    This is the key invariant that connects the physical implementation
    to the logical specifications. *)
Definition chan_logical (ch: loc) (γ : chan_names) (s : chan_phys_state V): iProp Σ :=
  match s with
  | Idle =>
       ∃ (Φr: V → bool → iProp Σ),
           "Hoffer" ∷ offer_bundle_empty γ ∗
           "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (K Φr) ∗
            own_channel ch chan_rep.Idle γ

  | SndWait v =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ),
          "Hoffer" ∷ offer_bundle_half γ (Some (Snd v)) P Φ ∗
          "HP" ∷ P ∗
          "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (K Φr) ∗
          "Hau" ∷ (P -∗ send_au_slow ch v γ Φ) ∗
           own_channel ch chan_rep.Idle γ

  | RcvWait =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
         "Hoffer" ∷ offer_bundle_half γ (Some Rcv) P True ∗
         "HP" ∷ P ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (K Φr) ∗
         "Hau" ∷ (P -∗ rcv_au_slow ch γ Φr) ∗
         own_channel ch chan_rep.Idle γ

  | SndDone v =>
       ∃ (P: iProp Σ) (Φr: V → bool → iProp Σ),
       "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn (1/2)) (K Φr) ∗
       "Hoffer" ∷ offer_bundle_half γ (Some Rcv) P True ∗
       "Hau" ∷ rcv_au_inner ch γ Φr ∗
       own_channel ch (chan_rep.SndCommit v) γ

  | RcvDone v =>
       ∃ (P: iProp Σ) (Φ: iProp Σ) (Φr: V → bool → iProp Σ),
         "Hoffer" ∷ offer_bundle_half γ (Some (Snd v)) P Φ ∗
         "Hpred" ∷ saved_pred_own γ.(offer_parked_pred_name) (DfracOwn 1) (K Φr) ∗
         "Hau" ∷ send_au_inner ch γ Φ ∗
       own_channel ch chan_rep.RcvCommit γ

  | Closed [] =>
          own_channel ch (chan_rep.Closed []) γ ∗
           "Hoffer" ∷ (⌜chan_cap γ = 0⌝ -∗ offer_bundle_empty γ)

  | Closed draining =>
          own_channel ch (chan_rep.Closed draining) γ

  | Buffered buff =>
          own_channel ch (chan_rep.Buffered buff) γ
  end.

(** The main invariant protected by the channel's mutex.
    This connects the physical heap state with the logical state. *)
Definition chan_inv_inner (ch: loc) (γ: chan_names) : iProp Σ :=
  ∃ (s : chan_phys_state V),
    "phys" ∷ chan_phys ch s ∗
    "offer" ∷ chan_logical ch γ s.

(* FIXME: is_channel should take [t] explicitly. *)
(** The public predicate that clients use to interact with channels.
    This is persistent and provides access to the channel's capabilities. *)
Definition is_channel (ch: loc) (γ: chan_names) : iProp Σ :=
  ∃ (mu_loc: loc),
    "#cap" ∷ ch.[channel.Channel t, "cap"] ↦□ (W64 (chan_cap γ)) ∗
    "#mu" ∷ ch.[channel.Channel t, "mu"] ↦□ mu_loc ∗
    "#lock" ∷ is_lock mu_loc (chan_inv_inner ch γ) ∗
    "%Hnotnull" ∷ ⌜ ch ≠ chan.nil ⌝.
#[global] Typeclasses Opaque is_channel.
#[global] Opaque is_channel.
#[local] Transparent is_channel.
#[local] Typeclasses Transparent is_channel.

Global Instance is_channel_pers ch γ : Persistent (is_channel ch γ).
Proof. apply _. Qed.

Global Instance own_channel_timeless ch s γ : Timeless (own_channel ch s γ).
Proof. apply _. Qed.

Lemma is_channel_not_null ch γ:
  is_channel ch γ -∗ ⌜ch ≠ null⌝.
Proof. iNamed 1. done. Qed.

End base.

#[global] Opaque is_channel own_channel.
