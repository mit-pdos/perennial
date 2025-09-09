From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_init.
From New.proof Require Import proof_prelude.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import auth gset.
Require Import New.proof.sync.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

(* Inductive mathematical representation *)
Module chan_rep.
Inductive t (V : Type) : Type :=
| Buffered (buff : list V)
| Idle
| SndWait (v : V)
| RcvWait  
| SndDone (v : V)
| RcvDone
| Closed (draining : list V).
  
  (* Global Arguments for clean syntax *)
  Global Arguments Buffered {V}.
  Global Arguments Idle {V}.
  Global Arguments SndWait {V}.
  Global Arguments RcvWait {V}.
  Global Arguments SndDone {V}.
  Global Arguments RcvDone {V}.
  Global Arguments Buffered {V}.
  Global Arguments Closed {V}.

  Definition buffer_valid {V} (c : chan_rep.t V) (cap: w64) : Prop :=
  match c with
  | chan_rep.Buffered buff =>
    length buff ≤ uint.Z cap
  | chan_rep.Closed draining =>
    length draining ≤ uint.Z cap
  | _ => True (* Invariant is vacuously true for unbuffered or empty closed states *)
  end.

End chan_rep.

(* Ghost state management *)
Record chan_names := {
  offer_name : gname;   (* For unbuffered offer/accept protocol *)
  state_name : gname;   (* For the main channel state *)
}.

Class chanGhostStateG Σ V := ChanGhostStateG {
  offer_tokG :: ghost_varG Σ (option V);
  chan_repG :: ghost_varG Σ (chan_rep.t V);
}.

Definition chanGhostStateΣ V : gFunctors :=
  #[ ghost_varΣ (option V); ghost_varΣ (chan_rep.t V) ].

#[global] Instance subG_chanGhostStateG Σ V :
  subG (chanGhostStateΣ V) Σ → chanGhostStateG Σ V.
Proof. solve_inG. Qed.

Section base.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!chanGhostStateG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
  
(* Offer tokens for unbuffered channels *)
Definition idle_tok (γ : gname) : iProp Σ :=
    ghost_var γ 1%Qp None.
  
(* Send offer is outgoing, we can unlock the channel and know that the channel was
  untouched other then by a receiver accepting the offer *)
Definition snd_wait_tok (γ : gname) (v: V) : iProp Σ :=
    ghost_var γ (1/2%Qp) (Some v).

(* Almost symmetric to snd_wait_tok, but we don't need to encode a value *)
Definition rcv_wait_tok (γ : gname) : iProp Σ :=
    ghost_var γ (1/2%Qp) None.

Lemma idle_to_two_snd_wait γ v :
  idle_tok γ ==∗ snd_wait_tok γ v ∗ snd_wait_tok γ v.
Proof.
  iIntros "Hidle".
  iMod (ghost_var_update (Some v) γ _ with "Hidle") as "Hfull".
  iDestruct "Hfull" as "[Hs1 Hs2]".
  iModIntro. iFrame.
Qed.

Lemma idle_to_two_rcv_wait γ :
  idle_tok γ ==∗ rcv_wait_tok γ ∗ rcv_wait_tok γ.
Proof.
  iIntros "Hidle".
  iMod (ghost_var_update _ γ _ with "Hidle") as "Hfull".
  iDestruct "Hfull" as "[Hs1 Hs2]".
  iModIntro. iFrame.
Qed.

Lemma two_snd_wait_to_idle γ v1 v2 :
  snd_wait_tok γ v1 -∗ snd_wait_tok γ v2 ==∗ idle_tok γ.
Proof.
  iIntros "Hs1 Hs2".
  iCombine "Hs1" "Hs2" as "Hfull".
  iMod (ghost_var_update None γ _ with "Hfull") as "Hidle".
  iModIntro. iExact "Hidle".
Qed.

Lemma two_rcv_wait_to_idle γ :
  rcv_wait_tok γ -∗ rcv_wait_tok γ ==∗ idle_tok γ.
Proof.
  iIntros "Hs1 Hs2".
  iCombine "Hs1" "Hs2" as "Hfull".
  iMod (ghost_var_update None γ _ with "Hfull") as "Hidle".
  iModIntro. iExact "Hidle".
Qed.


Definition offer_auth (γ : chan_names) (s : chan_rep.t V) : iProp Σ :=
  match s with
  | chan_rep.SndWait v   => snd_wait_tok γ.(offer_name) v
  | chan_rep.RcvWait     => rcv_wait_tok γ.(offer_name)
  | chan_rep.SndDone v   => rcv_wait_tok γ.(offer_name)
  | chan_rep.RcvDone     =>  ∃ v, snd_wait_tok γ.(offer_name) v
  | _  => idle_tok γ.(offer_name)
  end.

Lemma offer_snd_coherent γ (s : chan_rep.t V) v :
  offer_auth γ s -∗ snd_wait_tok γ.(offer_name) v -∗
  ⌜s = chan_rep.SndWait v ∨ s = chan_rep.RcvDone ⌝.
Proof.
  iIntros "Hpiece Htok".
  destruct s; simpl.
  - 
     iDestruct (ghost_var_valid_2 with "[$Hpiece] [$Htok]") as "%Hinvalid".
     destruct Hinvalid as [Hbad _]. apply  (Qp.not_add_le_r 1 (1/2)) in Hbad. contradiction.
  - 
     iDestruct (ghost_var_valid_2 with "[$Hpiece] [$Htok]") as "%Hinvalid".
     destruct Hinvalid as [Hbad _]. apply  (Qp.not_add_le_r 1 (1/2)) in Hbad. contradiction.
  - iDestruct (ghost_var_agree with "Hpiece Htok") as %Heq. inversion Heq. subst. iPureIntro. left. reflexivity.
  - iDestruct (ghost_var_agree with "Hpiece Htok") as %Eq.  
iPureIntro.
exfalso. discriminate Eq. 
  -  iDestruct (ghost_var_agree with "Hpiece Htok") as %Eq. 
iPureIntro.
exfalso. discriminate Eq.
  - iPureIntro. right. done.
  - iDestruct (ghost_var_valid_2 with "[$Hpiece] [$Htok]") as "%Hinvalid".
    destruct Hinvalid as [Hbad _]. apply  (Qp.not_add_le_r 1 (1/2)) in Hbad. contradiction.
Qed.

Lemma offer_rcv_coherent γ (s : chan_rep.t V) :
  offer_auth γ s -∗ rcv_wait_tok γ.(offer_name) -∗
  ⌜s = chan_rep.RcvWait ∨ ∃ v, s = chan_rep.SndDone v⌝.
Proof.
  iIntros "Hpiece Htok".
  destruct s; simpl in *.
  - iDestruct (ghost_var_valid_2 with "Hpiece Htok") as %[Hle _].
    iPureIntro. exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hle).
  - iDestruct (ghost_var_valid_2 with "Hpiece Htok") as %[Hle _]. 
    iPureIntro. exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hle).
  - iDestruct (ghost_var_agree with "Hpiece Htok") as %Eq. iPureIntro. exfalso. discriminate Eq.
  - iPureIntro. left; reflexivity.
  - iPureIntro. right. exists v. done.
  - iNamed "Hpiece".
    iDestruct (ghost_var_agree with "Hpiece Htok") as %Eq. iPureIntro. exfalso. discriminate Eq.
  - iDestruct (ghost_var_valid_2 with "Hpiece Htok") as %[Hle _]. 
    iPureIntro. exfalso. exact (Qp.not_add_le_l 1 (1/2)%Qp Hle).
Qed.


(* ghost state for channel mathematical representation. *)
Definition chan_rep (γ : gname) (q : Qp) (s : chan_rep.t V) : iProp Σ :=
  ghost_var γ q s.
Notation chan_rep_full γ s := (chan_rep γ 1 s).
Notation chan_rep_half γ s := (chan_rep γ (1/2)%Qp s).
Notation chan_rep_auth γ s := (chan_rep_half γ s).
Notation chan_rep_frag γ s := (chan_rep_half γ s).
Lemma chan_rep_update γ s s' :
  chan_rep_full γ s ==∗ chan_rep_full γ s'.
Proof.
  iApply (ghost_var_update s' γ s). Qed.
Lemma chan_rep_agree γ q1 q2 s s' :
  chan_rep γ q1 s -∗ chan_rep γ q2 s' -∗ ⌜s = s'⌝.
Proof. iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2"). Qed.

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
Admitted.


(* Physical state helper utility for the channel model that uses a simple blocking
   queue for buffered channels and an offer state machine for unbuffered channels
*)

  (* Unified physical state predicate *)
  Definition chan_phys (ch: loc) (s: chan_rep.t V) 
       : iProp Σ :=
    match s with
    | chan_rep.Closed [] => 
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 6) ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.Closed draining =>
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 6) ∗
        "slice" ∷ own_slice slice_val (DfracOwn 1) draining ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.Buffered buff => 
        ∃ (slice_val: slice.t),
        "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 0) ∗
        "slice" ∷ own_slice slice_val (DfracOwn 1) buff ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.Idle => 
      ∃ (v:V) (slice_val: slice.t),
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 1) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.SndWait v => 
      ∃ (slice_val: slice.t),
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 2) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗  
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.RcvWait => 
      ∃ (v:V) (slice_val: slice.t),
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 3) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.SndDone v => 
      ∃ (slice_val: slice.t),
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 4) ∗
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗  
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    | chan_rep.RcvDone => 
      ∃ (v:V) (slice_val: slice.t),
      "state" ∷ ch ↦s[(channel.Channel.ty t) :: "state"] (W64 5) ∗ 
      "v" ∷ ch ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
        "slice" ∷ own_slice slice_val (DfracOwn 1) ([] : list V) ∗
        "slice_cap" ∷ own_slice_cap V slice_val (DfracOwn 1) ∗ 
        "buffer" ∷ ch ↦s[(channel.Channel.ty t) :: "buffer"] slice_val
    end.

(* TODO: Add select physical state *)

(* Ownership *)

Definition cap_rel (cap : w64) (s : chan_rep.t V) : Prop :=
  match s with
  (* Once we're closed and drained, unbuffered/buffered work the same *)
  | chan_rep.Closed []                      => True
  | chan_rep.Buffered _ | chan_rep.Closed _ => cap ≠ W64 0 ∧ sint.Z cap > 0
  | _                                       => cap = W64 0
  end.
  
  (* What goes inside the mutex invariant *)
  Definition chan_inv_inner (ch: loc) (cap:w64) (γ: chan_names) : iProp Σ :=
    ∃ (s : chan_rep.t V),
      "phys" ∷ chan_phys ch s ∗
      "auth" ∷ chan_rep_auth γ.(state_name) s ∗
      "%Hcap"  ∷  
        ⌜cap_rel cap s⌝
      ∗  
      (* Offer ghost state for unbuffered channels *)
      "offer"  ∷ offer_auth γ s.
      
  (* Public channel interface - what clients see *)
  Definition is_channel (ch: loc) (cap :w64) (γ: chan_names) : iProp Σ :=
    ∃ (mu_loc: loc) (s: chan_rep.t V),
      "#cap" ∷ ch ↦s[(channel.Channel.ty t) :: "cap"]□ cap ∗
      "#mu" ∷ ch ↦s[(channel.Channel.ty t) :: "lock"]□ mu_loc ∗
      "#lock" ∷ is_Mutex mu_loc (chan_inv_inner ch cap γ).
      
  (* Fractional ownership for protocol development *)
  Definition own_channel (ch: loc) (s: chan_rep.t V) (cap: w64) (γ: chan_names) : iProp Σ :=
     "Hchanrepfrag" ∷ chan_rep_frag γ.(state_name) s ∗ "%Hbuffvalid" ∷ ⌜ chan_rep.buffer_valid s cap ⌝.

(* Helper lemmas *)
  
  (* Persistence *)
  Global Instance is_channel_pers ch cap γ : Persistent (is_channel ch cap γ).
  Proof.
  Admitted.
  
  (* Timelessness *)
  Global Instance own_channel_timeless ch s cap γ : Timeless (own_channel ch s cap γ).
  Proof.
  Admitted.

  Lemma is_channel_not_null ch γ cap :
    is_channel ch γ cap -∗ ⌜ch ≠ null⌝.
  Proof.
  Admitted.
End base.



