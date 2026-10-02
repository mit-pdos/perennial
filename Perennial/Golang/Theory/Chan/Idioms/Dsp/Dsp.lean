/-
Port of `new/golang/theory/chan/idioms/dsp/dsp.v`: Dependent Separation Protocols (DSP)
over Go channels.

This file implements dependent separation protocols using bidirectional Go channels.

Key concepts:
- Protocol endpoints communicate via two Go channels
- LR channel: left endpoint sends values to right endpoint
- RL channel: right endpoint sends values to left endpoint
- Protocol state is tracked using Actris iProto with sum types
- Channel closure is protocol-aware - only allowed when protocol permits

Lean notes: Rocq's `dspG Σ V` (`protoG Σ V`) is `allG GF` plus `[Pos.Countable V]`
(see `DspGhostTheory.lean`). The telescopic message `<?.. x> MSG v x {{ P x }}; p x` is
written `<?> iMsg_texist (fun x => iMsg_base (v x) (P x) (p x))`.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Dsp.DspGhostTheory
import Perennial.Ghost.Token

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

/-- Rocq `dspG Σ V`: just the protocol ghost state (the universal `allG`). -/
abbrev dspG (GF : BundledGFunctors) := allG GF

structure dsp_names where
  DSPNames ::
  chan_lr_name : chan_names
  chan_rl_name : chan_names
  /-- Token for excluding closed state of lr channel -/
  token_lr_name : GName
  /-- Token for excluding closed state of rl channel -/
  token_rl_name : GName
  /-- Protocol ownership for lr channel -/
  dsp_lr_name : GName
  /-- Protocol ownership for rl channel -/
  dsp_rl_name : GName

def flip_dsp_names (γ : dsp_names) : dsp_names :=
  dsp_names.DSPNames γ.chan_rl_name γ.chan_lr_name γ.token_rl_name γ.token_lr_name
    γ.dsp_rl_name γ.dsp_lr_name

/-- Defines when Go channel state matches expected message queue. -/
def buffer_matches {V : Type} (state : chanstate.t V) (vs : List V) : Prop :=
  match state with
  | .Buffered queue => vs = queue
  | .SndPending v | .SndCommit v => vs = [v]
  | .Closed drain => vs = drain
  | _ => vs = []

section dsp
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

/-- The namespace of the session invariant (Rocq `N`). -/
def dspN : Namespace := nroot .@ "dsp_chan"

/-- Ownership of the closing obligation of one direction. -/
def dsp_close_res (s : chanstate.t V) (γp γt : GName) : IProp GF :=
  match s with
  | .Closed _ => iProto_own γp (END : iProto GF V)
  | _ => token γt

/-- DSP session invariant - owns both channels and maintains protocol state. -/
def dsp_session_inv (γ : dsp_names) (lr_chan rl_chan : loc) : IProp GF :=
  iprop(∃ (lr_state rl_state : chanstate.t V) (vsl vsr : List V),
    ⌜buffer_matches lr_state vsl⌝ ∗
    ⌜buffer_matches rl_state vsr⌝ ∗
    own_chan γ.chan_lr_name V lr_state ∗
    own_chan γ.chan_rl_name V rl_state ∗
    dsp_close_res lr_state γ.dsp_lr_name γ.token_lr_name ∗
    dsp_close_res rl_state γ.dsp_rl_name γ.token_rl_name ∗
    iProto_ctx γ.dsp_lr_name γ.dsp_rl_name vsl vsr)

theorem dsp_session_inv_sym (γ : dsp_names) (lr_chan rl_chan : loc) :
    dsp_session_inv (V := V) γ lr_chan rl_chan ⊣⊢
      dsp_session_inv (V := V) (flip_dsp_names γ) rl_chan lr_chan := by
  constructor
  · unfold dsp_session_inv
    iintro ⟨%ls, %rs, %vsl, %vsr, %H1, %H2, Hl, Hr, Hcl, Hcr, Hp⟩
    ihave Hp := iProto_ctx_sym _ _ _ _ $$ Hp
    iexists rs, ls, vsr, vsl
    simp only [flip_dsp_names]
    iframe
    ipureintro
    exact ⟨H2, H1⟩
  · unfold dsp_session_inv
    iintro ⟨%ls, %rs, %vsl, %vsr, %H1, %H2, Hl, Hr, Hcl, Hcr, Hp⟩
    ihave Hp := iProto_ctx_sym _ _ _ _ $$ Hp
    iexists rs, ls, vsr, vsl
    simp only [flip_dsp_names] at *
    iframe
    ipureintro
    exact ⟨H2, H1⟩

/-- DSP session context - public interface with persistent channel handles. -/
def dsp_session (γ : dsp_names) (lr_chan rl_chan : loc) : IProp GF :=
  iprop(is_chan lr_chan γ.chan_lr_name V ∗
    is_chan rl_chan γ.chan_rl_name V ∗
    inv dspN (dsp_session_inv (V := V) γ lr_chan rl_chan))

instance dsp_session_persistent (γ : dsp_names) (lr_chan rl_chan : loc) :
    Persistent (dsp_session (V := V) γ lr_chan rl_chan) := by
  unfold dsp_session; infer_instance

/-- Left endpoint - can send via lr_chan, receive via rl_chan. -/
def dsp_endpoint (γ : dsp_names) (chans : chan.t × chan.t) (p : Option (iProto GF V)) :
    IProp GF :=
  iprop(dsp_session (V := V) γ chans.1 chans.2 ∗
    (match p with
     | none => token γ.token_lr_name
     | some p => iProto_own γ.dsp_lr_name p))

scoped notation:20 c " ↣{" γ "} " p => dsp_endpoint γ c (some p)
scoped notation:20 "↯{" γ "} " c => dsp_endpoint γ c none

omit [IntoValTyped (GF := GF) V t] in
instance dsp_endpoint_ne (γ : dsp_names) (c : chan.t × chan.t) :
    NonExpansive (dsp_endpoint (V := V) γ c) where
  ne n p1 p2 h := by
    unfold dsp_endpoint
    refine BI.sep_ne.ne .rfl ?_
    rcases p1 with _ | p1 <;> rcases p2 with _ | p2
    · exact .rfl
    · exact h.elim
    · exact h.elim
    · exact (iProto_own_ne γ.dsp_lr_name).ne h

theorem iProto_pointsto_le (γ : dsp_names) (c : chan.t × chan.t) (p1 p2 : iProto GF V) :
    (c ↣{γ} p1) ⊢ ▷ (p1 ⊑ p2) -∗ (c ↣{γ} p2) := by
  unfold dsp_endpoint
  iintro ⟨#Hc, Hp⟩ Hle'
  iframe Hc
  iapply iProto_own_le $$ Hp Hle'

/-- Initialize a new DSP session from basic channels. -/
theorem dsp_session_init (E : CoPset) (lr_chan rl_chan : loc) (lr_state rl_state : chanstate.t V)
    (γlr_names γrl_names : chan_names) (p : iProto GF V)
    (Hlr : lr_state = .Idle ∨ lr_state = .Buffered [])
    (Hrl : rl_state = .Idle ∨ rl_state = .Buffered []) :
    ⊢ is_chan lr_chan γlr_names V -∗ is_chan rl_chan γrl_names V -∗
      own_chan γlr_names V lr_state -∗ own_chan γrl_names V rl_state ={E}=∗
      ∃ γdsp1 γdsp2, ((lr_chan, rl_chan) ↣{γdsp1} p) ∗
        ((rl_chan, lr_chan) ↣{γdsp2} iProto_dual p) := by
  iintro #Hcl_is #Hcr_is Hcl_own Hcr_own
  imod iProto_init p with ⟨%γl, %γr, Hctx, Hpl, Hpr⟩
  imod token_alloc with ⟨%γtl, Htl⟩
  imod token_alloc with ⟨%γtr, Htr⟩
  imod inv_alloc dspN E (dsp_session_inv (V := V)
      (dsp_names.DSPNames γlr_names γrl_names γtl γtr γl γr) lr_chan rl_chan)
    $$ [Hcl_own Hcr_own Htl Htr Hctx] with #Hinv
  · inext
    unfold dsp_session_inv
    iexists lr_state, rl_state, [], []
    rcases Hlr with rfl | rfl <;> rcases Hrl with rfl | rfl <;>
      simp only [dsp_close_res, buffer_matches] <;> iframe <;> ipureintro <;> simp
  imodintro
  iexists (dsp_names.DSPNames γlr_names γrl_names γtl γtr γl γr),
    (flip_dsp_names (dsp_names.DSPNames γlr_names γrl_names γtl γtr γl γr))
  unfold dsp_endpoint dsp_session
  dsimp only
  isplitl [Hpl]
  · iframe
    iframe #
  · rw [← (dsp_session_inv_sym (V := V) _ lr_chan rl_chan).to_eq]
    simp only [flip_dsp_names]
    iframe
    iframe #

omit [IntoValTyped (GF := GF) V t] in
theorem iMsg_base_true_car (v : V) (p : iProto GF V) :
    ⊢ (iMsg_base (GF := GF) v iprop(True) p).car v (Later.next p) := by
  simp only [iMsg_base_car]
  isplitl []
  · ipureintro; trivial
  isplitl []
  · iapply (internalEq.refl (P := iprop(True)))
    itrivial
  · itrivial

set_option maxHeartbeats 400000 in
omit [IntoValTyped (GF := GF) V t] in
/-- Endpoint sends value. -/
theorem dsp_send_au (γ : dsp_names) (lr_chan rl_chan : loc) (v : V) (p : iProto GF V)
    (Φ : IProp GF) :
    ⊢ £ 1 -∗ ((lr_chan, rl_chan) ↣{γ} (<!> iMsg_base v iprop(True) p)) -∗
      ▷ (((lr_chan, rl_chan) ↣{γ} p) -∗ Φ) -∗
      send_au γ.chan_lr_name v Φ := by
  unfold dsp_endpoint dsp_session send_au
  iintro Hlc ⟨⟨#Hcl, #Hcr, #HI⟩, Hp⟩ HΦ
  dsimp only
  iinv HI with IH Hclose
  unfold dsp_session_inv
  icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose'
  inext
  iexists ls
  iframe Hownl
  rcases ls with buff | _ | v0 | _ | v0 | _ | d
  all_goals dsimp only [buffer_matches, dsp_close_res] at H1 ⊢
  case Buffered =>
    subst H1
    iintro Hownl
    imod iProto_send _ _ _ _ _ v p $$ Hctx Hp [] with ⟨Hctx, Hown⟩
    · iapply iMsg_base_true_car
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists (.Buffered (vsl ++ [v])), rs, vsl ++ [v], vsr
      iframe
      ipureintro
      exact ⟨rfl, H2⟩
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Idle =>
    subst H1
    iintro Hownl
    imod iProto_send _ _ _ _ _ v p $$ Hctx Hp [] with ⟨Hctx, Hown⟩
    · iapply iMsg_base_true_car
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists (.SndPending v), rs, (([] : List V) ++ [v]), vsr
      iframe
      ipureintro
      exact ⟨rfl, H2⟩
    imodintro
    unfold send_nested_au
    iinv HI with IH Hclose
    icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose'
    inext
    iexists ls
    iframe Hownl
    rcases ls with buff | _ | v0 | _ | v0 | _ | d
    all_goals dsimp only [buffer_matches, dsp_close_res] at H1 ⊢
    case RcvCommit =>
      iintro Hownl
      imod Hclose' with -
      imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
      · inext
        iexists .Idle, rs, vsl, vsr
        iframe
        ipureintro
        exact ⟨H1, H2⟩
      imodintro
      iapply HΦ
      iframe
      iframe #
    case Closed =>
      iapply iProto_own_excl $$ Hown Hclosel
    all_goals itrivial
  case RcvPending =>
    subst H1
    iintro Hownl
    imod iProto_send _ _ _ _ _ v p $$ Hctx Hp [] with ⟨Hctx, Hown⟩
    · iapply iMsg_base_true_car
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists (.SndCommit v), rs, (([] : List V) ++ [v]), vsr
      iframe
      ipureintro
      exact ⟨rfl, H2⟩
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Closed =>
    iapply iProto_own_excl $$ Hp Hclosel
  all_goals itrivial

omit [IntoValTyped (GF := GF) V t] in
/-- Unfold an endpoint into its (persistent) session and protocol ownership. -/
theorem dsp_endpoint_split (γ : dsp_names) (c : chan.t × chan.t) (p : Option (iProto GF V)) :
    dsp_endpoint γ c p ⊣⊢ dsp_session (V := V) γ c.1 c.2 ∗
      (match p with
       | none => token γ.token_lr_name
       | some p => iProto_own γ.dsp_lr_name p) := .rfl

theorem wp_dsp_send (lr_chan rl_chan : loc) (γ : dsp_names) (v : V) (p : iProto GF V) :
    {{ (lr_chan, rl_chan) ↣{γ} (<!> iMsg_base v iprop(True) p) }}
      (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #v))
    {{ RET #(); (lr_chan, rl_chan) ↣{γ} p }} := by
  iintro %Φ Hc HΦ
  icases (dsp_endpoint_split γ _ _).1 $$ Hc with ⟨#Hs, Hp⟩
  ihave #Hcl : is_chan lr_chan γ.chan_lr_name V $$ [Hs]
  · unfold dsp_session; icases Hs with ⟨$, -⟩
  iapply chan.wp_send lr_chan v γ.chan_lr_name $$ Hcl
  iintro ⟨Hlc1, -⟩
  iapply dsp_send_au γ lr_chan rl_chan v p (Φ #()) $$ Hlc1 [Hp] HΦ
  iapply (dsp_endpoint_split γ _ _).2
  iframe
  iframe #

omit [IntoValTyped (GF := GF) V t] in
theorem dsp_send_tele_au {TT : Tele} (tt : TT.Arg) (γ : dsp_names) (lr_chan rl_chan : loc)
    (v : TT.Arg → V) (P : TT.Arg → IProp GF) (p : TT.Arg → iProto GF V) (Φ : IProp GF) :
    ⊢ £ 1 -∗
      ((lr_chan, rl_chan) ↣{γ} (<!> iMsg_texist fun x => iMsg_base (v x) (P x) (p x))) -∗
      P tt -∗
      (((lr_chan, rl_chan) ↣{γ} p tt) -∗ Φ) -∗
      send_au γ.chan_lr_name (v tt) Φ := by
  iintro Hlc Hc HP HΦ
  ihave Hc := iProto_pointsto_le γ _ _ (<!> iMsg_base (v tt) iprop(True) (p tt)) $$ Hc [HP]
  · inext
    iapply iProto_le_trans $$ [] [HP]
    · iapply iProto_le_texist_intro_l (fun x => iMsg_base (v x) (P x) (p x)) tt
    · iapply iProto_le_payload_intro_l $$ HP
  iapply dsp_send_au $$ Hlc Hc
  inext
  iexact HΦ

theorem wp_dsp_send_tele {TT : Tele} (tt : TT.Arg) (lr_chan rl_chan : loc) (γ : dsp_names)
    (v : TT.Arg → V) (P : TT.Arg → IProp GF) (p : TT.Arg → iProto GF V) :
    {{ ((lr_chan, rl_chan) ↣{γ} (<!> iMsg_texist fun x => iMsg_base (v x) (P x) (p x))) ∗ P tt }}
      (App (App (Val (chan.send t)) (Val #lr_chan)) (Val #(v tt)))
    {{ RET #(); (lr_chan, rl_chan) ↣{γ} p tt }} := by
  iintro %Φ ⟨Hc, HP⟩ HΦ
  ihave Hc := iProto_pointsto_le γ _ _ (<!> iMsg_base (v tt) iprop(True) (p tt)) $$ Hc [HP]
  · inext
    iapply iProto_le_trans $$ [] [HP]
    · iapply iProto_le_texist_intro_l (fun x => iMsg_base (v x) (P x) (p x)) tt
    · iapply iProto_le_payload_intro_l $$ HP
  iapply wp_dsp_send $$ Hc HΦ

omit [IntoValTyped (GF := GF) V t] in
/-- One receive step on the protocol ghost state (factored out of Rocq's `dsp_recv_au`). -/
theorem dsp_recv_step {TT : Tele} (γl γr : GName) (vsl : List V) (b : V) (rest : List V)
    (v : TT.Arg → V) (P : TT.Arg → IProp GF) (p : TT.Arg → iProto GF V) (E : CoPset) :
    ⊢ iProto_ctx γl γr vsl (b :: rest) -∗
      iProto_own γl (<?> iMsg_texist fun x => iMsg_base (v x) iprop(▷ P x) (p x)) ==∗
      ▷ iProto_ctx γl γr vsl rest ∗
      (£ 1 -∗ £ 1 -∗ |={E}=> ∃ x, ⌜v x = b⌝ ∗ iProto_own γl (p x) ∗ P x) := by
  iintro Hctx Hp
  imod iProto_recv _ _ _ _ _ _ $$ Hctx Hp with H
  icases H with ⟨%p', Hctx, Hown, Hm⟩
  imodintro
  iframe Hctx
  iintro Hlc1 Hlc2
  ihave H : iprop(▷ (iProto_own γl p' ∗
      (iMsg_texist fun x => iMsg_base (v x) iprop(▷ P x) (p x)).car b (Later.next p'))) $$ [Hown Hm]
  · inext
    iframe
  imod lc_fupd_elim_later $$ Hlc1 H with ⟨Hown, Hm⟩
  icases (iMsg_texist_exist _ _ _).1 $$ Hm with Hm
  icases (texist_exist _).1 $$ Hm with ⟨%x, Hm⟩
  simp only [iMsg_base_car]
  icases Hm with ⟨%Hvx, Heq, HP⟩
  ihave Heq := (later_equivI _ _).1 $$ Heq
  ihave H : iprop(▷ ((p x ≡ p') ∗ P x)) $$ [Heq HP]
  · inext
    iframe
  imod lc_fupd_elim_later $$ Hlc2 H with ⟨Heq, HP⟩
  imodintro
  iexists x
  iframe HP
  isplitl []
  · ipureintro; exact Hvx
  irewrite [Heq]
  iexact Hown

set_option maxHeartbeats 800000 in
omit [IntoValTyped (GF := GF) V t] in
/-- Endpoint receives value. -/
theorem dsp_recv_au {TT : Tele} (γ : dsp_names) (lr_chan rl_chan : loc) (v : TT.Arg → V)
    (P : TT.Arg → IProp GF) (p : TT.Arg → iProto GF V) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗
      ((lr_chan, rl_chan) ↣{γ} (<?> iMsg_texist fun x => iMsg_base (v x) iprop(▷ P x) (p x))) -∗
      ▷ (∀ x, ((lr_chan, rl_chan) ↣{γ} p x) ∗ P x -∗ Φ (v x) true) -∗
      recv_au γ.chan_rl_name V Φ := by
  unfold dsp_endpoint dsp_session recv_au
  iintro ⟨Hlc1, Hlc2⟩ ⟨⟨#Hcl, #Hcr, #HI⟩, Hp⟩ HΦ
  dsimp only
  iinv HI with IH Hclose
  unfold dsp_session_inv
  icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose'
  inext
  iexists rs
  iframe Hownr
  rcases rs with (_ | ⟨b, buff⟩) | _ | b | _ | b | _ | (_ | ⟨b, drain⟩)
  all_goals dsimp only [buffer_matches, dsp_close_res] at H2 ⊢
  case Buffered.cons =>
    subst H2
    iintro Hownr
    imod dsp_recv_step _ _ _ _ _ v P p ⊤ $$ Hctx Hp with ⟨Hctx, Hrecv⟩
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists ls, .Buffered buff, vsl, buff
      iframe
      ipureintro
      exact ⟨H1, rfl⟩
    imod Hrecv $$ Hlc1 Hlc2 with ⟨%x, %Hvx, Hown, HP⟩
    subst Hvx
    imodintro
    iapply HΦ
    iframe
    iframe #
  case SndPending =>
    subst H2
    iintro Hownr
    imod dsp_recv_step _ _ _ _ _ v P p ⊤ $$ Hctx Hp with ⟨Hctx, Hrecv⟩
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists ls, .RcvCommit, vsl, []
      iframe
      ipureintro
      exact ⟨H1, rfl⟩
    imod Hrecv $$ Hlc1 Hlc2 with ⟨%x, %Hvx, Hown, HP⟩
    subst Hvx
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Closed.cons =>
    subst H2
    iintro Hownr
    imod dsp_recv_step _ _ _ _ _ v P p ⊤ $$ Hctx Hp with ⟨Hctx, Hrecv⟩
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists ls, .Closed drain, vsl, drain
      iframe
      ipureintro
      exact ⟨H1, rfl⟩
    imod Hrecv $$ Hlc1 Hlc2 with ⟨%x, %Hvx, Hown, HP⟩
    subst Hvx
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Closed.nil =>
    subst H2
    iintro Hownr
    ihave H := iProto_recv_end_inv_l _ _ _ _ $$ Hctx Hp Hcloser
    imod lc_fupd_elim_later $$ Hlc1 H with %HF
    cases HF
  case Idle =>
    subst H2
    iintro Hownr
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists ls, .RcvPending, vsl, []
      iframe
      ipureintro
      exact ⟨H1, rfl⟩
    imodintro
    unfold recv_nested_au
    iinv HI with IH Hclose
    icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose'
    inext
    iexists rs
    iframe Hownr
    rcases rs with (_ | ⟨b, buff⟩) | _ | b | _ | b | _ | (_ | ⟨b, drain⟩)
    all_goals dsimp only [buffer_matches, dsp_close_res] at H2 ⊢
    case SndCommit =>
      subst H2
      iintro Hownr
      imod dsp_recv_step _ _ _ _ _ v P p ⊤ $$ Hctx Hp with ⟨Hctx, Hrecv⟩
      imod Hclose' with -
      imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
      · inext
        iexists ls, .Idle, vsl, []
        iframe
        ipureintro
        exact ⟨H1, rfl⟩
      imod Hrecv $$ Hlc1 Hlc2 with ⟨%x, %Hvx, Hown, HP⟩
      subst Hvx
      imodintro
      iapply HΦ
      iframe
      iframe #
    case Closed.nil =>
      subst H2
      iintro Hownr
      ihave H := iProto_recv_end_inv_l _ _ _ _ $$ Hctx Hp Hcloser
      imod lc_fupd_elim_later $$ Hlc1 H with %HF
      cases HF
    all_goals itrivial
  all_goals itrivial

theorem wp_dsp_recv {TT : Tele} (γ : dsp_names) (lr_chan rl_chan : loc) (v : TT.Arg → V)
    (P : TT.Arg → IProp GF) (p : TT.Arg → iProto GF V) :
    {{ (lr_chan, rl_chan) ↣{γ} (<?> iMsg_texist fun x => iMsg_base (v x) iprop(▷ P x) (p x)) }}
      (App (Val (chan.receive t)) (Val #rl_chan))
    {{ (x : TT.Arg), RET (PairV #(v x) #true); ((lr_chan, rl_chan) ↣{γ} p x) ∗ P x }} := by
  iintro %Φ Hc HΦ
  icases (dsp_endpoint_split γ _ _).1 $$ Hc with ⟨#Hs, Hp⟩
  ihave #Hcr : is_chan rl_chan γ.chan_rl_name V $$ [Hs]
  · unfold dsp_session; icases Hs with ⟨-, $, -⟩
  iapply chan.wp_receive rl_chan γ.chan_rl_name $$ Hcr
  iintro ⟨Hlc1, Hlc2, -⟩
  iapply dsp_recv_au γ lr_chan rl_chan v P p (fun w ok => Φ (PairV #w #ok)) $$ [$Hlc1 $Hlc2] [Hp] [HΦ]
  · iapply (dsp_endpoint_split γ _ _).2
    iframe
    iframe #
  · inext
    iintro %x H
    iapply HΦ $$ H

set_option maxHeartbeats 400000 in
omit [IntoValTyped (GF := GF) V t] in
/-- Endpoint closes (stops sending val). -/
theorem wp_dsp_close (γ : dsp_names) (lr_chan rl_chan : loc) (_p : iProto GF V) (Φ : IProp GF) :
    ⊢ ((lr_chan, rl_chan) ↣{γ} (END : iProto GF V)) -∗ (dsp_endpoint (V := V) γ (lr_chan, rl_chan) none -∗ Φ) -∗
      close_au γ.chan_lr_name V Φ := by
  unfold dsp_endpoint dsp_session close_au
  iintro ⟨⟨#Hcl, #Hcr, #HI⟩, Hp⟩ HΦ
  dsimp only
  iinv HI with IH Hclose
  unfold dsp_session_inv
  icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose'
  inext
  iexists ls
  iframe Hownl
  rcases ls with buff | _ | v0 | _ | v0 | _ | d
  all_goals dsimp only [buffer_matches, dsp_close_res] at H1 ⊢
  case Buffered =>
    subst H1
    iintro Hownl
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hcloser Hctx Hp] with -
    · inext
      iexists .Closed vsl, rs, vsl, vsr
      iframe
      ipureintro
      exact ⟨rfl, H2⟩
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Idle =>
    subst H1
    iintro Hownl
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hcloser Hctx Hp] with -
    · inext
      iexists .Closed [], rs, [], vsr
      iframe
      ipureintro
      exact ⟨rfl, H2⟩
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Closed =>
    iapply iProto_own_excl $$ Hp Hclosel
  all_goals itrivial

set_option maxHeartbeats 800000 in
omit [IntoValTyped (GF := GF) V t] in
/-- Endpoint receives on an ended channel. -/
theorem wp_dsp_recv_end (γ : dsp_names) (lr_chan rl_chan : loc) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ ((lr_chan, rl_chan) ↣{γ} (END : iProto GF V)) -∗
      (((lr_chan, rl_chan) ↣{γ} (END : iProto GF V)) -∗ Φ (zero_val V) false) -∗
      recv_au γ.chan_rl_name V Φ := by
  unfold dsp_endpoint dsp_session recv_au
  iintro ⟨Hlc1, Hlc2⟩ ⟨⟨#Hcl, #Hcr, #HI⟩, Hp⟩ HΦ
  dsimp only
  iinv HI with IH Hclose
  unfold dsp_session_inv
  icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose'
  inext
  iexists rs
  iframe Hownr
  rcases rs with (_ | ⟨b, buff⟩) | _ | b | _ | b | _ | (_ | ⟨b, drain⟩)
  all_goals dsimp only [buffer_matches, dsp_close_res] at H2 ⊢
  case Buffered.cons =>
    iintro Hownr
    ihave H := iProto_end_inv_l _ _ _ _ $$ Hctx Hp
    imod lc_fupd_elim_later $$ Hlc1 H with %Hnil
    rw [H2] at Hnil; cases Hnil
  case SndPending =>
    iintro Hownr
    ihave H := iProto_end_inv_l _ _ _ _ $$ Hctx Hp
    imod lc_fupd_elim_later $$ Hlc1 H with %Hnil
    rw [H2] at Hnil; cases Hnil
  case Closed.cons =>
    iintro Hownr
    ihave H := iProto_end_inv_l _ _ _ _ $$ Hctx Hp
    imod lc_fupd_elim_later $$ Hlc1 H with %Hnil
    rw [H2] at Hnil; cases Hnil
  case Closed.nil =>
    iintro Hownr
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists ls, .Closed [], vsl, vsr
      iframe
      ipureintro
      exact ⟨H1, H2⟩
    imodintro
    iapply HΦ
    iframe
    iframe #
  case Idle =>
    iintro Hownr
    imod Hclose' with -
    imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
    · inext
      iexists ls, .RcvPending, vsl, vsr
      iframe
      ipureintro
      exact ⟨H1, H2⟩
    imodintro
    unfold recv_nested_au
    iinv HI with IH Hclose
    icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
    imod lc_fupd_elim_later $$ Hlc1 Hctx with Hctx
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose'
    iexists rs
    iframe Hownr
    rcases rs with (_ | ⟨b, buff⟩) | _ | b | _ | b | _ | (_ | ⟨b, drain⟩)
    all_goals dsimp only [buffer_matches, dsp_close_res] at H2 ⊢
    case SndCommit =>
      inext
      iintro Hownr
      ihave H := iProto_end_inv_l _ _ _ _ $$ Hctx Hp
      imod lc_fupd_elim_later $$ Hlc2 H with %Hnil
      rw [H2] at Hnil; cases Hnil
    case Closed.nil =>
      inext
      iintro Hownr
      imod Hclose' with -
      imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
      · inext
        iexists ls, .Closed [], vsl, vsr
        iframe
        ipureintro
        exact ⟨H1, H2⟩
      imodintro
      iapply HΦ
      iframe
      iframe #
    all_goals inext; itrivial
  all_goals itrivial

omit [IntoValTyped (GF := GF) V t] in
theorem iProto_end_inv_l_keep (γl γr : GName) (vsl vsr : List V) :
    iProto_ctx (GF := GF) γl γr vsl vsr ∗ iProto_own γl (END : iProto GF V) ⊢
      (iProto_ctx γl γr vsl vsr ∗ iProto_own γl (END : iProto GF V)) ∗ ▷ ⌜vsr = []⌝ := by
  apply persistent_entails_left
  iintro ⟨H1, H2⟩
  iapply iProto_end_inv_l $$ H1 H2

set_option maxHeartbeats 800000 in
omit [IntoValTyped (GF := GF) V t] in
/-- Endpoint receives on a closed channel. -/
theorem wp_dsp_recv_closed (γ : dsp_names) (lr_chan rl_chan : loc) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ dsp_endpoint (V := V) γ (lr_chan, rl_chan) none -∗
      (dsp_endpoint (V := V) γ (lr_chan, rl_chan) none -∗ Φ (zero_val V) false) -∗
      recv_au γ.chan_rl_name V Φ := by
  unfold dsp_endpoint dsp_session recv_au
  iintro ⟨Hlc1, Hlc2⟩ ⟨⟨#Hcl, #Hcr, #HI⟩, Hp⟩ HΦ
  dsimp only
  iinv HI with IH Hclose
  unfold dsp_session_inv
  icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
  ihave H : iprop(▷ (iProto_ctx γ.dsp_lr_name γ.dsp_rl_name vsl vsr ∗
      dsp_close_res ls γ.dsp_lr_name γ.token_lr_name)) $$ [Hctx Hclosel]
  · inext
    iframe
  imod lc_fupd_elim_later $$ Hlc1 H with ⟨Hctx, Hclosel⟩
  rcases ls with buff | _ | v0 | _ | v0 | _ | d
  all_goals dsimp only [buffer_matches, dsp_close_res] at H1 ⊢
  case Closed =>
    subst H1
    icases iProto_end_inv_l_keep _ _ _ _ $$ [$Hctx $Hclosel] with ⟨⟨Hctx, Hclosel⟩, >%Hnil⟩
    subst Hnil
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hclose'
    inext
    iexists rs
    iframe Hownr
    rcases rs with (_ | ⟨b, buff⟩) | _ | b | _ | b | _ | (_ | ⟨b, drain⟩)
    all_goals dsimp only [buffer_matches, dsp_close_res] at H2 ⊢
    case Closed.nil =>
      iintro Hownr
      imod Hclose' with -
      imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
      · inext
        iexists .Closed vsl, .Closed [], vsl, []
        iframe
        ipureintro
        exact ⟨rfl, rfl⟩
      imodintro
      iapply HΦ
      iframe
      iframe #
    case Idle =>
      iintro Hownr
      imod Hclose' with -
      imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
      · inext
        iexists .Closed vsl, .RcvPending, vsl, []
        iframe
        ipureintro
        exact ⟨rfl, rfl⟩
      imodintro
      unfold recv_nested_au
      iinv HI with IH Hclose
      icases IH with ⟨%ls, %rs, %vsl, %vsr, >%H1, >%H2, >Hownl, >Hownr, Hclosel, Hcloser, Hctx⟩
      ihave H : iprop(▷ (iProto_ctx γ.dsp_lr_name γ.dsp_rl_name vsl vsr ∗
          dsp_close_res ls γ.dsp_lr_name γ.token_lr_name)) $$ [Hctx Hclosel]
      · inext
        dsimp only [dsp_close_res]
        iframe
      imod lc_fupd_elim_later $$ Hlc2 H with ⟨Hctx, Hclosel⟩
      rcases ls with buff | _ | v0 | _ | v0 | _ | d
      all_goals dsimp only [buffer_matches, dsp_close_res] at H1 ⊢
      case Closed =>
        subst H1
        icases iProto_end_inv_l_keep _ _ _ _ $$ [$Hctx $Hclosel] with ⟨⟨Hctx, Hclosel⟩, >%Hnil⟩
        subst Hnil
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hclose'
        inext
        iexists rs
        iframe Hownr
        rcases rs with (_ | ⟨b, buff⟩) | _ | b | _ | b | _ | (_ | ⟨b, drain⟩)
        all_goals dsimp only [buffer_matches, dsp_close_res] at H2 ⊢
        case Closed.nil =>
          iintro Hownr
          imod Hclose' with -
          imod Hclose $$ [Hownl Hownr Hclosel Hcloser Hctx] with -
          · inext
            iexists .Closed vsl, .Closed [], vsl, []
            iframe
            ipureintro
            exact ⟨rfl, rfl⟩
          imodintro
          iapply HΦ
          iframe
          iframe #
        case SndCommit => cases H2
        all_goals itrivial
      all_goals
        iexfalso
        iapply token_exclusive $$ Hp Hclosel
    case Buffered.cons => cases H2
    case SndPending => cases H2
    case Closed.cons => cases H2
    all_goals itrivial
  all_goals
    iexfalso
    iapply token_exclusive $$ Hp Hclosel

omit [IntoValTyped (GF := GF) V t] in
theorem wp_dsp_recv_false (b : Bool) (γ : dsp_names) (lr_chan rl_chan : loc)
    (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗
      (if b then ((lr_chan, rl_chan) ↣{γ} (END : iProto GF V))
        else dsp_endpoint (V := V) γ (lr_chan, rl_chan) none) -∗
      ((if b then ((lr_chan, rl_chan) ↣{γ} (END : iProto GF V))
        else dsp_endpoint (V := V) γ (lr_chan, rl_chan) none) -∗ Φ (zero_val V) false) -∗
      recv_au γ.chan_rl_name V Φ := by
  cases b
  · exact wp_dsp_recv_closed γ lr_chan rl_chan Φ
  · exact wp_dsp_recv_end γ lr_chan rl_chan Φ

end dsp

end Perennial
