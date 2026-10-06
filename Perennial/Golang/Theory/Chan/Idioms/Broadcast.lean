/-
Port of `new/golang/theory/chan/idioms/broadcast.v`.

A pattern for channel usage: a channel that never has anything sent, and is only closed at
some point. Closing broadcasts a persistent proposition to all readers.

Lean notes: Rocq's `own γ (to_dfrac_agree dq b)` is `dghostVar γ dq b`
(`Perennial/Ghost/DGhostVar.lean`).
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

structure BroadcastInternalNames where
  doneGn : GName

inductive Broadcast where
  | Pending
  | Done
  | Unknown

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]

/-- The broadcast invariant. -/
def broadcastInv (γ : ChanNames) (γch : BroadcastInternalNames) (Q : IProp GF) : IProp GF :=
  iprop(∃ (st : ChanState Unit),
    "Hch" ∷ ownChan γ Unit st ∗
    "Hs" ∷ (match st with
      | .Idle | .RcvPending => dghostVar γch.doneGn (.own (1 : Qp).half) false
      | .Closed [] => iprop(□ Q ∗ dghostVar γch.doneGn .discard true)
      | _ => iprop(False)))

/-- (Note (Rocq): could make the namespace be user-chosen.) -/
def isBroadcastChanInternal (ch : GoChan) (γ : ChanNames) (γch : BroadcastInternalNames)
    (Q : IProp GF) : IProp GF :=
  iprop("#His_ch" ∷ isChan ch γ Unit ∗ "#Hinv" ∷ inv nroot (broadcastInv γ γch Q))

instance isBroadcastChanInternal_pers (ch : GoChan) γ γch (Q : IProp GF) :
    Persistent (isBroadcastChanInternal ch γ γch Q) := by
  unfold isBroadcastChanInternal; infer_instance

def ownBroadcastChanDef (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (st : Broadcast) :
    IProp GF :=
  iprop(∃ γch,
    "#Hinv" ∷ isBroadcastChanInternal ch γ γch Q ∗
    "Hown" ∷ (match st with
      | .Pending => dghostVar γch.doneGn (.own (1 : Qp).half) false
      | .Done => dghostVar γch.doneGn .discard true
      | .Unknown => iprop(True)))
/-- (Rocq: `Opaque ownBroadcastChan`) -/
@[irreducible] def ownBroadcastChan (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (st : Broadcast) : IProp GF := ownBroadcastChanDef ch γ Q st
theorem ownBroadcastChan_unseal : @ownBroadcastChan = @ownBroadcastChanDef := by
  funext; with_unfolding_all rfl

instance ownBroadcastChan_Unknown_pers (ch : GoChan) γ (Q : IProp GF) :
    Persistent (ownBroadcastChan ch γ Q .Unknown) := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef; infer_instance

instance ownBroadcastChan_Done_pers (ch : GoChan) γ (Q : IProp GF) :
    Persistent (ownBroadcastChan ch γ Q .Done) := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef; infer_instance

theorem broadcast_chan_done (ch : GoChan) (γ : ChanNames) (Q : IProp GF) :
    ⊢ £ 1 -∗ ownBroadcastChan ch γ Q .Done ={⊤}=∗ Q := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef isBroadcastChanInternal
  iintro Hlc ⟨%γch, ⟨#His_ch, #Hinv⟩, #Hown⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold broadcastInv
  icases Hi with ⟨%st, Hch, Hs⟩
  rcases st with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  case RcvPending =>
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iexact HQ
  all_goals (iexfalso; iexact Hs)

theorem broadcast_chan_receive (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (cl : Broadcast) :
    ⊢ ownBroadcastChan ch γ Q cl -∗
      (□ Q ∗ ownBroadcastChan ch γ Q .Done -∗ Φ () false) -∗
      recvAu γ Unit Φ := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef isBroadcastChanInternal recvAu
  iintro ⟨%γch, ⟨#His_ch, #Hinv⟩, Hown⟩ HΦ
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcastInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    imod Hclose $$ [Hch Hs] with -
    · inext; iexists .RcvPending; dsimp only; iframe
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    icases Hi with ⟨%st, Hch, Hs⟩
    iexists st
    iframe Hch
    rcases st with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case Closed.nil =>
      iintro Hch
      icases Hs with ⟨#HQ, #Hs⟩
      imod Hmask with -
      imod Hclose $$ [Hch] with -
      · inext; iexists .Closed []; dsimp only; iframe Hch
        isplitl []
        · imodintro; iexact HQ
        · iexact Hs
      imodintro
      iapply HΦ
      isplitl []
      · imodintro; iexact HQ
      iexists γch
      isplitl []
      · isplitl []
        · iexact His_ch
        · iexact Hinv
      · iexact Hs
    all_goals first | itrivial | (iexfalso; iexact Hs)
  case Closed.nil =>
    iintro Hch
    icases Hs with ⟨#HQ, #Hs⟩
    imod Hmask with -
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hs
    imodintro
    iapply HΦ
    isplitl []
    · imodintro; iexact HQ
    iexists γch
    isplitl []
    · isplitl []
      · iexact His_ch
      · iexact Hinv
    · iexact Hs
  all_goals first | itrivial | (iexfalso; iexact Hs)

theorem ownBroadcastChan_open (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (st : Broadcast) :
    ownBroadcastChan ch γ Q st ⊢ ∃ γch, isBroadcastChanInternal ch γ γch Q ∗
      (match st with
        | .Pending => dghostVar γch.doneGn (.own (1 : Qp).half) false
        | .Done => dghostVar γch.doneGn .discard true
        | .Unknown => iprop(True)) := by
  rw [ownBroadcastChan_unseal]; exact .rfl

theorem ownBroadcastChan_close (ch : GoChan) (γ : ChanNames) (Q : IProp GF) (st : Broadcast)
    (γch : BroadcastInternalNames) :
    isBroadcastChanInternal ch γ γch Q ∗
      (match st with
        | .Pending => dghostVar γch.doneGn (.own (1 : Qp).half) false
        | .Done => dghostVar γch.doneGn .discard true
        | .Unknown => iprop(True)) ⊢ ownBroadcastChan ch γ Q st := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef
  iintro H; iexists γch; iexact H

theorem isBroadcastChanInternal_inv (ch : GoChan) γ γch (Q : IProp GF) :
    isBroadcastChanInternal ch γ γch Q ⊢ inv nroot (broadcastInv γ γch Q) := by
  unfold isBroadcastChanInternal; iintro ⟨-, $⟩

theorem isBroadcastChanInternal_is_chan (ch : GoChan) γ γch (Q : IProp GF) :
    isBroadcastChanInternal ch γ γch Q ⊢ isChan ch γ Unit := by
  unfold isBroadcastChanInternal; iintro ⟨$, -⟩

theorem ownBroadcastChan_nonblocking_receive (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) (cl : Broadcast) :
    ⊢ ownBroadcastChan ch γ Q cl -∗
      ((match cl with
        | .Unknown | .Done => iprop(ownBroadcastChan ch γ Q .Done -∗ Φ () false)
        | _ => iprop(True)) ∧
       (match cl with
        | .Unknown | .Pending => iprop(ownBroadcastChan ch γ Q cl -∗ Φnotready)
        | _ => iprop(True))) -∗
      nonblockingRecvAuAlt γ Unit Φ Φnotready := by
  iintro Hown HΦ
  icases ownBroadcastChan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, Hown⟩
  ihave #Hinv := isBroadcastChanInternal_inv _ _ _ _ $$ Hint
  unfold nonblockingRecvAuAlt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcastInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Done =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .Idle; dsimp only; iframe
      imodintro
      iapply HΦ
      iapply ownBroadcastChan_close _ _ _ _ γch
      iframe #
      try iframe
  case RcvPending =>
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Done =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .RcvPending; dsimp only; iframe
      imodintro
      iapply HΦ
      iapply ownBroadcastChan_close _ _ _ _ γch
      iframe #
      try iframe
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Pending =>
      ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨HΦ, -⟩
      imod Hclose $$ [Hch] with -
      · inext; iexists .Closed []; dsimp only; iframe Hch
        isplitl []
        · imodintro; iexact HQ
        · iexact Hs
      imodintro
      iapply HΦ
      iapply ownBroadcastChan_close _ _ _ _ γch
      dsimp only
      iframe #
  all_goals (iexfalso; iexact Hs)

theorem broadcast_close_au (ch : GoChan) (γch : ChanNames) (Q : IProp GF) (Φ : IProp GF) :
    ⊢ ownBroadcastChan ch γch Q .Pending -∗ □ Q -∗
      ▷ (ownBroadcastChan ch γch Q .Done -∗ Φ) -∗ closeAu γch Unit Φ := by
  iintro Hown #HQ HΦ
  icases ownBroadcastChan_open _ _ _ _ $$ Hown with ⟨%γi, #Hint, Hown⟩
  ihave #Hinv := isBroadcastChanInternal_inv _ _ _ _ $$ Hint
  unfold closeAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcastInv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    imod dghostVar_update_halves true _ _ _ $$ Hown Hs with ⟨Hown, -⟩
    imod dghostVar_persist _ _ _ $$ Hown with #Hown
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hown
    imodintro
    iapply HΦ
    iapply ownBroadcastChan_close _ _ _ _ γi
    dsimp only
    iframe #
  case Closed.nil =>
    icases Hs with ⟨-, #Hs⟩
    ihave %Hbad := dghostVar_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  all_goals first | itrivial | (iexfalso; iexact Hs)

theorem ownBroadcastChan_is_chan (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (cl : Broadcast) :
    ⊢ ownBroadcastChan ch γ Q cl -∗ isChan ch γ Unit := by
  iintro Hown
  icases ownBroadcastChan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, -⟩
  iapply isBroadcastChanInternal_is_chan _ _ _ _ $$ Hint

theorem ownBroadcastChan_Unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (cl : Broadcast) :
    ⊢ ownBroadcastChan ch γ Q cl -∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro Hown
  icases ownBroadcastChan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, -⟩
  iapply ownBroadcastChan_close _ _ _ _ γch
  iframe #

theorem wp_broadcast_chan_close {ty : go.GoType} {dir : go.ChanDir}
    [ty ↓u go.ChannelType dir (go.StructType [])] (ch : GoChan) (γch : ChanNames) (Q : IProp GF) :
    {{ ownBroadcastChan ch γch Q .Pending ∗ □ Q }}
      (App (Val #(functions go.close [ty])) (Val #ch))
    {{ RET #(); ownBroadcastChan ch γch Q .Done }} := by
  iintro %Φ ⟨Hown, #HQ⟩ HΦ
  ihave #His := ownBroadcastChan_is_chan _ _ _ _ $$ Hown
  iapply chan.wp_close (ct := ty) (V := Unit) ch γch $$ His
  iintro _
  iapply broadcast_close_au _ _ _ _ $$ Hown HQ HΦ

theorem alloc_broadcast_chan {E : CoPset} (Q : IProp GF) (γ : ChanNames) (ch : GoChan) :
    ⊢ isChan ch γ Unit -∗ ownChan γ Unit .Idle ={E}=∗ ownBroadcastChan ch γ Q .Pending := by
  iintro #Hch Hoc
  imod dghostVar_alloc false with ⟨%tok_gn, Htok⟩
  icases dghostVar_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Htok] with ⟨Htok, Htok2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Htok
  imod inv_alloc nroot E (broadcastInv γ ⟨tok_gn⟩ Q) $$ [Hoc Htok2] with #Hinv
  · inext; unfold broadcastInv; iexists .Idle; dsimp only; iframe
  imodintro
  iapply ownBroadcastChan_close _ _ _ _ ⟨tok_gn⟩
  dsimp only
  iframe
  unfold isBroadcastChanInternal
  iframe #

end proof

end Perennial
