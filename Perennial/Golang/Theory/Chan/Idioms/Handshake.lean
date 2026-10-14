/-
A simple handshake on an unbuffered
channel.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section handshake
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The handshake invariant. -/
def handshakeInv (γ : ChanNames) (P : V → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(∃ s, "Hch" ∷ ownChan γ V s ∗
    (match s with
     | .Idle => iprop(True)
     | .SndPending v | .SndCommit v => P v
     | .RcvPending | .RcvCommit => Q
     -- Can't use buffered channel and we don't close here.
     | _ => iprop(False)))

/-- Invariant for a simple handshake on an unbuffered channel with unit payloads.

- When the channel has an in-flight *send* (SndWait/SndDone), predicate `P` must hold
  (producer-side obligation).
- When the channel has an in-flight *receive* (RcvWait/RcvDone), predicate `Q` must hold
  (consumer-side obligation).
- Buffered channels are intentionally disallowed.
- Closing is also disallowed in this idiom (`_ => False`). -/
def isHandshake (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Q : IProp GF) : IProp GF :=
  iprop(isChan ch γ V ∗ inv nroot (handshakeInv γ P Q))

instance isHandshake_persistent (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Q : IProp GF) :
    Persistent (isHandshake γ ch P Q) := by
  unfold isHandshake; infer_instance

omit [IntoValTyped (GF := GF) V t] in
theorem start_handshake (ch : Loc) (P : V → IProp GF) (Q : IProp GF) (γ : ChanNames) :
    ⊢ isChan ch γ V -∗ ownChan γ V .Idle ={⊤}=∗ isHandshake γ ch P Q := by
  iintro #Hch Hchan
  unfold isHandshake
  iframe Hch
  iapply inv_alloc
  inext
  unfold handshakeInv
  iexists .Idle
  iframe

theorem handshake_receive_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Q : IProp GF)
    (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isHandshake γ ch P Q -∗ Q -∗ ▷ (∀ v, P v -∗ Φ v true) -∗ recvAu γ V Φ := by
  unfold isHandshake recvAu
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hchan, #Hinv⟩ HQ Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold handshakeInv
  -- (`iNamed Hi` fails with "unknown free variable" on a `match` on the bound variable)
  icases Hi with ⟨%s, Hch, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with (_ | ⟨_, _⟩) | _ | v | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H HQ] with -
    · inext
      iexists .RcvPending
      iframe
    imodintro
    unfold recvNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hch, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      iintro Hid
      imod Hmask with -
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ Hi
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case SndPending =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H HQ] with -
    · inext
      iexists .RcvCommit
      iframe
    imodintro
    iapply Hau $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_handshake_receive (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Q : IProp GF) :
    {{ isHandshake γ ch P Q ∗ Q }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V), RET (PairV #v #true); P v }} := by
  iintro %Φ ⟨#His, HQ⟩ HΦ
  ihave #Hchan : isChan ch γ V $$ [His]
  · unfold isHandshake; icases His with ⟨$, -⟩
  iapply chan.wp_receive ch γ $$ Hchan
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply handshake_receive_au γ ch P Q (fun v ok => Φ (PairV #v #ok)) $$ [$Hlc1 $Hlc2] His HQ HΦ

theorem handshake_send_au (γ : ChanNames) (ch : Loc) (v : V) (P : V → IProp GF) (Q : IProp GF)
    (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 ∗ £ 1 -∗ isHandshake γ ch P Q -∗ P v -∗ ▷ (Q -∗ Φ) -∗ sendAu γ v Φ := by
  unfold isHandshake sendAu
  iintro ⟨Hlc1, Hlc2, Hlc3⟩ ⟨#Hchan, #Hinv⟩ HP Hau
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold handshakeInv
  icases Hi with ⟨%s, Hch, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with b | _ | _ | _ | _ | _ | d
  all_goals dsimp only
  case Idle =>
    iintro H
    imod Hmask with -
    imod Hclose $$ [H HP] with -
    · inext
      iexists .SndPending v
      iframe
    imodintro
    unfold sendNestedAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hch, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with _ | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    case RcvCommit =>
      iintro Hid
      imod Hmask with -
      imod Hclose $$ [Hid] with -
      · inext
        iexists .Idle
        iframe
      imodintro
      iapply Hau $$ Hi
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    iintro Hsd
    imod Hmask with -
    imod Hclose $$ [Hsd HP] with -
    · inext
      iexists .SndCommit v
      iframe
    imodintro
    iapply Hau $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_handshake_send (γ : ChanNames) (ch : Loc) (v : V) (P : V → IProp GF) (Q : IProp GF) :
    {{ isHandshake γ ch P Q ∗ P v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); Q }} := by
  iintro %Φ ⟨#His, HP⟩ HΦ
  ihave #Hchan : isChan ch γ V $$ [His]
  · unfold isHandshake; icases His with ⟨$, -⟩
  iapply chan.wp_send ch v γ $$ Hchan
  iintro ⟨Hlc1, Hlc2, Hlc3, _⟩
  iapply handshake_send_au γ ch v P Q (Φ #()) $$ [$Hlc1 $Hlc2 $Hlc3] His HP HΦ

end handshake

end Perennial
