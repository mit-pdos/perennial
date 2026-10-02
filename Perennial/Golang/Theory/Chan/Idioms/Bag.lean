/-
Port of `new/golang/theory/chan/idioms/bag.v`: the "bag" channel specification.

This channel spec has a user-chosen predicate `P` over values sent on the channel, but no
ordering guarantees. It's like a "bag" of values, with `send` inserting and `receive`
removing.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

/-- The bag invariant. -/
def chan_bag_inv (γ : chan_names) (P : V → IProp GF) : IProp GF :=
  iprop(∃ (s : chanstate.t V), "Hch" ∷ own_chan γ V s ∗
    (match s with
     | .Idle => iprop(True)
     | .SndPending v => P v
     | .SndCommit v => P v
     | .Buffered vs => iprop([∗list] v ∈ vs, P v)
     | .Closed _ => iprop(False)
     | _ => iprop(True)))

def is_chan_bag_def (γ : chan_names) (ch : loc) (P : V → IProp GF) : IProp GF :=
  iprop("#Hch" ∷ is_chan ch γ V ∗ "#Hinv" ∷ inv nroot (chan_bag_inv γ P))
/-- (Rocq: `Opaque is_chan_bag`) -/
@[irreducible] def is_chan_bag (γ : chan_names) (ch : loc) (P : V → IProp GF) : IProp GF :=
  is_chan_bag_def γ ch P
theorem is_chan_bag_unseal : @is_chan_bag = @is_chan_bag_def := by funext; with_unfolding_all rfl

instance is_chan_bag_pers (γ : chan_names) (ch : loc) (P : V → IProp GF) :
    Persistent (is_chan_bag γ ch P) := by
  rw [is_chan_bag_unseal]; unfold is_chan_bag_def; infer_instance

theorem start_bag (P : V → IProp GF) (s : chanstate.t V) (ch : loc) (γ : chan_names)
    (Hs : match s with | .Idle | .Buffered [] => True | _ => False) :
    ⊢ is_chan ch γ V -∗ own_chan γ V s ={⊤}=∗ is_chan_bag γ ch P := by
  iintro #Hch Hoc
  imod inv_alloc nroot ⊤ (chan_bag_inv γ P) $$ [Hoc] with #Hinv
  · inext
    unfold chan_bag_inv
    iexists s
    iframe
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | _ <;> simp at Hs <;> dsimp only
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · itrivial
  imodintro
  rw [is_chan_bag_unseal]; unfold is_chan_bag_def
  iframe #

theorem is_bag_is_chan (γ : chan_names) (ch : loc) (P : V → IProp GF) :
    ⊢ is_chan_bag γ ch P -∗ is_chan ch γ V := by
  rw [is_chan_bag_unseal]; unfold is_chan_bag_def
  iintro ⟨$, -⟩

theorem bag_recv_au (γ : chan_names) (ch : loc) (P : V → IProp GF) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ is_chan_bag γ ch P -∗ (▷ ∀ v, P v -∗ Φ v true) -∗ recv_au γ V Φ := by
  rw [is_chan_bag_unseal]; unfold is_chan_bag_def recv_au
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hch, #Hinv⟩ HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chan_bag_inv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
  all_goals dsimp only
  case Buffered.cons =>
    iintro Hoc
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered buff'; iframe
    imodintro
    iapply HΦ $$ HP
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvPending; iframe
    imodintro
    unfold recv_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hoc1, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc1
    rcases s with _ | _ | _ | _ | v | _ | (_ | ⟨_, _⟩)
    all_goals dsimp only
    case SndCommit =>
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext; iexists .Idle; iframe
      imodintro
      iapply HΦ $$ Hi
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imodintro
    iapply HΦ $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_bag_receive (γ : chan_names) (ch : loc) (P : V → IProp GF) :
    {{ is_chan_bag γ ch P }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V), RET (PairV #v #true); P v }} := by
  iintro %Φ #Hbag HΦ
  ihave #Hch := is_bag_is_chan γ ch P $$ Hbag
  iapply chan.wp_receive ch γ $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply bag_recv_au γ ch P (fun v ok => Φ (PairV #v #ok)) $$ [$Hlc1 $Hlc2] Hbag HΦ

theorem bag_send_au (γ : chan_names) (ch : loc) (P : V → IProp GF) (v : V) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ is_chan_bag γ ch P -∗ P v -∗ ▷ Φ -∗ send_au γ v Φ := by
  rw [is_chan_bag_unseal]; unfold is_chan_bag_def send_au
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hch, #Hinv⟩ HP HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chan_bag_inv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hoc0
  rcases s with buff | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  case Buffered =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc Hi HP] with -
    · inext; iexists .Buffered (buff ++ [v])
      dsimp only
      iframe Hoc
      iapply BigSepL.bigSepL_append.2
      iframe Hi
      iapply BigSepL.bigSepL_singleton.2
      iexact HP
    imodintro
    iexact HΦ
  case Idle =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndPending v; iframe
    imodintro
    unfold send_nested_au
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc2 Hi with Hi
    icases Hi with ⟨%s, Hoc1, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc1
    rcases s with _ | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    case RcvCommit =>
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext; iexists .Idle; iframe
      imodintro
      iexact HΦ
    all_goals first | itrivial | (iexfalso; iexact Hi)
  case RcvPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HP] with -
    · inext; iexists .SndCommit v; iframe
    imodintro
    iexact HΦ
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_bag_send (γ : chan_names) (ch : loc) (v : V) (P : V → IProp GF) :
    {{ is_chan_bag γ ch P ∗ P v }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); True }} := by
  iintro %Φ ⟨#Hbag, HP⟩ HΦ
  ihave #Hch := is_bag_is_chan γ ch P $$ Hbag
  iapply chan.wp_send ch v γ $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply bag_send_au γ ch P v (Φ #()) $$ [$Hlc1 $Hlc2] Hbag HP
  inext
  iapply HΦ
  itrivial

end proof

end Perennial
