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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The bag invariant. -/
def chanBagInv (γ : ChanNames) (P : V → IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState V), "Hch" ∷ ownChan γ V s ∗
    (match s with
     | .Idle => iprop(True)
     | .SndPending v => P v
     | .SndCommit v => P v
     | .Buffered vs => iprop([∗list] v ∈ vs, P v)
     | .Closed _ => iprop(False)
     | _ => iprop(True)))

def isChanBagDef (γ : ChanNames) (ch : Loc) (P : V → IProp GF) : IProp GF :=
  iprop("#Hch" ∷ isChan ch γ V ∗ "#Hinv" ∷ inv nroot (chanBagInv γ P))
/-- (Rocq: `Opaque isChanBag`) -/
@[irreducible] def isChanBag (γ : ChanNames) (ch : Loc) (P : V → IProp GF) : IProp GF :=
  isChanBagDef γ ch P
theorem isChanBag_unseal : @isChanBag = @isChanBagDef := by funext; with_unfolding_all rfl

instance isChanBag_pers (γ : ChanNames) (ch : Loc) (P : V → IProp GF) :
    Persistent (isChanBag γ ch P) := by
  rw [isChanBag_unseal]; unfold isChanBagDef; infer_instance

theorem start_bag (P : V → IProp GF) (s : ChanState V) (ch : Loc) (γ : ChanNames)
    (Hs : match s with | .Idle | .Buffered [] => True | _ => False) :
    ⊢ isChan ch γ V -∗ ownChan γ V s ={⊤}=∗ isChanBag γ ch P := by
  iintro #Hch Hoc
  imod inv_alloc nroot ⊤ (chanBagInv γ P) $$ [Hoc] with #Hinv
  · inext
    unfold chanBagInv
    iexists s
    iframe
    rcases s with (_ | ⟨_, _⟩) | _ | _ | _ | _ | _ | _ <;> simp at Hs <;> dsimp only
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · itrivial
  imodintro
  rw [isChanBag_unseal]; unfold isChanBagDef
  iframe #

theorem is_bag_is_chan (γ : ChanNames) (ch : Loc) (P : V → IProp GF) :
    ⊢ isChanBag γ ch P -∗ isChan ch γ V := by
  rw [isChanBag_unseal]; unfold isChanBagDef
  iintro ⟨$, -⟩

theorem bag_recv_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (Φ : V → Bool → IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isChanBag γ ch P -∗ (▷ ∀ v, P v -∗ Φ v true) -∗ recvAu γ V Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef recvAu
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hch, #Hinv⟩ HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
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
    unfold recvNestedAu
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

theorem wp_bag_receive (γ : ChanNames) (ch : Loc) (P : V → IProp GF) :
    {{ isChanBag γ ch P }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V), RET (PairV #v #true); P v }} := by
  iintro %Φ #Hbag HΦ
  ihave #Hch := is_bag_is_chan γ ch P $$ Hbag
  iapply chan.wp_receive ch γ $$ Hch
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply bag_recv_au γ ch P (fun v ok => Φ (PairV #v #ok)) $$ [$Hlc1 $Hlc2] Hbag HΦ

theorem bag_send_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF) (v : V) (Φ : IProp GF) :
    ⊢ £ 1 ∗ £ 1 -∗ isChanBag γ ch P -∗ P v -∗ ▷ Φ -∗ sendAu γ v Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef sendAu
  iintro ⟨Hlc1, Hlc2⟩ ⟨#Hch, #Hinv⟩ HP HΦ
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc1 Hi with Hi
  unfold chanBagInv
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
    unfold sendNestedAu
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

theorem wp_bag_send (γ : ChanNames) (ch : Loc) (v : V) (P : V → IProp GF) :
    {{ isChanBag γ ch P ∗ P v }}
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
