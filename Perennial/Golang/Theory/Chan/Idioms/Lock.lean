/-
The lock channel idiom.

Note: If you can change the code and you aren't using select, just use a mutex. This
pattern otherwise doesn't serve a practical purpose.

A buffered channel with capacity 1 is used as a lock: an empty buffer means unlocked
(resource `R` available), one value in the buffer means locked. Unbuffered and close
operations are banned. Lock acquisition is a send, release is a receive.
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

structure LockChannelNames where
  /-- Underlying channel ghost state -/
  lchanName : ChanNames
  /-- Ghost bool tracking lock state -/
  lockedName : GName

section lock_channel
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- The lock channel invariant. -/
def lockChannelInv (γ : ChanNames) (R : IProp GF) : IProp GF :=
  iprop(∃ (s : ChanState V) (locked : Bool),
    "Hch" ∷ ownChan γ V s ∗
    "%Hcap" ∷ ⌜γ.chanCap = W64 1⌝ ∗
    (match s with
     | .Buffered [] => iprop(⌜locked = false⌝ ∗ R)
     | .Buffered [_] => iprop(⌜locked = true⌝)
     -- Ban unbuffered and close states
     | _ => iprop(False)))

variable (V) in
def isLockChannel (γ : LockChannelNames) (ch : Loc) (R : IProp GF) : IProp GF :=
  iprop("#Hchan" ∷ isChan ch γ.lchanName V ∗
    "#Hinv" ∷ inv nroot (lockChannelInv (V := V) γ.lchanName R))

instance isLockChannel_persistent (γ : LockChannelNames) (ch : Loc) (R : IProp GF) :
    Persistent (isLockChannel V γ ch R) := by
  unfold isLockChannel; infer_instance

theorem start_lock_channel (ch : Loc) (R : IProp GF) (γ : ChanNames)
    (Hcap : γ.chanCap = W64 1) :
    ⊢ isChan ch γ V -∗ ownChan γ V (.Buffered []) -∗ ▷ R ={⊤}=∗
      ∃ γlock, isLockChannel V γlock ch R := by
  iintro #Hch Hoc HR
  imod ghostVar_alloc false with ⟨%γlocked, -⟩
  imod inv_alloc nroot ⊤ (lockChannelInv (V := V) γ R) $$ [Hoc HR] with #Hinv
  · inext
    unfold lockChannelInv
    iexists .Buffered [], false
    dsimp only
    iframe
    ipureintro; exact ⟨Hcap, rfl⟩
  imodintro
  iexists ⟨γ, γlocked⟩
  unfold isLockChannel
  iframe #

theorem isLockChannel_is_chan (γ : LockChannelNames) (ch : Loc) (R : IProp GF) :
    isLockChannel V γ ch R ⊢ isChan ch γ.lchanName V := by
  unfold isLockChannel
  iintro ⟨$, -⟩

theorem lock_channel_send_au (γ : LockChannelNames) (ch : Loc) (v : V) (R : IProp GF)
    (Φ : IProp GF) :
    ⊢ isLockChannel V γ ch R -∗ £ 1 -∗ ▷ (R -∗ Φ) -∗ sendAu γ.lchanName v Φ := by
  unfold isLockChannel sendAu
  iintro ⟨#Hchan, #Hinv⟩ Hlc Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold lockChannelInv
  icases Hi with ⟨%s, %locked, Hch, %Hcap, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with ((_ | ⟨v', _ | ⟨_, _⟩⟩)) | _ | _ | _ | _ | _ | _
  all_goals dsimp only
  · icases Hi with ⟨%Hlocked, HR⟩
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext
      iexists .Buffered [v], true
      simp only [List.nil_append]
      iframe
      ipureintro; exact ⟨Hcap, trivial⟩
    imodintro
    iapply Hcont $$ HR
  · iintro H
    ihave %Hbad := ownChan_buffer_size _ _ _ $$ H
    rw [Hcap] at Hbad
    simp at Hbad
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem lock_channel_nonblocking_send_au (γ : LockChannelNames) (ch : Loc) (v : V)
    (R : IProp GF) (Φ : IProp GF) :
    ⊢ isLockChannel V γ ch R -∗ £ 1 -∗ (R -∗ Φ) -∗
      nonblockingSendAu γ.lchanName v Φ iprop(True) := by
  unfold isLockChannel nonblockingSendAu nonblockingSendAuInner
  iintro ⟨#Hchan, #Hinv⟩ Hlc HΦ
  isplit
  · iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
    unfold lockChannelInv
    icases Hi with ⟨%s, %locked, Hch, %Hcap, Hi⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hch
    rcases s with ((_ | ⟨v', _ | ⟨_, _⟩⟩)) | _ | _ | _ | _ | _ | _
    all_goals dsimp only
    · icases Hi with ⟨%Hlocked, HR⟩
      iintro Hoc
      imod Hmask with -
      imod Hclose $$ [Hoc] with -
      · inext
        iexists .Buffered [v], true
        simp only [List.nil_append]
        iframe
        ipureintro; exact ⟨Hcap, trivial⟩
      imodintro
      iapply HΦ $$ HR
    · iintro H
      ihave %Hbad := ownChan_buffer_size _ _ _ $$ H
      rw [Hcap] at Hbad
      simp at Hbad
    all_goals first | itrivial | (iexfalso; iexact Hi)
  · itrivial

theorem wp_lock_channel_lock (γ : LockChannelNames) (ch : Loc) (v : V) (R : IProp GF) :
    {{ isLockChannel V γ ch R }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); R }} := by
  iintro %Φ #Hlock HΦ
  ihave #Hchan := isLockChannel_is_chan γ ch R $$ Hlock
  iapply chan.wp_send ch v γ.lchanName $$ Hchan
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply lock_channel_send_au γ ch v R (Φ #()) $$ Hlock Hlc1 HΦ

theorem lock_channel_recv_au (γ : LockChannelNames) (ch : Loc) (R : IProp GF)
    (Φ : V → Bool → IProp GF) :
    ⊢ isLockChannel V γ ch R -∗ R -∗ £ 1 -∗ ▷ (∀ v, True -∗ Φ v true) -∗
      recvAu γ.lchanName V Φ := by
  unfold isLockChannel recvAu
  iintro ⟨#Hchan, #Hinv⟩ HR Hlc HΦcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold lockChannelInv
  icases Hi with ⟨%s, %locked, Hch, %Hcap, Hi⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists s
  iframe Hch
  rcases s with ((_ | ⟨v', _ | ⟨_, _⟩⟩)) | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  · itrivial
  · -- value in buffer: can unlock
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc HR] with -
    · inext
      iexists .Buffered [], false
      dsimp only
      iframe
      ipureintro; exact ⟨Hcap, rfl⟩
    imodintro
    iapply HΦcont
    itrivial
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem wp_lock_channel_unlock (γ : LockChannelNames) (ch : Loc) (R : IProp GF) :
    {{ isLockChannel V γ ch R ∗ R }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V), RET (PairV #v #true); True }} := by
  iintro %Φ ⟨#Hlock, HR⟩ HΦ
  ihave #Hchan := isLockChannel_is_chan γ ch R $$ Hlock
  iapply chan.wp_receive ch γ.lchanName $$ Hchan
  iintro ⟨Hlc1, Hlc2⟩
  iapply lock_channel_recv_au γ ch R (fun v ok => Φ (PairV #v #ok)) $$ Hlock HR Hlc1 HΦ

end lock_channel

end Perennial
