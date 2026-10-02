/-
Port of `new/golang/theory/chan/idioms/lock.v`: the lock channel idiom.

Note: If you can change the code and you aren't using select, just use a mutex. This
pattern otherwise doesn't serve a practical purpose.

A buffered channel with capacity 1 is used as a lock: an empty buffer means unlocked
(resource `R` available), one value in the buffer means locked. Unbuffered and close
operations are banned. Lock acquisition is a send, release is a receive.
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

structure lock_channel_names where
  /-- Underlying channel ghost state -/
  lchan_name : chan_names
  /-- Ghost bool tracking lock state -/
  locked_name : GName

section lock_channel
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.type}
  [IntoValTyped (GF := GF) V t]

/-- The lock channel invariant. -/
def lock_channel_inv (γ : chan_names) (R : IProp GF) : IProp GF :=
  iprop(∃ (s : chanstate.t V) (locked : Bool),
    "Hch" ∷ own_chan γ V s ∗
    "%Hcap" ∷ ⌜γ.chan_cap = W64 1⌝ ∗
    (match s with
     | .Buffered [] => iprop(⌜locked = false⌝ ∗ R)
     | .Buffered [_] => iprop(⌜locked = true⌝)
     -- Ban unbuffered and close states
     | _ => iprop(False)))

variable (V) in
def is_lock_channel (γ : lock_channel_names) (ch : loc) (R : IProp GF) : IProp GF :=
  iprop("#Hchan" ∷ is_chan ch γ.lchan_name V ∗
    "#Hinv" ∷ inv nroot (lock_channel_inv (V := V) γ.lchan_name R))

instance is_lock_channel_persistent (γ : lock_channel_names) (ch : loc) (R : IProp GF) :
    Persistent (is_lock_channel V γ ch R) := by
  unfold is_lock_channel; infer_instance

theorem start_lock_channel (ch : loc) (R : IProp GF) (γ : chan_names)
    (Hcap : γ.chan_cap = W64 1) :
    ⊢ is_chan ch γ V -∗ own_chan γ V (.Buffered []) -∗ ▷ R ={⊤}=∗
      ∃ γlock, is_lock_channel V γlock ch R := by
  iintro #Hch Hoc HR
  imod ghost_var_alloc false with ⟨%γlocked, -⟩
  imod inv_alloc nroot ⊤ (lock_channel_inv (V := V) γ R) $$ [Hoc HR] with #Hinv
  · inext
    unfold lock_channel_inv
    iexists .Buffered [], false
    dsimp only
    iframe
    ipureintro; exact ⟨Hcap, rfl⟩
  imodintro
  iexists ⟨γ, γlocked⟩
  unfold is_lock_channel
  iframe #

theorem is_lock_channel_is_chan (γ : lock_channel_names) (ch : loc) (R : IProp GF) :
    is_lock_channel V γ ch R ⊢ is_chan ch γ.lchan_name V := by
  unfold is_lock_channel
  iintro ⟨$, -⟩

theorem lock_channel_send_au (γ : lock_channel_names) (ch : loc) (v : V) (R : IProp GF)
    (Φ : IProp GF) :
    ⊢ is_lock_channel V γ ch R -∗ £ 1 -∗ ▷ (R -∗ Φ) -∗ send_au γ.lchan_name v Φ := by
  unfold is_lock_channel send_au
  iintro ⟨#Hchan, #Hinv⟩ Hlc Hcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold lock_channel_inv
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
    ihave %Hbad := own_chan_buffer_size _ _ _ $$ H
    rw [Hcap] at Hbad
    simp at Hbad
  all_goals first | itrivial | (iexfalso; iexact Hi)

theorem lock_channel_nonblocking_send_au (γ : lock_channel_names) (ch : loc) (v : V)
    (R : IProp GF) (Φ : IProp GF) :
    ⊢ is_lock_channel V γ ch R -∗ £ 1 -∗ (R -∗ Φ) -∗
      nonblocking_send_au γ.lchan_name v Φ iprop(True) := by
  unfold is_lock_channel nonblocking_send_au nonblocking_send_au_inner
  iintro ⟨#Hchan, #Hinv⟩ Hlc HΦ
  isplit
  · iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
    unfold lock_channel_inv
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
      ihave %Hbad := own_chan_buffer_size _ _ _ $$ H
      rw [Hcap] at Hbad
      simp at Hbad
    all_goals first | itrivial | (iexfalso; iexact Hi)
  · itrivial

theorem wp_lock_channel_lock (γ : lock_channel_names) (ch : loc) (v : V) (R : IProp GF) :
    {{ is_lock_channel V γ ch R }}
      (App (App (Val (chan.send t)) (Val #ch)) (Val #v))
    {{ RET #(); R }} := by
  iintro %Φ #Hlock HΦ
  ihave #Hchan := is_lock_channel_is_chan γ ch R $$ Hlock
  iapply chan.wp_send ch v γ.lchan_name $$ Hchan
  iintro ⟨Hlc1, Hlc2, Hlc3, Hlc4⟩
  iapply lock_channel_send_au γ ch v R (Φ #()) $$ Hlock Hlc1 HΦ

theorem lock_channel_recv_au (γ : lock_channel_names) (ch : loc) (R : IProp GF)
    (Φ : V → Bool → IProp GF) :
    ⊢ is_lock_channel V γ ch R -∗ R -∗ £ 1 -∗ ▷ (∀ v, True -∗ Φ v true) -∗
      recv_au γ.lchan_name V Φ := by
  unfold is_lock_channel recv_au
  iintro ⟨#Hchan, #Hinv⟩ HR Hlc HΦcont
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold lock_channel_inv
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

theorem wp_lock_channel_unlock (γ : lock_channel_names) (ch : loc) (R : IProp GF) :
    {{ is_lock_channel V γ ch R ∗ R }}
      (App (Val (chan.receive t)) (Val #ch))
    {{ (v : V), RET (PairV #v #true); True }} := by
  iintro %Φ ⟨#Hlock, HR⟩ HΦ
  ihave #Hchan := is_lock_channel_is_chan γ ch R $$ Hlock
  iapply chan.wp_receive ch γ.lchan_name $$ Hchan
  iintro ⟨Hlc1, Hlc2⟩
  iapply lock_channel_recv_au γ ch R (fun v ok => Φ (PairV #v #ok)) $$ Hlock HR Hlc1 HΦ

end lock_channel

end Perennial
