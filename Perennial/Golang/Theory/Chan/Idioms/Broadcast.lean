/-
Port of `new/golang/theory/chan/idioms/broadcast.v`.

A pattern for channel usage: a channel that never has anything sent, and is only closed at
some point. Closing broadcasts a persistent proposition to all readers.

Lean notes: Rocq's `own γ (to_dfrac_agree dq b)` is `dghost_var γ dq b`
(`Perennial/Ghost/DGhostVar.lean`).
-/
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

structure broadcast_internal_names where
  done_gn : GName

namespace broadcast
inductive t where
  | Pending
  | Done
  | Unknown
end broadcast

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]

/-- The broadcast invariant. -/
def broadcast_inv (γ : chan_names) (γch : broadcast_internal_names) (Q : IProp GF) : IProp GF :=
  iprop(∃ (st : chanstate.t Unit),
    "Hch" ∷ own_chan γ Unit st ∗
    "Hs" ∷ (match st with
      | .Idle | .RcvPending => dghost_var γch.done_gn (.own (1 : Qp).half) false
      | .Closed [] => iprop(□ Q ∗ dghost_var γch.done_gn .discard true)
      | _ => iprop(False)))

/-- (Note (Rocq): could make the namespace be user-chosen.) -/
def is_broadcast_chan_internal (ch : chan.t) (γ : chan_names) (γch : broadcast_internal_names)
    (Q : IProp GF) : IProp GF :=
  iprop("#His_ch" ∷ is_chan ch γ Unit ∗ "#Hinv" ∷ inv nroot (broadcast_inv γ γch Q))

instance is_broadcast_chan_internal_pers (ch : chan.t) γ γch (Q : IProp GF) :
    Persistent (is_broadcast_chan_internal ch γ γch Q) := by
  unfold is_broadcast_chan_internal; infer_instance

def own_broadcast_chan_def (ch : chan.t) (γ : chan_names) (Q : IProp GF) (st : broadcast.t) :
    IProp GF :=
  iprop(∃ γch,
    "#Hinv" ∷ is_broadcast_chan_internal ch γ γch Q ∗
    "Hown" ∷ (match st with
      | .Pending => dghost_var γch.done_gn (.own (1 : Qp).half) false
      | .Done => dghost_var γch.done_gn .discard true
      | .Unknown => iprop(True)))
/-- (Rocq: `Opaque own_broadcast_chan`) -/
@[irreducible] def own_broadcast_chan (ch : chan.t) (γ : chan_names) (Q : IProp GF)
    (st : broadcast.t) : IProp GF := own_broadcast_chan_def ch γ Q st
theorem own_broadcast_chan_unseal : @own_broadcast_chan = @own_broadcast_chan_def := by
  funext; with_unfolding_all rfl

instance own_broadcast_chan_Unknown_pers (ch : chan.t) γ (Q : IProp GF) :
    Persistent (own_broadcast_chan ch γ Q .Unknown) := by
  rw [own_broadcast_chan_unseal]; unfold own_broadcast_chan_def; infer_instance

instance own_broadcast_chan_Done_pers (ch : chan.t) γ (Q : IProp GF) :
    Persistent (own_broadcast_chan ch γ Q .Done) := by
  rw [own_broadcast_chan_unseal]; unfold own_broadcast_chan_def; infer_instance

theorem broadcast_chan_done (ch : chan.t) (γ : chan_names) (Q : IProp GF) :
    ⊢ £ 1 -∗ own_broadcast_chan ch γ Q .Done ={⊤}=∗ Q := by
  rw [own_broadcast_chan_unseal]; unfold own_broadcast_chan_def is_broadcast_chan_internal
  iintro Hlc ⟨%γch, ⟨#His_ch, #Hinv⟩, #Hown⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑nroot) $$ Hlc Hi with Hi
  unfold broadcast_inv
  icases Hi with ⟨%st, Hch, Hs⟩
  rcases st with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  case RcvPending =>
    ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hown Hs
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

theorem broadcast_chan_receive (ch : chan.t) (γ : chan_names) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (cl : broadcast.t) :
    ⊢ own_broadcast_chan ch γ Q cl -∗
      (□ Q ∗ own_broadcast_chan ch γ Q .Done -∗ Φ () false) -∗
      recv_au γ Unit Φ := by
  rw [own_broadcast_chan_unseal]; unfold own_broadcast_chan_def is_broadcast_chan_internal recv_au
  iintro ⟨%γch, ⟨#His_ch, #Hinv⟩, Hown⟩ HΦ
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcast_inv
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
    unfold recv_nested_au
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

theorem own_broadcast_chan_open (ch : chan.t) (γ : chan_names) (Q : IProp GF) (st : broadcast.t) :
    own_broadcast_chan ch γ Q st ⊢ ∃ γch, is_broadcast_chan_internal ch γ γch Q ∗
      (match st with
        | .Pending => dghost_var γch.done_gn (.own (1 : Qp).half) false
        | .Done => dghost_var γch.done_gn .discard true
        | .Unknown => iprop(True)) := by
  rw [own_broadcast_chan_unseal]; exact .rfl

theorem own_broadcast_chan_close (ch : chan.t) (γ : chan_names) (Q : IProp GF) (st : broadcast.t)
    (γch : broadcast_internal_names) :
    is_broadcast_chan_internal ch γ γch Q ∗
      (match st with
        | .Pending => dghost_var γch.done_gn (.own (1 : Qp).half) false
        | .Done => dghost_var γch.done_gn .discard true
        | .Unknown => iprop(True)) ⊢ own_broadcast_chan ch γ Q st := by
  rw [own_broadcast_chan_unseal]; unfold own_broadcast_chan_def
  iintro H; iexists γch; iexact H

theorem is_broadcast_chan_internal_inv (ch : chan.t) γ γch (Q : IProp GF) :
    is_broadcast_chan_internal ch γ γch Q ⊢ inv nroot (broadcast_inv γ γch Q) := by
  unfold is_broadcast_chan_internal; iintro ⟨-, $⟩

theorem is_broadcast_chan_internal_is_chan (ch : chan.t) γ γch (Q : IProp GF) :
    is_broadcast_chan_internal ch γ γch Q ⊢ is_chan ch γ Unit := by
  unfold is_broadcast_chan_internal; iintro ⟨$, -⟩

theorem own_broadcast_chan_nonblocking_receive (ch : chan.t) (γ : chan_names) (Q : IProp GF)
    (Φ : Unit → Bool → IProp GF) (Φnotready : IProp GF) (cl : broadcast.t) :
    ⊢ own_broadcast_chan ch γ Q cl -∗
      ((match cl with
        | .Unknown | .Done => iprop(own_broadcast_chan ch γ Q .Done -∗ Φ () false)
        | _ => iprop(True)) ∧
       (match cl with
        | .Unknown | .Pending => iprop(own_broadcast_chan ch γ Q cl -∗ Φnotready)
        | _ => iprop(True))) -∗
      nonblocking_recv_au_alt γ Unit Φ Φnotready := by
  iintro Hown HΦ
  icases own_broadcast_chan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, Hown⟩
  ihave #Hinv := is_broadcast_chan_internal_inv _ _ _ _ $$ Hint
  unfold nonblocking_recv_au_alt
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcast_inv
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
      ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .Idle; dsimp only; iframe
      imodintro
      iapply HΦ
      iapply own_broadcast_chan_close _ _ _ _ γch
      iframe #
      try iframe
  case RcvPending =>
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Done =>
      ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hown Hs
      cases Hbad
    all_goals
      icases HΦ with ⟨-, HΦ⟩
      imod Hclose $$ [Hch Hs] with -
      · inext; iexists .RcvPending; dsimp only; iframe
      imodintro
      iapply HΦ
      iapply own_broadcast_chan_close _ _ _ _ γch
      iframe #
      try iframe
  case Closed.nil =>
    icases Hs with ⟨#HQ, #Hs⟩
    iintro Hch
    imod Hmask with -
    rcases cl with _ | _ | _
    all_goals dsimp only
    case Pending =>
      ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hown Hs
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
      iapply own_broadcast_chan_close _ _ _ _ γch
      dsimp only
      iframe #
  all_goals (iexfalso; iexact Hs)

theorem broadcast_close_au (ch : chan.t) (γch : chan_names) (Q : IProp GF) (Φ : IProp GF) :
    ⊢ own_broadcast_chan ch γch Q .Pending -∗ □ Q -∗
      ▷ (own_broadcast_chan ch γch Q .Done -∗ Φ) -∗ close_au γch Unit Φ := by
  iintro Hown #HQ HΦ
  icases own_broadcast_chan_open _ _ _ _ $$ Hown with ⟨%γi, #Hint, Hown⟩
  ihave #Hinv := is_broadcast_chan_internal_inv _ _ _ _ $$ Hint
  unfold close_au
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold broadcast_inv
  icases Hi with ⟨%st, Hch, Hs⟩
  iexists st
  iframe Hch
  rcases st with _ | _ | _ | _ | _ | _ | (_ | ⟨_, _⟩)
  all_goals dsimp only
  case Idle =>
    iintro Hch
    imod Hmask with -
    imod dghost_var_update_halves true _ _ _ $$ Hown Hs with ⟨Hown, -⟩
    imod dghost_var_persist _ _ _ $$ Hown with #Hown
    imod Hclose $$ [Hch] with -
    · inext; iexists .Closed []; dsimp only; iframe Hch
      isplitl []
      · imodintro; iexact HQ
      · iexact Hown
    imodintro
    iapply HΦ
    iapply own_broadcast_chan_close _ _ _ _ γi
    dsimp only
    iframe #
  case Closed.nil =>
    icases Hs with ⟨-, #Hs⟩
    ihave %Hbad := dghost_var_agree _ _ _ _ _ $$ Hown Hs
    cases Hbad
  all_goals first | itrivial | (iexfalso; iexact Hs)

theorem own_broadcast_chan_is_chan (ch : chan.t) (γ : chan_names) (Q : IProp GF)
    (cl : broadcast.t) :
    ⊢ own_broadcast_chan ch γ Q cl -∗ is_chan ch γ Unit := by
  iintro Hown
  icases own_broadcast_chan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, -⟩
  iapply is_broadcast_chan_internal_is_chan _ _ _ _ $$ Hint

theorem own_broadcast_chan_Unknown (ch : chan.t) (γ : chan_names) (Q : IProp GF)
    (cl : broadcast.t) :
    ⊢ own_broadcast_chan ch γ Q cl -∗ own_broadcast_chan ch γ Q .Unknown := by
  iintro Hown
  icases own_broadcast_chan_open _ _ _ _ $$ Hown with ⟨%γch, #Hint, -⟩
  iapply own_broadcast_chan_close _ _ _ _ γch
  iframe #

theorem wp_broadcast_chan_close {ty : go.type} {dir : go.chan_dir}
    [ty ↓u go.ChannelType dir (go.StructType [])] (ch : chan.t) (γch : chan_names) (Q : IProp GF) :
    {{ own_broadcast_chan ch γch Q .Pending ∗ □ Q }}
      (App (Val #(functions go.close [ty])) (Val #ch))
    {{ RET #(); own_broadcast_chan ch γch Q .Done }} := by
  iintro %Φ ⟨Hown, #HQ⟩ HΦ
  ihave #His := own_broadcast_chan_is_chan _ _ _ _ $$ Hown
  iapply chan.wp_close (ct := ty) (V := Unit) ch γch $$ His
  iintro _
  iapply broadcast_close_au _ _ _ _ $$ Hown HQ HΦ

theorem alloc_broadcast_chan {E : CoPset} (Q : IProp GF) (γ : chan_names) (ch : chan.t) :
    ⊢ is_chan ch γ Unit -∗ own_chan γ Unit .Idle ={E}=∗ own_broadcast_chan ch γ Q .Pending := by
  iintro #Hch Hoc
  imod dghost_var_alloc false with ⟨%tok_gn, Htok⟩
  icases dghost_var_split _ _ (.own (1 : Qp).half) (.own (1 : Qp).half) $$ [Htok] with ⟨Htok, Htok2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Htok
  imod inv_alloc nroot E (broadcast_inv γ ⟨tok_gn⟩ Q) $$ [Hoc Htok2] with #Hinv
  · inext; unfold broadcast_inv; iexists .Idle; dsimp only; iframe
  imodintro
  iapply own_broadcast_chan_close _ _ _ _ ⟨tok_gn⟩
  dsimp only
  iframe
  unfold is_broadcast_chan_internal
  iframe #

end proof

end Perennial
