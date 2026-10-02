/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_select_tricky_examples.v`:
tricky nonblocking `select` examples.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Base

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : channel.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel

/-- Invariant: channel must be Idle, all other states are False -/
def is_select_nb_only (γ : chan_names) (ch : loc) : IProp GF :=
  iprop("#Hch" ∷ is_chan ch γ Unit ∗
    "#Hinv" ∷ inv nroot (∃ s : chanstate.t Unit,
      "Hoc" ∷ own_chan γ Unit s ∗
      "%Hs" ∷ ⌜match s with | .Idle => True | _ => False⌝))

instance is_select_nb_only_pers (γ : chan_names) (ch : loc) :
    Persistent (is_select_nb_only (GF := GF) γ ch) := by
  unfold is_select_nb_only; infer_instance

theorem start_select_nb_only (ch : loc) (γ : chan_names) :
    ⊢ is_chan (GF := GF) ch γ Unit -∗ own_chan γ Unit .Idle ={⊤}=∗ is_select_nb_only γ ch := by
  iintro #Hch Hoc
  imod inv_alloc nroot ⊤ (∃ s : chanstate.t Unit,
      "Hoc" ∷ own_chan (GF := GF) γ Unit s ∗
      "%Hs" ∷ ⌜match s with | .Idle => True | _ => False⌝) $$ [Hoc] with #Hinv
  · inext; iexists .Idle; iframe; ipureintro; trivial
  imodintro
  unfold is_select_nb_only
  iframe #

/-- Nonblocking send AU - vacuous since we ban all send preconditions -/
theorem select_nb_only_send_au (γ : chan_names) (ch : loc) (v : Unit) (Φ Φnotready : IProp GF) :
    ⊢ is_select_nb_only γ ch -∗ Φnotready -∗ nonblocking_send_au γ v Φ Φnotready := by
  iintro #Hnb Hnotready
  unfold is_select_nb_only nonblocking_send_au nonblocking_send_au_inner
  icases Hnb with ⟨#Hch, #Hinv⟩
  isplit
  · iinv Hinv with ⟨%s, >Hoc, >%Hs⟩ Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc
    rcases s with _ | _ | _ | _ | _ | _ | _ <;> simp at Hs
    dsimp only
    itrivial
  · iexact Hnotready

/-- Nonblocking receive AU - vacuous since we ban all receive preconditions -/
theorem select_nb_only_rcv_au (γ : chan_names) (ch : loc) (Φ : Unit → Bool → IProp GF)
    (Φnotready : IProp GF) :
    ⊢ is_select_nb_only γ ch -∗ Φnotready -∗ nonblocking_recv_au γ Unit Φ Φnotready := by
  iintro #Hnb Hnotready
  unfold is_select_nb_only nonblocking_recv_au nonblocking_recv_au_inner
  icases Hnb with ⟨#Hch, #Hinv⟩
  isplit
  · iinv Hinv with ⟨%s, >Hoc, >%Hs⟩ Hclose
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists s
    iframe Hoc
    rcases s with _ | _ | _ | _ | _ | _ | _ <;> simp at Hs
    dsimp only
    itrivial
  · iexact Hnotready

set_option goose.wp.extras true

/-- Example 1 -/
theorem wp_select_nb_not_ready :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! select_nb_not_ready)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#His_chan, -, Hownchan⟩
  imod start_select_nb_only ch γ $$ His_chan Hownchan with #Hnb
  ipersist ch
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply_core chan.wp_select_nonblocking
    isplit
    · simp only [BigAndL.bigAndL_cons, BigAndL.bigAndL_nil]
      isplit
      · unfold chan.nonblocking_clause_pre
        iexists Unit, _, _, _, _, ch, γ
        isplitr
        · ipureintro; rfl
        isplitr
        · iexact His_chan
        iapply select_nb_only_rcv_au $$ Hnb []
        itrivial
      · itrivial
    · wp_auto
      itrivial
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · simp only [BigAndL.bigAndL_cons, BigAndL.bigAndL_nil]
    isplit
    · unfold chan.nonblocking_clause_pre
      iexists Unit, _, _, _, _, ch, γ, ()
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iexact His_chan
      iapply select_nb_only_send_au $$ Hnb []
      itrivial
    · itrivial
  · wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
