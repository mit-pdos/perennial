/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel_select_tricky_examples.v`:
tricky nonblocking `select` examples.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel_examples_init
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Base

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

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

/-- The invariant body of `is_select_nb_only`. -/
abbrev select_nb_only_inv (γ : chan_names) : IProp GF :=
  iprop(∃ s : chanstate.t Unit,
    "Hoc" ∷ own_chan γ Unit s ∗
    "%Hs" ∷ ⌜match s with | .Idle => True | _ => False⌝)

/-- Invariant: channel must be Idle, all other states are False -/
def is_select_nb_only (γ : chan_names) (ch : loc) : IProp GF :=
  iprop("#Hch" ∷ is_chan ch γ Unit ∗
    "#Hinv" ∷ inv nroot (select_nb_only_inv γ))

instance is_select_nb_only_pers (γ : chan_names) (ch : loc) :
    Persistent (is_select_nb_only (GF := GF) γ ch) := by
  unfold is_select_nb_only; infer_instance

theorem start_select_nb_only (ch : loc) (γ : chan_names) :
    ⊢ is_chan (GF := GF) ch γ Unit -∗ own_chan γ Unit .Idle ={⊤}=∗ is_select_nb_only γ ch := by
  iintro #Hch Hoc
  imod inv_alloc nroot ⊤ (select_nb_only_inv (GF := GF) γ) $$ [Hoc] with #Hinv
  · inext; iexists .Idle; iframe
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
    · iapply BigAndL.bigAndL_singleton.2
      simp only [chan.nonblocking_clause_pre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
      isplitr
      · ipureintro; rfl
      isplitr
      · iexact His_chan
      iapply select_nb_only_rcv_au $$ Hnb []
      itrivial
    · wp_auto
      itrivial
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblocking_clause_pre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ, ()
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iexact His_chan
    iapply select_nb_only_send_au $$ Hnb []
    itrivial
  · wp_auto
    iapply HΦ
    itrivial


/-- Example 2 -/
theorem wp_select_nb_guaranteed_ready :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! select_nb_guaranteed_ready)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make1 (V := w64) as %ch %γ ⟨#His_ch, %Hcap, Hch⟩
  wp_apply_core chan.wp_close (V := w64) ch γ $$ His_ch
  iintro -
  unfold close_au
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Idle
  iframe Hch
  dsimp only
  iintro Hch
  imod Hmask with -
  imodintro
  wp_auto
  wp_apply_core chan.wp_select_nonblocking_alt [iprop(False)] (own_chan γ w64 (.Closed [])) $$ [HΦ] Hch []
  · iapply BigSepL2.bigSepL2_singleton.2
    iintro HP
    simp only [chan.nonblocking_alt_clause_pre]
    iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ
    isplitr
    · ipureintro; rfl
    isplitr
    · iexact His_ch
    unfold nonblocking_recv_au_alt
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists .Closed []
    iframe HP
    dsimp only
    iintro Hch
    imod Hmask with -
    imodintro
    wp_auto
    iapply HΦ
    itrivial
  · iintro - Hnr
    icases BigSepL.bigSepL_singleton.1 $$ Hnr with Hf
    iexfalso; iexact Hf


/-- Invariant for the "full buffer" situation -/
def is_select_nb_full1 (γ : chan_names) (ch : loc) : IProp GF :=
  iprop("#Hch" ∷ is_chan ch γ w64 ∗
    "%Hcap1" ∷ ⌜γ.chan_cap = W64 1⌝ ∗
    "Hinv" ∷ own_chan γ w64 (.Buffered [W64 0]))

theorem start_select_nb_full1 (ch : loc) (γ : chan_names) :
    ⊢ is_chan (GF := GF) ch γ w64 -∗ ⌜γ.chan_cap = W64 1⌝ -∗
      own_chan γ w64 (.Buffered [W64 0]) ={⊤}=∗ is_select_nb_full1 γ ch := by
  iintro #Hch %Hcap Hoc
  imodintro
  unfold is_select_nb_full1 named
  iframe Hoc
  isplitr
  · iexact Hch
  ipureintro; exact Hcap

theorem select_nb_full1_send_au (γ : chan_names) (ch : loc) (Φ Φnotready : IProp GF) :
    ⊢ is_select_nb_full1 γ ch -∗ Φnotready -∗ nonblocking_send_au γ (W64 0) Φ Φnotready := by
  iintro Hfull Hnotready
  unfold is_select_nb_full1 nonblocking_send_au nonblocking_send_au_inner
  icases Hfull with ⟨#Hch, %Hcap1, Hoc⟩
  isplit
  · iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists .Buffered [W64 0]
    iframe Hoc
    dsimp only
    iintro Hoc
    -- Show this contradicts the capacity bound.
    ihave %Hle := own_chan_buffer_size _ _ _ $$ Hoc
    rw [Hcap1] at Hle
    simp at Hle
  · iexact Hnotready

theorem SendAU_from_empty_buffer_to (_ch : loc) (γ : chan_names) (Φ : IProp GF) :
    ⊢ own_chan γ w64 (.Buffered []) -∗ (own_chan γ w64 (.Buffered [W64 0]) -∗ Φ) -∗
      send_au γ (W64 0) Φ := by
  iintro Hoc Hk
  unfold send_au
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Buffered []
  iframe Hoc
  dsimp only
  iintro Hoc
  simp only [List.nil_append]
  imod Hmask with -
  imodintro
  iapply Hk $$ Hoc

/-- From a send on full buffer (which blocks indefinitely), any Φ can be derived -/
theorem SendAU_full_cap1_vacuous (_ch : loc) (γ : chan_names) (v0 v : w64) (Φ : IProp GF)
    (Hcap : γ.chan_cap = W64 1) :
    ⊢ own_chan γ w64 (.Buffered [v0]) -∗ send_au γ v Φ := by
  iintro Hoc
  unfold send_au
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Buffered [v0]
  iframe Hoc
  dsimp only
  iintro Hoc
  ihave %Hle := own_chan_buffer_size _ _ _ $$ Hoc
  rw [Hcap] at Hle
  simp at Hle

/-- Example 3 -/
theorem wp_select_nb_full_buffer_not_ready :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! select_nb_full_buffer_not_ready)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply chan.wp_make2 (V := w64) (W64 1) $$ [] as %ch %γ ⟨#His_chan, %Hcap, Hown⟩
  · ipureintro; decide
  -- First send: use the empty-buffer AU to fill buffer to [0].
  wp_apply_core chan.wp_send ch (W64 0) γ $$ His_chan
  iintro -
  iapply SendAU_from_empty_buffer_to ch γ $$ Hown
  -- Now we have: own_chan (Buffered [0]) in the continuation.
  iintro Hoc
  imod start_select_nb_full1 ch γ $$ His_chan [] Hoc with Hfull
  · ipureintro; exact Hcap
  wp_auto
  -- Nonblocking select: show send case is disabled -> default taken.
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_singleton.2
    simp only [chan.nonblocking_clause_pre]
    iexists w64, inferInstance, inferInstance, inferInstance, inferInstance, ch, γ, W64 0
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iexact His_chan
    -- AU for send case: forced not-ready by full-buffer invariant.
    iapply select_nb_full1_send_au γ ch $$ Hfull []
    itrivial
  · -- default branch
    wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
