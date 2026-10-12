/-
Tricky nonblocking `select` examples.

This file: the channel invariants and
the atomic updates used by the examples.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.Assumptions]

/-- The invariant body of `isSelectNbOnly`. -/
abbrev selectNbOnlyInv (γ : ChanNames) : IProp GF :=
  iprop(∃ s : ChanState Unit,
    "Hoc" ∷ ownChan γ Unit s ∗
    "%Hs" ∷ ⌜match s with | .Idle => True | _ => False⌝)

/-- Invariant: channel must be Idle, all other states are False -/
def isSelectNbOnly (γ : ChanNames) (ch : Loc) : IProp GF :=
  iprop("#Hch" ∷ isChan ch γ Unit ∗
    "#Hinv" ∷ inv nroot (selectNbOnlyInv γ))

instance isSelectNbOnly_pers (γ : ChanNames) (ch : Loc) :
    Persistent (isSelectNbOnly (GF := GF) γ ch) := by
  unfold isSelectNbOnly; infer_instance

theorem start_select_nb_only (ch : Loc) (γ : ChanNames) :
    ⊢ isChan (GF := GF) ch γ Unit -∗ ownChan γ Unit .Idle ={⊤}=∗ isSelectNbOnly γ ch := by
  iintro #Hch Hoc
  imod inv_alloc nroot ⊤ (selectNbOnlyInv (GF := GF) γ) $$ [Hoc] with #Hinv
  · inext; iexists .Idle; iframe
  imodintro
  unfold isSelectNbOnly
  iframe #

/-- Nonblocking send AU - vacuous since we ban all send preconditions -/
theorem select_nb_only_send_au (γ : ChanNames) (ch : Loc) (v : Unit) (Φ Φnotready : IProp GF) :
    ⊢ isSelectNbOnly γ ch -∗ Φnotready -∗ nonblockingSendAu γ v Φ Φnotready := by
  iintro #Hnb Hnotready
  unfold isSelectNbOnly nonblockingSendAu nonblockingSendAuInner
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
theorem select_nb_only_rcv_au (γ : ChanNames) (ch : Loc) (Φ : Unit → Bool → IProp GF)
    (Φnotready : IProp GF) :
    ⊢ isSelectNbOnly γ ch -∗ Φnotready -∗ nonblockingRecvAu γ Unit Φ Φnotready := by
  iintro #Hnb Hnotready
  unfold isSelectNbOnly nonblockingRecvAu nonblockingRecvAuInner
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

/-- Invariant for the "full buffer" situation -/
def isSelectNbFull1 (γ : ChanNames) (ch : Loc) : IProp GF :=
  iprop("#Hch" ∷ isChan ch γ w64 ∗
    "%Hcap1" ∷ ⌜γ.chanCap = W64 1⌝ ∗
    "Hinv" ∷ ownChan γ w64 (.Buffered [W64 0]))

theorem start_select_nb_full1 (ch : Loc) (γ : ChanNames) :
    ⊢ isChan (GF := GF) ch γ w64 -∗ ⌜γ.chanCap = W64 1⌝ -∗
      ownChan γ w64 (.Buffered [W64 0]) ={⊤}=∗ isSelectNbFull1 γ ch := by
  iintro #Hch %Hcap Hoc
  imodintro
  unfold isSelectNbFull1 named
  iframe Hoc
  isplitr
  · iexact Hch
  ipureintro; exact Hcap

theorem select_nb_full1_send_au (γ : ChanNames) (ch : Loc) (Φ Φnotready : IProp GF) :
    ⊢ isSelectNbFull1 γ ch -∗ Φnotready -∗ nonblockingSendAu γ (W64 0) Φ Φnotready := by
  iintro Hfull Hnotready
  unfold isSelectNbFull1 nonblockingSendAu nonblockingSendAuInner
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
    ihave %Hle := ownChan_buffer_size _ _ _ $$ Hoc
    rw [Hcap1] at Hle
    simp at Hle
  · iexact Hnotready

theorem SendAU_from_empty_buffer_to (_ch : Loc) (γ : ChanNames) (Φ : IProp GF) :
    ⊢ ownChan γ w64 (.Buffered []) -∗ (ownChan γ w64 (.Buffered [W64 0]) -∗ Φ) -∗
      sendAu γ (W64 0) Φ := by
  iintro Hoc Hk
  unfold sendAu
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
theorem SendAU_full_cap1_vacuous (_ch : Loc) (γ : ChanNames) (v0 v : w64) (Φ : IProp GF)
    (Hcap : γ.chanCap = W64 1) :
    ⊢ ownChan γ w64 (.Buffered [v0]) -∗ sendAu γ v Φ := by
  iintro Hoc
  unfold sendAu
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists .Buffered [v0]
  iframe Hoc
  dsimp only
  iintro Hoc
  ihave %Hle := ownChan_buffer_size _ _ _ $$ Hoc
  rw [Hcap] at Hle
  simp at Hle

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel

end Perennial
