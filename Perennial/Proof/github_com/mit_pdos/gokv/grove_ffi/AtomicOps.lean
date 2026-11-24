/-
Logically atomic specs of the Grove extension's operations that `grove_ffi`'s trusted models
call (`Perennial/GooseLang/Ext/Grove/Specs.lean` has their Hoare triples): the client's
mask-changing update runs at the operation's step. An operation may stutter before it steps,
so it is not `Atomic` and a triple cannot be opened around it; these lemmas run the update
inside `wp_GroveOp`'s step instead. `wp_SendOp_atomic` also states that the message is always
added (the step does, whatever it returns). (`FileAppend`'s model appends in several steps; its
proof uses `wp_FileAppendOp` for each.)
-/
module

public import Perennial.Proof.GrovePrelude

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode grove_ext

namespace github_com.mit_pdos.gokv.grove_ffi

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

theorem wp_SendOp_atomic (c_l c_r : Endpoint) (data : List w8) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ ms : GSet message, c_r c↦ ms ∗
      (c_r c↦ (ms ∪ {[Message c_l data]}) ={∅,E}=∗ ∀ b : Bool, Φ #b))
    ⊢ WP (ExternalOp groveExt.name "Send" (Val (PairV (connectionSocket c_l c_r) (#data))))
        @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_GroveOp
  case Hop => decide
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  have H := He data c_l c_r rfl
  imod HAU with ⟨%ms, Hc, Hclose⟩
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Hlis, Htime⟩
  unfold chanPointsto
  icases genHeap_lookup (G := (gooseGroveGS (G := G)).groveGNetHeapG) $$ Hnet Hc with %Heq
  change g1.groveNet !! c_r = some ms at Heq
  rw [Heq] at H
  obtain ⟨b, rfl, rfl⟩ := H
  imod genHeap_update' (G := (gooseGroveGS (G := G)).groveGNetHeapG)
    (v₂ := ms ∪ {[Message c_l data]}) $$ [Hnet Hc] with ⟨Hnet, Hc⟩
  · iframe
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hl
  isplitl [Hnet Hlis Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold groveTimeAuth; iframe
  iapply wp_value'
  iapply HΦ

theorem wp_RecvOp_atomic (c_l c_r : Endpoint) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ ms : GSet message, c_l c↦ ms ∗
      (c_l c↦ ms ={∅,E}=∗ ∀ (err : Bool) (data : List w8),
        ⌜if err then True else Message c_r data ∈ ms⌝ -∗ Φ (PairV (#err) (#data))))
    ⊢ WP (ExternalOp groveExt.name "Receive" (Val (connectionSocket c_l c_r))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_GroveOp
  case Hop => decide
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain ⟨err, H⟩ := He c_l c_r rfl
  imod HAU with ⟨%ms, Hc, Hclose⟩
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Hlis, Htime⟩
  unfold chanPointsto
  icases genHeap_lookup (G := (gooseGroveGS (G := G)).groveGNetHeapG) $$ Hnet Hc with %Heq
  change g1.groveNet !! c_l = some ms at Heq
  rw [Heq] at H
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hl
  isplitl [Hnet Hlis Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold groveTimeAuth; iframe
  cases err with
  | true =>
    obtain rfl := H
    iapply wp_value'
    iapply HΦ $$ %true %([] : List w8)
    ipureintro; simp
  | false =>
    obtain ⟨d, Hd, rfl⟩ := H
    iapply wp_value'
    iapply HΦ $$ %false %d
    ipureintro; simpa using Hd

theorem wp_FileReadOp_atomic (f : GoString) (Hf : ValidFileName f) (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ (q : DFrac) (c : List w8), f f↦{q} c ∗ (f f↦{q} c ={∅,E}=∗ Φ #c))
    ⊢ WP (ExternalOp groveExt.name "FileRead" (Val (#f))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_GroveOp
  case Hop => decide
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  have H := He f rfl
  rw [if_pos Hf] at H
  imod HAU with ⟨%q, %c, Hc, Hclose⟩
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold filePointsto
  icases genHeap_lookup (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG) $$ Hfiles Hc
    with %Heq
  change σ1.groveNodeFiles !! f = some c at Heq
  rw [Heq] at H
  obtain rfl := H
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iexact HΦ

theorem wp_FileWriteOp_atomic (f : GoString) (new : List w8) (Hf : ValidFileName f)
    (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ old : List w8, f f↦ old ∗ (f f↦ new ={∅,E}=∗ Φ #()))
    ⊢ WP (ExternalOp groveExt.name "FileWrite" (Val (PairV (#f) (#new)))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_GroveOp
  case Hop => decide
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  have H := He f new rfl
  rw [if_pos Hf] at H
  obtain ⟨rfl, rfl⟩ := H
  imod HAU with ⟨%old, Hc, Hclose⟩
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold filePointsto
  imod genHeap_update' (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG) (v₂ := new)
    $$ [Hfiles Hc] with ⟨Hfiles, Hc⟩
  · iframe
  imod Hclose $$ Hc with HΦ
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iexact HΦ

theorem wp_GetTscOp_atomic (Φ : val → IProp GF) :
    (|={E,∅}=> ∃ prev : Nat, tscLb (L := L) prev ∗
      (∀ t : w64, ⌜prev ≤ t.toNat⌝ -∗ tscLb t.toNat ={∅,E}=∗ Φ #t))
    ⊢ WP (ExternalOp groveExt.name "GetTSC" (Val (#()))) @ s; E {{ Φ }} := by
  iintro HAU
  iapply wp_GroveOp
  case Hop => decide
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, new_time, Hle, rfl, rfl⟩ := Hstep
  imod HAU with ⟨%prev, Hlb, Hclose⟩
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold tscLb groveTscAuth
  icases @MonoNat.auth_lb_own_valid GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG
    _ _ _ _ $$ Htsc Hlb with % ⟨-, Hprev⟩
  have Hprev' := (MaxNat.le_toNat _ _).mp Hprev
  imod @MonoNat.own_update GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG _ _
    (MaxNat.ofNat new_time.toNat) ((MaxNat.le_toNat _ _).mpr Hle) $$ Htsc with ⟨Htsc, Hlb'⟩
  imod Hclose $$ %new_time %(Nat.le_trans Hprev' Hle) Hlb' with HΦ
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iexact HΦ

end lifting

end github_com.mit_pdos.gokv.grove_ffi

end Perennial
