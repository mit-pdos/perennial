/-
Iris reasoning principles for core Grove FFI. Port of
`src/goose_lang/ffi/grove_ffi/grove_ffi.v`.

Differences from the Rocq version:
* No crash reasoning: `ffi_restart`, `ffi_crash_rel`, `file_pointsto_post_crash`
  and the `IntoCrash` instance are omitted.
* The ghost state uses iris-lean's `genHeapGS` (with `gmap` as the map type)
  and `MonoNatG`. The `groveGS`/`groveNodeGS` fields are not instances (there
  are two `genHeapGS` and possibly two `MonoNatG` in play); definitions pass
  them explicitly.
* `|NC={E}=>` becomes `|={E}=>`.
* `wp_SendOp` drops the unused `(l : loc)` parameter.
* `ffi_global_start`/`ffi_local_start` (and the adequacy instance
  `grove_interp_adequacy`) live in `Perennial/GooseLang/Ffi/GroveFfi/Adequacy.lean`.
-/
import Iris.BI.Lib.GenHeap
import Iris.BI.Lib.MonoNat
import Perennial.GooseLang.Lifting
import Perennial.GooseLang.Ffi.GroveFfi.Impl
import Perennial.GooseLang.Ffi.GenHeap

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Grove semantic interpretation -/

class groveGS (GF : BundledGFunctors) where
  groveG_net_heapG : genHeapGS endpoint (gset message) GF (gmap endpoint)
  grove_time_name : GName
  groveG_timeG : MonoNatG GF

class groveGpreS (GF : BundledGFunctors) where
  grove_preG_net_heapG : genHeapPreS endpoint (gset message) GF (gmap endpoint)
  grove_preG_files_heapG : genHeapPreS byte_string (List w8) GF (gmap byte_string)
  grove_preG_tscG : MonoNatG GF

class groveNodeGS (GF : BundledGFunctors) where
  groveG_preS : groveGpreS GF
  grove_tsc_name : GName
  groveG_files_heapG : genHeapGS byte_string (List w8) GF (gmap byte_string)

section grove
variable {GF : BundledGFunctors}

/-- The authoritative mono-nat for the global time. -/
def grove_time_auth (hG : groveGS GF) (t : Nat) : IProp GF :=
  @MonoNat.auth_own GF hG.groveG_timeG hG.grove_time_name (.own 1) (MaxNat.ofNat t)

/-- The authoritative mono-nat for a node's TSC. -/
def grove_tsc_auth (hL : groveNodeGS GF) (t : Nat) : IProp GF :=
  @MonoNat.auth_own GF hL.groveG_preS.grove_preG_tscG hL.grove_tsc_name (.own 1) (MaxNat.ofNat t)

/-- The GooseLang `ffi_interp` for Grove. -/
@[reducible] def grove_interp : ffi_interp grove_model where
  ffiGlobalGS := groveGS
  ffiLocalGS := groveNodeGS
  ffi_local_ctx hL σ :=
    iprop(grove_tsc_auth hL σ.grove_node_tsc.toNat ∗
      genHeapInterp (G := hL.groveG_files_heapG) σ.grove_node_files)
  ffi_global_ctx hG g :=
    iprop(genHeapInterp (G := hG.groveG_net_heapG) g.grove_net ∗
      grove_time_auth hG g.grove_global_time.toNat)

theorem grove_interp_global_ctx_eq (hG : groveGS GF) (g : grove_global_state) :
    grove_interp.ffi_global_ctx hG g ⊣⊢
      iprop(genHeapInterp (G := hG.groveG_net_heapG) g.grove_net ∗
        @MonoNat.auth_own GF hG.groveG_timeG hG.grove_time_name (.own 1)
          (MaxNat.ofNat g.grove_global_time.toNat)) := .rfl

theorem grove_interp_local_ctx_eq (hL : groveNodeGS GF) (σ : grove_node_state) :
    grove_interp.ffi_local_ctx hL σ ⊣⊢
      iprop(@MonoNat.auth_own GF hL.groveG_preS.grove_preG_tscG hL.grove_tsc_name (.own 1)
          (MaxNat.ofNat σ.grove_node_tsc.toNat) ∗
        genHeapInterp (G := hL.groveG_files_heapG) σ.grove_node_files) := .rfl

/-- Rocq `c c↦ ms`. -/
def chan_pointsto (hG : groveGS GF) (c : endpoint) (ms : gset message) : IProp GF :=
  pointsTo (G := hG.groveG_net_heapG) c (.own 1) ms

/-- Rocq `s f↦{q} c`. -/
def file_pointsto (hL : groveNodeGS GF) (f : byte_string) (q : DFrac) (c : List w8) : IProp GF :=
  pointsTo (G := hL.groveG_files_heapG) f q c

instance chan_pointsto_timeless (hG : groveGS GF) (c : endpoint) (ms : gset message) :
    Timeless (chan_pointsto hG c ms) := by
  unfold chan_pointsto; infer_instance

instance file_pointsto_timeless (hL : groveNodeGS GF) (f : byte_string) (q : DFrac)
    (c : List w8) : Timeless (file_pointsto hL f q c) := by
  unfold file_pointsto; infer_instance

end grove

section lifting
attribute [local instance] grove_op grove_model grove_semantics grove_interp
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev goose_groveGS : groveGS GF := G.goose_ffiGlobalGS
abbrev goose_groveNodeGS : groveNodeGS GF := L.goose_ffiLocalGS

/- Rocq notations `c c↦ ms`, `s f↦{q} c` and `s f↦ c`. -/
namespace grove_ffi
scoped notation:50 c:51 " c↦ " ms:50 => chan_pointsto goose_groveGS c ms
scoped notation:50 f:51 " f↦{" q "} " c:50 => file_pointsto goose_groveNodeGS f q c
scoped notation:50 f:51 " f↦ " c:50 => file_pointsto goose_groveNodeGS f (DFrac.own 1) c
end grove_ffi
open grove_ffi

def chan_meta_token (c : endpoint) (E : CoPset) : IProp GF :=
  metaToken (G := (goose_groveGS (G := G)).groveG_net_heapG) c E

def chan_meta {A : Type} [Pos.Countable A] (c : endpoint) (N : Namespace) (x : A) : IProp GF :=
  metaInfo (G := (goose_groveGS (G := G)).groveG_net_heapG) c N x

/-- "The TSC is at least" -/
def tsc_lb (time : Nat) : IProp GF :=
  @MonoNat.lb_own GF (goose_groveNodeGS (L := L)).groveG_preS.grove_preG_tscG
    (goose_groveNodeGS (L := L)).grove_tsc_name (MaxNat.ofNat time)

def is_time_lb (t : w64) : IProp GF :=
  @MonoNat.lb_own GF (goose_groveGS (G := G)).groveG_timeG (goose_groveGS (G := G)).grove_time_name
    (MaxNat.ofNat t.toNat)

def own_time (t : w64) : IProp GF :=
  grove_time_auth (goose_groveGS (G := G)) t.toNat

instance is_time_lb_persistent (t : w64) : Persistent (is_time_lb (G := G) t) := by
  unfold is_time_lb; infer_instance

instance tsc_lb_persistent (t : Nat) : Persistent (tsc_lb (L := L) t) := by
  unfold tsc_lb; infer_instance

theorem own_time_get_lb (t : w64) : ⊢ own_time (G := G) t -∗ is_time_lb t := by
  unfold own_time is_time_lb grove_time_auth
  exact @MonoNat.lb_own_get GF (goose_groveGS (G := G)).groveG_timeG _ _ _

theorem is_time_lb_mono (t t' : w64) (h : t.toNat ≤ t'.toNat) :
    ⊢ is_time_lb (G := G) t' -∗ is_time_lb t := by
  unfold is_time_lb
  exact @MonoNat.lb_own_le GF (goose_groveGS (G := G)).groveG_timeG _ _ _
    ((MaxNat.le_toNat _ _).mpr h)

theorem tsc_lb_0 : ⊢ |==> tsc_lb (L := L) 0 := by
  unfold tsc_lb
  exact @MonoNat.lb_own_0 GF (goose_groveNodeGS (L := L)).groveG_preS.grove_preG_tscG _

theorem tsc_lb_weaken (t1 t2 : Nat) (h : t1 ≤ t2) : ⊢ tsc_lb (L := L) t2 -∗ tsc_lb t1 := by
  unfold tsc_lb
  exact @MonoNat.lb_own_le GF (goose_groveNodeGS (L := L)).groveG_preS.grove_preG_tscG _ _ _
    ((MaxNat.le_toNat _ _).mpr h)

abbrev connection_socket (c_l : endpoint) (c_r : endpoint) : val :=
  ExtV (ConnectionSocketV c_l c_r)
abbrev listen_socket (c : endpoint) : val :=
  ExtV (ListenSocketV c)
abbrev bad_socket : val :=
  ExtV BadSocketV

theorem grove_global_ctx_eq (g : grove_global_state) :
    ffi_global_ctx G.goose_ffiGlobalGS g ⊣⊢
      iprop(genHeapInterp (G := (goose_groveGS (G := G)).groveG_net_heapG) g.grove_net ∗
        grove_time_auth (goose_groveGS (G := G)) g.grove_global_time.toNat) := .rfl

theorem grove_local_ctx_eq (σ : grove_node_state) :
    ffi_local_ctx L.goose_ffiLocalGS σ ⊣⊢
      iprop(grove_tsc_auth (goose_groveNodeGS (L := L)) σ.grove_node_tsc.toNat ∗
        genHeapInterp (G := (goose_groveNodeGS (L := L)).groveG_files_heapG)
          σ.grove_node_files) := .rfl

open EctxLanguage

/-- The core lifting lemma for Grove operations. -/
theorem wp_GroveOp (op : GroveOp) (v : val) (Φ : val → IProp GF) :
    ▷ (∀ σ1 g1 e2 σ2 g2, ⌜is_grove_ffi_step op v e2 σ1 σ2 g1 g2⌝ -∗
        ffi_local_ctx L.goose_ffiLocalGS σ1 -∗ ffi_global_ctx G.goose_ffiGlobalGS g1 ={E}=∗
        ffi_local_ctx L.goose_ffiLocalGS σ2 ∗ ffi_global_ctx G.goose_ffiGlobalGS g2 ∗
        WP e2 @ s; E {{ Φ }})
    ⊢ WP (ExternalOp op (Val v)) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro HΦ
  iapply wp_lift_step rfl
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  have Hred : BaseStep.Reducible (ExternalOp op (Val v), σ₁) :=
    ⟨[], _, _, [], base_step.ExternalOpS op v _ σ₁ _
      ⟨σ₁.1.world, σ₁.2.global_world, rfl, .inl ⟨rfl, rfl, rfl⟩⟩⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducible]
    exact primStep_reducible_of_baseStep_reducible Hred
  inext
  iintro %e₂ %σ₂ %eₜ %Hstep Hcred
  have Hbs := baseStep_of_primStep_of_baseStep_reducible Hred Hstep
  cases Hbs with
  | ExternalOpS _ _ _ _ _ Hffi_step =>
  obtain ⟨s', w', rfl, Hcase⟩ := Hffi_step
  imod Hclose
  rcases Hcase with ⟨rfl, rfl, rfl⟩ | Hgrove
  · imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph]
    · iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    isplitl [IH HΦ]
    · iapply IH
      inext
      iexact HΦ
    iapply BigSepL.bigSepL_nil.2
    itrivial
  · imod HΦ $$ %_ %_ %_ %_ %_ %Hgrove Hffi Hgffi with ⟨Hffi, Hgffi, Hwp⟩
    imodintro
    isplitl [Hheap Hffi Hgs Hgffi Hproph]
    · iapply (goose_stateInterp_eq _ _ _ _).mpr
      dsimp only [List.nil_append]
      iframe
      ipureintro; exact Hlctx
    iframe Hwp
    iapply BigSepL.bigSepL_nil.2
    itrivial

theorem wp_ListenOp (c : w64) :
    {{ (True : IProp GF) }} (ExternalOp GroveOp.ListenOp (Val (#c))) @ s; E
    {{ RET listen_socket c; True }} := by
  iintro %Φ _ HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain rfl := He c rfl
  imodintro
  iframe Hl Hg
  iapply wp_value'
  iapply HΦ
  itrivial

theorem wp_ConnectOp (c_r : endpoint) :
    {{ (True : IProp GF) }} (ExternalOp GroveOp.ConnectOp (Val (#c_r))) @ s; E
    {{ (err : Bool) (c_l : endpoint),
      RET PairV (#err) (if err then bad_socket else connection_socket c_l c_r);
      if err then True else c_l c↦ ∅ }} := by
  iintro %Φ _ HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, c_l, Hfresh, H⟩ := Hstep c_r rfl
  cases c_l with
  | none =>
    obtain ⟨rfl, rfl⟩ := H
    imodintro
    iframe Hl Hg
    iapply wp_value'
    rw [show PairV (#true) (ExtV BadSocketV) =
      PairV (#true) (if true then bad_socket else connection_socket 0 c_r) from rfl]
    iapply HΦ $$ %true %0
    simp only [↓reduceIte]
    itrivial
  | some c_l =>
    obtain ⟨rfl, rfl⟩ := H
    icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
    imod genHeap_alloc' (G := (goose_groveGS (G := G)).groveG_net_heapG) (v := (∅ : gset message))
      (show g1.grove_net !! c_l = none from Hfresh) $$ Hnet with ⟨Hnet, Hc, -⟩
    imodintro
    iframe Hl
    isplitl [Hnet Htime]
    · iapply (grove_global_ctx_eq _).mpr; unfold grove_time_auth; iframe
    iapply wp_value'
    rw [show PairV (#false) (ExtV (ConnectionSocketV c_l c_r)) =
      PairV (#false) (if false then bad_socket else connection_socket c_l c_r) from rfl]
    iapply HΦ $$ %false %c_l
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold chan_pointsto
    iexact Hc

theorem wp_AcceptOp (c_l : endpoint) :
    {{ (True : IProp GF) }} (ExternalOp GroveOp.AcceptOp (Val (listen_socket c_l))) @ s; E
    {{ (c_r : endpoint), RET connection_socket c_l c_r; True }} := by
  iintro %Φ _ HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain ⟨c_r, -, rfl⟩ := He c_l rfl
  imodintro
  iframe Hl Hg
  iapply wp_value'
  iapply HΦ $$ %c_r
  itrivial

theorem wp_SendOp (c_l c_r : endpoint) (ms : gset message) (data : List w8) :
    {{ (c_r c↦ ms : IProp GF) }}
      (ExternalOp GroveOp.SendOp (Val (PairV (connection_socket c_l c_r) (#data)))) @ s; E
    {{ (err_early err_late : Bool), RET #(err_early || err_late);
       c_r c↦ (if err_early then ms else ms ∪ {[Message c_l data]}) }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  have H := He data c_l c_r rfl
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold chan_pointsto
  icases genHeap_lookup (G := (goose_groveGS (G := G)).groveG_net_heapG) $$ Hnet Hc with %Heq
  change g1.grove_net !! c_r = some ms at Heq
  rw [Heq] at H
  obtain ⟨b, rfl, rfl⟩ := H
  imod genHeap_update' (G := (goose_groveGS (G := G)).groveG_net_heapG)
    (v₂ := ms ∪ {[Message c_l data]}) $$ [Hnet Hc] with ⟨Hnet, Hc⟩
  · iframe
  imodintro
  iframe Hl
  isplitl [Hnet Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold grove_time_auth; iframe
  iapply wp_value'
  rw [show (#b : val) = #(false || b) from by simp]
  iapply HΦ $$ %false %b
  simp only [Bool.false_eq_true, ↓reduceIte]
  iexact Hc

theorem wp_RecvOp (c_l c_r : endpoint) (ms : gset message) :
    {{ (c_l c↦ ms : IProp GF) }}
      (ExternalOp GroveOp.RecvOp (Val (connection_socket c_l c_r))) @ s; E
    {{ (err : Bool) (data : List w8), RET PairV (#err) (#data);
        ⌜if err then True else Message c_r data ∈ ms⌝ ∗ c_l c↦ ms }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain ⟨err, H⟩ := He c_l c_r rfl
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold chan_pointsto
  icases genHeap_lookup (G := (goose_groveGS (G := G)).groveG_net_heapG) $$ Hnet Hc with %Heq
  change g1.grove_net !! c_l = some ms at Heq
  rw [Heq] at H
  imodintro
  iframe Hl
  isplitl [Hnet Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold grove_time_auth; iframe
  cases err with
  | true =>
    obtain rfl := H
    iapply wp_value'
    iapply HΦ $$ %true %([] : List w8)
    iframe Hc
    ipureintro; simp
  | false =>
    obtain ⟨d, Hd, rfl⟩ := H
    iapply wp_value'
    iapply HΦ $$ %false %d
    iframe Hc
    ipureintro; simpa using Hd

theorem wp_FileReadOp (f : go_string) (q : DFrac) (c : List w8) :
    {{ (f f↦{q} c : IProp GF) }} (ExternalOp GroveOp.FileReadOp (Val (#f))) @ s; E
    {{ RET #c; f f↦{q} c }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  have H := He f rfl
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold file_pointsto
  icases genHeap_lookup (G := (goose_groveNodeGS (L := L)).groveG_files_heapG) $$ Hfiles Hc
    with %Heq
  change σ1.grove_node_files !! f = some c at Heq
  rw [Heq] at H
  obtain rfl := H
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold grove_tsc_auth; iframe
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_FileWriteOp (f : go_string) (old new : List w8) :
    {{ (f f↦ old : IProp GF) }} (ExternalOp GroveOp.FileWriteOp (Val (PairV (#f) (#new)))) @ s; E
    {{ RET #(); f f↦ new }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := He f new rfl
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold file_pointsto
  imod genHeap_update' (G := (goose_groveNodeGS (L := L)).groveG_files_heapG) (v₂ := new)
    $$ [Hfiles Hc] with ⟨Hfiles, Hc⟩
  · iframe
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold grove_tsc_auth; iframe
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_FileAppendOp (f : go_string) (old new : List w8) :
    {{ (f f↦ old : IProp GF) }} (ExternalOp GroveOp.FileAppendOp (Val (PairV (#f) (#new)))) @ s; E
    {{ RET #(); f f↦ (old ++ new) }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  have H := He f new rfl
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold file_pointsto
  icases genHeap_lookup (G := (goose_groveNodeGS (L := L)).groveG_files_heapG) $$ Hfiles Hc
    with %Heq
  change σ1.grove_node_files !! f = some old at Heq
  rw [Heq] at H
  obtain ⟨rfl, rfl⟩ := H
  imod genHeap_update' (G := (goose_groveNodeGS (L := L)).groveG_files_heapG) (v₂ := old ++ new)
    $$ [Hfiles Hc] with ⟨Hfiles, Hc⟩
  · iframe
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold grove_tsc_auth; iframe
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_GetTscOp (prev_time : Nat) :
    {{ tsc_lb (L := L) prev_time }} (ExternalOp GroveOp.GetTscOp (Val (#()))) @ s; E
    {{ (new_time : w64), RET #new_time;
      ⌜prev_time ≤ new_time.toNat⌝ ∗ tsc_lb new_time.toNat }} := by
  iintro %Φ Hlb HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, new_time, Hle, rfl, rfl⟩ := Hstep
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold tsc_lb grove_tsc_auth
  icases @MonoNat.auth_lb_own_valid GF (goose_groveNodeGS (L := L)).groveG_preS.grove_preG_tscG
    _ _ _ _ $$ Htsc Hlb with %⟨-, Hprev⟩
  have Hprev' := (MaxNat.le_toNat _ _).mp Hprev
  imod @MonoNat.own_update GF (goose_groveNodeGS (L := L)).groveG_preS.grove_preG_tscG _ _
    (MaxNat.ofNat new_time.toNat) ((MaxNat.le_toNat _ _).mpr Hle) $$ Htsc with ⟨Htsc, Hlb'⟩
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold grove_tsc_auth; iframe
  iapply wp_value'
  iapply HΦ $$ %new_time
  iframe Hlb'
  ipureintro
  exact Nat.le_trans Hprev' Hle

theorem wp_GetTimeRangeOp (Φ : val → IProp GF) :
    ⊢ (∀ (l h t : w64), ⌜t.toNat ≤ h.toNat⌝ -∗ ⌜l.toNat ≤ t.toNat⌝ -∗
        own_time (G := G) t ={E}=∗ own_time t ∗ Φ (PairV (#l) (#h))) -∗
      WP (ExternalOp GroveOp.GetTimeRangeOp (Val (#()))) @ s; E {{ Φ }} := by
  unfold own_time grove_time_auth
  iintro HΦ
  iapply wp_GroveOp
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, new_time, low, high, Hle, Hlow, Hhigh, rfl, rfl⟩ := Hstep
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold grove_time_auth
  imod @MonoNat.own_update GF (goose_groveGS (G := G)).groveG_timeG _ _
    (MaxNat.ofNat new_time.toNat) ((MaxNat.le_toNat _ _).mpr Hle) $$ Htime with ⟨Htime, -⟩
  imod HΦ $$ %low %high %new_time %Hhigh %Hlow Htime with ⟨Htime, HΦ⟩
  imodintro
  iframe Hl
  isplitl [Hnet Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold grove_time_auth; iframe
  iapply wp_value'
  iexact HΦ

theorem wp_time_acc (e : expr) (Φ : val → IProp GF) (h : to_val e = none) :
    ⊢ (∀ t, own_time (G := G) t ={E}=∗ own_time t ∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  unfold own_time
  iintro Hacc
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  icases (grove_global_ctx_eq _).mp $$ Hgffi with ⟨Hnet, Htime⟩
  imod Hacc $$ %σ₁.2.global_world.grove_global_time Htime with ⟨Htime, Hwp⟩
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  iapply Hwp $$ %σ₁ %ns %obs %obs' %nt
  iapply (goose_stateInterp_eq _ _ _ _).mpr
  iframe
  isplitr
  · ipureintro; exact Hlctx
  iapply (grove_global_ctx_eq _).mpr
  iframe

end lifting

end Perennial
