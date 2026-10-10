/-
Iris reasoning principles for core Grove FFI.

Notes:
* No crash reasoning (no restart or crash relation, no post-crash points-to).
* The ghost state uses iris-lean's `genHeapGS` (with `gmap` as the map type)
  and `MonoNatG`. The `groveGS`/`groveNodeGS` fields are not instances (there
  are two `genHeapGS` and possibly two `MonoNatG` in play); definitions pass
  them explicitly.
* Updates are plain fancy updates `|={E}=>`.
* `ffiGlobalStart`/`ffiLocalStart` (and the adequacy instance
  `grove_interp_adequacy`) live in `Perennial/GooseLang/Ffi/GroveFfi/Adequacy.lean`.
-/
module

public import Iris.BI.Lib.GenHeap
public import Iris.BI.Lib.MonoNat
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.GooseLang.Ffi.GroveFfi.Impl
public import Perennial.GooseLang.Ffi.GenHeap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## Grove semantic interpretation -/

class GroveGS (GF : BundledGFunctors) where
  groveGNetHeapG : genHeapGS Endpoint (GSet message) GF (GMap Endpoint)
  groveTimeName : GName
  groveGTimeG : MonoNatG GF

class GroveGpreS (GF : BundledGFunctors) where
  grovePreGNetHeapG : genHeapPreS Endpoint (GSet message) GF (GMap Endpoint)
  grovePreGFilesHeapG : genHeapPreS byte_string (List w8) GF (GMap byte_string)
  grovePreGTscG : MonoNatG GF

class GroveNodeGS (GF : BundledGFunctors) where
  groveGPreS : GroveGpreS GF
  groveTscName : GName
  groveGFilesHeapG : genHeapGS byte_string (List w8) GF (GMap byte_string)

section grove
variable {GF : BundledGFunctors}

/-- The authoritative mono-nat for the global time. -/
def groveTimeAuth (hG : GroveGS GF) (t : Nat) : IProp GF :=
  @MonoNat.auth_own GF hG.groveGTimeG hG.groveTimeName (.own 1) (MaxNat.ofNat t)

/-- The authoritative mono-nat for a node's TSC. -/
def groveTscAuth (hL : GroveNodeGS GF) (t : Nat) : IProp GF :=
  @MonoNat.auth_own GF hL.groveGPreS.grovePreGTscG hL.groveTscName (.own 1) (MaxNat.ofNat t)

/-- The GooseLang `FfiInterp` for Grove. -/
@[reducible] def grove_interp : FfiInterp grove_model where
  ffiGlobalGS := GroveGS
  ffiLocalGS := GroveNodeGS
  ffiLocalCtx hL σ :=
    iprop(groveTscAuth hL σ.groveNodeTsc.toNat ∗
      genHeapInterp (G := hL.groveGFilesHeapG) σ.groveNodeFiles)
  ffiGlobalCtx hG g :=
    iprop(genHeapInterp (G := hG.groveGNetHeapG) g.groveNet ∗
      groveTimeAuth hG g.groveGlobalTime.toNat)

theorem grove_interp_global_ctx_eq (hG : GroveGS GF) (g : GroveGlobalState) :
    grove_interp.ffiGlobalCtx hG g ⊣⊢
      iprop(genHeapInterp (G := hG.groveGNetHeapG) g.groveNet ∗
        @MonoNat.auth_own GF hG.groveGTimeG hG.groveTimeName (.own 1)
          (MaxNat.ofNat g.groveGlobalTime.toNat)) := .rfl

theorem grove_interp_local_ctx_eq (hL : GroveNodeGS GF) (σ : GroveNodeState) :
    grove_interp.ffiLocalCtx hL σ ⊣⊢
      iprop(@MonoNat.auth_own GF hL.groveGPreS.grovePreGTscG hL.groveTscName (.own 1)
          (MaxNat.ofNat σ.groveNodeTsc.toNat) ∗
        genHeapInterp (G := hL.groveGFilesHeapG) σ.groveNodeFiles) := .rfl

/-- `c c↦ ms`: the network channel `c` has received the messages `ms`. -/
def chanPointsto (hG : GroveGS GF) (c : Endpoint) (ms : GSet message) : IProp GF :=
  pointsTo (G := hG.groveGNetHeapG) c (.own 1) ms

/-- `f f↦{q} c`: the file `f` has contents `c`. -/
def filePointsto (hL : GroveNodeGS GF) (f : byte_string) (q : DFrac) (c : List w8) : IProp GF :=
  pointsTo (G := hL.groveGFilesHeapG) f q c

instance chanPointsto_timeless (hG : GroveGS GF) (c : Endpoint) (ms : GSet message) :
    Timeless (chanPointsto hG c ms) := by
  unfold chanPointsto; infer_instance

instance filePointsto_timeless (hL : GroveNodeGS GF) (f : byte_string) (q : DFrac)
    (c : List w8) : Timeless (filePointsto hL f q c) := by
  unfold filePointsto; infer_instance

end grove

section lifting
attribute [local instance] grove_op grove_model grove_semantics grove_interp
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseGroveGS : GroveGS GF := G.gooseFfiGlobalGS
abbrev gooseGroveNodeGS : GroveNodeGS GF := L.gooseFfiLocalGS

/- Notations `c c↦ ms`, `f f↦{q} c` and `f f↦ c`. -/
namespace grove_ffi
scoped notation:50 c:51 " c↦ " ms:50 => chanPointsto gooseGroveGS c ms
scoped notation:50 f:51 " f↦{" q "} " c:50 => filePointsto gooseGroveNodeGS f q c
scoped notation:50 f:51 " f↦ " c:50 => filePointsto gooseGroveNodeGS f (DFrac.own 1) c
end grove_ffi
open grove_ffi

def chanMetaToken (c : Endpoint) (E : CoPset) : IProp GF :=
  metaToken (G := (gooseGroveGS (G := G)).groveGNetHeapG) c E

def chanMeta {A : Type} [Pos.Countable A] (c : Endpoint) (N : Namespace) (x : A) : IProp GF :=
  metaInfo (G := (gooseGroveGS (G := G)).groveGNetHeapG) c N x

/-- "The TSC is at least" -/
def tscLb (time : Nat) : IProp GF :=
  @MonoNat.lb_own GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG
    (gooseGroveNodeGS (L := L)).groveTscName (MaxNat.ofNat time)

def isTimeLb (t : w64) : IProp GF :=
  @MonoNat.lb_own GF (gooseGroveGS (G := G)).groveGTimeG (gooseGroveGS (G := G)).groveTimeName
    (MaxNat.ofNat t.toNat)

def ownTime (t : w64) : IProp GF :=
  groveTimeAuth (gooseGroveGS (G := G)) t.toNat

instance isTimeLb_persistent (t : w64) : Persistent (isTimeLb (G := G) t) := by
  unfold isTimeLb; infer_instance

instance tscLb_persistent (t : Nat) : Persistent (tscLb (L := L) t) := by
  unfold tscLb; infer_instance

theorem ownTime_get_lb (t : w64) : ⊢ ownTime (G := G) t -∗ isTimeLb t := by
  unfold ownTime isTimeLb groveTimeAuth
  exact @MonoNat.lb_own_get GF (gooseGroveGS (G := G)).groveGTimeG _ _ _

theorem isTimeLb_mono (t t' : w64) (h : t.toNat ≤ t'.toNat) :
    ⊢ isTimeLb (G := G) t' -∗ isTimeLb t := by
  unfold isTimeLb
  exact @MonoNat.lb_own_le GF (gooseGroveGS (G := G)).groveGTimeG _ _ _
    ((MaxNat.le_toNat _ _).mpr h)

theorem tscLb_0 : ⊢ |==> tscLb (L := L) 0 := by
  unfold tscLb
  exact @MonoNat.lb_own_0 GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG _

theorem tscLb_weaken (t1 t2 : Nat) (h : t1 ≤ t2) : ⊢ tscLb (L := L) t2 -∗ tscLb t1 := by
  unfold tscLb
  exact @MonoNat.lb_own_le GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG _ _ _
    ((MaxNat.le_toNat _ _).mpr h)

abbrev connectionSocket (c_l : Endpoint) (c_r : Endpoint) : val :=
  ExtV (ConnectionSocketV c_l c_r)
abbrev listen_socket (c : Endpoint) : val :=
  ExtV (ListenSocketV c)
abbrev badSocket : val :=
  ExtV BadSocketV

theorem grove_global_ctx_eq (g : GroveGlobalState) :
    ffiGlobalCtx G.gooseFfiGlobalGS g ⊣⊢
      iprop(genHeapInterp (G := (gooseGroveGS (G := G)).groveGNetHeapG) g.groveNet ∗
        groveTimeAuth (gooseGroveGS (G := G)) g.groveGlobalTime.toNat) := .rfl

theorem grove_local_ctx_eq (σ : GroveNodeState) :
    ffiLocalCtx L.gooseFfiLocalGS σ ⊣⊢
      iprop(groveTscAuth (gooseGroveNodeGS (L := L)) σ.groveNodeTsc.toNat ∗
        genHeapInterp (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG)
          σ.groveNodeFiles) := .rfl

open EctxLanguage

/-- The core lifting lemma for Grove operations. -/
theorem wp_GroveOp (op : GroveOp) (v : val) (Φ : val → IProp GF) (Hv : v.isPanic = false) :
    ▷ (∀ σ1 g1 e2 σ2 g2, ⌜IsGroveFfiStep op v e2 σ1 σ2 g1 g2⌝ -∗
        ffiLocalCtx L.gooseFfiLocalGS σ1 -∗ ffiGlobalCtx G.gooseFfiGlobalGS g1 ={E}=∗
        ffiLocalCtx L.gooseFfiLocalGS σ2 ∗ ffiGlobalCtx G.gooseFfiGlobalGS g2 ∗
        WP e2 @ s; E {{ Φ }})
    ⊢ WP (ExternalOp op (Val v)) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro HΦ
  iapply goose_wp_lift_base_step rfl rfl (by not_unwinds)
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨[], _, _, [], BaseStep.ExternalOpS op v _ σ₁ _
      ⟨σ₁.1.world, σ₁.2.globalWorld, rfl, .inl ⟨rfl, rfl, rfl⟩⟩⟩
  inext
  iintro %e₂ %σ₂ %eₜ %Hbs Hcred
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
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain rfl := He c rfl
  imodintro
  iframe Hl Hg
  iapply wp_value'
  iapply HΦ
  itrivial

theorem wp_ConnectOp (c_r : Endpoint) :
    {{ (True : IProp GF) }} (ExternalOp GroveOp.ConnectOp (Val (#c_r))) @ s; E
    {{ (err : Bool) (c_l : Endpoint),
      RET PairV (#err) (if err then badSocket else connectionSocket c_l c_r);
      if err then True else c_l c↦ ∅ }} := by
  iintro %Φ _ HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
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
      PairV (#true) (if true then badSocket else connectionSocket 0 c_r) from rfl]
    iapply HΦ $$ %true %0
    simp only [↓reduceIte]
    itrivial
  | some c_l =>
    obtain ⟨rfl, rfl⟩ := H
    icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
    imod genHeap_alloc' (G := (gooseGroveGS (G := G)).groveGNetHeapG) (v := (∅ : GSet message))
      (show g1.groveNet !! c_l = none from Hfresh) $$ Hnet with ⟨Hnet, Hc, -⟩
    imodintro
    iframe Hl
    isplitl [Hnet Htime]
    · iapply (grove_global_ctx_eq _).mpr; unfold groveTimeAuth; iframe
    iapply wp_value'
    rw [show PairV (#false) (ExtV (ConnectionSocketV c_l c_r)) =
      PairV (#false) (if false then badSocket else connectionSocket c_l c_r) from rfl]
    iapply HΦ $$ %false %c_l
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold chanPointsto
    iexact Hc

theorem wp_AcceptOp (c_l : Endpoint) :
    {{ (True : IProp GF) }} (ExternalOp GroveOp.AcceptOp (Val (listen_socket c_l))) @ s; E
    {{ (c_r : Endpoint), RET connectionSocket c_l c_r; True }} := by
  iintro %Φ _ HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain ⟨c_r, -, rfl⟩ := He c_l rfl
  imodintro
  iframe Hl Hg
  iapply wp_value'
  iapply HΦ $$ %c_r
  itrivial

theorem wp_SendOp (c_l c_r : Endpoint) (ms : GSet message) (data : List w8) :
    {{ (c_r c↦ ms : IProp GF) }}
      (ExternalOp GroveOp.SendOp (Val (PairV (connectionSocket c_l c_r) (#data)))) @ s; E
    {{ (err_early err_late : Bool), RET #(err_early || err_late);
       c_r c↦ (if err_early then ms else ms ∪ {[Message c_l data]}) }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  have H := He data c_l c_r rfl
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold chanPointsto
  icases genHeap_lookup (G := (gooseGroveGS (G := G)).groveGNetHeapG) $$ Hnet Hc with %Heq
  change g1.groveNet !! c_r = some ms at Heq
  rw [Heq] at H
  obtain ⟨b, rfl, rfl⟩ := H
  imod genHeap_update' (G := (gooseGroveGS (G := G)).groveGNetHeapG)
    (v₂ := ms ∪ {[Message c_l data]}) $$ [Hnet Hc] with ⟨Hnet, Hc⟩
  · iframe
  imodintro
  iframe Hl
  isplitl [Hnet Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold groveTimeAuth; iframe
  iapply wp_value'
  rw [show (#b : val) = #(false || b) from by simp]
  iapply HΦ $$ %false %b
  simp only [Bool.false_eq_true, ↓reduceIte]
  iexact Hc

theorem wp_RecvOp (c_l c_r : Endpoint) (ms : GSet message) :
    {{ (c_l c↦ ms : IProp GF) }}
      (ExternalOp GroveOp.RecvOp (Val (connectionSocket c_l c_r))) @ s; E
    {{ (err : Bool) (data : List w8), RET PairV (#err) (#data);
        ⌜if err then True else Message c_r data ∈ ms⌝ ∗ c_l c↦ ms }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  obtain ⟨err, H⟩ := He c_l c_r rfl
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold chanPointsto
  icases genHeap_lookup (G := (gooseGroveGS (G := G)).groveGNetHeapG) $$ Hnet Hc with %Heq
  change g1.groveNet !! c_l = some ms at Heq
  rw [Heq] at H
  imodintro
  iframe Hl
  isplitl [Hnet Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold groveTimeAuth; iframe
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

theorem wp_FileReadOp (f : GoString) (q : DFrac) (c : List w8) :
    {{ (f f↦{q} c : IProp GF) }} (ExternalOp GroveOp.FileReadOp (Val (#f))) @ s; E
    {{ RET #c; f f↦{q} c }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, rfl, He⟩ := Hstep
  have H := He f rfl
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold filePointsto
  icases genHeap_lookup (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG) $$ Hfiles Hc
    with %Heq
  change σ1.groveNodeFiles !! f = some c at Heq
  rw [Heq] at H
  obtain rfl := H
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_FileWriteOp (f : GoString) (old new : List w8) :
    {{ (f f↦ old : IProp GF) }} (ExternalOp GroveOp.FileWriteOp (Val (PairV (#f) (#new)))) @ s; E
    {{ RET #(); f f↦ new }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  obtain ⟨rfl, rfl⟩ := He f new rfl
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold filePointsto
  imod genHeap_update' (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG) (v₂ := new)
    $$ [Hfiles Hc] with ⟨Hfiles, Hc⟩
  · iframe
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_FileAppendOp (f : GoString) (old new : List w8) :
    {{ (f f↦ old : IProp GF) }} (ExternalOp GroveOp.FileAppendOp (Val (PairV (#f) (#new)))) @ s; E
    {{ RET #(); f f↦ (old ++ new) }} := by
  iintro %Φ Hc HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, He⟩ := Hstep
  have H := He f new rfl
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold filePointsto
  icases genHeap_lookup (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG) $$ Hfiles Hc
    with %Heq
  change σ1.groveNodeFiles !! f = some old at Heq
  rw [Heq] at H
  obtain ⟨rfl, rfl⟩ := H
  imod genHeap_update' (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG) (v₂ := old ++ new)
    $$ [Hfiles Hc] with ⟨Hfiles, Hc⟩
  · iframe
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iapply HΦ
  iexact Hc

theorem wp_GetTscOp (prev_time : Nat) :
    {{ tscLb (L := L) prev_time }} (ExternalOp GroveOp.GetTscOp (Val (#()))) @ s; E
    {{ (new_time : w64), RET #new_time;
      ⌜prev_time ≤ new_time.toNat⌝ ∗ tscLb new_time.toNat }} := by
  iintro %Φ Hlb HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, new_time, Hle, rfl, rfl⟩ := Hstep
  icases (grove_local_ctx_eq σ1).mp $$ Hl with ⟨Htsc, Hfiles⟩
  unfold tscLb groveTscAuth
  icases @MonoNat.auth_lb_own_valid GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG
    _ _ _ _ $$ Htsc Hlb with %⟨-, Hprev⟩
  have Hprev' := (MaxNat.le_toNat _ _).mp Hprev
  imod @MonoNat.own_update GF (gooseGroveNodeGS (L := L)).groveGPreS.grovePreGTscG _ _
    (MaxNat.ofNat new_time.toNat) ((MaxNat.le_toNat _ _).mpr Hle) $$ Htsc with ⟨Htsc, Hlb'⟩
  imodintro
  iframe Hg
  isplitl [Htsc Hfiles]
  · iapply (grove_local_ctx_eq _).mpr; unfold groveTscAuth; iframe
  iapply wp_value'
  iapply HΦ $$ %new_time
  iframe Hlb'
  ipureintro
  exact Nat.le_trans Hprev' Hle

theorem wp_GetTimeRangeOp (Φ : val → IProp GF) :
    ⊢ (∀ (l h t : w64), ⌜t.toNat ≤ h.toNat⌝ -∗ ⌜l.toNat ≤ t.toNat⌝ -∗
        ownTime (G := G) t ={E}=∗ ownTime t ∗ Φ (PairV (#l) (#h))) -∗
      WP (ExternalOp GroveOp.GetTimeRangeOp (Val (#()))) @ s; E {{ Φ }} := by
  unfold ownTime groveTimeAuth
  iintro HΦ
  iapply wp_GroveOp
  case Hv => simp [val.isPanic]
  inext
  iintro %σ1 %g1 %e2 %σ2 %g2 %Hstep Hl Hg
  obtain ⟨rfl, new_time, low, high, Hle, Hlow, Hhigh, rfl, rfl⟩ := Hstep
  icases (grove_global_ctx_eq g1).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold groveTimeAuth
  imod @MonoNat.own_update GF (gooseGroveGS (G := G)).groveGTimeG _ _
    (MaxNat.ofNat new_time.toNat) ((MaxNat.le_toNat _ _).mpr Hle) $$ Htime with ⟨Htime, -⟩
  imod HΦ $$ %low %high %new_time %Hhigh %Hlow Htime with ⟨Htime, HΦ⟩
  imodintro
  iframe Hl
  isplitl [Hnet Htime]
  · iapply (grove_global_ctx_eq _).mpr; unfold groveTimeAuth; iframe
  iapply wp_value'
  iexact HΦ

theorem wp_time_acc (e : Expr) (Φ : val → IProp GF) (h : toVal e = none) :
    ⊢ (∀ t, ownTime (G := G) t ={E}=∗ ownTime t ∗ WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }} := by
  have h' : ToVal.toVal (Val := val) e = none := h
  unfold ownTime
  iintro Hacc
  iapply wp_unfold.2
  unfold wp.pre
  rw [h']
  dsimp only
  iintro %σ₁ %ns %obs %obs' %nt Hσ
  rcases σ₁ with ⟨σ₁, c⟩
  icases (goose_bstateInterp_eq σ₁ c ns (obs ++ obs') nt).1 $$ Hσ with ⟨Hσ, Hc⟩
  icases (goose_stateInterp_eq σ₁ ns (obs ++ obs') nt).mp $$ Hσ with
    ⟨Hheap, Hffi, Hgs, %Hlctx, Hgffi, Hproph⟩
  icases (grove_global_ctx_eq _).mp $$ Hgffi with ⟨Hnet, Htime⟩
  imod Hacc $$ %σ₁.2.globalWorld.groveGlobalTime Htime with ⟨Htime, Hwp⟩
  ihave Hwp := wp_unfold.1 $$ Hwp
  unfold wp.pre
  rw [h']
  dsimp only
  iapply Hwp $$ %(σ₁, c) %ns %obs %obs' %nt
  iapply (goose_bstateInterp_eq σ₁ c _ _ _).2
  iframe Hc
  iapply (goose_stateInterp_eq _ _ _ _).mpr
  iframe
  isplitr
  · ipureintro; exact Hlctx
  iapply (grove_global_ctx_eq _).mpr
  iframe

end lifting

end Perennial
