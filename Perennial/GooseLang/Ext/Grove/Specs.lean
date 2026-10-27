/-
Iris reasoning principles for the Grove extension.

Notes:
* No crash reasoning (no post-crash points-to, no `ExtCrashInterp`).
* The ghost state uses iris-lean's `genHeapGS` (with `gmap` as the map type)
  and `MonoNatG`. The `groveGS`/`groveNodeGS` fields are not instances (there
  are two `genHeapGS` and possibly two `MonoNatG` in play); definitions pass
  them explicitly.
* Updates are plain fancy updates `|={E}=>`.
* The ghost state is the `ExtInterp` instance `grove_interp`, with its start
  resources and allocation (for adequacy, `Perennial/GooseLang/Ext/Grove/Adequacy.lean`).
* The specs hold for any program whose extensions include Grove (`HasExt groveExt`).
-/
module

public import Iris.BI.Lib.GenHeap
public import Iris.BI.Lib.MonoNat
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable
public import Perennial.GooseLang.Ext.Grove.Impl
public import Perennial.GooseLang.Ext.GenHeap

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

/-- The interpretation of a node's state: its TSC and its files. -/
def groveLocalCtx (hL : GroveNodeGS GF) (σ : GroveNodeState) : IProp GF :=
  iprop(groveTscAuth hL σ.groveNodeTsc.toNat ∗
    genHeapInterp (G := hL.groveGFilesHeapG) σ.groveNodeFiles)

/-- The interpretation of the global state: the network and the global time. -/
def groveGlobalCtx (hG : GroveGS GF) (g : GroveGlobalState) : IProp GF :=
  iprop(genHeapInterp (G := hG.groveGNetHeapG) g.groveNet ∗
    groveTimeAuth hG g.groveGlobalTime.toNat)

/-- `c c↦ ms`: the network channel `c` has received the messages `ms`. -/
def chanPointsto (hG : GroveGS GF) (c : Endpoint) (ms : GSet message) : IProp GF :=
  pointsTo (G := hG.groveGNetHeapG) c (.own 1) ms

/-- `f f↦{q} c`: the file `f` has contents `c`. -/
def filePointsto (hL : GroveNodeGS GF) (f : byte_string) (q : DFrac) (c : List w8) : IProp GF :=
  pointsTo (G := hL.groveGFilesHeapG) f q c

open ProofMode in
theorem grove_global_init (hPre : GroveGpreS GF) (g : GroveGlobalState) :
    ⊢@{IProp GF} |==> ∃ hG : GroveGS GF, groveGlobalCtx hG g ∗
      [∗map] e ↦ ms ∈ g.groveNet, chanPointsto hG e ms := by
  letI := hPre.grovePreGNetHeapG
  imod genHeap_init (H := GMap Endpoint) g.groveNet with ⟨%names, H1, H2, -⟩
  imod @MonoNat.own_alloc GF hPre.grovePreGTscG (MaxNat.ofNat g.groveGlobalTime.toNat)
    with ⟨%γ, Ht, -⟩
  imodintro
  iexists (⟨names, γ, hPre.grovePreGTscG⟩ : GroveGS GF)
  isplitl [H1 Ht]
  · unfold groveGlobalCtx groveTimeAuth; iframe
  · unfold chanPointsto; iexact H2

open ProofMode in
theorem grove_local_init (hPre : GroveGpreS GF) (σ : GroveNodeState) :
    ⊢@{IProp GF} |==> ∃ hL : GroveNodeGS GF, groveLocalCtx hL σ ∗
      [∗map] f ↦ c ∈ σ.groveNodeFiles, filePointsto hL f (.own 1) c := by
  letI := hPre.grovePreGFilesHeapG
  imod @MonoNat.own_alloc GF hPre.grovePreGTscG (MaxNat.ofNat σ.groveNodeTsc.toNat)
    with ⟨%γ, Htsc, -⟩
  imod genHeap_init (H := GMap byte_string) σ.groveNodeFiles with ⟨%names, H1, H2, -⟩
  imodintro
  iexists (⟨hPre, γ, names⟩ : GroveNodeGS GF)
  isplitl [H1 Htsc]
  · unfold groveLocalCtx groveTscAuth; iframe
  · unfold filePointsto; iexact H2

end grove

/-- The ghost state of the Grove extension. The program gets ownership of the
initial network (`c↦`) and of the node's initial files (`f↦`). -/
instance grove_interp : ExtInterp groveExt where
  GlobalGS := GroveGS
  LocalGS := GroveNodeGS
  localCtx := groveLocalCtx
  globalCtx := groveGlobalCtx
  PreG := GroveGpreS
  initgP _ := True
  initP _ _ := True
  globalStart hG g := iprop([∗map] e ↦ ms ∈ g.groveNet, chanPointsto hG e ms)
  localStart hL σ := iprop([∗map] f ↦ c ∈ σ.groveNodeFiles, filePointsto hL f (.own 1) c)
  global_init _ hPre g _ := grove_global_init hPre g
  local_init _ hPre σ _ _ := grove_local_init hPre σ

section grove
variable {GF : BundledGFunctors}

instance chanPointsto_timeless (hG : GroveGS GF) (c : Endpoint) (ms : GSet message) :
    Timeless (chanPointsto hG c ms) := by
  unfold chanPointsto; infer_instance

instance filePointsto_timeless (hL : GroveNodeGS GF) (f : byte_string) (q : DFrac)
    (c : List w8) : Timeless (filePointsto hL f q c) := by
  unfold filePointsto; infer_instance

end grove

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt groveExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

abbrev gooseGroveGS : GroveGS GF := extGlobalGS groveExt
abbrev gooseGroveNodeGS : GroveNodeGS GF := extLocalGS groveExt

/- Notations `c c↦ ms`, `f f↦{q} c` and `f f↦ c`. -/
namespace grove_ext
scoped notation:50 c:51 " c↦ " ms:50 => chanPointsto gooseGroveGS c ms
scoped notation:50 f:51 " f↦{" q "} " c:50 => filePointsto gooseGroveNodeGS f q c
scoped notation:50 f:51 " f↦ " c:50 => filePointsto gooseGroveNodeGS f (DFrac.own 1) c
end grove_ext
open grove_ext

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
  groveV (ConnectionSocketV c_l c_r)
abbrev listen_socket (c : Endpoint) : val :=
  groveV (ListenSocketV c)
abbrev badSocket : val :=
  groveV BadSocketV

theorem grove_global_ctx_eq (g : GroveGlobalState) :
    ExtInterp.globalCtx (E := groveExt) (extGlobalGS groveExt) g ⊣⊢
      iprop(genHeapInterp (G := (gooseGroveGS (G := G)).groveGNetHeapG) g.groveNet ∗
        groveTimeAuth (gooseGroveGS (G := G)) g.groveGlobalTime.toNat) := .rfl

theorem grove_local_ctx_eq (σ : GroveNodeState) :
    ExtInterp.localCtx (E := groveExt) (extLocalGS groveExt) σ ⊣⊢
      iprop(groveTscAuth (gooseGroveNodeGS (L := L)) σ.groveNodeTsc.toNat ∗
        genHeapInterp (G := (gooseGroveNodeGS (L := L)).groveGFilesHeapG)
          σ.groveNodeFiles) := .rfl

open EctxLanguage

/-- The core lifting lemma for Grove operations: the stutter steps are handled
here, by Löb induction. -/
theorem wp_GroveOp (op : String) (v : val) (Φ : val → IProp GF) (Hv : v.isPanic = false) :
    ▷ (∀ σ1 g1 e2 σ2 g2, ⌜IsGroveStep op v e2 σ1 σ2 g1 g2⌝ -∗
        ExtInterp.localCtx (E := groveExt) (extLocalGS groveExt) σ1 -∗
        ExtInterp.globalCtx (E := groveExt) (extGlobalGS groveExt) g1 ={E}=∗
        ExtInterp.localCtx (E := groveExt) (extLocalGS groveExt) σ2 ∗
        ExtInterp.globalCtx (E := groveExt) (extGlobalGS groveExt) g2 ∗
        WP e2 @ s; E {{ Φ }})
    ⊢ WP (ExternalOp groveExt.name op (Val v)) @ s; E {{ Φ }} := by
  iloeb as IH
  iintro HΦ
  iapply wp_extStep op v Φ Hv
  iintro %h %σ1 %g1 Hheap Hl Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ1, g1, (show GroveStep op v h σ1 g1 _ h σ1 g1 from ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩)⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, Hcase⟩ := (show GroveStep op v h σ1 g1 e' h' σ' g' from Hst)
  imod Hclose
  rcases Hcase with ⟨rfl, rfl, rfl⟩ | Hgrove
  · imodintro
    iframe Hheap Hl Hg
    iapply IH
    inext
    iexact HΦ
  · imod HΦ $$ %_ %_ %_ %_ %_ %Hgrove Hl Hg with ⟨Hl, Hg, Hwp⟩
    imodintro
    iframe

theorem wp_ListenOp (c : w64) :
    {{ (True : IProp GF) }} (ExternalOp groveExt.name "Listen" (Val (#c))) @ s; E
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
    {{ (True : IProp GF) }} (ExternalOp groveExt.name "Connect" (Val (#c_r))) @ s; E
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
    rw [show PairV (#true) (groveV BadSocketV) =
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
    rw [show PairV (#false) (groveV (ConnectionSocketV c_l c_r)) =
      PairV (#false) (if false then badSocket else connectionSocket c_l c_r) from rfl]
    iapply HΦ $$ %false %c_l
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold chanPointsto
    iexact Hc

theorem wp_AcceptOp (c_l : Endpoint) :
    {{ (True : IProp GF) }} (ExternalOp groveExt.name "Accept" (Val (listen_socket c_l))) @ s; E
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
      (ExternalOp groveExt.name "Send" (Val (PairV (connectionSocket c_l c_r) (#data)))) @ s; E
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
      (ExternalOp groveExt.name "Receive" (Val (connectionSocket c_l c_r))) @ s; E
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
    {{ (f f↦{q} c : IProp GF) }} (ExternalOp groveExt.name "FileRead" (Val (#f))) @ s; E
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
    {{ (f f↦ old : IProp GF) }} (ExternalOp groveExt.name "FileWrite" (Val (PairV (#f) (#new)))) @ s; E
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
    {{ (f f↦ old : IProp GF) }} (ExternalOp groveExt.name "FileAppend" (Val (PairV (#f) (#new)))) @ s; E
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
    {{ tscLb (L := L) prev_time }} (ExternalOp groveExt.name "GetTSC" (Val (#()))) @ s; E
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
      WP (ExternalOp groveExt.name "GetTimeRange" (Val (#()))) @ s; E {{ Φ }} := by
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
  iintro Hacc
  iapply wp_ext_acc (X := groveExt) e Φ h
  iintro %σ %g Hl Hg
  icases (grove_global_ctx_eq g).mp $$ Hg with ⟨Hnet, Htime⟩
  unfold ownTime
  imod Hacc $$ %g.groveGlobalTime Htime with ⟨Htime, Hwp⟩
  imodintro
  iframe Hl Hwp
  iapply (grove_global_ctx_eq _).mpr
  iframe

end lifting

end Perennial
