/-
Port of `new/proof/go_etcd_io/etcd/client/v3/leasing.v`.

Lean notes:
* The `bytes` and `strings` package-init instances come from
  `Perennial/Proof/{bytes,strings}.lean` (Rocq re-declares them here).
* The `rpctypes` init instance here is `True` (as in Rocq's `leasing.v`);
  Rocq's `cache/v3.v` declares a different one, so (as in Rocq) the two files
  should not be imported together.
* `trivial_WaitGroup_start_done` is proved with a token counter (`ownToks`,
  `Perennial/Proof/TokSet.lean`) instead of Rocq's `ghost_map` over
  `seq 0 n`.
* Rocq's `q/2` fractions are `q.half`.
* `wp_leasingKV__monitorSession` ends in `Abort` in Rocq and is not ported.

Definition changes vs Rocq (Rocq's `ownLeasingKVLocked_frac` is `Admitted`
and false for Rocq's definition; worth reporting upstream):
* `ownLeaseCacheLocked lc γ q` now scales *all* of its ownership by `q`,
  so that `ownLeasingKVLocked` (the `RWMutex` predicate, which
  `init_RWMutex` requires to be `Fractional`) really is fractional. Rocq held
  `entries_ptr ↦$ entries`, `revokes_ptr ↦$ revokes`, each `lk_ptr ↦ lk`
  in `Hentries`, and (when not ready) `dghostVar γ.entriesReadyGn
  (DfracOwn 1) false` at full ownership regardless of `q`, so the predicate
  could not be split for readers. Now these are `↦${DFrac.own q}`,
  `↦{DFrac.own q}` and `DFrac.own q` respectively (unchanged: `DFrac.discard`
  when ready). Readers holding `P q` can still read the maps; a writer holding
  `P 1` has full ownership as before.
* `ownLeasingKVLocked_frac` is proved from that. Supporting lemmas added
  here (not in Rocq): `ownLeaseKey_persistent`, `ownMap_split`,
  `ownMap_split_frac`, `ownMap_combine`, `ownMap_combine_eq` (map
  points-to fractional split/agreement; candidates for `Golang/Theory/Map`),
  `typedPointsto_frac`, `own_leaseCache_entries_frac`,
  `own_leaseCache_entry_frac`, `ownLeaseCacheLocked_frac`.
-/
import Perennial.Code.go_etcd_io.etcd.client.v3.leasing
import Perennial.GeneratedProof.go_etcd_io.etcd.client.v3.leasing
import Perennial.GeneratedProof.go_etcd_io.etcd.api.v3.v3rpc.rpctypes
import Perennial.Proof.ProofPrelude
import Perennial.Proof.context
import Perennial.Proof.sync
import Perennial.Proof.bytes
import Perennial.Proof.strings
import Perennial.Proof.go_etcd_io.etcd.client.v3.concurrency
import Perennial.Proof.go_etcd_io.etcd.client.v3
import Perennial.Golang.Theory.Chan.Idioms.Broadcast

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open go_etcd_io.etcd.client.v3_proof go_etcd_io.etcd.client.v3.concurrency

namespace go_etcd_io.etcd.client.v3.leasing

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : leasing.Assumptions]

-- (Rocq FIXME: move these)
instance rpc_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.genproto.googleapis.rpc.status :=
  define_is_pkg_init iprop(True)
instance rpc_status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.genproto.googleapis.rpc.status :=
  build_get_is_pkg_init_wf

instance status_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.status :=
  define_is_pkg_init iprop(True)
instance status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.status :=
  build_get_is_pkg_init_wf

instance codes_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  define_is_pkg_init iprop(True)
instance codes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  build_get_is_pkg_init_wf

instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init iprop(True)
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  build_get_is_pkg_init_wf

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing :=
  build_get_is_pkg_init_wf

end init

-- (declared before the proofs: a command such as `structure`, `macro` or `notation`
-- declared after asynchronously elaborated proofs waits for them)
structure LeasingKVNames where
  etcdGn : Clientv3Names
  entriesReadyGn : GName

theorem seq_replicate_fmap {A : Type} (y n : Nat) (a : A) :
    (List.range' y n).map (fun _ => a) = List.replicate n a := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp [List.range'_succ, ih, List.replicate_succ]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : leasing.Assumptions]

/-- (Rocq TODO: move this somewhere else) -/
theorem trivial_WaitGroup_start_done (N' : Namespace) (wg_ptr : Loc) (γ : sync.WaitGroupNames)
    (N : Namespace) (ctr : w32) (HN : (↑N' : CoPset) ## ↑N) :
    sync.isWaitGroup wg_ptr γ N ∗ sync.ownWaitGroup γ ctr ={⊤}=∗
    [∗list] P ∈ (List.replicate (sint.Z ctr).toNat
        iprop(∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync -∗ Φ #() -∗
          WP (App (Val (wg_ptr @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
            {{ Φ }})), P := by
  iintro ⟨#His, Hctr⟩
  by_cases hpos : ¬ sint.Z ctr > 0
  · rw [show (sint.Z ctr).toNat = 0 by omega]
    imodintro
    simp only [List.replicate]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  imod ownTokAuth_alloc with ⟨%γt, Hauth⟩
  imod ownTokAuth_add (sint.Z ctr).toNat γt 0 $$ Hauth with ⟨Hauth, Htoks⟩
  imod inv_alloc N' ⊤ iprop(∃ c : w32, sync.ownWaitGroup γ c ∗ ownTokAuth γt (sint.Z c).toNat)
    $$ [Hctr Hauth] with #Hinv
  · inext; iexists ctr; rw [Nat.zero_add]; iframe
  imodintro
  have hsub : (↑N : CoPset) ⊆ ⊤ \ ↑N' := by
    intro p hp
    rw [LawfulSet.mem_diff]
    exact ⟨CoPset.mem_full, fun h' => HN p ⟨h', hp⟩⟩
  -- one token gives one call to `Done`
  have one : ⊢ sync.isWaitGroup wg_ptr γ N -∗ inv N' iprop(∃ c : w32, sync.ownWaitGroup γ c ∗ ownTokAuth γt (sint.Z c).toNat) -∗
      ownToks γt 1 -∗
      (∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync -∗ Φ #() -∗
          WP (App (Val (wg_ptr @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Done")) (Val #()))
            {{ Φ }}) := by
    iintro #His #Hinv Htok %Φ #Hinit HΦ
    wp_apply_core sync.WaitGroup.wp_Done wg_ptr γ N $$ [] [-]
    · iframe #
    imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
    iapply fupd_mask_intro hsub
    iintro Hmask
    inext
    icases Hi with ⟨%c, Hwg, Hauth⟩
    icombine Hauth Htok gives %Hle
    iexists c
    iframe Hwg
    isplitr
    · ipureintro; word
    iintro Hwg
    imod Hmask with -
    imod ownTokAuth_sub 1 γt _ $$ Hauth Htok with Hauth
    imod Hclose $$ [Hwg Hauth] with -
    · inext; iexists (c - W32 1)
      rw [show (sint.Z (c - W32 1)).toNat = (sint.Z c).toNat - 1 by word]
      iframe
    imodintro
    iexact HΦ
  generalize (sint.Z ctr).toNat = n
  iinduction n with
  | zero => simp only [List.replicate]; iapply BigSepL.bigSepL_nil.2; iempintro
  | succ n IH =>
    simp only [List.replicate]
    iapply BigSepL.bigSepL_cons.2
    icases ownToks_add_1 1 n γt $$ Htoks with ⟨Htoks, Htok⟩
    isplitl [Htok]
    · iapply one $$ His Hinv Htok
    · iapply IH $$ Htoks

def ownLeaseKey (lk : leaseKey) (_γ : LeasingKVNames) (_key : GoString) : IProp GF :=
  iprop(
  "Hwaitc" ∷ (⌜lk.waitc' = chan.nil⌝ ∨
              ∃ γlk, ownBroadcastChan lk.waitc' γlk iprop(True) .Unknown) ∗
  "_" ∷ True)
  -- (Rocq TODO: repr predicate for RangeResponse)

def ownLeaseCacheLocked (lc : Loc) (γ : LeasingKVNames) (q : Qp) : IProp GF :=
  iprop(∃ (entries_ptr : Loc) (entries : GMap GoString Loc) (revokes_ptr : Loc)
      (revokes : GMap GoString time.Time) (entries_ready : Bool),
    "entries_ptr" ∷ lc.[leaseCache, go!"entries"] ↦{DFrac.own q} entries_ptr ∗
    "entries" ∷ (if entries_ready then entries_ptr ↦${DFrac.own q} entries
                 else iprop(⌜entries_ptr = null ∧ entries = ∅⌝)) ∗
    "Hentries" ∷ ([∗map] key ↦ lk_ptr ∈ entries,
      ∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ ownLeaseKey lk γ key) ∗
    "revokes_ptr" ∷ lc.[leaseCache, go!"revokes"] ↦{DFrac.own q} revokes_ptr ∗
    "revokes" ∷ revokes_ptr ↦${DFrac.own q} revokes ∗
    "Hentries_ready" ∷ dghostVar γ.entriesReadyGn
      (if entries_ready then DFrac.discard else DFrac.own q) entries_ready)
  -- (Rocq TODO: header?)

def isEntriesReady (γ : LeasingKVNames) : IProp GF :=
  dghostVar γ.entriesReadyGn DFrac.discard true

/-- Proposition guarded by `lkv.leases.mu`. -/
def ownLeasingKVLocked (lkv : Loc) (γ : LeasingKVNames) (q : Qp) : IProp GF :=
  iprop(∃ (sessionc : GoChan) (session : Loc) (γsession : ChanNames),
    "sessionc" ∷ lkv.[leasingKV, go!"sessionc"] ↦{DFrac.own q.half} sessionc ∗
    "#Hsessionc" ∷ ownBroadcastChan sessionc γsession (isEntriesReady γ) .Unknown ∗
    "session" ∷ lkv.[leasingKV, go!"session"] ↦{DFrac.own q.half} session ∗
    "#Hsession" ∷ (if session = null then iprop(True)
                   else ∃ lease, isSession session γ.etcdGn lease) ∗
    "Hleases" ∷ ownLeaseCacheLocked (lkv.[leasingKV, go!"leases"]) γ q)

/-- This is owned by the background thread running `monitorSession`. -/
def ownLeasingKVMonitorSession (lkv : Loc) (γ : LeasingKVNames) : IProp GF :=
  iprop(∃ (session : Loc) (sessionc : GoChan) («open» : Bool) (γsessionc : ChanNames),
    "session" ∷ lkv.[leasingKV, go!"session"] ↦{DFrac.own (1 : Qp).half} session ∗
    "#Hsession" ∷ (if session = null then iprop(True)
                   else ∃ lease, isSession session γ.etcdGn lease) ∗
    "sessionc" ∷ lkv.[leasingKV, go!"sessionc"] ↦{DFrac.own (1 : Qp).half} sessionc ∗
    "Hsessionc" ∷ ownBroadcastChan sessionc γsessionc (isEntriesReady γ)
      (if «open» then .Pending else .Done))

/-- Almost persistent. -/
def ownLeasingKVDef (lkv : Loc) (γ : LeasingKVNames) : IProp GF :=
  iprop(∃ (cl : Loc) (ctx : GoInterfaceOk) (ctx_st : context.ContextDesc (IProp GF)),
    "#cl" ∷ lkv.[leasingKV, go!"cl"] ↦□ cl ∗
    "#Hcl" ∷ isClient cl γ.etcdGn ∗
    "#ctx" ∷ lkv.[leasingKV, go!"ctx"] ↦□ (interface.ok ctx) ∗
    "#Hctx" ∷ context.isContext ctx ctx_st ∗
    "#session_opts" ∷ lkv.[leasingKV, go!"sessionOpts"] ↦□ slice.nil ∗
    "Hmu" ∷ sync.ownRWMutex (lkv.[leasingKV, go!"leases"].[leaseCache, go!"mu"])
      (ownLeasingKVLocked lkv γ))
/-- (Rocq: `Opaque ownLeasingKV`) -/
@[irreducible] def ownLeasingKV (lkv : Loc) (γ : LeasingKVNames) : IProp GF :=
  ownLeasingKVDef lkv γ
theorem ownLeasingKV_unseal : @ownLeasingKV = @ownLeasingKVDef := by
  funext; with_unfolding_all rfl

instance ownLeaseKey_persistent (lk : leaseKey) (γ : LeasingKVNames) (key : GoString) :
    Persistent (ownLeaseKey (GF := GF) lk γ key) := by
  unfold ownLeaseKey; simp only [named]; infer_instance

section own_map_frac
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

theorem ownMap_split (l : Loc) (dq1 dq2 : DFrac) (m : GMap K V) :
    (l ↦${dq1 • dq2} m : IProp GF) ⊢ l ↦${dq1} m ∗ l ↦${dq2} m := by
  rw [ownMap_unseal]
  iintro Hm
  iNamed Hm
  icases (dfractional (Φ := fun dq => heapPointsto l dq mv) dq1 dq2).1 $$ Hown
    with ⟨H1, H2⟩
  unfold ownMapDef
  simp only [named]
  isplitl [H1]
  · iexists mv, mp; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
  · iexists mv, mp; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩

theorem ownMap_split_frac (l : Loc) (p q : Qp) (m : GMap K V) :
    (l ↦${DFrac.own (p + q)} m : IProp GF) ⊢ l ↦${DFrac.own p} m ∗ l ↦${DFrac.own q} m :=
  ownMap_split l (DFrac.own p) (DFrac.own q) m

theorem ownMap_combine (l : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap K V) :
    (l ↦${dq1} m1 : IProp GF) ∗ l ↦${dq2} m2 ⊢
      l ↦${dq1 • dq2} m1 ∗
      ⌜∀ k : K, (match m1 !! k with | none => (false, #(zero_val V)) | some v => (true, #v)) =
        (match m2 !! k with | none => (false, #(zero_val V)) | some v => (true, #v))⌝ := by
  rw [ownMap_unseal]
  unfold ownMapDef
  simp only [named]
  iintro ⟨H1, H2⟩
  icases H1 with ⟨%mv1, %mp1, Hown1, %His1, %Hagree1, %Hdom1, %Hdef1⟩
  icases H2 with ⟨%mv2, %mp2, Hown2, %His2, %Hagree2, %Hdom2, %Hdef2⟩
  ihave %Heq := heapPointsto_agree l dq1 dq2 mv1 mv2 $$ [$Hown1 $Hown2]
  subst Heq
  isplitl [Hown1 Hown2]
  · iexists mv1, mp1
    isplitl
    · iapply (dfractional (Φ := fun dq => heapPointsto l dq mv1) dq1 dq2).2
      iframe
    · ipureintro; exact ⟨His1, Hagree1, Hdom1, Hdef1⟩
  · ipureintro
    intro k
    exact (Hagree1 k).symm.trans ((go.mapLookup_pure _ _ _ His1).symm.trans
      ((go.mapLookup_pure _ _ _ His2).trans (Hagree2 k)))

theorem ownMap_combine_eq [go.IntoValInj V] (l : Loc) (dq1 dq2 : DFrac) (m1 m2 : GMap K V) :
    (l ↦${dq1} m1 : IProp GF) ∗ l ↦${dq2} m2 ⊢ l ↦${dq1 • dq2} m1 ∗ ⌜m1 = m2⌝ := by
  iintro H
  icases ownMap_combine l dq1 dq2 m1 m2 $$ H with ⟨H, %H'⟩
  iframe H
  ipureintro
  apply GMap.map_eq
  intro k
  have := H' k
  cases h1 : m1 !! k <;> cases h2 : m2 !! k <;> simp only [h1, h2] at this
  · rfl
  · simp at this
  · simp at this
  · simp only [Prod.mk.injEq, true_and] at this
    rw [go.intoVal_inj this]

end own_map_frac

instance own_leaseCache_entry_frac (lk_ptr : Loc) (γ : LeasingKVNames) (key : GoString) :
    Fractional (fun q => iprop(∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ ownLeaseKey (GF := GF) lk γ key)) where
  fractional p q := by
    constructor
    · iintro ⟨%lk, Hlk, #Hk⟩
      icases ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF) lk_ptr lk dq)).fractional
        p q).1 $$ Hlk with ⟨H1, H2⟩
      isplitl [H1]
      · iexists lk; iframe H1 Hk
      · iexists lk; iframe H2 Hk
    · iintro ⟨⟨%lk1, H1, #Hk⟩, ⟨%lk2, H2, -⟩⟩
      icombine H1 H2 gives %Heq
      subst Heq
      iexists lk1
      iframe Hk
      iapply ((fractional_of_dfractional (fun dq => typedPointsto (GF := GF) lk_ptr lk1 dq)).fractional
        p q).2
      iframe

theorem own_leaseCache_entries_frac (γ : LeasingKVNames) (entries : GMap GoString Loc) :
    Fractional (fun q => iprop([∗map] key ↦ lk_ptr ∈ entries,
      ∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ ownLeaseKey (GF := GF) lk γ key)) :=
  fractional_bigSepM (Ψ := fun key lk_ptr q =>
    iprop(∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ ownLeaseKey (GF := GF) lk γ key))

theorem typedPointsto_frac {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (p q : Qp) :
    typedPointsto (GF := GF) l v (DFrac.own (p + q)) ⊣⊢
      typedPointsto l v (DFrac.own p) ∗ typedPointsto l v (DFrac.own q) :=
  (fractional_of_dfractional (fun dq => typedPointsto (GF := GF) l v dq)).fractional p q

instance ownLeaseCacheLocked_frac (lc : Loc) (γ : LeasingKVNames) :
    Fractional (ownLeaseCacheLocked (GF := GF) lc γ) where
  fractional p q := by
    unfold ownLeaseCacheLocked
    simp only [named]
    constructor
    · iintro ⟨%ep, %en, %rp, %rv, %rd, Hep, Hen, Hents, Hrp, Hrv, Hrd⟩
      icases (typedPointsto_frac _ ep p q).1 $$ Hep with ⟨Hep1, Hep2⟩
      icases (typedPointsto_frac _ rp p q).1 $$ Hrp with ⟨Hrp1, Hrp2⟩
      icases ownMap_split_frac rp p q rv $$ Hrv with ⟨Hrv1, Hrv2⟩
      icases ((own_leaseCache_entries_frac γ en).fractional p q).1 $$ Hents with ⟨Hents1, Hents2⟩
      cases rd
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hen with %Hen
        icases ((dghostVar_fractional γ.entriesReadyGn false).fractional p q).1 $$ Hrd
          with ⟨Hrd1, Hrd2⟩
        isplitl [Hep1 Hrp1 Hrv1 Hents1 Hrd1]
        · iexists ep, en, rp, rv, false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          ipureintro; exact Hen
        · iexists ep, en, rp, rv, false
          simp only [Bool.false_eq_true, ↓reduceIte]
          iframe
          ipureintro; exact Hen
      · simp only [↓reduceIte]
        icases ownMap_split_frac ep p q en $$ Hen with ⟨Hen1, Hen2⟩
        icases Hrd with #Hrd
        isplitl [Hep1 Hrp1 Hrv1 Hents1 Hen1]
        · iexists ep, en, rp, rv, true
          simp only [↓reduceIte]
          iframe
          iexact Hrd
        · iexists ep, en, rp, rv, true
          simp only [↓reduceIte]
          iframe
          iexact Hrd
    · iintro ⟨⟨%ep, %en, %rp, %rv, %rd, Hep, Hen, Hents, Hrp, Hrv, Hrd⟩,
        ⟨%ep', %en', %rp', %rv', %rd', Hep', Hen', Hents', Hrp', Hrv', Hrd'⟩⟩
      icombine Hep Hep' gives %Hep_eq
      icombine Hrp Hrp' gives %Hrp_eq
      subst Hep_eq Hrp_eq
      ihave %Hrd_eq := dghostVar_agree γ.entriesReadyGn rd _ rd' _ $$ Hrd Hrd'
      subst Hrd_eq
      icases ownMap_combine rp (DFrac.own p) (DFrac.own q) rv rv' $$ [$Hrv $Hrv'] with ⟨Hrv, -⟩
      icases (typedPointsto_frac _ ep p q).2 $$ [$Hep $Hep'] with Hep
      icases (typedPointsto_frac _ rp p q).2 $$ [$Hrp $Hrp'] with Hrp
      cases rd
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hen with %Hen
        icases Hen' with %Hen'
        have : en = en' := Hen.2.trans Hen'.2.symm
        subst this
        icases ((own_leaseCache_entries_frac γ en).fractional p q).2 $$ [$Hents $Hents'] with Hents
        icombine Hrd Hrd' as Hrd
        iexists ep, en, rp, rv, false
        simp only [Bool.false_eq_true, ↓reduceIte]
        iframe
        ipureintro; exact Hen
      · simp only [↓reduceIte]
        icases ownMap_combine_eq ep (DFrac.own p) (DFrac.own q) en en' $$ [$Hen $Hen'] with ⟨Hen, %Hen_eq⟩
        subst Hen_eq
        icases ((own_leaseCache_entries_frac γ en).fractional p q).2 $$ [$Hents $Hents'] with Hents
        iexists ep, en, rp, rv, true
        simp only [↓reduceIte]
        iframe

instance ownLeasingKVLocked_frac (lkv : Loc) (γ : LeasingKVNames) :
    Fractional (ownLeasingKVLocked (GF := GF) lkv γ) where
  fractional p q := by
    have hhalf : (p + q).half = p.half + q.half := Subtype.ext (by simp; grind)
    unfold ownLeasingKVLocked
    simp only [named]
    rw [hhalf]
    have _hpers : ∀ se : Loc, Persistent (if se = null then iprop(True)
        else iprop(∃ lease, isSession se γ.etcdGn lease) : IProp GF) := fun se => by
      split <;> infer_instance
    constructor
    · iintro ⟨%sc, %se, %γs, Hsc, #Hsc_ch, Hse, #Hse_is, Hl⟩
      icases (typedPointsto_frac _ sc p.half q.half).1 $$ Hsc with ⟨Hsc1, Hsc2⟩
      icases (typedPointsto_frac _ se p.half q.half).1 $$ Hse with ⟨Hse1, Hse2⟩
      icases ((ownLeaseCacheLocked_frac _ γ).fractional p q).1 $$ Hl with ⟨Hl1, Hl2⟩
      isplitl [Hsc1 Hse1 Hl1]
      · iexists sc, se, γs; iframe; iframe #
      · iexists sc, se, γs; iframe; iframe #
    · iintro ⟨⟨%sc, %se, %γs, Hsc, #Hsc_ch, Hse, #Hse_is, Hl⟩,
        ⟨%sc', %se', %γs', Hsc', -, Hse', -, Hl'⟩⟩
      icombine Hsc Hsc' gives %H1
      icombine Hse Hse' gives %H2
      subst H1 H2
      iexists sc, se, γs
      icases (typedPointsto_frac _ sc p.half q.half).2 $$ [$Hsc $Hsc'] with Hsc
      icases (typedPointsto_frac _ se p.half q.half).2 $$ [$Hse $Hse'] with Hse
      icases ((ownLeaseCacheLocked_frac _ γ).fractional p q).2 $$ [$Hl $Hl'] with Hl
      iframe; iframe #

end proof

end go_etcd_io.etcd.client.v3.leasing

end Perennial
end
