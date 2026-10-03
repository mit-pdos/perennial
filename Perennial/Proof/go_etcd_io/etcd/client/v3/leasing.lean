/-
Port of `new/proof/go_etcd_io/etcd/client/v3/leasing.v`.

Lean notes:
* The `bytes` and `strings` package-init instances come from
  `Perennial/Proof/{bytes,strings}.lean` (Rocq re-declares them here).
* The `rpctypes` init instance here is `True` (as in Rocq's `leasing.v`);
  Rocq's `cache/v3.v` declares a different one, so (as in Rocq) the two files
  should not be imported together.
* `trivial_WaitGroup_start_done` is proved with a token counter (`own_toks`,
  `Perennial/Proof/TokSet.lean`) instead of Rocq's `ghost_map` over
  `seq 0 n`.
* Rocq's `q/2` fractions are `q.half`.
* `wp_leasingKV__monitorSession` ends in `Abort` in Rocq and is not ported.

Definition changes vs Rocq (Rocq's `own_leasingKV_locked_frac` is `Admitted`
and false for Rocq's definition; worth reporting upstream):
* `own_leaseCache_locked lc γ q` now scales *all* of its ownership by `q`,
  so that `own_leasingKV_locked` (the `RWMutex` predicate, which
  `init_RWMutex` requires to be `Fractional`) really is fractional. Rocq held
  `entries_ptr ↦$ entries`, `revokes_ptr ↦$ revokes`, each `lk_ptr ↦ lk`
  in `Hentries`, and (when not ready) `dghost_var γ.entries_ready_gn
  (DfracOwn 1) false` at full ownership regardless of `q`, so the predicate
  could not be split for readers. Now these are `↦${DFrac.own q}`,
  `↦{DFrac.own q}` and `DFrac.own q` respectively (unchanged: `DFrac.discard`
  when ready). Readers holding `P q` can still read the maps; a writer holding
  `P 1` has full ownership as before.
* `own_leasingKV_locked_frac` is proved from that. Supporting lemmas added
  here (not in Rocq): `own_leaseKey_persistent`, `own_map_split`,
  `own_map_split_frac`, `own_map_combine`, `own_map_combine_eq` (map
  points-to fractional split/agreement; candidates for `Golang/Theory/Map`),
  `typed_pointsto_frac`, `own_leaseCache_entries_frac`,
  `own_leaseCache_entry_frac`, `own_leaseCache_locked_frac`.
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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
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

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing :=
  build_get_is_pkg_init_wf

end init

theorem seq_replicate_fmap {A : Type} (y n : Nat) (a : A) :
    (List.range' y n).map (fun _ => a) = List.replicate n a := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp [List.range'_succ, ih, List.replicate_succ]

section proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : leasing.Assumptions]

/-- (Rocq TODO: move this somewhere else) -/
theorem trivial_WaitGroup_start_done (N' : Namespace) (wg_ptr : loc) (γ : sync.WaitGroup_names)
    (N : Namespace) (ctr : w32) (HN : (↑N' : CoPset) ## ↑N) :
    sync.is_WaitGroup wg_ptr γ N ∗ sync.own_WaitGroup γ ctr ={⊤}=∗
    [∗list] P ∈ (List.replicate (sint.Z ctr).toNat
        iprop(∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync -∗ Φ #() -∗
          WP (App (Val (wg_ptr @!! go.type.PointerType sync.WaitGroup @!! go!"Done")) (Val #()))
            {{ Φ }})), P := by
  iintro ⟨#His, Hctr⟩
  by_cases hpos : ¬ sint.Z ctr > 0
  · rw [show (sint.Z ctr).toNat = 0 by omega]
    imodintro
    simp only [List.replicate]
    iapply BigSepL.bigSepL_nil.2
    iempintro
  imod own_tok_auth_alloc with ⟨%γt, Hauth⟩
  imod own_tok_auth_add (sint.Z ctr).toNat γt 0 $$ Hauth with ⟨Hauth, Htoks⟩
  imod inv_alloc N' ⊤ iprop(∃ c : w32, sync.own_WaitGroup γ c ∗ own_tok_auth γt (sint.Z c).toNat)
    $$ [Hctr Hauth] with #Hinv
  · inext; iexists ctr; rw [Nat.zero_add]; iframe
  imodintro
  have hsub : (↑N : CoPset) ⊆ ⊤ \ ↑N' := by
    intro p hp
    rw [LawfulSet.mem_diff]
    exact ⟨CoPset.mem_full, fun h' => HN p ⟨h', hp⟩⟩
  -- one token gives one call to `Done`
  have one : ⊢ sync.is_WaitGroup wg_ptr γ N -∗ inv N' iprop(∃ c : w32, sync.own_WaitGroup γ c ∗ own_tok_auth γt (sint.Z c).toNat) -∗
      own_toks γt 1 -∗
      (∀ Φ : val → IProp GF, is_pkg_init (PROP := IProp GF) pkg_id.sync -∗ Φ #() -∗
          WP (App (Val (wg_ptr @!! go.type.PointerType sync.WaitGroup @!! go!"Done")) (Val #()))
            {{ Φ }}) := by
    iintro #His #Hinv Htok %Φ #Hinit HΦ
    wp_apply_core sync.wp_WaitGroup__Done wg_ptr γ N $$ [] [-]
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
    imod own_tok_auth_sub 1 γt _ $$ Hauth Htok with Hauth
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
    icases own_toks_add_1 1 n γt $$ Htoks with ⟨Htoks, Htok⟩
    isplitl [Htok]
    · iapply one $$ His Hinv Htok
    · iapply IH $$ Htoks

structure leasingKV_names where
  etcd_gn : clientv3_names
  entries_ready_gn : GName

def own_leaseKey (lk : leaseKey.t) (_γ : leasingKV_names) (_key : go_string) : IProp GF :=
  iprop(
  "Hwaitc" ∷ (⌜lk.waitc' = chan.nil⌝ ∨
              ∃ γlk, own_broadcast_chan lk.waitc' γlk iprop(True) .Unknown) ∗
  "_" ∷ True)
  -- (Rocq TODO: repr predicate for RangeResponse)

def own_leaseCache_locked (lc : loc) (γ : leasingKV_names) (q : Qp) : IProp GF :=
  iprop(∃ (entries_ptr : loc) (entries : gmap go_string loc) (revokes_ptr : loc)
      (revokes : gmap go_string time.Time.t) (entries_ready : Bool),
    "entries_ptr" ∷ lc.[leaseCache.t, go!"entries"] ↦{DFrac.own q} entries_ptr ∗
    "entries" ∷ (if entries_ready then entries_ptr ↦${DFrac.own q} entries
                 else iprop(⌜entries_ptr = null ∧ entries = ∅⌝)) ∗
    "Hentries" ∷ ([∗map] key ↦ lk_ptr ∈ entries,
      ∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ own_leaseKey lk γ key) ∗
    "revokes_ptr" ∷ lc.[leaseCache.t, go!"revokes"] ↦{DFrac.own q} revokes_ptr ∗
    "revokes" ∷ revokes_ptr ↦${DFrac.own q} revokes ∗
    "Hentries_ready" ∷ dghost_var γ.entries_ready_gn
      (if entries_ready then DFrac.discard else DFrac.own q) entries_ready)
  -- (Rocq TODO: header?)

def is_entries_ready (γ : leasingKV_names) : IProp GF :=
  dghost_var γ.entries_ready_gn DFrac.discard true

/-- Proposition guarded by `lkv.leases.mu`. -/
def own_leasingKV_locked (lkv : loc) (γ : leasingKV_names) (q : Qp) : IProp GF :=
  iprop(∃ (sessionc : chan.t) (session : loc) (γsession : chan_names),
    "sessionc" ∷ lkv.[leasingKV.t, go!"sessionc"] ↦{DFrac.own q.half} sessionc ∗
    "#Hsessionc" ∷ own_broadcast_chan sessionc γsession (is_entries_ready γ) .Unknown ∗
    "session" ∷ lkv.[leasingKV.t, go!"session"] ↦{DFrac.own q.half} session ∗
    "#Hsession" ∷ (if session = null then iprop(True)
                   else ∃ lease, is_Session session γ.etcd_gn lease) ∗
    "Hleases" ∷ own_leaseCache_locked (lkv.[leasingKV.t, go!"leases"]) γ q)

/-- This is owned by the background thread running `monitorSession`. -/
def own_leasingKV_monitorSession (lkv : loc) (γ : leasingKV_names) : IProp GF :=
  iprop(∃ (session : loc) (sessionc : chan.t) («open» : Bool) (γsessionc : chan_names),
    "session" ∷ lkv.[leasingKV.t, go!"session"] ↦{DFrac.own (1 : Qp).half} session ∗
    "#Hsession" ∷ (if session = null then iprop(True)
                   else ∃ lease, is_Session session γ.etcd_gn lease) ∗
    "sessionc" ∷ lkv.[leasingKV.t, go!"sessionc"] ↦{DFrac.own (1 : Qp).half} sessionc ∗
    "Hsessionc" ∷ own_broadcast_chan sessionc γsessionc (is_entries_ready γ)
      (if «open» then .Pending else .Done))

/-- Almost persistent. -/
def own_leasingKV_def (lkv : loc) (γ : leasingKV_names) : IProp GF :=
  iprop(∃ (cl : loc) (ctx : interface.t_ok) (ctx_st : context.Context_desc.t (IProp GF)),
    "#cl" ∷ lkv.[leasingKV.t, go!"cl"] ↦□ cl ∗
    "#Hcl" ∷ is_Client cl γ.etcd_gn ∗
    "#ctx" ∷ lkv.[leasingKV.t, go!"ctx"] ↦□ (interface.ok ctx) ∗
    "#Hctx" ∷ context.is_Context ctx ctx_st ∗
    "#session_opts" ∷ lkv.[leasingKV.t, go!"sessionOpts"] ↦□ slice.nil ∗
    "Hmu" ∷ sync.own_RWMutex (lkv.[leasingKV.t, go!"leases"].[leaseCache.t, go!"mu"])
      (own_leasingKV_locked lkv γ))
/-- (Rocq: `Opaque own_leasingKV`) -/
@[irreducible] def own_leasingKV (lkv : loc) (γ : leasingKV_names) : IProp GF :=
  own_leasingKV_def lkv γ
theorem own_leasingKV_unseal : @own_leasingKV = @own_leasingKV_def := by
  funext; with_unfolding_all rfl

instance own_leaseKey_persistent (lk : leaseKey.t) (γ : leasingKV_names) (key : go_string) :
    Persistent (own_leaseKey (GF := GF) lk γ key) := by
  unfold own_leaseKey; simp only [named]; infer_instance

section own_map_frac
variable {K V : Type} [ZeroVal K] [DecidableEq K] [ZeroVal V] [go.IntoValInj K]

theorem own_map_split (l : loc) (dq1 dq2 : DFrac) (m : gmap K V) :
    (l ↦${dq1 • dq2} m : IProp GF) ⊢ l ↦${dq1} m ∗ l ↦${dq2} m := by
  rw [own_map_unseal]
  iintro Hm
  iNamed Hm
  icases (dfractional (Φ := fun dq => heap_pointsto l dq mv) dq1 dq2).1 $$ Hown
    with ⟨H1, H2⟩
  unfold own_map_def
  simp only [named]
  isplitl [H1]
  · iexists mv, mp; iframe H1; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩
  · iexists mv, mp; iframe H2; ipureintro; exact ⟨His_map, Hagree, Hdom, Hdefault⟩

theorem own_map_split_frac (l : loc) (p q : Qp) (m : gmap K V) :
    (l ↦${DFrac.own (p + q)} m : IProp GF) ⊢ l ↦${DFrac.own p} m ∗ l ↦${DFrac.own q} m :=
  own_map_split l (DFrac.own p) (DFrac.own q) m

theorem own_map_combine (l : loc) (dq1 dq2 : DFrac) (m1 m2 : gmap K V) :
    (l ↦${dq1} m1 : IProp GF) ∗ l ↦${dq2} m2 ⊢
      l ↦${dq1 • dq2} m1 ∗
      ⌜∀ k : K, (match m1 !! k with | none => (false, #(zero_val V)) | some v => (true, #v)) =
        (match m2 !! k with | none => (false, #(zero_val V)) | some v => (true, #v))⌝ := by
  rw [own_map_unseal]
  unfold own_map_def
  simp only [named]
  iintro ⟨H1, H2⟩
  icases H1 with ⟨%mv1, %mp1, Hown1, %His1, %Hagree1, %Hdom1, %Hdef1⟩
  icases H2 with ⟨%mv2, %mp2, Hown2, %His2, %Hagree2, %Hdom2, %Hdef2⟩
  ihave %Heq := heap_pointsto_agree l dq1 dq2 mv1 mv2 $$ [$Hown1 $Hown2]
  subst Heq
  isplitl [Hown1 Hown2]
  · iexists mv1, mp1
    isplitl
    · iapply (dfractional (Φ := fun dq => heap_pointsto l dq mv1) dq1 dq2).2
      iframe
    · ipureintro; exact ⟨His1, Hagree1, Hdom1, Hdef1⟩
  · ipureintro
    intro k
    exact (Hagree1 k).symm.trans ((go.map_lookup_pure _ _ _ His1).symm.trans
      ((go.map_lookup_pure _ _ _ His2).trans (Hagree2 k)))

theorem own_map_combine_eq [go.IntoValInj V] (l : loc) (dq1 dq2 : DFrac) (m1 m2 : gmap K V) :
    (l ↦${dq1} m1 : IProp GF) ∗ l ↦${dq2} m2 ⊢ l ↦${dq1 • dq2} m1 ∗ ⌜m1 = m2⌝ := by
  iintro H
  icases own_map_combine l dq1 dq2 m1 m2 $$ H with ⟨H, %H'⟩
  iframe H
  ipureintro
  apply gmap.map_eq
  intro k
  have := H' k
  cases h1 : m1 !! k <;> cases h2 : m2 !! k <;> simp only [h1, h2] at this
  · rfl
  · simp at this
  · simp at this
  · simp only [Prod.mk.injEq, true_and] at this
    rw [go.into_val_inj this]

end own_map_frac

instance own_leaseCache_entry_frac (lk_ptr : loc) (γ : leasingKV_names) (key : go_string) :
    Fractional (fun q => iprop(∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ own_leaseKey (GF := GF) lk γ key)) where
  fractional p q := by
    constructor
    · iintro ⟨%lk, Hlk, #Hk⟩
      icases ((fractional_of_dfractional (fun dq => typed_pointsto (GF := GF) lk_ptr lk dq)).fractional
        p q).1 $$ Hlk with ⟨H1, H2⟩
      isplitl [H1]
      · iexists lk; iframe H1 Hk
      · iexists lk; iframe H2 Hk
    · iintro ⟨⟨%lk1, H1, #Hk⟩, ⟨%lk2, H2, -⟩⟩
      icombine H1 H2 gives %Heq
      subst Heq
      iexists lk1
      iframe Hk
      iapply ((fractional_of_dfractional (fun dq => typed_pointsto (GF := GF) lk_ptr lk1 dq)).fractional
        p q).2
      iframe

theorem own_leaseCache_entries_frac (γ : leasingKV_names) (entries : gmap go_string loc) :
    Fractional (fun q => iprop([∗map] key ↦ lk_ptr ∈ entries,
      ∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ own_leaseKey (GF := GF) lk γ key)) :=
  fractional_bigSepM (Ψ := fun key lk_ptr q =>
    iprop(∃ lk, lk_ptr ↦{DFrac.own q} lk ∗ own_leaseKey (GF := GF) lk γ key))

theorem typed_pointsto_frac {V : Type} [TypedPointsto (GF := GF) V] (l : loc) (v : V) (p q : Qp) :
    typed_pointsto (GF := GF) l v (DFrac.own (p + q)) ⊣⊢
      typed_pointsto l v (DFrac.own p) ∗ typed_pointsto l v (DFrac.own q) :=
  (fractional_of_dfractional (fun dq => typed_pointsto (GF := GF) l v dq)).fractional p q

instance own_leaseCache_locked_frac (lc : loc) (γ : leasingKV_names) :
    Fractional (own_leaseCache_locked (GF := GF) lc γ) where
  fractional p q := by
    unfold own_leaseCache_locked
    simp only [named]
    constructor
    · iintro ⟨%ep, %en, %rp, %rv, %rd, Hep, Hen, Hents, Hrp, Hrv, Hrd⟩
      icases (typed_pointsto_frac _ ep p q).1 $$ Hep with ⟨Hep1, Hep2⟩
      icases (typed_pointsto_frac _ rp p q).1 $$ Hrp with ⟨Hrp1, Hrp2⟩
      icases own_map_split_frac rp p q rv $$ Hrv with ⟨Hrv1, Hrv2⟩
      icases ((own_leaseCache_entries_frac γ en).fractional p q).1 $$ Hents with ⟨Hents1, Hents2⟩
      cases rd
      · simp only [Bool.false_eq_true, ↓reduceIte]
        icases Hen with %Hen
        icases ((dghost_var_fractional γ.entries_ready_gn false).fractional p q).1 $$ Hrd
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
        icases own_map_split_frac ep p q en $$ Hen with ⟨Hen1, Hen2⟩
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
      ihave %Hrd_eq := dghost_var_agree γ.entries_ready_gn rd _ rd' _ $$ Hrd Hrd'
      subst Hrd_eq
      icases own_map_combine rp (DFrac.own p) (DFrac.own q) rv rv' $$ [$Hrv $Hrv'] with ⟨Hrv, -⟩
      icases (typed_pointsto_frac _ ep p q).2 $$ [$Hep $Hep'] with Hep
      icases (typed_pointsto_frac _ rp p q).2 $$ [$Hrp $Hrp'] with Hrp
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
        icases own_map_combine_eq ep (DFrac.own p) (DFrac.own q) en en' $$ [$Hen $Hen'] with ⟨Hen, %Hen_eq⟩
        subst Hen_eq
        icases ((own_leaseCache_entries_frac γ en).fractional p q).2 $$ [$Hents $Hents'] with Hents
        iexists ep, en, rp, rv, true
        simp only [↓reduceIte]
        iframe

instance own_leasingKV_locked_frac (lkv : loc) (γ : leasingKV_names) :
    Fractional (own_leasingKV_locked (GF := GF) lkv γ) where
  fractional p q := by
    have hhalf : (p + q).half = p.half + q.half := Subtype.ext (by simp; grind)
    unfold own_leasingKV_locked
    simp only [named]
    rw [hhalf]
    have _hpers : ∀ se : loc, Persistent (if se = null then iprop(True)
        else iprop(∃ lease, is_Session se γ.etcd_gn lease) : IProp GF) := fun se => by
      split <;> infer_instance
    constructor
    · iintro ⟨%sc, %se, %γs, Hsc, #Hsc_ch, Hse, #Hse_is, Hl⟩
      icases (typed_pointsto_frac _ sc p.half q.half).1 $$ Hsc with ⟨Hsc1, Hsc2⟩
      icases (typed_pointsto_frac _ se p.half q.half).1 $$ Hse with ⟨Hse1, Hse2⟩
      icases ((own_leaseCache_locked_frac _ γ).fractional p q).1 $$ Hl with ⟨Hl1, Hl2⟩
      isplitl [Hsc1 Hse1 Hl1]
      · iexists sc, se, γs; iframe; iframe #
      · iexists sc, se, γs; iframe; iframe #
    · iintro ⟨⟨%sc, %se, %γs, Hsc, #Hsc_ch, Hse, #Hse_is, Hl⟩,
        ⟨%sc', %se', %γs', Hsc', -, Hse', -, Hl'⟩⟩
      icombine Hsc Hsc' gives %H1
      icombine Hse Hse' gives %H2
      subst H1 H2
      iexists sc, se, γs
      icases (typed_pointsto_frac _ sc p.half q.half).2 $$ [$Hsc $Hsc'] with Hsc
      icases (typed_pointsto_frac _ se p.half q.half).2 $$ [$Hse $Hse'] with Hse
      icases ((own_leaseCache_locked_frac _ γ).fractional p q).2 $$ [$Hl $Hl'] with Hl
      iframe; iframe #

end proof

end go_etcd_io.etcd.client.v3.leasing

end Perennial
end
