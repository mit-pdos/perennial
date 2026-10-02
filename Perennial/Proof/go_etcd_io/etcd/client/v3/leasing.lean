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
    "entries" ∷ (if entries_ready then entries_ptr ↦$ entries
                 else iprop(⌜entries_ptr = null ∧ entries = ∅⌝)) ∗
    "Hentries" ∷ ([∗map] key ↦ lk_ptr ∈ entries, ∃ lk, lk_ptr ↦ lk ∗ own_leaseKey lk γ key) ∗
    "revokes_ptr" ∷ lc.[leaseCache.t, go!"revokes"] ↦{DFrac.own q} revokes_ptr ∗
    "revokes" ∷ revokes_ptr ↦$ revokes ∗
    "Hentries_ready" ∷ dghost_var γ.entries_ready_gn
      (if entries_ready then DFrac.discard else DFrac.own 1) entries_ready)
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

instance own_leasingKV_locked_frac (lkv : loc) (γ : leasingKV_names) :
    Fractional (own_leasingKV_locked (GF := GF) lkv γ) :=
  -- False as stated: `own_leasingKV_locked` holds `revokes_ptr ↦$ revokes`, `entries_ptr ↦$ entries` and (if not ready) `dghost_var .. (DFrac.own 1)` unscaled by `q`, so it cannot be split.
  sorry -- Rocq: Admitted

end proof

end go_etcd_io.etcd.client.v3.leasing

end Perennial
end
