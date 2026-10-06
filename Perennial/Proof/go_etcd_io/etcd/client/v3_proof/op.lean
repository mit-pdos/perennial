/-
Port of `new/proof/go_etcd_io/etcd/client/v3_proof/op.v`.

Lean notes:
* Rocq's `clientv3G Σ` is an unbound (implicitly generalized) class; it is
  `[allG GF]` here.
* Rocq names the persistent points-to of `op.sort` `"%Hsort"`; it is not pure,
  so here it is `"#Hsort"`.
* Deviation: in `isOpRangeRequest`, Rocq's `op.sort' ↦□ SortOption.mk ..`
  becomes `⌜op.sort' = null ∧ req.sort_target = 0 ∧ req.sort_order = 0⌝ ∨
  op.sort' ↦□ SortOption.mk ..`, matching `Op.toRangeRequest` (a nil `sort`
  leaves the request's sort fields 0). Rocq's version excludes a nil `sort`,
  which made its admitted `wp_OpGet` false (`OpGet` with no options returns
  an `Op` with nil `sort`). `wp_OpGet` is now proved.
* New helper specs (not in Rocq): `wp_NewOp`, `wp_IsOptsWithPrefix_nil`,
  `wp_IsOptsWithFromKey_nil`. `Op.wp_applyOpts` is moved before `wp_OpGet`.
* New (not in Rocq), for `OpGet` with options (used by `cache.wp_Cache__Get`):
  `isOpOption f pfx fk` (a client-supplied spec of an `OpOption` closure: it
  sets `isOptsWithPrefix`/`isOptsWithFromKey` only if `pfx`/`fk`, and maps a
  `Get` op to a `Get` op), `isOpOptions`, and the specs `wp_IsOptsWithPrefix`,
  `wp_IsOptsWithFromKey`, `Op.wp_applyOpts_Get`, `wp_OpGet_opts` (for
  `¬ (pfx ∧ fk)`; the request is existential).
-/
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.base
import Perennial.Proof.go_etcd_io.etcd.client.v3_proof.definitions

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option goose.wp.extras true

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace go_etcd_io.etcd.client.v3_proof

/-- Abstraction of an etcd `Op`. -/
inductive Op.t where
  | Get (req : RangeRequest.t)
  | Put (req : PutRequest.t)
  | DeleteRange (req : DeleteRangeRequest.t)
  | Txn (req : TxnRequest.t)

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [AllG GF]

local notation "pkg" => pkg_id.go_etcd_io.etcd.client.v3

def isOpRangeRequest (op : v3.Op) (req : RangeRequest.t) : IProp GF :=
  iprop(
  "%Ht" ∷ ⌜op.t' = W64 1⌝ ∗
  "#key" ∷ op.key' ↦*□ req.key ∗
  "#end" ∷ op.end' ↦*□ req.range_end ∗
  "%Hlimit" ∷ ⌜op.limit' = req.limit⌝ ∗
  -- Lean deviation (Rocq: just `op.sort' ↦□ SortOption.mk ..`, which excludes a nil
  -- `sort`, so the admitted `wp_OpGet` was false): as in `Op.toRangeRequest`, a nil
  -- `sort` means sort target and order 0.
  "#Hsort" ∷
    (⌜op.sort' = null ∧ req.sort_target = W32 0 ∧ req.sort_order = W32 0⌝ ∨
     op.sort' ↦□
      (v3.SortOption.mk (W64 (sint.Z req.sort_target)) (W64 (sint.Z req.sort_order)))) ∗
  "%Hserializable" ∷ ⌜op.serializable' = req.serializable⌝ ∗
  "%HkeysOnly" ∷ ⌜op.keysOnly' = req.keys_only⌝ ∗
  "%HcountOnly" ∷ ⌜op.countOnly' = req.count_only⌝ ∗
  "%HminModRev" ∷ ⌜op.minModRev' = req.min_mod_revision⌝ ∗
  "%HmaxModRev" ∷ ⌜op.maxModRev' = req.max_mod_revision⌝ ∗
  "%HminCreateRev" ∷ ⌜op.minCreateRev' = req.min_create_revision⌝ ∗
  "%HmaxCreateRev" ∷ ⌜op.maxCreateRev' = req.max_create_revision⌝)

def isOpPutRequest (op : v3.Op) (req : PutRequest.t) : IProp GF :=
  iprop(
  "%Ht" ∷ ⌜op.t' = W64 2⌝ ∗
  "#key" ∷ op.key' ↦*□ req.key ∗
  "#value" ∷ op.val' ↦*□ req.value ∗
  "%Hlease" ∷ ⌜op.leaseID' = req.lease⌝ ∗
  "%HprevKV" ∷ ⌜op.prevKV' = req.prev_kv⌝ ∗
  "%Hignore_value" ∷ ⌜op.ignoreValue' = req.ignore_value⌝ ∗
  "%Hignore_lease" ∷ ⌜op.ignoreLease' = req.ignore_lease⌝)

def isOpDef (op : v3.Op) (o : Op.t) : IProp GF :=
  match o with
  | .Get req => isOpRangeRequest op req
  | .Put req => isOpPutRequest op req
  | _ => iprop(False)
/-- (Rocq: `Opaque isOp`) -/
@[irreducible] def isOp (op : v3.Op) (o : Op.t) : IProp GF :=
  isOpDef op o
theorem isOp_unseal : @isOp = @isOpDef := by funext; with_unfolding_all rfl

instance isOp_persistent (op : v3.Op) (o : Op.t) :
    Persistent (isOp (GF := GF) op o) := by
  rw [isOp_unseal]; unfold isOpDef
  cases o <;> dsimp only <;> (try unfold isOpRangeRequest) <;> (try unfold isOpPutRequest) <;> infer_instance

theorem Op.wp_applyOpts (op : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (op @!! go.GoType.PointerType v3.Op.ty @!! go!"applyOpts")) (Val #slice.nil))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_for
  wp_end

/-- Lean addition (used by `wp_OpGet`). -/
theorem wp_NewOp :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! v3.NewOp)) (Val #()))
    {{ (l : Loc), RET #l; ∃ op : v3.Op, l ↦ op ∗
        ⌜op.isOptsWithPrefix' = false ∧ op.isOptsWithFromKey' = false⌝ }} := by
  wp_start
  wp_apply wp_string_to_bytes as %key_sl ⟨key_sl, -⟩
  wp_alloc l as Hl
  wp_auto
  iapply HΦ
  iexists _
  iframe Hl
  ipureintro
  exact ⟨rfl, rfl⟩

/-- Lean addition (used by `wp_OpGet`). -/
theorem wp_IsOptsWithPrefix_nil :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! v3.IsOptsWithPrefix)) (Val #slice.nil))
    {{ RET #false; True }} := by
  wp_start
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_apply wp_NewOp with %l ⟨%op, Hl, %Hop⟩
  wp_for
  rw [Hop.1]
  iapply HΦ
  itrivial

/-- Lean addition (used by `wp_OpGet`). -/
theorem wp_IsOptsWithFromKey_nil :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! v3.IsOptsWithFromKey)) (Val #slice.nil))
    {{ RET #false; True }} := by
  wp_start
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_apply wp_NewOp with %l ⟨%op, Hl, %Hop⟩
  wp_for
  rw [Hop.2]
  iapply HΦ
  itrivial

/-- NOTE (Rocq): for simplicity, this only supports empty opts list. -/
theorem wp_OpGet (key : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (App (Val (@! v3.OpGet)) (Val #key)) (Val #slice.nil))
    {{ (op : v3.Op), RET #op;
        isOp op (.Get { RangeRequest.default with key := key }) }} := by
  wp_start
  wp_auto
  wp_apply wp_IsOptsWithPrefix_nil
  wp_apply wp_string_to_bytes as %key_sl ⟨key_sl, -⟩
  ipersist key_sl
  wp_apply Op.wp_applyOpts
  iapply HΦ
  simp only [isOp_unseal, isOpDef, isOpRangeRequest, RangeRequest.default, named]
  iframe key_sl
  isplit
  · iapply ownSlice_nil
  isplit
  · ipureintro; rfl
  isplitl []
  · ileft; ipureintro; simp
  ipureintro
  simp

/-- Lean addition: a client-supplied spec of an `OpOption` closure `f` (`OpGet`,
`IsOptsWithPrefix` and `IsOptsWithFromKey` call the options on arbitrary `*Op`s).
Calling `f` on `l ↦ op` returns with `l ↦ op'`, where
* `op'` has `isOptsWithPrefix` (resp. `isOptsWithFromKey`) set only if `op` had,
  or `pfx` (resp. `fk`) holds: `pfx`/`fk` say whether `f` may be a
  `WithPrefix`/`WithFromKey` option;
* a `Get` op stays a `Get` op (for some request).
Every option of `op.go` used with `OpGet` satisfies it (`WithPrefix` with
`pfx = true`, `WithFromKey` with `fk = true`, the others for all `pfx fk`). -/
abbrev isOpOption (f : func.t) (pfx fk : Bool) : IProp GF :=
  iprop(□ (∀ (l : Loc) (op : v3.Op) (Φ : val → IProp GF),
    l ↦ op -∗
    ▷ (∀ op' : v3.Op,
        (l ↦ op' ∗
         ⌜(op'.isOptsWithPrefix' = true → op.isOptsWithPrefix' = true ∨ pfx = true) ∧
          (op'.isOptsWithFromKey' = true → op.isOptsWithFromKey' = true ∨ fk = true)⌝ ∗
         (∀ req, isOp op (.Get req) -∗ ∃ req', isOp op' (.Get req'))) -∗ Φ #()) -∗
    WP (App (Val #f) (Val #l)) {{ Φ }}))

instance isOpOption_persistent (f : func.t) (pfx fk : Bool) :
    Persistent (isOpOption (GF := GF) f pfx fk) := by
  unfold isOpOption; infer_instance

/-- Lean addition: every option in `opts` satisfies `isOpOption _ pfx fk`. -/
abbrev isOpOptions (opts : List func.t) (pfx fk : Bool) : IProp GF :=
  iprop(□ (∀ f : func.t, ⌜f ∈ opts⌝ -∗ isOpOption f pfx fk))

instance isOpOptions_persistent (opts : List func.t) (pfx fk : Bool) :
    Persistent (isOpOptions (GF := GF) opts pfx fk) := by
  unfold isOpOptions; infer_instance

theorem isOpOptions_nil (pfx fk : Bool) : ⊢ isOpOptions (GF := GF) [] pfx fk := by
  unfold isOpOptions
  imodintro
  iintro %f %Hf
  simp at Hf

/-- Lean addition (generalizes `wp_IsOptsWithPrefix_nil`). -/
theorem wp_IsOptsWithPrefix (opts_sl : slice.t) (opts : List func.t) (dq : DFrac) (pfx fk : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ opts_sl ↦*{dq} opts ∗ isOpOptions opts pfx fk }}
      (App (Val (@! v3.IsOptsWithPrefix)) (Val #opts_sl))
    {{ (b : Bool), RET #b; opts_sl ↦*{dq} opts ∗ ⌜b = true → pfx = true⌝ }} := by
  wp_start as ⟨Hs, #Hopts⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply wp_NewOp with %l ⟨%op0, Hl, %Hop0⟩
  ihave HI : (∃ (i : w64) (op : v3.Op) (f : func.t),
      "i" ∷ i_ptr ↦ i ∗ "opt" ∷ opt_ptr ↦ f ∗ "Hl" ∷ l ↦ op ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z opts_sl.len⌝ ∗
      "%Hpfx" ∷ ⌜op.isOptsWithPrefix' = true → pfx = true⌝ : IProp GF) $$ [i opt Hl]
  · iexists (W64 0), op0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    intro h; rw [Hop0.1] at h; cases h
  wp_for HI
  simp only [decide_eq_true_eq]
  by_cases Hif : sint.Z i < sint.Z opts_sl.len
  · simp only [Hif, ↓reduceIte]
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    list_elem opts (sint.nat i) as g
    wp_apply wp_load_slice_index opts_sl (sint.Z i) opts dq g Hi.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hg_lookup
    ihave #Hg := Hopts $$ %g %(List.mem_of_getElem? Hg_lookup)
    wp_apply Hg $$ Hl as %op' ⟨Hl, %Hop', -⟩
    wp_for_post
    iframe
    iexists (i + W64 1), op', g
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    intro h
    rcases Hop'.1 h with h' | h'
    · exact Hpfx h'
    · exact h'
  · simp only [Hif, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact Hpfx

/-- Lean addition (generalizes `wp_IsOptsWithFromKey_nil`). -/
theorem wp_IsOptsWithFromKey (opts_sl : slice.t) (opts : List func.t) (dq : DFrac) (pfx fk : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ opts_sl ↦*{dq} opts ∗ isOpOptions opts pfx fk }}
      (App (Val (@! v3.IsOptsWithFromKey)) (Val #opts_sl))
    {{ (b : Bool), RET #b; opts_sl ↦*{dq} opts ∗ ⌜b = true → fk = true⌝ }} := by
  wp_start as ⟨Hs, #Hopts⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply wp_NewOp with %l ⟨%op0, Hl, %Hop0⟩
  ihave HI : (∃ (i : w64) (op : v3.Op) (f : func.t),
      "i" ∷ i_ptr ↦ i ∗ "opt" ∷ opt_ptr ↦ f ∗ "Hl" ∷ l ↦ op ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z opts_sl.len⌝ ∗
      "%Hfk" ∷ ⌜op.isOptsWithFromKey' = true → fk = true⌝ : IProp GF) $$ [i opt Hl]
  · iexists (W64 0), op0, _
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    intro h; rw [Hop0.2] at h; cases h
  wp_for HI
  simp only [decide_eq_true_eq]
  by_cases Hif : sint.Z i < sint.Z opts_sl.len
  · simp only [Hif, ↓reduceIte]
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    list_elem opts (sint.nat i) as g
    wp_apply wp_load_slice_index opts_sl (sint.Z i) opts dq g Hi.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hg_lookup
    ihave #Hg := Hopts $$ %g %(List.mem_of_getElem? Hg_lookup)
    wp_apply Hg $$ Hl as %op' ⟨Hl, %Hop', -⟩
    wp_for_post
    iframe
    iexists (i + W64 1), op', g
    iframe
    ipureintro
    refine ⟨by word, ?_⟩
    intro h
    rcases Hop'.2 h with h' | h'
    · exact Hfk h'
    · exact h'
  · simp only [Hif, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe
    ipureintro; exact Hfk

/-- Lean addition (generalizes `Op.wp_applyOpts`): applying options to a `Get` op
gives a `Get` op. -/
theorem Op.wp_applyOpts_Get (l : Loc) (op : v3.Op) (req : RangeRequest.t) (opts_sl : slice.t)
    (opts : List func.t) (dq : DFrac) (pfx fk : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ l ↦ op ∗ isOp op (.Get req) ∗
        opts_sl ↦*{dq} opts ∗ isOpOptions opts pfx fk }}
      (App (Val (l @!! go.GoType.PointerType v3.Op.ty @!! go!"applyOpts")) (Val #opts_sl))
    {{ (op' : v3.Op) (req' : RangeRequest.t), RET #();
        l ↦ op' ∗ isOp op' (.Get req') ∗ opts_sl ↦*{dq} opts }} := by
  wp_start as ⟨Hl, #Hop, Hs, #Hopts⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave HI : (∃ (i : w64) (op : v3.Op) (req : RangeRequest.t) (f : func.t),
      "i" ∷ i_ptr ↦ i ∗ "opt" ∷ opt_ptr ↦ f ∗ "Hl" ∷ l ↦ op ∗ "#Hop" ∷ isOp op (.Get req) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z opts_sl.len⌝ : IProp GF) $$ [i opt Hl]
  · iexists (W64 0), op, req, _
    iframe # ∗
    ipureintro; word
  wp_for HI
  simp only [decide_eq_true_eq]
  by_cases Hif : sint.Z i < sint.Z opts_sl.len
  · simp only [Hif, ↓reduceIte]
    wp_auto
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    list_elem opts (sint.nat i) as g
    wp_apply wp_load_slice_index opts_sl (sint.Z i) opts dq g Hi.1 $$ [Hs] with Hs
    · iframe Hs; ipureintro; exact Hg_lookup
    ihave #Hg := Hopts $$ %g %(List.mem_of_getElem? Hg_lookup)
    wp_apply Hg $$ Hl as %op' ⟨Hl, %-, Hget⟩
    icases Hget $$ Hop with ⟨%req', #Hop'⟩
    wp_for_post
    iframe
    iexists (i + W64 1), op', req', g
    iframe # ∗
    ipureintro; word
  · simp only [Hif, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe # ∗

/-- Lean addition: `OpGet` with options (generalizes `wp_OpGet`). The options may not
be both a `WithPrefix` and a `WithFromKey` (else `OpGet` panics). -/
theorem wp_OpGet_opts (key : GoString) (opts_sl : slice.t) (opts : List func.t) (dq : DFrac)
    (pfx fk : Bool) (Hpfx_fk : ¬ (pfx = true ∧ fk = true)) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ opts_sl ↦*{dq} opts ∗ isOpOptions opts pfx fk }}
      (App (App (Val (@! v3.OpGet)) (Val #key)) (Val #opts_sl))
    {{ (op : v3.Op) (req : RangeRequest.t), RET #op; opts_sl ↦*{dq} opts ∗
        isOp op (.Get req) }} := by
  wp_start as ⟨Hs, #Hopts⟩
  wp_auto
  wp_apply wp_IsOptsWithPrefix opts_sl opts dq pfx fk $$ [$Hs $Hopts] as %b1 ⟨Hs, %Hb1⟩
  cases b1
  case' true =>
    wp_auto
    wp_apply wp_IsOptsWithFromKey opts_sl opts dq pfx fk $$ [$Hs $Hopts] as %b2 ⟨Hs, %Hb2⟩
    cases b2
    case true =>
      exact absurd ⟨Hb1 rfl, Hb2 rfl⟩ Hpfx_fk
  all_goals
    wp_auto
    wp_apply wp_string_to_bytes as %key_sl ⟨key_sl, -⟩
    ipersist key_sl
    wp_apply Op.wp_applyOpts_Get _ _ { RangeRequest.default with key := key } opts_sl opts dq
      pfx fk $$ [ret Hs] as %op' %req' ⟨ret, #Hop', Hs⟩
    · iframe # ∗
      simp only [isOp_unseal, isOpDef, isOpRangeRequest, RangeRequest.default, named]
      iframe key_sl
      isplit
      · iapply ownSlice_nil
      isplit
      · ipureintro; rfl
      isplitl []
      · ileft; ipureintro; simp
      ipureintro
      simp
    iapply HΦ
    iframe # ∗

theorem wp_OpPut (key v : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (App (App (Val (@! v3.OpPut)) (Val #key)) (Val #v)) (Val #slice.nil))
    {{ (op : v3.Op), RET #op;
        isOp op (.Put { PutRequest.default with key := key, value := v }) }} := by
  wp_start
  wp_auto
  wp_apply wp_string_to_bytes as %key_sl ⟨key_sl, -⟩
  wp_apply wp_string_to_bytes as %val_sl ⟨val_sl, -⟩
  ipersist key_sl
  ipersist val_sl
  wp_apply Op.wp_applyOpts
  iapply HΦ
  simp only [isOp_unseal, isOpDef, isOpPutRequest]
  iframe # ∗
  ipureintro
  simp [PutRequest.default]

theorem Op.wp_KeyBytes (op : v3.Op) (req : PutRequest.t) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isOp op (.Put req) }}
      (App (Val (op @!! v3.Op.ty @!! go!"KeyBytes")) (Val #()))
    {{ (key_sl : slice.t), RET #key_sl; key_sl ↦*□ req.key }} := by
  wp_start as Hop
  wp_auto
  simp only [isOp_unseal, isOpDef, isOpPutRequest]
  iNamed Hop
  iapply HΦ $$ key

end wps

end go_etcd_io.etcd.client.v3_proof

end Perennial
end
