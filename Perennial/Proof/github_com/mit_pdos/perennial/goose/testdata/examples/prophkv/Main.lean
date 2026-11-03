/-
The proofs of `github.com/mit-pdos/perennial/goose/testdata/examples/prophkv`: the key-value
map `KV`, `GetAny`'s logically atomic spec, and `Test`.

`GetAny` reads a key twice and returns one of the two answers, chosen at random afterwards.
Its spec is logically atomic: the caller's atomic update `AU` of the map's abstract state fires
once, at the point of the read whose answer `GetAny` returns. At the first read, the proof must
know whether that read's answer is the one returned: it takes a prediction `pv` of the result,
and fires the update at the first read that answers `pv`; the post holds when the result is
`pv`. The prediction comes from a prophecy of the program's result (`wp_withProph`), which the
Go code does not contain: `Results.lean` concludes about the program as it runs
(`goose_adequacy_withProph`).
-/
module

public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Code.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv
public import Perennial.Golang.Theory.WithProph
public import Perennial.GooseLang.FuncInstrument
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

/-- `GetAny`'s instrumented body: its body under a prophecy of its result (`prophFnV`). -/
def GetAnyP [GooseExts] [GoGlobalContext] : val := prophFnV GetAny.impl

/-- The package's assumptions in the instrumented model: `Assumptions`, with `GetAny` resolving
to its instrumented body `GetAnyP` (`FuncProph.lean` builds such a model from a real one). -/
class AssumptionsP [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions] : Prop
    where
  KV_instance : KV.TypeAssumptions
  NewKV_unfold : FuncUnfold NewKV [] NewKV.impl
  GetAny_unfold : FuncUnfold GetAny [] GetAnyP
  Test_unfold : FuncUnfold Test [] Test.impl
  import_primitive_Assumption : _root_.Perennial.github_com.goose_lang.primitive.Assumptions

attribute [instance] AssumptionsP.KV_instance AssumptionsP.NewKV_unfold AssumptionsP.GetAny_unfold
  AssumptionsP.Test_unfold AssumptionsP.import_primitive_Assumption

/-! The generated instances of `KV` (`GeneratedProof`) take the package's `Assumptions`, which
the instrumented model does not satisfy (`GetAny` resolves to `GetAnyP`); the same instances
from `AssumptionsP`. -/
namespace KV
section shim
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : AssumptionsP]

noncomputable instance KVP_typed_pointsto :
    TypedPointsto (GF := GF) KV where
  typedPointstoDef l v dq := iprop(
    "mu" ∷ typedPointsto (structFieldRef KV go!"mu" l) v.mu' dq ∗
    "m" ∷ typedPointsto (structFieldRef KV go!"m" l) v.m' dq ∗
    "_" ∷ True)
  typedPointstoDef_dfractional := by solve_typed_pointsto_dfractional
  typedPointstoDef_timeless := by solve_typed_pointsto_timeless
  typedPointsto_agree := by solve_typed_pointsto_agree

noncomputable instance KVP_into_val_typed :
    IntoValTypedUnderlying (GF := GF) KV KV.underlying := by
  solve_into_val_typed_struct

noncomputable instance KVP_access_load_mu (l : Loc) (v : KV) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef KV go!"mu" l) v.mu' dq)
      (typedPointsto (structFieldRef KV go!"mu" l) v.mu' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

noncomputable instance KVP_access_store_mu (l : Loc) (v : KV) (mu' : Loc) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef KV go!"mu" l) v.mu' (DFrac.own 1))
      (typedPointsto (structFieldRef KV go!"mu" l) mu' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with mu' := mu' } : KV) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

noncomputable instance KVP_access_load_m (l : Loc) (v : KV) (dq : DFrac) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef KV go!"m" l) v.m' dq)
      (typedPointsto (structFieldRef KV go!"m" l) v.m' dq)
      (typedPointsto l v dq) (typedPointsto l v dq) :=
 by
  solve_pointsto_access_struct

noncomputable instance KVP_access_store_m (l : Loc) (v : KV) (m' : GoMap) :
    AccessStrict (PROP := IProp GF)
      (typedPointsto (structFieldRef KV go!"m" l) v.m' (DFrac.own 1))
      (typedPointsto (structFieldRef KV go!"m" l) m' (DFrac.own 1))
      (typedPointsto l v (DFrac.own 1)) (typedPointsto l ({ v with m' := m' } : KV) (DFrac.own 1)) :=
 by
  solve_pointsto_access_struct

end shim
end KV

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : AssumptionsP]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg :=
  build_get_is_pkg_init_wf

/-! ## The key-value map -/

/-- The abstract state of the map `γ`: half of it (the lock holds the other half). -/
def kvState (γ : GName) (m : GMap GoString GoString) : IProp GF := ghostVar γ (1 : Qp).half m

instance kvState_timeless (γ : GName) (m : GMap GoString GoString) :
    Timeless (kvState (GF := GF) γ m) := by
  unfold kvState; infer_instance

/-- The lock's invariant: the Go map, and the lock's half of the abstract state. -/
def kvLockInv (mref : Loc) (γ : GName) : IProp GF :=
  iprop(∃ m : GMap GoString GoString, mref ↦$ m ∗ kvState γ m)

/-- `kv` is a map with abstract state `γ` (persistent). -/
def isKV (kv : Loc) (γ : GName) : IProp GF :=
  iprop(∃ (mu mref : Loc), kv ↦□ (KV.mk mu mref) ∗
    github_com.goose_lang.primitive.isMutex mu (kvLockInv mref γ))

instance isKV_persistent (kv : Loc) (γ : GName) : Persistent (isKV (GF := GF) kv γ) := by
  unfold isKV; infer_instance

theorem wp_NewKV :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! NewKV)) (Val #()))
    {{ (kv : Loc) (γ : GName), RET #kv; isKV kv γ ∗ kvState γ ∅ }} := by
  wp_start as #Hpkg
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %mref Hm
  imod (ghostVar_alloc (GF := GF) (∅ : GMap GoString GoString)) with ⟨%γ, Hγ⟩
  icases (ghostVar_split_half γ 1 (∅ : GMap GoString GoString)).1 $$ Hγ with ⟨Hγ1, Hγ2⟩
  imod (github_com.goose_lang.primitive.init_Mutex (kvLockInv mref γ) ⊤ «$v0_ptr»)
    $$ «$v0» [Hm Hγ1] with #Hmu
  · inext; unfold kvLockInv kvState; iexists ∅; iframe Hm; iexact Hγ1
  ipersist «$r0»
  imodintro
  iapply HΦ
  unfold isKV kvState
  iframe Hγ2
  iexists «$v0_ptr», mref
  iframe «$r0» Hmu

/-- `kv.Put(k, v)`, with the caller's ghost step at its linearization point (inside the lock):
from the abstract state `m` to `<[k := v]> m`, producing `R`. -/
theorem wp_Put (kv : Loc) (γ : GName) (k v : GoString) (R : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isKV kv γ ∗
        (∀ m, kvState γ m ={⊤}=∗ kvState γ (<[k := v]> m) ∗ R) }}
      (App (App (Val (kv @!! go.GoType.PointerType KV.ty @!! go!"Put")) (Val #k)) (Val #v))
    {{ RET #(); R }} := by
  wp_start as ⟨#Hkv, Hstep⟩
  iunfold isKV at Hkv
  icases Hkv with ⟨%mu, %mref, #Hkvp, #Hmu⟩
  iStructNamed Hkvp
  wp_auto
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold kvLockInv at HR
  icases HR with ⟨%m, Hm, Hst⟩
  wp_apply wp_mapInsert $$ Hm as Hm
  imod Hstep $$ %m Hst with ⟨Hst, HR⟩
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hst]
  · iunfold kvLockInv; iexists _; iframe
  iapply HΦ $$ HR

/-- `kv.Get(k)`, with the caller's ghost step at its linearization point (inside the lock),
which sees the abstract state `m` and the answer, `k`'s value in `m` (`""` if none). -/
theorem wp_Get (kv : Loc) (γ : GName) (k : GoString) (R : GoString → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isKV kv γ ∗
        (∀ m, kvState γ m ={⊤}=∗ kvState γ m ∗ R ((m !! k).getD go!"")) }}
      (App (Val (kv @!! go.GoType.PointerType KV.ty @!! go!"Get")) (Val #k))
    {{ (r : GoString), RET #r; R r }} := by
  wp_start as ⟨#Hkv, Hstep⟩
  iunfold isKV at Hkv
  icases Hkv with ⟨%mu, %mref, #Hkvp, #Hmu⟩
  iStructNamed Hkvp
  wp_auto
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold kvLockInv at HR
  icases HR with ⟨%m, Hm, Hst⟩
  wp_apply wp_map_lookup1 $$ Hm as Hm
  imod Hstep $$ %m Hst with ⟨Hst, HR⟩
  wp_apply github_com.goose_lang.primitive.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hm Hst]
  · iunfold kvLockInv; iexists _; iframe
  iapply HΦ $$ HR

theorem str_inj [go.IntoValInj GoString] {a b : GoString} (h : (#a : val) = #b) : a = b :=
  go.IntoValInj.intoVal_inj h

/-! ## `GetAny`: logically atomic, with a prediction of its result -/

/-- The first read's outcome: the caller's update fired (the answer is the prediction `pv`),
or not yet, the update kept. -/
def firstRead (γ : GName) (k : GoString) (pv : val) (Q : GoString → IProp GF) (v1 : GoString) :
    IProp GF :=
  iprop((⌜(#v1 : val) = pv⌝ ∗ Q v1) ∨
    (⌜(#v1 : val) ≠ pv⌝ ∗ AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
      <{ kvState γ m, COMM Q ((m !! k).getD go!"") }>))

/-- **`GetAny(kv, k)`, logically atomic**, given a prediction `pv` of its result: the caller's
atomic update of the abstract state fires once, at the first of the two reads whose answer is
`pv`, with that answer, so that a result equal to `pv` comes with `Q` of it. The prediction is a
prophecy of the result (`Test`'s proof), which the Go code does not contain. -/
theorem wp_GetAny_pred (kv : Loc) (γ : GName) (k : GoString) (pv : val) (Q : GoString → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isKV kv γ ∗
        AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
          <{ kvState γ m, COMM Q ((m !! k).getD go!"") }> }}
      (App (App (Val GetAny.impl) (Val #kv)) (Val #k))
    {{ (r : GoString), RET #r; ⌜(#r : val) = pv⌝ -∗ Q r }} := by
  wp_start as ⟨#Hkv, HAU⟩
  wp_auto
  -- the first read: the update fires if the answer is the prediction
  wp_apply (wp_Get kv γ k (firstRead γ k pv Q)) $$ [$Hkv HAU] as %v1 H1
  · iintro %m Hst
    by_cases hv : (#((m !! k).getD go!"") : val) = pv
    · imod HAU with ⟨%m', Hst', Hclose⟩
      rcases m' with ⟨m', ⟨⟩⟩
      iunfold kvState at Hst Hst'
      simp only [Tele.app]
      icombine Hst Hst' gives %Hagree
      obtain ⟨_, Heq⟩ := Hagree
      subst Heq
      icases Hclose with ⟨-, Hcommit⟩
      iunfold kvState at Hcommit
      imod Hcommit $$ %PUnit.unit Hst' with HQ
      imodintro
      unfold kvState firstRead
      iframe Hst
      ileft
      iframe HQ
      ipureintro; exact hv
    · imodintro
      iframe Hst
      unfold firstRead
      iright
      iframe HAU
      ipureintro; exact hv
  unfold firstRead
  icases H1 with (⟨%h1, HQ1⟩ | ⟨%h1, HAU⟩)
  · -- fired at the first read: the second is a plain read
    wp_apply (wp_Get kv γ k (fun _ => iprop(True))) $$ [$Hkv] as %v2 _
    · iintro %m Hst; imodintro; iframe
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
    wp_if_destruct
    · iapply HΦ
      iintro _
      iexact HQ1
    · iapply HΦ
      iintro %h2
      rw [← str_inj (h2.trans h1.symm)]
      iexact HQ1
  · -- not yet: the second read fires it if its answer is the prediction
    wp_apply (wp_Get kv γ k (fun v2 => iprop(⌜(#v2 : val) = pv⌝ -∗ Q v2))) $$ [$Hkv HAU] as %v2 H2
    · iintro %m Hst
      by_cases hv : (#((m !! k).getD go!"") : val) = pv
      · imod HAU with ⟨%m', Hst', Hclose⟩
        rcases m' with ⟨m', ⟨⟩⟩
        iunfold kvState at Hst Hst'
        simp only [Tele.app]
        icombine Hst Hst' gives %Hagree
        obtain ⟨_, Heq⟩ := Hagree
        subst Heq
        icases Hclose with ⟨-, Hcommit⟩
        iunfold kvState at Hcommit
        imod Hcommit $$ %PUnit.unit Hst' with HQ
        imodintro
        unfold kvState
        iframe Hst
        iintro _
        iexact HQ
      · imodintro
        iframe Hst
        iintro %h
        exact absurd h hv
    wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
    wp_if_destruct
    · iapply HΦ
      iintro %h
      exact absurd h h1
    · iapply HΦ
      iexact H2

/-- **`GetAny(kv, k)`, logically atomic**: the caller's atomic update of the abstract state
fires once, with the answer `GetAny` returns. The proof runs `GetAny`'s instrumented body, whose
prophecy of the result is the prediction `wp_GetAny_pred` takes; the spec does not mention it. -/
theorem wp_GetAny (kv : Loc) (γ : GName) (k : GoString) (Q : GoString → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isKV kv γ ∗
        AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
          <{ kvState γ m, COMM Q ((m !! k).getD go!"") }> }}
      (App (App (Val (@! GetAny)) (Val #kv)) (Val #k))
    {{ (r : GoString), RET #r; Q r }} := by
  wp_start as ⟨#Hkv, HAU⟩
  iapply wp_prophWrapper
  iintro %vs
  wp_apply (wp_GetAny_pred kv γ k (vs.head?.getD #()) Q) $$ [$Hkv $HAU] as %r Hr
  isplit
  · ipureintro; exact isPanic_intoVal r
  iintro %Hh
  iapply HΦ
  iapply Hr
  ipureintro
  simp [Hh]

/-! ## `Test` -/

/-- The answers `Test`'s map ever gives for `"k"`. -/
def goodVal (v : GoString) : Prop := v = go!"a" ∨ v = go!"b"

/-- `Test`'s invariant: the client's half of the abstract state, in which `"k"` is `"a"` or
`"b"`. -/
abbrev testInv (γ : GName) : IProp GF :=
  iprop(∃ m : GMap GoString GoString, kvState γ m ∗ ⌜∃ v, m !! go!"k" = some v ∧ goodVal v⌝)

def testN : Namespace := nroot.@"prophkv"

/-- The atomic update `GetAny` takes, from the invariant: a read of `"k"` answers a good value. -/
theorem au_of_inv (γ : GName) :
    inv testN (testInv (GF := GF) γ) ⊢
      AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
        <{ kvState γ m, COMM ⌜goodVal ((m !! go!"k").getD go!"")⌝ }> := by
  refine (and_intro .rfl true_intro).trans (aupd_intro ?_)
  iintro ⟨#Hinv, -⟩
  unfold atomic_acc
  iinv Hinv with ⟨%m, >Hst, >%Hgood⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  iexists ⟨m, ⟨⟩⟩
  simp only [Tele.app]
  iframe Hst
  isplit
  · iintro Hst
    imod Hmask with -
    imod Hclose $$ [Hst] with -
    · inext; iexists m; iframe Hst; ipureintro; exact Hgood
    imodintro; itrivial
  · iintro %y Hst
    imod Hmask with -
    imod Hclose $$ [Hst] with -
    · inext; iexists m; iframe Hst; ipureintro; exact Hgood
    imodintro
    ipureintro
    obtain ⟨v, hv, hg⟩ := Hgood
    simp [hv, hg]

/-- **`Test()`**: the result is `"a"` or `"b"`. -/
theorem wp_Test :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! Test)) (Val #()))
    {{ (r : GoString), RET #r; ⌜goodVal r⌝ }} := by
  wp_start as #Hpkg
  wp_auto
  wp_apply wp_NewKV as %kv %γ ⟨#Hkv, Hst⟩
  -- `Put("k", "a")`, on the client's own half of the abstract state
  wp_apply (wp_Put kv γ go!"k" go!"a" (kvState γ (<[go!"k" := go!"a"]> ∅))) $$ [$Hkv Hst]
    as Hst
  · iintro %m Hlk
    iunfold kvState at Hlk Hst
    icombine Hlk Hst gives %Hagree
    obtain ⟨_, rfl⟩ := Hagree
    imod ghostVar_update_halves (<[go!"k" := go!"a"]> ∅) γ ∅ ∅ $$ Hlk Hst with ⟨Hlk, Hst⟩
    imodintro
    unfold kvState
    iframe
  -- the invariant: `"k"` is `"a"` or `"b"`
  imod inv_alloc testN ⊤ (testInv γ) $$ [Hst] with #Hinv
  · inext; iexists _; iframe Hst; ipureintro; exact ⟨go!"a", by simp, Or.inl rfl⟩
  -- the goroutine: `Put("k", "b")`, through the invariant
  ipersist kv
  wp_apply wp_fork $$ []
  · wp_auto
    wp_apply (wp_Put kv γ go!"k" go!"b" iprop(True)) $$ [$Hkv]
    · iintro %m Hlk
      iinv Hinv with ⟨%m', >Hst, >%Hgood⟩ Hclose
      iunfold kvState at Hlk Hst
      icombine Hlk Hst gives %Hagree
      obtain ⟨_, rfl⟩ := Hagree
      imod ghostVar_update_halves (<[go!"k" := go!"b"]> m) γ m m $$ Hlk Hst with ⟨Hlk, Hst⟩
      imod Hclose $$ [Hst] with -
      · inext; iexists _; unfold kvState; iframe Hst
        ipureintro; exact ⟨go!"b", by simp, Or.inr rfl⟩
      imodintro
      unfold kvState
      iframe
    itrivial
  -- `GetAny`, with the update from the invariant
  ihave HAU := au_of_inv γ $$ Hinv
  wp_apply (wp_GetAny kv γ go!"k" (fun x => iprop(⌜goodVal x⌝))) $$ [$Hkv $HAU] as %r Hr
  iapply HΦ $$ Hr

/-! ## The program: initialization, then `Test()` -/

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hprim⟩
  iframe Hown
  is_pkg_init_finish

/-- The program: initialize the package, then call `Test` (as goose calls a function). -/
def prog : Expr :=
  Seq (App (Val initialize') (Val #()))
    (App (App (Val (GoInstruction (FuncResolve Test []))) (Val #())) (Val #()))

/-- What the program returns: `"a"` or `"b"`. -/
def resultOk (v : val) : Prop := v = #go!"a" ∨ v = #go!"b"

/-- **The program**: its result is `"a"` or `"b"`. -/
theorem wp_prog (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg get_is_pkg_init) :
    ownInitializing get_is_pkg_init ⊢ WP prog {{ v, ⌜resultOk v⌝ }} := by
  iintro Hown
  unfold prog
  wp_apply wp_initialize' _ Hinit $$ Hown as ⟨_, #Hpkg⟩
  wp_apply wp_Test as %r %Hg
  ipureintro
  rcases Hg with h | h <;> subst h <;> simp [resultOk]

end proofs

end github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

end Perennial
