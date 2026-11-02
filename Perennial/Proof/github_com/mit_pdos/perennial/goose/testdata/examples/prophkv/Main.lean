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
public import Perennial.Ghost.GhostVar

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

namespace github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg :=
  build_get_is_pkg_init_wf

/-! ## The key-value map -/

/-- The abstract state of the map `γ`: half of it (the lock holds the other half). -/
def kvState (γ : GName) (m : GMap GoString GoString) : IProp GF := ghostVar γ (1 : Qp).half m

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

/-- The two halves of the abstract state agree. -/
theorem kvState_agree (γ : GName) (m1 m2 : GMap GoString GoString) :
    kvState (GF := GF) γ m1 ∗ kvState γ m2 ⊢ ⌜m1 = m2⌝ ∗ kvState γ m1 ∗ kvState γ m2 := by
  unfold kvState
  iintro ⟨H1, H2⟩
  icombine H1 H2 gives %H
  obtain ⟨-, rfl⟩ := H
  iframe H1 H2
  ipureintro; rfl

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
theorem wp_GetAny (kv : Loc) (γ : GName) (k : GoString) (pv : val) (Q : GoString → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isKV kv γ ∗
        AU <{ ∃∃ (m : GMap GoString GoString), kvState γ m }> @ ⊤, ∅
          <{ kvState γ m, COMM Q ((m !! k).getD go!"") }> }}
      (App (App (Val (@! GetAny)) (Val #kv)) (Val #k))
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

end proofs

end github_com.mit_pdos.perennial.goose.testdata.examples.prophkv

end Perennial
