/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/unittest.v`:
specs for some of the goose unit tests.

Differences from Rocq:
* `unittest` imports `github.com/goose-lang/primitive/disk`, so the FFI is the
  disk FFI (the generated `unittest.Assumptions` is stated for `disk_op`); the
  section does not bind `FfiSyntax`/`FfiModel`.
-/
import Perennial.Proof.DiskPrelude
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.unittest
import Perennial.Golang.Theory.IfJoin
import Perennial.Proof.fmt
import Perennial.Proof.log
import Perennial.Proof.sync_proof.base
import Perennial.Proof.github_com.goose_lang.primitive
import Perennial.Proof.github_com.goose_lang.primitive.disk
import Perennial.Proof.github_com.goose_lang.std

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unittest


section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unittest.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest :=
  build_get_is_pkg_init_wf

/-- `wp_auto`, also rewriting with a negated hypothesis `h : ¬ P` (to decide
`decide P` and `if P` as they appear). -/
local macro "wp_auto_neg " h:ident : tactic =>
  `(tactic| repeat (first | wp_auto | simp only [$h:ident, decide_false, ↓reduceIte]))

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem wp_BasicNamedReturn :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! BasicNamedReturn)) (Val #()))
    {{ RET #(go!"ok"); True }} := by
  wp_start
  wp_auto
  wp_end

theorem wp_VoidButEndsWithReturn :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! VoidButEndsWithReturn)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_apply wp_BasicNamedReturn
  wp_end

theorem wp_VoidImplicitReturnInBranch (b : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! VoidImplicitReturnInBranch)) (Val #b))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  cases b
  · wp_auto
    wp_apply wp_BasicNamedReturn
    wp_end
  · wp_auto
    wp_end

theorem wp_typeAssertInt (x : interface.t) (v : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ⌜x = interface.mkOk go.int #v⌝ }}
      (App (Val (@! typeAssertInt)) (Val #x))
    {{ RET #v; True }} := by
  wp_start as %Hx
  subst Hx
  wp_auto
  wp_end

theorem wp_wrapUnwrapInt :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! wrapUnwrapInt)) (Val #()))
    {{ RET #(W64 1); True }} := by
  wp_start
  wp_apply wp_typeAssertInt
  · ipureintro; rfl
  -- the continuation was not introduced since `v` was still a metavariable
  iintro _
  wp_end

theorem wp_checkedTypeAssert (x : interface.t) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ⌜match x with
          | interface.ok i =>
              if i.ty = go.uint64 then ∃ v : w64, i.v = #v else True
          | interface.nil => True⌝ }}
      (App (Val (@! checkedTypeAssert)) (Val #x))
    {{ (y : w64), RET #y; True }} := by
  wp_start as %Htype
  wp_auto
  cases x with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok i =>
    obtain ⟨ty, v⟩ := i
    by_cases h : ty = go.uint64
    · subst h
      simp only [eq_self, ite_true] at Htype
      obtain ⟨v', rfl⟩ := Htype
      wp_auto
      wp_end
    · wp_auto_neg h
      wp_end

theorem wp_basicTypeSwitch (x : interface.t) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ⌜match x with
          | interface.ok ⟨ty, v⟩ =>
              (ty = go.int → ∃ v' : w64, v = #v') ∧
              (ty = go.string → ∃ v' : GoString, v = #v')
          | _ => True⌝ }}
      (App (Val (@! basicTypeSwitch)) (Val #x))
    {{ (y : w64), RET #y; True }} := by
  wp_start as %Htype
  wp_auto
  cases x with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok i =>
    obtain ⟨ty, v⟩ := i
    by_cases h : ty = go.int
    · subst h
      wp_auto
      wp_end
    · wp_auto_neg h
      by_cases h' : ty = go.string
      · subst h'
        wp_auto
        wp_end
      · wp_auto_neg h'
        wp_end

theorem wp_fancyTypeSwitch (x : interface.t) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ⌜match x with
          | interface.ok ⟨ty, v⟩ =>
              (ty = go.int → ∃ v' : w64, v = #v') ∧
              (ty = go.string → ∃ v' : GoString, v = #v')
          | _ => True⌝ }}
      (App (Val (@! fancyTypeSwitch)) (Val #x))
    {{ (y : w64), RET #y; True }} := by
  wp_start as %Htype
  wp_auto
  cases x with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok i =>
    obtain ⟨ty, v⟩ := i
    by_cases h : ty = go.int
    · subst h
      obtain ⟨v', rfl⟩ := Htype.1 rfl
      wp_auto
      wp_end
    · wp_auto_neg h
      by_cases h' : ty = go.string
      · subst h'
        obtain ⟨v', rfl⟩ := Htype.2 rfl
        wp_auto
        wp_end
      · wp_auto_neg h'
        wp_end

theorem wp_multiTypeSwitch (x : interface.t) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        ⌜match x with
          | interface.ok ⟨ty, v⟩ =>
              (ty = go.int → ∃ v' : w64, v = #v') ∧
              (ty = go.string → ∃ v' : GoString, v = #v')
          | _ => True⌝ }}
      (App (Val (@! multiTypeSwitch)) (Val #x))
    {{ (y : w64), RET #y; True }} := by
  wp_start as %Htype
  wp_auto
  cases x with
  | nil =>
    dsimp only
    wp_auto
    wp_end
  | ok i =>
    obtain ⟨ty, v⟩ := i
    by_cases h : ty = go.int
    · subst h
      wp_auto
      wp_end
    · wp_auto_neg h
      wp_end

theorem wp_testSwitchMultiple (x : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! testSwitchMultiple)) (Val #x))
    {{ (y : w64), RET #y;
        ⌜(uint.Z x = 10 → sint.Z y = 1) ∧
         (uint.Z x = 1 → sint.Z y = 1) ∧
         (uint.Z x = 0 → sint.Z y = 2) ∧
         (10 < uint.Z x → sint.Z y = 3)⌝ }} := by
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ; ipureintro; word
  wp_if_destruct
  · iapply HΦ; ipureintro; word
  wp_if_destruct
  · iapply HΦ; ipureintro; word
  iapply HΦ; ipureintro; word

theorem Point.wp_IgnoreReceiver (p : Point.t) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (p @!! Point @!! go!"IgnoreReceiver")) (Val #()))
    {{ RET #(go!"ok"); True }} := by
  wp_start
  wp_end

theorem wp_mapGetCall :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! mapGetCall)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := func.t)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_map_lookup1 $$ Hm with Hm
  wp_end

theorem wp_NamedMapAssignment :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! NamedMapAssignment)) (Val #()))
    {{ (m : Loc), RET #m; m ↦$ ({[W64 1 := true]} : GMap w64 Bool) }} := by
  wp_start
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := MapWrapper)]
  wp_apply (wp_map_make1 (K := w64) (V := Bool)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  rw [GMap.insert_empty]
  wp_end

theorem wp_mapLiteralTest :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! mapLiteralTest)) (Val #()))
    {{ (l : Loc), RET #l;
        l ↦$ (<[go!"c" := W64 99]> (<[go!"b" := W64 98]> {[go!"a" := W64 97]}) : GMap GoString w64) }} := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w64)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  rw [GMap.insert_empty]
  iapply HΦ $$ Hm

theorem wp_testConversionLiteral :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! testConversionLiteral)) (Val #()))
    {{ RET #true; True }} := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := interface.t) (V := interface.t)) with %m Hm
  have hnil : SafeMapKey (GF := GF) go.any (interface.nil : interface.t) :=
    ⟨fun s E Φ => by iintro H; wp_auto; iapply H⟩
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  have hs : SafeMapKey (GF := GF) go.any
      (interface.mkOk withInterface #(withInterface.t.mk interface.nil)) :=
    ⟨fun s E Φ => by iintro H; wp_auto; iapply H⟩
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_map_lookup1 $$ Hm with Hm
  wp_apply wp_map_lookup1 $$ Hm with Hm
  iapply HΦ
  itrivial

theorem wp_useNilField :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! useNilField)) (Val #()))
    {{ (l : Loc), RET #l; l ↦ containsPointer.t.mk null }} := by
  wp_start
  wp_alloc x as Hx
  wp_auto
  iapply HΦ
  iframe

theorem wp_testU32NewtypeLen :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! testU32NewtypeLen)) (Val #()))
    {{ RET #true; True }} := by
  wp_start
  wp_auto
  wp_apply (wp_slice_make2 (V := w8)) with %sl ⟨Hs, Hcap⟩
  · ipureintro; word
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have h : sint.Z sl.len = 20 := by
    have h1 := Hlen.1
    have h2 := Hlen.2
    simp only [List.length_replicate] at h1
    word
  rw [decide_eq_true (by rw [h])]
  iapply HΦ
  itrivial

theorem wp_signedMidpoint (x y : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ ⌜-2^63 < sint.Z x + sint.Z y ∧ sint.Z x + sint.Z y < 2^63⌝ }}
      (App (App (Val (@! signedMidpoint)) (Val #x)) (Val #y))
    {{ (z : w64), RET #z; ⌜sint.Z z = (sint.Z x + sint.Z y).tdiv 2⌝ }} := by
  wp_start as %H
  wp_auto
  iapply HΦ
  ipureintro
  simp only [sint.Z] at H ⊢
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr (by decide)),
    BitVec.toInt_add_of_not_saddOverflow (by
      simp only [BitVec.saddOverflow, Bool.or_eq_true, decide_eq_true_eq, not_or, ge_iff_le,
        Int.not_le, Int.not_lt]
      omega)]
  rfl

theorem wp_useFloat :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! useFloat)) (Val #()))
    {{ (f : w64), RET #f; True }} := by
  wp_start
  -- the package constant `a` (a `def` of type `val`) must be unfolded
  simp only [a]
  wp_auto
  wp_end

theorem wp_intSliceLoop (s : slice.t) (xs : List w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ s ↦* xs }}
      (App (Val (@! intSliceLoop)) (Val #s))
    {{ (z : w64), RET #z; s ↦* xs }} := by
  wp_start as Hs
  wp_auto
  ihave %Hs_len := ownSlice_len _ _ _ $$ Hs
  ihave %Hs_wf := ownSlice_wf _ _ _ $$ Hs
  ihave HI : (∃ i sum : w64,
      "i" ∷ i_ptr ↦ i ∗
      "xs" ∷ xs_ptr ↦ s ∗
      "sum" ∷ sum_ptr ↦ sum ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i sum xs]
  · iexists _, _
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif⟩)]
    obtain ⟨x_i, Hx_i⟩ : ∃ x, xs[(sint.Z i).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by simp only [sint.nat, sint.Z] at Hs_len Hi Hif ⊢; omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x_i Hi.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx_i
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; word
  · iapply HΦ
    iframe

theorem wp_useEmbeddedMethod (d : embedD.t) (b : embedB.t) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ d.embedC'.embedB' ↦ b }}
      (App (Val (@! useEmbeddedMethod)) (Val #d))
    {{ RET #true; True }} := by
  wp_start
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  repeat wp_call
  wp_auto
  wp_method_call
  repeat wp_call
  wp_auto
  iapply HΦ
  itrivial

theorem wp_pointerAny :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! pointerAny)) (Val #()))
    {{ (l : Loc), RET #l; l ↦ interface.nil }} := by
  wp_start
  wp_alloc p as Hp
  wp_auto
  wp_end

theorem wp_useRuneOps (r0 : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! useRuneOps)) (Val #r0))
    {{ (r : w32), RET #r; ⌜r = W32 98⌝ }} := by
  wp_start
  wp_auto
  wp_end

section no_slice_literal_step
-- Workaround: `wp_auto` unfolds slice literals (`composite_literal_slice` is a
-- pure step), but `wp_slice_literal` expects the literal to be folded.
attribute [-instance] go.SliceSemantics.composite_literal_slice

set_option hygiene false in
/-- `arr = append(arr, []int{x})` (the slice is `Hz`, its capacity `Hzcap`). -/
local macro "wp_append_lit" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, _⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hz Hzcap Hsl2] with %sl1 ⟨Hz, Hzcap, _⟩
  · iframe
  try wp_auto))

theorem wp_ifJoinDemo (arg1 arg2 : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (App (Val (@! ifJoinDemo)) (Val #arg1)) (Val #arg2))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hz, Hzcap⟩
  wp_auto
  cases arg1
  · wp_auto
    cases arg2
    · wp_auto; wp_end
    · wp_auto; wp_append_lit; wp_end
  · wp_auto
    wp_append_lit
    cases arg2
    · wp_auto; wp_end
    · wp_auto; wp_append_lit; wp_end

/-- The Rocq proof of `wp_ifJoinDemo`, which joins the branches of the first
`if` with `wp_if_join` instead of case-splitting the rest of the function. -/
theorem wp_ifJoinDemo_join (arg1 arg2 : Bool) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (App (Val (@! ifJoinDemo)) (Val #arg1)) (Val #arg2))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hz, Hzcap⟩
  wp_auto
  wp_if_join (fun v => (iprop(⌜v = executeVal⌝ ∗
      ∃ (sl : slice.t) (xs : List w64),
        arr_ptr ↦ sl ∗ sl ↦* xs ∗ ownSliceCap w64 sl (DFrac.own 1)) : IProp GF))
    with [arr Hz Hzcap]
  · -- `arg1 = false`
    isplitr
    · ipureintro; trivial
    iexists _; iexists _; iframe
  · -- `arg1 = true`
    wp_append_lit
    isplitr
    · ipureintro; trivial
    iexists _; iexists _; iframe
  · iintro %v ⟨%Hv, %sl1, %xs, arr, Hz, Hzcap⟩
    subst Hv
    wp_auto
    wp_if_destruct
    · wp_end
    · wp_append_lit; wp_end

end no_slice_literal_step

theorem wp_repeatLocalVars :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! repeatLocalVars)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_auto
  wp_end

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.unittest

end Perennial
