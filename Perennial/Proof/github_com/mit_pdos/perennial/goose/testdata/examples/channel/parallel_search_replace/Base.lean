/-
A parallel search-and-replace over a slice, with work items sent over a channel
(bag idiom) and completion tracked by a `sync.WaitGroup` (join idiom).

This file: the package's `isPkgInit` instances, the pure `searchReplace` and its
lemmas, and the channel predicate `chanP`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.WaitGroupDefs
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : parallel_search_replace.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF)
      pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace :=
  build_get_is_pkg_init_wf

end init

structure SearchReplaceNames where
  wg : sync.WaitGroupNames
  wgAdded : GName

def searchReplace (x y : w64) (l : List w64) : List w64 :=
  l.map (fun a => if a = x then y else a)

@[simp] theorem searchReplace_length (x y : w64) (l : List w64) :
    (searchReplace x y l).length = l.length := by
  simp [searchReplace]

theorem searchReplace_lookup (x y : w64) (xs : List w64) (i : Nat) (x' : w64)
    (h : xs[i]? = some x') :
    (searchReplace x y (xs.take i) ++ xs.drop i)[i]? = some x' := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 h).1
  have h3 : (searchReplace x y (xs.take i)).length = i := by simp; omega
  rw [List.getElem?_append_right (by omega), h3, Nat.sub_self, List.getElem?_drop, Nat.add_zero, h]

theorem searchReplace_step (x y : w64) (xs : List w64) (i : Nat) (x' : w64)
    (h : xs[i]? = some x') :
    (searchReplace x y (xs.take i) ++ xs.drop i).set i (if x' = x then y else x') =
      searchReplace x y (xs.take (i + 1)) ++ xs.drop (i + 1) := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.1 h).1
  have h3 : (searchReplace x y (xs.take i)).length = i := by simp; omega
  rw [List.set_append_right _ _ (by omega), h3, Nat.sub_self, List.take_add_one, h,
    List.drop_eq_getElem_cons hi]
  simp only [Option.toList_some, List.set_cons_zero, searchReplace, List.map_append, List.map_cons,
    List.map_nil, List.append_assoc, List.singleton_append]

theorem searchReplace_step_ne (x y : w64) (xs : List w64) (i : Nat) (x' : w64)
    (h : xs[i]? = some x') (hne : ¬ x' = x) :
    searchReplace x y (xs.take i) ++ xs.drop i =
      searchReplace x y (xs.take (i + 1)) ++ xs.drop (i + 1) := by
  rw [← searchReplace_step x y xs i x' h, ite_eq_right_iff.2 (fun h => absurd h hne),
    list_set_lookup_self _ _ _ (searchReplace_lookup x y xs i x' h)]

theorem searchReplace_take_append (x y : w64) (xs : List w64) (o n : Nat) (h : o ≤ n) :
    (searchReplace x y xs).take o ++ searchReplace x y ((xs.drop o).take (n - o)) =
      (searchReplace x y xs).take n := by
  have hn : n = o + (n - o) := by omega
  conv => rhs; rw [hn]
  unfold searchReplace
  rw [← List.map_take, ← List.map_take, ← List.map_append, ← List.take_add]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace.Assumptions]

def chanP (wg : Loc) (x y : w64) (s : GoSlice) : IProp GF :=
  iprop(∃ xs : List w64,
    "Hxs" ∷ s ↦* xs ∗
    "Hwg_done" ∷ sync.join.ownDone wg (s ↦* (searchReplace x y xs)))

def waitgroupN : Namespace := nroot.@"waitgroup"

/-- An empty subslice is owned persistently. TODO: move to the slice theory. -/
theorem ownSlice_slice_empty (index : w64) (s : GoSlice) (xs : List w64)
    (h : 0 ≤ sint.Z index ∧ sint.Z index ≤ sint.Z s.cap) :
    (s ↦* xs : IProp GF) ⊢ □ (slice.slice s w64 index index ↦* ([] : List w64)) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %Hc⟩)
  · obtain ⟨rfl, rfl⟩ := H
    have hi : index = W64 0 := by simp only [slice.nil] at h; word
    subst hi
    imodintro
    ileft
    ipureintro
    refine ⟨?_, rfl⟩
    simp only [slice.slice, sliceIndexRef, slice.nil]
    rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0]
    rfl
  · ihave %Hnn := typedPointsto_not_null _ _ _ $$ H
    have hslice : slice.slice s w64 index index =
        slice.mk (sliceIndexRef w64 (sint.Z index) s) (W64 0) (s.cap - index) := by
      simp [slice.slice]
    rw [hslice]
    have hp : sliceIndexRef w64 (sint.Z index) s ≠ null :=
      fun hn => Hnn (go.arrayIndexRef_null_inv _ _ _ hn)
    imodintro
    iright
    isplit
    · exact array_empty (V := w64) _ _ hp
    · ipureintro; word

end proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.parallel_search_replace

end Perennial
