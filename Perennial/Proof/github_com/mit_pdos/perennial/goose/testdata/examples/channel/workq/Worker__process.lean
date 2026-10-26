/-
The proof of `workq.(*Worker).process`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker__process
public import Perennial.Spec.strings.Fields
public import Perennial.Spec.sync.atomic.Int64__Add

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.process.wp_proof
    (wp_Fields : strings.Fields.spec (GF := GF) (hG := hG))
    (wp_Int64_Add : sync.atomic.Int64.Add.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.process.spec
      (GF := GF) (hG := hG) := fun γ w doc sh => by
  wp_start as ⟨#Hw, #Hcoord, Hdoc⟩
  wp_auto
  wp_apply wp_Fields doc as %sl ⟨Hsl, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  iNamed Hcoord
  iNamed Hcoord
  iNamed Hdoc
  wp_apply_core wp_Int64_Add $$ [] [-]
  · iPkgInit
  iinv Hi with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold coordinatorInv
  iNamedSuffix Hi "_inv"
  unfold ownTask
  icases Hdoc with ⟨%i, Hdoc⟩
  unfold ownTaskAuth
  icombine Hauth_inv Hdoc gives %Hlookup
  have Hdoc_i : γ.docs[i]? = some doc := Hdocs_agree_inv i _ Hlookup
  by_cases Hz : remainingv = W64 0
  · exfalso
    have : remaining_docs.size = 0 := by rw [← Hremaining_size_inv, Hz]; rfl
    rw [GMap.map_size_empty_inv _ this] at Hlookup; simp at Hlookup
  simp only [Hz, ↓reduceIte]
  iNamedSuffix H_inv "_inv"
  iexists totalv
  iframe Htotal_inv
  iintro Htotal_inv
  imod ghost_map_update none $$ Hauth_inv Hdoc with ⟨Hauth_inv, Hdoc⟩
  imod Hmask with -
  imod Hclose $$ [Hauth_inv Htotal_inv Hdone_inv Hremaining_inv] with -
  · inext
    iexists (<[i := none]> remaining_docs), remainingv
    simp only [Hz, ↓reduceIte]
    isplitl [Htotal_inv Hdone_inv]
    · iexists _
      iframe
      ipureintro
      rw [imap_sum_insert_none word_count _ _ _ _ Hlookup Hdoc_i, Htotal_inv]
      unfold word_count
      rw [Hlen.1, Int.natCast_add, show ((sint.nat sl.len : Nat) : Int) = sint.Z sl.len from
        Int.toNat_of_nonneg Hlen.2]
      simp only [W64, sint.Z, BitVec.ofInt_add, BitVec.ofInt_toInt]
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [GMap.map_size_insert_Some _ _ _ _ Hlookup]; exact Hremaining_size_inv
    · intro j v hj
      simp only [GMap.lookup_insert_eq_iff] at hj
      split at hj
      · cases hj; trivial
      · exact Hdocs_agree_inv j v hj
  imodintro
  wp_auto
  wp_apply_core wp_Int64_Add $$ [] [-]
  · iPkgInit
  iinv Hi with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iNamedSuffix Hi "_inv"
  iexists remainingv
  iframe Hremaining_inv
  iintro Hremaining_inv
  icombine Hauth_inv Hdoc gives %Hlookup0
  imod ghost_map_delete $$ Hauth_inv Hdoc with Hauth_inv
  have Hne0 := GMap.map_size_ne_0_lookup_2 remaining_docs Hlookup0
  have Hsize_del := GMap.map_size_delete_Some remaining_docs i _ Hlookup0
  by_cases Hz0 : remainingv = W64 0
  · exfalso; apply Hne0; rw [← Hremaining_size_inv, Hz0]; rfl
  simp only [Hz0, ↓reduceIte]
  iNamedSuffix H_inv "_inv"
  by_cases Hz1 : remainingv + W64 (-1) = W64 0
  · -- about to close done
    have Hr1 : remainingv = W64 1 := by word
    have Hsize1 : remaining_docs.size = 1 := by rw [← Hremaining_size_inv, Hr1]; rfl
    have Htot : countedSum word_count γ.docs remaining_docs = (γ.docs.map word_count).sum :=
      imap_sum_no_some_some _ _ _ (fun j _ d hd => by
        by_cases hj : j = i
        · subst hj; rw [Hlookup0] at hd; cases hd
        · rw [map_size1_lookup_ne remaining_docs i _ Hlookup0 Hsize1 j hj] at hd; cases hd)
    imod Hmask with -
    imod Hclose $$ [Hauth_inv Hremaining_inv] with -
    · inext
      iexists (remaining_docs.delete i), remainingv + W64 (-1)
      simp only [Hz1, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨?_, ?_⟩
      · rw [Hsize_del, ← Hremaining_size_inv, Hr1]; rfl
      · intro j v hj
        simp only [GMap.lookup_delete_iff] at hj
        split at hj
        · cases hj
        · exact Hdocs_agree_inv j v hj
    imodintro
    wp_auto
    wp_if_destruct
    · ipersist Htotal_inv
      wp_apply wp_broadcast_chan_close sh.done' γdone (isTasksDone γ sh) $$ [Hdone_inv Htotal_inv]
        as -
      · iframe
        unfold isTasksDone
        rw [← Htot, ← Htotal_inv]
        iframe #
      iapply HΦ
      itrivial
    · exfalso; simp_all
  · -- not going to close done
    imod Hmask with -
    imod Hclose $$ [Hauth_inv Hremaining_inv Htotal_inv Hdone_inv] with -
    · inext
      iexists (remaining_docs.delete i), remainingv + W64 (-1)
      simp only [Hz1, ↓reduceIte]
      isplitl [Htotal_inv Hdone_inv]
      · iexists _
        iframe
        ipureintro
        rw [imap_sum_delete_none word_count _ _ _ Hlookup0, Htotal_inv]
      iframe
      ipureintro
      refine ⟨?_, ?_⟩
      · rw [Hsize_del, ← Hremaining_size_inv]
        exact sint_nat_sub1 _ (by rw [Hremaining_size_inv]; exact Hne0)
      · intro j v hj
        simp only [GMap.lookup_delete_iff] at hj
        split at hj
        · cases hj
        · exact Hdocs_agree_inv j v hj
    imodintro
    wp_auto
    wp_if_destruct
    · exfalso; simp_all
    · iapply HΦ
      itrivial

end proof

end Perennial
