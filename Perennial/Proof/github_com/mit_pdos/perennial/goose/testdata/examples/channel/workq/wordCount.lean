/-
The proof of `workq.wordCount`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.wordCount
public import Perennial.Spec.sync.atomic.Int64__Store
public import Perennial.Spec.sync.atomic.Int64__Load
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker__run

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

set_option goose.wp.extras true

set_option maxHeartbeats 1000000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.wordCount.wp_proof
    (wp_Int64_Store : sync.atomic.Int64.Store.spec (GF := GF) (hG := hG))
    (wp_Int64_Load : sync.atomic.Int64.Load.spec (GF := GF) (hG := hG))
    (wp_Worker_run :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Worker.run.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.wordCount.spec
      (GF := GF) (hG := hG) := fun docs_sl docs hdocs => by
  wp_start as Hdocs
  iNamed Hdocs
  wp_auto
  ihave %Hdocs_len := ownSlice_len _ _ _ $$ Hdocs
  wp_if_destruct
  · have : docs = [] := List.eq_nil_of_length_eq_zero (by rw [Hdocs_len.1, Hif]; rfl)
    subst this
    rw [show (W64 (((([] : List GoString).map word_count).sum : Nat) : Int)) = W64 0 from rfl]
    iapply HΦ
    itrivial
  wp_apply wp_slice_make2 (V := Loc) (W64 2) $$ [] as %workers_sl ⟨workers_sl, -⟩
  · ipureintro; decide
  rename_i j_ptr
  irename : (j_ptr ↦ zero_val w64 : IProp GF) => j
  imod ghost_map_alloc (GMap.mapSeq 0 (docs.map some)) with ⟨%γtask_gn, Hauth, Htasks⟩
  ihave HI : (∃ (i j : w64) (workers : List Loc),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "workers_sl" ∷ workers_sl ↦* (workers ++ List.replicate (2 - sint.nat i) null) ∗
      "#Hworkers" ∷ □ (∀ w, ⌜w ∈ workers⌝ → isWorker ⟨docs, γtask_gn⟩ w) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 2 ∧ workers.length = sint.nat i⌝ : IProp GF)
    $$ [i j workers_sl]
  · iexists W64 0, _, []
    rw [show List.replicate 2 (zero_val Loc) =
      [] ++ List.replicate (2 - sint.nat (W64 0)) null from rfl]
    iframe
    isplitr
    · imodintro; iintro %w %Hw; simp at Hw
    · ipureintro; decide
  wp_for HI
  ihave %Hwl := ownSlice_len _ _ _ $$ workers_sl
  simp only [List.length_append, List.length_replicate] at Hwl
  by_cases hP : sint.Z i < sint.Z workers_sl.len
  · simp only [hP, decide_true, ↓reduceIte]
    wp_auto
    simp only [Hi.1, hP, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl (sint.Z i) _ _ null Hi.1 $$ [workers_sl] as workers_sl
    · iframe
      ipureintro
      have h1 := Hi.2.2
      have h2 := Hwl.1
      simp only [sint.nat, sint.Z] at h1 h2 hP ⊢
      rw [List.getElem?_append_right (by omega), List.getElem?_replicate_of_lt (by omega)]
    wp_apply chan.wp_make2 (V := GoString) docs_sl.len $$ [] as %queue %γqueue ⟨#Hq_is, %Hqcap, Hq_own⟩
    · ipureintro
      refine ⟨Hdocs_len.2, ?_⟩
      have := Hdocs_len.1; simp only [sint.nat, sint.Z] at this ⊢; omega
    wp_apply chan.wp_make1 (V := GoChan) as %steal %γsteal ⟨#Hs_is, %Hscap, Hs_own⟩
    simp only [Hi.1, hP, and_self, ↓reduceIte]
    irename «$r0» => Hwr
    imod (typedPointsto_dfractional (GF := GF) «$r0_ptr»
      ({ queue' := queue, steal' := steal } : Worker)).dfractional_persist _ $$ Hwr with #Hwr
    simp only [Hif, ↓reduceIte]
    imod start_bag (ownTask (GF := GF) ⟨docs, γtask_gn⟩) _ queue γqueue (by trivial)
      $$ Hq_is Hq_own with #Hqueue
    imod start_bag (fun (reply : GoChan) => iprop(∃ γreply : ChanNames,
        isChanBag γreply reply (stealReplyPred (GF := GF) ⟨docs, γtask_gn⟩))) _ steal γsteal
      (by trivial) $$ Hs_is Hs_own with #Hsteal
    wp_apply wp_store_slice_index workers_sl (sint.Z i) _ «$r0_ptr» $$ [workers_sl] as workers_sl
    · iframe
      ipureintro
      simp only [List.length_append, List.length_replicate]
      have h0 := Hi
      have h2 := Hwl.1
      simp only [sint.nat, sint.Z] at h0 h2 hP ⊢
      omega
    wp_for_post
    iframe
    iexists i + W64 1, i, workers ++ [«$r0_ptr»]
    have h0 := Hi
    have h2 := Hwl.1
    simp only [sint.nat, sint.Z] at h0 h2 hP
    have hi1 : (i + W64 1).toInt = i.toInt + 1 := by word
    obtain ⟨k, hk⟩ : ∃ k, 2 - i.toInt.toNat = k + 1 := ⟨2 - i.toInt.toNat - 1, by omega⟩
    rw [show (workers ++ List.replicate (2 - sint.nat i) null).set (sint.Z i).toNat «$r0_ptr» =
        workers ++ [«$r0_ptr»] ++ List.replicate (2 - sint.nat (i + W64 1)) null by
      simp only [sint.nat, sint.Z, hi1, hk, List.replicate_succ]
      rw [show i.toInt.toNat = workers.length by omega, List.set_append_right _ _ (by omega)]
      simp only [Nat.sub_self, List.set_cons_zero, List.append_assoc, List.singleton_append]
      rw [show 2 - (BitVec.toInt i + 1).toNat = k by omega]]
    iframe
    isplitr
    · imodintro
      iintro %w %Hw
      rcases List.mem_append.1 Hw with Hw | Hw
      · iapply Hworkers $$ %w %Hw
      · simp only [List.mem_singleton] at Hw
        subst Hw
        unfold isWorker
        iexists ({ queue' := queue, steal' := steal } : Worker), γsteal, γqueue
        iframe #
    · ipureintro
      simp only [sint.nat, sint.Z, hi1, List.length_append, List.length_singleton]
      omega
  simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
  have h0 := Hi
  have h2 := Hwl.1
  simp only [sint.nat, sint.Z] at h0 h2 hP
  have Hwlen : workers.length = 2 := by omega
  rw [show List.replicate (2 - sint.nat i) null = ([] : List Loc) by
    simp only [sint.nat, List.replicate_eq_nil_iff]; omega, List.append_nil]
  wp_auto
  ihave Htasks := tasks_to_list ⟨docs, γtask_gn⟩ 0 docs $$ Htasks
  ihave HI : (∃ (i : w64) (d : GoString),
      "doc" ∷ doc_ptr ↦ d ∗
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z docs_sl.len⌝ ∗
      "Htasks" ∷ [∗list] d ∈ docs.drop (sint.nat i), ownTask (GF := GF) ⟨docs, γtask_gn⟩ d : IProp GF)
    $$ [doc i Htasks]
  · iexists W64 0, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe
    ipureintro; exact ⟨by decide, Hdocs_len.2⟩
  wp_for HI
  by_cases hP : sint.Z i < sint.Z docs_sl.len
  · simp only [hP, _root_.decide_true, ↓reduceIte]
    wp_auto
    simp only [Hi.1, hP, and_self, ↓reduceIte]
    have hlt : sint.nat i < docs.length := by
      have := Hdocs_len.1; simp only [sint.nat, sint.Z] at this hP Hi ⊢; omega
    obtain ⟨dc, Hdc⟩ : ∃ dc, docs[sint.nat i]? = some dc := ⟨_, List.getElem?_eq_getElem hlt⟩
    wp_apply wp_load_slice_index docs_sl (sint.Z i) docs _ dc Hi.1 $$ [Hdocs] as Hdocs
    · iframe; ipureintro; exact Hdc
    ihave %Hwl2 := ownSlice_len _ _ _ $$ workers_sl
    rw [Hwlen] at Hwl2
    have hw0 : (0 : Int) < sint.Z workers_sl.len := by
      have := Hwl2.1; simp only [sint.nat, sint.Z] at this ⊢; omega
    obtain ⟨w0, Hw0⟩ : ∃ w0, workers[0]? = some w0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [show sint.Z (W64 0) = 0 from rfl, Int.le_refl, hw0, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl 0 workers _ w0 (Int.le_refl _) $$ [workers_sl] as workers_sl
    · iframe; ipureintro; exact Hw0
    ihave Hw := Hworkers $$ %w0 %(List.mem_of_getElem? Hw0)
    iunfold isWorker at Hw
    icases Hw with ⟨%wv, %γsteal, %γqueue, #Hwpt, #Hqueue, #Hsteal⟩
    icases Hwpt with ∗Hwpt
    iStructNamed Hwpt
    wp_auto
    rw [List.drop_eq_getElem_cons hlt]
    icases BigSepL.bigSepL_cons.1 $$ Htasks with ⟨Hdoc, Htasks⟩
    rw [(List.getElem?_eq_some_iff.1 Hdc).2]
    wp_apply wp_bag_send γqueue wv.queue' dc (ownTask (GF := GF) ⟨docs, γtask_gn⟩) $$ [Hdoc]
    · iframe #; iframe
    wp_for_post
    iframe
    iexists i + W64 1, dc
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by
      simp only [sint.nat, sint.Z] at hP Hi ⊢; word
    rw [hi1]
    iframe
    ipureintro
    simp only [sint.Z] at hP Hi ⊢
    word
  simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
  iclear Htasks
  wp_auto
  ihave Hrem : sync.atomic.ownInt64 (GF := GF) «$v0_ptr» (DFrac.own 1) (W64 0) $$ [«$v0»]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ _0' := zero_val _, _1' := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact «$v0»
  ihave Htot : sync.atomic.ownInt64 (GF := GF) «$v1_ptr» (DFrac.own 1) (W64 0) $$ [«$v1»]
  · rw [sync.atomic.ownInt64_unseal]
    unfold sync.atomic.ownInt64Def
    rw [show ({ _0' := zero_val _, _1' := zero_val _, v' := W64 0 } : sync.atomic.Int64) =
      zero_val _ from rfl]
    iexact «$v1»
  wp_apply chan.wp_make1 (V := Unit) as %done %γdone ⟨#Hdone_is, %Hdcap, Hdone⟩
  wp_apply_core wp_Int64_Store $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Hrem
  iintro Hrem
  imod Hmask with -
  imodintro
  wp_auto
  imod alloc_broadcast_chan (E := ⊤)
    (isTasksDone (GF := GF) ⟨docs, γtask_gn⟩ ⟨«$v0_ptr», «$v1_ptr», done⟩) γdone done
    $$ Hdone_is Hdone with Hopen
  ihave #Hdone_unk := ownBroadcastChan_Unknown _ _ _ _ $$ Hopen
  imod inv_alloc nroot ⊤ (coordinatorInv (GF := GF) ⟨docs, γtask_gn⟩ ⟨«$v0_ptr», «$v1_ptr», done⟩ γdone)
    $$ [Hopen Htot Hrem Hauth] with #Hinv
  · inext
    unfold coordinatorInv ownTaskAuth
    iexists GMap.mapSeq 0 (docs.map some), docs_sl.len
    simp only [Hif, ↓reduceIte]
    isplitl [Htot Hopen]
    · iexists W64 0
      iframe
      ipureintro
      rw [imap_sum_all_some]
      · rfl
      · intro j hj
        exact ⟨docs[j], by simp [GMap.lookup_map_seq_0, List.getElem?_eq_getElem hj]⟩
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [mapSeq_size, List.length_map, Hdocs_len.1]
    · intro j v hj
      rw [GMap.lookup_map_seq_0, List.getElem?_map] at hj
      cases h : docs[j]? with
      | none => simp [h] at hj
      | some d' =>
        simp only [h, Option.map_some, Option.some.injEq] at hj
        subst hj
        simp
  ihave #Hcoord : isCoordinator (GF := GF) ⟨docs, γtask_gn⟩ ⟨«$v0_ptr», «$v1_ptr», done⟩ $$ []
  · unfold isCoordinator
    iexists γdone
    iframe #
  rename_i jj_ptr
  irename : (jj_ptr ↦ zero_val w64 : IProp GF) => j
  ihave HI : (∃ (i j : w64) (wv : Loc),
      "w" ∷ w_ptr ↦ wv ∗
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ jj_ptr ↦ j ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 2⌝ : IProp GF) $$ [w i j]
  · iexists W64 0, _, _
    iframe
    ipureintro; decide
  ihave %Hwl3 := ownSlice_len _ _ _ $$ workers_sl
  rw [Hwlen] at Hwl3
  have hwlen2 : sint.Z workers_sl.len = 2 := by
    have := Hwl3.1; simp only [sint.nat, sint.Z] at this ⊢; omega
  wp_for HI
  by_cases hP : sint.Z i < sint.Z workers_sl.len
  · simp only [hP, _root_.decide_true, ↓reduceIte]
    wp_auto
    rw [hwlen2] at hP
    have hlt : sint.nat i < workers.length := by
      rw [Hwlen]; simp only [sint.nat, sint.Z] at hP Hi ⊢; omega
    obtain ⟨w, Hw⟩ : ∃ w, workers[sint.nat i]? = some w := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hi.1, hwlen2, hP, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl (sint.Z i) workers _ w Hi.1 $$ [workers_sl] as workers_sl
    · iframe; ipureintro; exact Hw
    have Hb := mods_2_bound i Hi.1 hP
    have hlt2 : sint.nat ((i + W64 1).srem (W64 2)) < workers.length := by
      rw [Hwlen]; simp only [sint.nat, sint.Z] at Hb ⊢; omega
    obtain ⟨nb, Hnb⟩ : ∃ nb, workers[sint.nat ((i + W64 1).srem (W64 2))]? = some nb :=
      ⟨_, List.getElem?_eq_getElem hlt2⟩
    simp only [Hb.1, Hb.2, hwlen2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl _ workers _ nb Hb.1 $$ [workers_sl] as workers_sl
    · iframe; ipureintro; exact Hnb
    ihave #Hw := Hworkers $$ %w %(List.mem_of_getElem? Hw)
    ihave #Hnb := Hworkers $$ %nb %(List.mem_of_getElem? Hnb)
    wp_apply wp_fork $$ []
    · wp_apply wp_Worker_run ⟨docs, γtask_gn⟩ w nb ⟨«$v0_ptr», «$v1_ptr», done⟩ $$ []
      · iframe #
      itrivial
    wp_for_post
    iframe
    iexists i + W64 1, i, w
    iframe
    ipureintro
    simp only [sint.Z] at hP Hi ⊢
    word
  simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
  cleanup_bool_decide
  wp_auto
  wp_apply_core chan.wp_receive (V := Unit) done γdone $$ Hdone_is [-]
  iintro -
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_unk
  iintro ⟨#Htotal, -⟩
  wp_auto
  wp_apply_core wp_Int64_Load $$ [] [-]
  · iPkgInit
  unfold isTasksDone
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Htotal
  iintro -
  imod Hmask with -
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
