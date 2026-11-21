/-
The proof of `io.ReadAll`.
-/
module

public import Perennial.Spec.io.ReadAll

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- The chunks `ReadAll` has filled: each a slice holding its bytes, read-only from then on. -/
def io.readAllChunks (cd : List (GoSlice × List w8)) : IProp GF :=
  iprop([∗list] x ∈ cd, x.1 ↦*□ x.2)

instance io.readAllChunks_persistent (cd : List (GoSlice × List w8)) :
    Persistent (io.readAllChunks (GF := GF) cd) := by
  unfold io.readAllChunks; infer_instance

theorem io.readAllChunks_nil : ⊢ io.readAllChunks (GF := GF) [] := by
  unfold io.readAllChunks
  exact BigSepL.bigSepL_nil_intro (Φ := fun _ (x : GoSlice × List w8) => iprop(x.1 ↦*□ x.2))

theorem io.readAll_bound {S : List w8 → IProp GF} (hS : ∀ r, S r ⊢ ⌜r.length < 2 ^ 60⌝)
    (r : List w8) : S r ⊢ ⌜r.length < 2 ^ 60⌝ ∗ S r := by
  exact persistent_entails_right (hS r)

set_option maxHeartbeats 1000000 in
theorem io.ReadAll.wp_proof :
    io.ReadAll.spec (GF := GF) (hG := hG) := by
  intro ri S E r0 eof hS
  wp_start as ⟨#Hr, #Heof, HS⟩
  ihave HEOF := io.eof_of_init $$ Hpkg
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Heof HEOF
  subst Heq
  try wp_auto
  wp_apply wp_slice_make3 (V := w8) (W64 0) (W64 512) ⟨by decide, by decide⟩
    as %b0 ⟨Hb0, Hb0cap, %Hb0c⟩
  try wp_auto
  wp_apply wp_slice_make3 (V := GoSlice) (W64 0) (W64 4) ⟨by decide, by decide⟩
    as %c0 ⟨Hc0, Hc0cap, -⟩
  try wp_auto
  simp only [List.replicate_zero]
  ihave IH : (∃ (bsl : GoSlice) (cur : List w8) (nxt : w64) (csl : GoSlice)
      (cd : List (GoSlice × List w8)) (fs : w64),
      "b" ∷ b_ptr ↦ bsl ∗ "Hb" ∷ bsl ↦* cur ∗ "Hbcap" ∷ ownSliceCap w8 bsl (DFrac.own 1) ∗
      "next" ∷ next_ptr ↦ nxt ∗ "chunks" ∷ chunks_ptr ↦ csl ∗
      "Hcs" ∷ csl ↦* cd.map Prod.fst ∗ "Hcscap" ∷ ownSliceCap GoSlice csl (DFrac.own 1) ∗
      "#Hcd" ∷ io.readAllChunks cd ∗ "finalSize" ∷ finalSize_ptr ↦ fs ∗
      "HS" ∷ S (r0 ++ (cd.map Prod.snd).flatten ++ cur) ∗
      "%Hinv" ∷ ⌜sint.Z fs = ((cd.map Prod.snd).flatten).length ∧ 0 ≤ sint.Z nxt ∧
        sint.Z nxt ≤ 2 * sint.Z bsl.cap ∧ sint.Z nxt ≤ 4 * sint.Z fs + 256⌝ : IProp GF)
      $$ [b next chunks finalSize Hb0 Hb0cap Hc0 Hc0cap HS]
  · iexists b0, [], (W64 256), c0, [], _
    simp only [List.map_nil, List.flatten_nil, List.append_nil]
    iframe
    isplitl []
    · iapply io.readAllChunks_nil
    ipureintro
    simp only [zero_val, ZeroVal.zeroValDef, Hb0c, List.length_nil]
    refine ⟨by word, by word, by word, by word⟩
  wp_for IH
  try simp only [decide_true, ↓reduceIte]
  ihave %Hbwf := ownSlice_wf $$ Hb
  ihave %Hblen := ownSlice_len $$ Hb
  try wp_auto
  simp only [show 0 ≤ sint.Z bsl.len ∧ sint.Z bsl.len ≤ sint.Z bsl.cap ∧
      sint.Z bsl.cap ≤ sint.Z bsl.cap from ⟨Hbwf.1, Hbwf.2, Int.le_refl _⟩]
  icases ownSlice_slice_into_capacity bsl.len bsl.cap bsl cur $$ [Hb Hbcap]
    with ⟨%vsc, Hb1, Hb2, Hb2cap⟩
  · iframe; ipureintro; exact ⟨Hbwf.1, Hbwf.2, Hbwf.2, Int.le_refl _⟩
  have Htk : (cur ++ vsc).take (sint.nat bsl.len) = cur := by
    rw [show sint.nat bsl.len = cur.length by word, List.take_left]
  have Hdr : (cur ++ vsc).drop (sint.nat bsl.len) = vsc := by
    rw [show sint.nat bsl.len = cur.length by word, List.drop_left]
  rw [Htk, Hdr]
  try wp_auto
  wp_apply io.wp_reader_Read ri (fun _ _ => True) S E (r0 ++ (cd.map Prod.snd).flatten ++ cur)
      _ vsc trivial $$ [Hb2 HS]
    as %n %err ⟨%zs, %Hzs, Hb2, HS, #Herr, %Hty⟩
  · iframe Hr HS Hb2
  ihave %Hb2len := ownSlice_len $$ Hb2
  ihave %Hb2wf := ownSlice_wf $$ Hb2
  simp only [slice.slice, List.length_append, List.length_drop] at Hb2len Hb2wf
  have Hvsc : (vsc.length : Int) = sint.Z bsl.cap - sint.Z bsl.len := by
    have := Hzs.2; word
  have Hn : sint.Z (bsl.len + n) = sint.Z bsl.len + zs.length := by
    have := Hzs.2; have := Hzs.1; word
  rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (bsl.len + n) ∧
      sint.Z (bsl.len + n) ≤ sint.Z bsl.cap by
    have := Hzs.2; refine ⟨by decide, by word, by word⟩)]
  -- the new `b`: `b[:len(b)+n]`, the rest of the old capacity its capacity
  ihave Hball := ownSlice_combine (GF := GF) (V := w8) bsl.len bsl (DFrac.own 1) cur
    (zs ++ List.drop zs.length vsc) (W64 0) bsl.cap
    ⟨by word, by decide, Hbwf.1, Hbwf.2⟩ $$ Hb1 Hb2
  ihave Hballcap := ownSliceCap_slice_change_first (V := w8) bsl bsl.len (W64 0) bsl.cap
    (DFrac.own 1) ⟨Int.le_refl _, Hbwf.1, Hbwf.2, by decide, by word⟩ $$ Hb2cap
  icases ownSlice_slice_with_cap (W64 0) (bsl.len + n) (slice.slice bsl w8 (W64 0) bsl.cap) _
    ⟨by decide, by word, by simp only [slice.slice]; word⟩ $$ [Hball Hballcap]
    with ⟨-, Hbn, Hbncap⟩
  · iframe
  rw [slice_slice bsl (W64 0) bsl.cap (W64 0) (bsl.len + n) ⟨by decide, by decide⟩,
    show W64 0 + W64 0 = W64 0 from rfl, show W64 0 + (bsl.len + n) = bsl.len + n by word]
  have Hsub : subslice (sint.nat (W64 0)) (sint.nat (bsl.len + n))
      (cur ++ (zs ++ List.drop zs.length vsc)) = cur ++ zs := by
    simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    rw [show sint.nat (bsl.len + n) = cur.length + zs.length by word, ← List.append_assoc,
      List.take_left' (by simp)]
  rw [Hsub]
  wp_auto
  icases io.readAll_bound hS _ $$ HS with ⟨%Hbound, HS⟩
  simp only [List.length_append] at Hbound
  have Hfl : sint.Z fs = ((cd.map Prod.snd).flatten).length := Hinv.1
  have Hbc : (slice.slice bsl w8 (W64 0) (bsl.len + n)).cap = bsl.cap := by
    simp only [slice.slice]; word
  have Hbl : sint.Z (slice.slice bsl w8 (W64 0) (bsl.len + n)).len =
      cur.length + zs.length := by
    simp only [slice.slice]; have := Hzs.2; word
  rcases err with ei | _
  rotate_left
  · -- `err == nil`: on to a new buffer if this one is nearly full, and read again
    wp_auto
    wp_if_destruct
    · -- the buffer becomes a chunk
      ipersist Hbn
      wp_apply wp_slice_literal (V := GoSlice) [slice.slice bsl w8 (W64 0) (bsl.len + n)]
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply wp_slice_append $$ [$Hcs $Hcscap $Hsl2] as %csl' ⟨Hcs, Hcscap, -⟩
      try wp_auto
      wp_apply wp_slice_make2 (V := w8) nxt as %m ⟨Hm, -⟩
      · ipureintro; exact Hinv.2.1
      try wp_auto
      wp_apply wp_slice_append (V := w8) slice.nil [] m _ (DFrac.own 1) $$ [Hm]
        as %s' ⟨Hs', Hs'cap, -⟩
      · isplitl []
        · iapply ownSlice_nil
        isplitl []
        · iapply ownSliceCap_nil
        iexact Hm
      ihave %Hs'wf := ownSlice_wf $$ Hs'
      ihave %Hs'len := ownSlice_len $$ Hs'
      simp only [List.nil_append, List.length_replicate] at Hs'len
      rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
          sint.Z (W64 0) ≤ sint.Z s'.cap by refine ⟨by decide, by decide, by word⟩)]
      icases ownSlice_slice_with_cap (W64 0) (W64 0) s' _ ⟨by decide, by decide, by word⟩
        $$ [Hs' Hs'cap] with ⟨-, Hbn', Hbn'cap⟩
      · iframe
      have Hcap' : sint.Z (slice.slice s' w8 (W64 0) (W64 0)).cap = sint.Z s'.cap := by
        simp only [slice.slice]; word
      wp_auto
      wp_for_post
      iframe
      iexists _, [], _, csl', cd ++ [(slice.slice bsl w8 (W64 0) (bsl.len + n), cur ++ zs)], _
      simp only [subslice, show sint.nat (W64 0) = 0 from rfl, List.take_zero,
        List.drop_zero, List.append_nil, List.map_append,
        List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons, List.flatten_nil,
        List.append_assoc]
      iframe
      isplitl []
      · unfold io.readAllChunks
        iapply BigSepL.bigSepL_snoc.2
        iframe Hcd Hbn
      ipureintro
      have h1 := Hinv.2.1; have h2 := Hinv.2.2.1; have h3 := Hinv.2.2.2
      have hsw := Hif
      have hcl : (cur.length : Int) = sint.Z bsl.len := by word
      have hzl : (zs.length : Int) ≤ sint.Z bsl.cap - sint.Z bsl.len := by
        have := Hzs.2; omega
      have hC : sint.Z bsl.cap < 2 ^ 63 := by word
      have e1 : sint.Z (bsl.len + n - W64 0) = cur.length + zs.length := by word
      have e2 : sint.Z (fs + (bsl.len + n - W64 0)) =
          ((cd.map Prod.snd).flatten).length + cur.length + zs.length := by word
      have e3 : sint.Z (bsl.cap - W64 0 - (bsl.len + n - W64 0)) =
          sint.Z bsl.cap - (cur.length + zs.length) := by word
      have e4 : sint.Z (BitVec.sdiv (bsl.cap - W64 0) (W64 16)) = sint.Z bsl.cap / 16 := by
        word
      have e5 : sint.Z (nxt + BitVec.sdiv nxt (W64 2)) = sint.Z nxt + sint.Z nxt / 2 := by
        word
      have hs' : sint.Z nxt ≤ sint.Z s'.cap := by word
      rw [e3, e4] at hsw
      simp only [List.length_append]
      refine ⟨by rw [e2]; push_cast; omega, by rw [e5]; omega, by rw [e5, Hcap']; omega,
        by rw [e5, e2]; omega⟩
    · -- not yet: read on into this buffer
      wp_for_post
      iframe
      iexists _, cur ++ zs, nxt, csl, cd, fs
      rw [show r0 ++ (cd.map Prod.snd).flatten ++ (cur ++ zs) =
        r0 ++ (cd.map Prod.snd).flatten ++ cur ++ zs by simp only [List.append_assoc]]
      iframe
      iframe Hcd
      ipureintro
      refine ⟨Hfl, Hinv.2.1, by rw [Hbc]; exact Hinv.2.2.1, Hinv.2.2.2⟩
  · -- `err != nil`: the end of the reads
    unfold io.errAt
    icases Herr with (%Hnil | #HE)
    · exfalso; cases Hnil
    wp_auto
    -- `if err == EOF { err = nil }`
    wp_join iprop(∃ e' : GoInterface, "err" ∷ err_ptr ↦ e' ∗
        "%He'" ∷ ⌜(GoInterface.ok ei = interface.mkOk (go.GoType.PointerType errors.errorString.ty)
            #xeof → e' = interface.nil) ∧
          (GoInterface.ok ei ≠ interface.mkOk (go.GoType.PointerType errors.errorString.ty)
            #xeof → e' = GoInterface.ok ei)⌝) at next with [err] as ⟨%e', err, %He'⟩
    · by_cases hty : ei.ty = go.GoType.PointerType errors.errorString.ty
      · obtain ⟨l, hl⟩ := Hty ei _ rfl hty
        obtain ⟨ty, v⟩ := ei
        simp only at hty hl
        subst hty hl
        simp only [↓reduceIte]
        wp_auto
        wp_if_destruct
        · wp_join_done
          iexists _
          iframe
          ipureintro
          refine ⟨fun _ => rfl, fun h => absurd ?_ h⟩
          simp only [interface.mkOk, Hif]
        · wp_join_done
          iexists _
          iframe
          ipureintro
          refine ⟨fun h => absurd ?_ Hif, fun _ => rfl⟩
          simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at h
          exact go.intoVal_inj h.2
      · simp only [hty, ↓reduceIte]
        wp_auto
        wp_join_done
        iexists _
        iframe
        ipureintro
        refine ⟨fun h => absurd ?_ hty, fun _ => rfl⟩
        simp only [interface.mkOk, GoInterface.ok.injEq] at h
        rw [h]
    have Hpost : ∀ (rr : List w8), ⊢ (□ E rr (GoInterface.ok ei) : IProp GF) -∗
        (⌜e' = interface.nil⌝ ∗ □ E rr (interface.mkOk
            (go.GoType.PointerType errors.errorString.ty) #xeof) ∨
          ⌜e' ≠ interface.nil ∧ e' ≠ interface.mkOk (go.GoType.PointerType errors.errorString.ty)
            #xeof⌝ ∗ □ E rr e') := by
      intro rr
      iintro #HE
      by_cases heq : GoInterface.ok ei = interface.mkOk
          (go.GoType.PointerType errors.errorString.ty) #xeof
      · ileft
        rw [← heq]
        iframe HE
        ipureintro; exact He'.1 heq
      · iright
        rw [He'.2 heq]
        iframe HE
        ipureintro; exact ⟨by simp, heq⟩
    ihave %Hcslen := ownSlice_len $$ Hcs
    wp_if_destruct
    · -- no chunks: the buffer is the result
      have Hcd0 : cd = [] := by
        apply List.eq_nil_of_length_eq_zero
        have := Hcslen.1; simp only [List.length_map] at this; rw [this, Hif]; rfl
      subst Hcd0
      wp_for_post
      iapply HΦ
      iexists cur ++ zs
      simp only [List.map_nil, List.flatten_nil, List.append_nil] at *
      rw [← List.append_assoc]
      iframe Hbn HS
      iapply Hpost (r0 ++ cur ++ zs) $$ HE
    -- the result: the chunks and the buffer, copied into one slice
    have hcl : (cur.length : Int) = sint.Z bsl.len := by word
    have hzl : (zs.length : Int) ≤ sint.Z bsl.cap - sint.Z bsl.len := by
      have := Hzs.2; omega
    have hC : sint.Z bsl.cap < 2 ^ 63 := by word
    have e1 : sint.Z (bsl.len + n - W64 0) = cur.length + zs.length := by word
    have e2 : sint.Z (fs + (bsl.len + n - W64 0)) =
        ((cd.map Prod.snd).flatten).length + cur.length + zs.length := by word
    wp_apply wp_slice_make2 (V := w8) (fs + (bsl.len + n - W64 0)) as %m ⟨Hm, -⟩
    · ipureintro; rw [e2]; omega
    try wp_auto
    wp_apply wp_slice_append (V := w8) slice.nil [] m _ (DFrac.own 1) $$ [Hm]
      as %f0 ⟨Hf0, Hf0cap, -⟩
    · isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      iexact Hm
    ihave %Hf0wf := ownSlice_wf $$ Hf0
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
        sint.Z (W64 0) ≤ sint.Z f0.cap by refine ⟨by decide, by decide, by word⟩)]
    icases ownSlice_slice_with_cap (W64 0) (W64 0) f0 _ ⟨by decide, by decide, by word⟩
      $$ [Hf0 Hf0cap] with ⟨-, Hfin, Hfincap⟩
    · iframe
    try simp only [List.drop_zero]
    wp_auto
    have Hcdl : (cd.length : Int) = sint.Z csl.len := by
      have := Hcslen.1; have := Hcslen.2; simp only [List.length_map] at *; word
    ihave IL : (∃ (i : w64) (fsl : GoSlice) (cv : GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "final" ∷ final_ptr ↦ fsl ∗
        "Hfin" ∷ fsl ↦* ((cd.take (sint.nat i)).map Prod.snd).flatten ∗
        "Hfincap" ∷ ownSliceCap w8 fsl (DFrac.own 1) ∗ "chunk" ∷ chunk_ptr ↦ cv ∗
        "Hcs" ∷ csl ↦* cd.map Prod.fst ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ cd.length⌝ : IProp GF)
        $$ [i final Hfin Hfincap chunk Hcs]
    · iexists _, _, _
      rw [show (List.map Prod.snd (List.take (sint.nat (W64 0)) cd)).flatten = [] by
        rw [show sint.nat (W64 0) = 0 by word]; simp]
      iframe
      isplitl [Hfin]
      · rw [show subslice (sint.nat (W64 0)) (sint.nat (W64 0)) ([] ++ List.replicate
            (sint.nat (fs + (bsl.len + n - W64 0))) (zero_val w8)) = ([] : List w8) by
          simp [subslice]]
        iexact Hfin
      ipureintro
      exact ⟨by decide, by have : sint.Z (W64 0) = 0 := by decide
                           omega⟩
    wp_for IL
    wp_if_destruct
    · -- another chunk
      have Hif' : sint.Z i < sint.Z csl.len := Hif
      have Hlt : sint.nat i < cd.length := by
        have h := Hif'; have h2 := Hi.1
        rw [show sint.nat i = (sint.Z i).toNat from rfl]; omega
      obtain ⟨x, Hx⟩ : ∃ x, cd[sint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hxf : (cd.map Prod.fst)[(sint.Z i).toNat]? = some x.1 := by
        rw [List.getElem?_map]; simp only [show (sint.Z i).toNat = sint.nat i from rfl, Hx,
          Option.map_some]
      rw [ite_eq_left ⟨Hi.1, Hif'⟩]
      wp_apply wp_load_slice_index csl (sint.Z i) (cd.map Prod.fst) (DFrac.own 1) x.1 Hi.1
        $$ [Hcs] as Hcs
      · iframe; ipureintro; exact Hxf
      try wp_auto
      ihave #Hx1 := (show io.readAllChunks (GF := GF) cd ⊢ x.1 ↦*□ x.2 from by
        unfold io.readAllChunks
        exact BigSepL.bigSepL_lookup (Φ := fun _ (y : GoSlice × List w8) => iprop(y.1 ↦*□ y.2)) Hx)
        $$ Hcd
      wp_apply wp_slice_append (V := w8) fsl _ x.1 x.2 DFrac.discard $$ [Hfin Hfincap]
        as %fsl' ⟨Hfin, Hfincap, -⟩
      · iframe; iexact Hx1
      wp_for_post
      iframe
      iexists _, _, _
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hx]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
        List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil]
      iframe
      ipureintro; exact ⟨by word, by word⟩
    · -- all the chunks copied: then the buffer
      have Hif' : ¬ sint.Z i < sint.Z csl.len := Hif
      rw [show sint.nat i = cd.length by
        have h2 := Hi.2; have h3 := Hif'; rw [show sint.nat i = (sint.Z i).toNat from rfl]; omega,
        List.take_length]
      try wp_auto
      wp_apply wp_slice_append (V := w8) fsl _ _ _ (DFrac.own 1) $$ [Hfin Hfincap Hbn]
        as %fsl' ⟨Hfin, Hfincap, -⟩
      · iframe
      wp_auto
      wp_for_post
      iapply HΦ
      iexists (cd.map Prod.snd).flatten ++ (cur ++ zs)
      rw [show r0 ++ ((cd.map Prod.snd).flatten ++ (cur ++ zs)) =
        r0 ++ (cd.map Prod.snd).flatten ++ cur ++ zs by simp only [List.append_assoc]]
      iframe Hfin HS
      iapply Hpost $$ HE

end proof

end Perennial
