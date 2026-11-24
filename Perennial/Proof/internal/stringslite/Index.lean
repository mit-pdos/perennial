/-
The proof of `internal.stringslite.Index`.
-/
module

public import Perennial.Spec.internal.stringslite.Index
public import Perennial.Spec.internal.stringslite.IndexByte
public import Perennial.Spec.internal.bytealg.IndexString
public import Perennial.Spec.internal.bytealg.IndexRabinKarp
public import Perennial.Spec.internal.bytealg.Cutover
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

set_option maxHeartbeats 1600000 in
theorem internal.stringslite.Index.wp_proof
    (wp_IndexByte : internal.stringslite.IndexByte.spec (GF := GF) (hG := hG))
    (wp_IndexString : internal.bytealg.IndexString.spec (GF := GF) (hG := hG))
    (wp_IndexRabinKarp : internal.bytealg.IndexRabinKarp.spec (GF := GF) (hG := hG))
    (wp_Cutover : internal.bytealg.Cutover.spec (GF := GF) (hG := hG)) :
    internal.stringslite.Index.spec (GF := GF) (hG := hG) := by
  intro s sep
  wp_start as #Hinit
  ihave #Hb : isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg $$ []
  · iPkgInit
  ihave ⟨%m, #HMaxLen, %Hm⟩ := internal.bytealg.isInit_access $$ Hb
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hn
  wp_if_destruct
  · -- `n == 0`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Hsep : sep = [] := List.eq_nil_of_length_eq_zero (by revert Hif; word)
    subst Hsep
    try wp_auto
    rw [internal.bytealg.index_eq_of s [] 0 List.nil_prefix (by simp)]
    iapply HΦ
    ipureintro; simp
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  have Hn0 : 0 < sep.length := by
    rcases Nat.eq_zero_or_pos sep.length with h | h
    · exact absurd (by rw [h]; rfl) Hif
    · exact h
  wp_if_destruct
  · -- `n == 1`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have H1 : sep.length = 1 := by revert Hif; word
    obtain ⟨c, Hc⟩ : ∃ c, sep = [c] := by
      match sep, H1 with
      | [c], _ => exact ⟨c, rfl⟩
    subst Hc
    try wp_auto
    wp_apply wp_IndexByte as %Hsl
    unfold internal.bytealg.indexByte
    iapply HΦ
    ipureintro
    exact fun _ => Hsl
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  wp_if_destruct
  · -- `n == len(s)`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Heq : sep.length = s.length := by revert Hif; word
    try wp_auto
    wp_if_destruct
    · subst Hif
      try wp_auto
      rw [internal.bytealg.index_eq_of sep sep 0 (by simp) (by simp)]
      iapply HΦ
      ipureintro; exact fun _ => Hsl
    · try wp_auto
      rw [internal.bytealg.index_eq_neg s sep (fun k hk => by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          exact Hif (List.IsPrefix.eq_of_length (by simpa using hk) Heq)
        · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega) hk)]
      iapply HΦ
      ipureintro; exact fun _ => Hsl
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · -- `n > len(s)`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Hgt : s.length < sep.length := by revert Hif; word
    try wp_auto
    rw [internal.bytealg.index_eq_neg s sep (fun k =>
      internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega))]
    iapply HΦ
    ipureintro; exact fun _ => Hsl
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  have Hlt : sep.length < s.length := by revert Hif; word
  have Hn2 : 2 ≤ sep.length := by
    rcases Nat.lt_or_ge sep.length 2 with h | h
    · exfalso
      rcases (by omega : sep.length = 0 ∨ sep.length = 1) with h' | h'
      · omega
      · exact ‹¬W64 ↑(List.length sep) = W64 1› (by rw [h']; rfl)
    · exact h
  obtain ⟨c0, c1, rest, Hsep⟩ : ∃ c0 c1 rest, sep = c0 :: c1 :: rest := by
    match sep, Hn2 with
    | c0 :: c1 :: rest, _ => exact ⟨c0, c1, rest, rfl⟩
  have Hm' : sint.Z m = 31 ∨ sint.Z m = 63 := by
    rcases Hm with h | h <;> subst h
    · left; rfl
    · right; rfl
  wp_if_destruct
  · -- `n <= MaxLen`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Hnm : (sep.length : Int) ≤ sint.Z m := by revert Hif; word
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    wp_if_destruct
    · try wp_auto
      wp_apply wp_IndexString $$ []
      · iframe HMaxLen; ipureintro; exact ⟨Hn2, Hnm⟩
      iapply HΦ
      ipureintro; exact fun _ => Hsl
    have Hs0 : sep[0]? = some c0 := by rw [Hsep]; rfl
    have Hs1 : sep[1]? = some c1 := by rw [Hsep]; rfl
    try wp_auto
    simp only [Hs0]
    try wp_auto
    simp only [Hs1]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    rw [show W64 (s.length : Int) - W64 (sep.length : Int) + W64 1 =
      W64 ((s.length - sep.length + 1 : Nat) : Int) by word]
    ihave HI : (∃ (i : Nat) (f : w64), "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "fails" ∷ fails_ptr ↦ f ∗
        "%Hi" ∷ ⌜i ≤ s.length - sep.length + 1 ∧ ∀ k < i, ¬ sep <+: s.drop k⌝ : IProp GF)
        $$ [i fails]
    · iexists 0, _
      iframe
      ipureintro
      exact ⟨by omega, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    wp_for HI
    wp_if_destruct
    · have HiT : i < s.length - sep.length + 1 := by have := Hi.1; revert Hif; word
      have Hk : sint.nat (W64 (i : Int)) = i := by word
      have Hk0 : 0 ≤ sint.Z (W64 (i : Int)) := by word
      obtain ⟨b, Hb⟩ : ∃ b, s[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      simp only [Hk, Hk0, ↓reduceIte, Hb]
      try wp_auto
      wp_join (Q := fun v => iprop(s_ptr ↦ s ∗ c0_ptr ↦ c0 ∗
          t_ptr ↦ W64 ((s.length - sep.length + 1 : Nat) : Int) ∗
          ((⌜v = executeVal⌝ ∗ «$res0_ptr» ↦ zero_val w64 ∗ ∃ i' : Nat, i_ptr ↦ W64 (i' : Int) ∗
              ⌜i' < s.length - sep.length + 1 ∧ s[i']? = some c0 ∧
                ∀ k < i', ¬ sep <+: s.drop k⌝) ∨
            (⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ W64 (-1) ∗
              ⌜internal.bytealg.index s sep = -1⌝ ∗ ∃ i' : w64, i_ptr ↦ i'))))
          with [s c0 t «$res0» i]
      · -- `s[i] == c0`
        subst Hif
        iframe
        ileft
        iframe
        ipureintro
        exact ⟨HiT, Hb, Hi.2⟩
      · -- `s[i] != c0`: `IndexByte(s[i+1:t], c0)`
        have Hhead : ¬ sep <+: s.drop i := by
          rw [Hsep]; exact internal.bytealg.not_prefix_drop_of_head s _ c0 i (by rw [Hb]; simpa)
        rw [ite_eq_left (by word)]
        rw [show sint.nat (W64 ((s.length - sep.length + 1 : Nat) : Int)) -
            sint.nat (W64 (i : Int) + W64 1) = s.length - sep.length + 1 - (i + 1) by word,
          show sint.nat (W64 (i : Int) + W64 1) = i + 1 by word]
        try wp_auto
        wp_apply wp_IndexByte as %-
        rcases internal.bytealg.indexByte_slice_cases s c0 (i + 1)
            (s.length - sep.length + 1 - (i + 1)) with ⟨r, Hr, Hrb, Hrc, Hrmin⟩ | ⟨Hr, Hnone⟩
        · rw [Hr]
          try wp_auto
          wp_if_destruct
          · exfalso; revert Hif; word
          try wp_auto
          rw [show W64 (i : Int) + (W64 (r : Int) + W64 1) = W64 ((i + 1 + r : Nat) : Int) by word]
          iframe
          ileft
          iframe
          ipureintro
          refine ⟨by omega, Hrc, fun k hk => ?_⟩
          rcases Nat.lt_trichotomy k i with hki | rfl | hki
          · exact Hi.2 k hki
          · exact Hhead
          · rw [Hsep]
            exact internal.bytealg.not_prefix_drop_of_head s _ c0 k (by
              have := Hrmin (k - (i + 1)) (by omega)
              rwa [show i + 1 + (k - (i + 1)) = k by omega] at this)
        · rw [Hr]
          try wp_auto
          iframe
          iright
          isplitl []
          · ipureintro; rfl
          iframe
          ipureintro
          · refine internal.bytealg.index_eq_neg s sep (fun k => ?_)
            rcases Nat.lt_trichotomy k i with hki | rfl | hki
            · exact Hi.2 k hki
            · exact Hhead
            · rcases Nat.lt_or_ge k (s.length - sep.length + 1) with hkT | hkT
              · rw [Hsep]
                exact internal.bytealg.not_prefix_drop_of_head s _ c0 k (by
                  have := Hnone (k - (i + 1)) (by omega)
                  rwa [show i + 1 + (k - (i + 1)) = k by omega] at this)
              · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega)
      iintro ⟨s, c0, t, (⟨%Hv, «$res0», %j, i, %Hj⟩ | ⟨%Hv, «$res0», %Hidx, %iw, i⟩)⟩
      · subst Hv
        try wp_auto
        obtain ⟨HjT, Hjc, Hjmin⟩ := Hj
        have Hj1 : j + 1 < s.length := by omega
        obtain ⟨b1, Hb1⟩ : ∃ b1, s[j + 1]? = some b1 := ⟨_, List.getElem?_eq_getElem Hj1⟩
        simp only [show 0 ≤ sint.Z (W64 (j : Int) + W64 1) by word,
          show sint.nat (W64 (j : Int) + W64 1) = j + 1 by word, ↓reduceIte, Hb1]
        try wp_auto
        wp_join (Q := fun v => iprop(⌜v = #(decide (sep <+: s.drop j))⌝ ∗ s_ptr ↦ s ∗
            i_ptr ↦ W64 (j : Int) ∗ n_ptr ↦ W64 (sep.length : Int) ∗ substr_ptr ↦ sep))
            at (if: #(decide _) then _ else #false) with [s i n substr]
        · wp_if_destruct
          · try wp_auto
            rw [ite_eq_left (by word)]
            rw [show sint.nat (W64 (j : Int) + W64 (sep.length : Int)) - sint.nat (W64 (j : Int)) =
                sep.length by word, show sint.nat (W64 (j : Int)) = j by word]
            try wp_auto
            iframe
            ipureintro
            rw [decide_eq_decide.2 (show List.take sep.length (List.drop j s) = sep ↔
              sep <+: List.drop j s by rw [List.prefix_iff_eq_take]; exact eq_comm)]
          · iframe
            ipureintro
            rw [decide_eq_false (internal.bytealg.not_prefix_drop_of_getElem s sep c1 1 j Hs1
              (by rw [Hb1]; intro h; exact ‹¬b1 = c1› (Option.some.inj h)))]
        iintro ⟨%Hv, s, i, n, substr⟩
        subst Hv
        try wp_auto
        wp_if_destruct
        · -- found at `j`
          try wp_auto
          wp_for_post
          rw [internal.bytealg.index_eq_of s sep j Hif Hjmin]
          iapply HΦ
          ipureintro; exact fun _ => Hsl
        · have Hnf := Hif
          try wp_auto
          rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word]
          wp_apply wp_Cutover
          wp_if_destruct
          · -- `IndexString(s[i:], substr)`
            wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
            try wp_auto
            rw [ite_eq_left (by word)]
            rw [show sint.nat (W64 (s.length : Int)) - sint.nat (W64 ((j + 1 : Nat) : Int)) =
                s.length - (j + 1) by word,
              show sint.nat (W64 ((j + 1 : Nat) : Int)) = j + 1 by word,
              List.take_of_length_le (by simp)]
            try wp_auto
            wp_apply wp_IndexString $$ []
            · iframe HMaxLen; ipureintro; exact ⟨Hn2, Hnm⟩
            have Hnomatch : ∀ k < j + 1, ¬ sep <+: s.drop k := fun k hk => by
              rcases Nat.lt_or_ge k j with h | h
              · exact Hjmin k h
              · rw [show k = j by omega]; exact Hnf
            have Hdrop := internal.bytealg.index_drop s sep (j + 1) Hnomatch
            have Hrb := internal.bytealg.index_bounds (s.drop (j + 1)) sep
            generalize internal.bytealg.index (s.drop (j + 1)) sep = r at Hrb Hdrop ⊢
            have Hr63 : -1 ≤ r ∧ r < 2 ^ 63 := by
              simp only [List.length_drop] at Hrb
              rcases Int.lt_or_le r 0 with h | h
              · omega
              · have := Hrb.2 h; omega
            wp_if_destruct
            · try wp_auto
              wp_for_post
              rw [Hdrop, ite_eq_left (by revert Hif; word)]
              rw [show W64 r + W64 ((j + 1 : Nat) : Int) = W64 (r + ((j + 1 : Nat) : Int)) by word]
              iapply HΦ
              ipureintro; exact fun _ => Hsl
            · try wp_auto
              wp_for_post
              rw [Hdrop, ite_eq_right (by revert Hif; word)]
              iapply HΦ
              ipureintro; exact fun _ => Hsl
          · try wp_auto
            wp_for_post
            iframe
            iexists j + 1, _
            iframe
            ipureintro
            refine ⟨by omega, fun k hk => ?_⟩
            rcases Nat.lt_or_ge k j with h | h
            · exact Hjmin k h
            · rw [show k = j by omega]; exact Hnf
      · subst Hv
        try wp_auto
        wp_for_post
        rw [Hidx]
        iapply HΦ
        ipureintro; exact fun _ => Hsl
    · -- `i >= t`
      have HiT : s.length - sep.length + 1 ≤ i := by have := Hi.1; revert Hif; word
      rw [internal.bytealg.index_eq_neg s sep (fun k => by
        rcases Nat.lt_or_ge k i with h | h
        · exact Hi.2 k h
        · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega))]
      iapply HΦ
      ipureintro; exact fun _ => Hsl
  have Hs0 : sep[0]? = some c0 := by rw [Hsep]; rfl
  have Hs1 : sep[1]? = some c1 := by rw [Hsep]; rfl
  try wp_auto
  simp only [Hs0]
  try wp_auto
  simp only [Hs1]
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  rw [show W64 (s.length : Int) - W64 (sep.length : Int) + W64 1 =
    W64 ((s.length - sep.length + 1 : Nat) : Int) by word]
  ihave HI : (∃ (i : Nat) (f : w64), "i" ∷ i_ptr ↦ W64 (i : Int) ∗ "fails" ∷ fails_ptr ↦ f ∗
      "%Hi" ∷ ⌜i ≤ s.length - sep.length + 1 ∧ ∀ k < i, ¬ sep <+: s.drop k⌝ : IProp GF)
      $$ [i fails]
  · iexists 0, _
    iframe
    ipureintro
    exact ⟨by omega, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  wp_for HI
  wp_if_destruct
  · have HiT : i < s.length - sep.length + 1 := by have := Hi.1; revert Hif; word
    have Hk : sint.nat (W64 (i : Int)) = i := by word
    have Hk0 : 0 ≤ sint.Z (W64 (i : Int)) := by word
    obtain ⟨b, Hb⟩ : ∃ b, s[i]? = some b := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_join (Q := fun v => iprop(s_ptr ↦ s ∗ c0_ptr ↦ c0 ∗
        t_ptr ↦ W64 ((s.length - sep.length + 1 : Nat) : Int) ∗
        ((⌜v = executeVal⌝ ∗ «$res0_ptr» ↦ zero_val w64 ∗ ∃ i' : Nat, i_ptr ↦ W64 (i' : Int) ∗
            ⌜i' < s.length - sep.length + 1 ∧ s[i']? = some c0 ∧
              ∀ k < i', ¬ sep <+: s.drop k⌝) ∨
          (⌜v = returnVal #()⌝ ∗ «$res0_ptr» ↦ W64 (-1) ∗
            ⌜internal.bytealg.index s sep = -1⌝ ∗ ∃ i' : w64, i_ptr ↦ i'))))
        with [s c0 t «$res0» i]
    · -- `s[i] == c0`
      subst Hif
      iframe
      ileft
      iframe
      ipureintro
      exact ⟨HiT, Hb, Hi.2⟩
    · -- `s[i] != c0`: `IndexByte(s[i+1:t], c0)`
      have Hhead : ¬ sep <+: s.drop i := by
        rw [Hsep]; exact internal.bytealg.not_prefix_drop_of_head s _ c0 i (by rw [Hb]; simpa)
      rw [ite_eq_left (by word)]
      rw [show sint.nat (W64 ((s.length - sep.length + 1 : Nat) : Int)) -
          sint.nat (W64 (i : Int) + W64 1) = s.length - sep.length + 1 - (i + 1) by word,
        show sint.nat (W64 (i : Int) + W64 1) = i + 1 by word]
      try wp_auto
      wp_apply wp_IndexByte as %-
      rcases internal.bytealg.indexByte_slice_cases s c0 (i + 1)
          (s.length - sep.length + 1 - (i + 1)) with ⟨r, Hr, Hrb, Hrc, Hrmin⟩ | ⟨Hr, Hnone⟩
      · rw [Hr]
        try wp_auto
        wp_if_destruct
        · exfalso; revert Hif; word
        try wp_auto
        rw [show W64 (i : Int) + (W64 (r : Int) + W64 1) = W64 ((i + 1 + r : Nat) : Int) by word]
        iframe
        ileft
        iframe
        ipureintro
        refine ⟨by omega, Hrc, fun k hk => ?_⟩
        rcases Nat.lt_trichotomy k i with hki | rfl | hki
        · exact Hi.2 k hki
        · exact Hhead
        · rw [Hsep]
          exact internal.bytealg.not_prefix_drop_of_head s _ c0 k (by
            have := Hrmin (k - (i + 1)) (by omega)
            rwa [show i + 1 + (k - (i + 1)) = k by omega] at this)
      · rw [Hr]
        try wp_auto
        iframe
        iright
        isplitl []
        · ipureintro; rfl
        iframe
        ipureintro
        · refine internal.bytealg.index_eq_neg s sep (fun k => ?_)
          rcases Nat.lt_trichotomy k i with hki | rfl | hki
          · exact Hi.2 k hki
          · exact Hhead
          · rcases Nat.lt_or_ge k (s.length - sep.length + 1) with hkT | hkT
            · rw [Hsep]
              exact internal.bytealg.not_prefix_drop_of_head s _ c0 k (by
                have := Hnone (k - (i + 1)) (by omega)
                rwa [show i + 1 + (k - (i + 1)) = k by omega] at this)
            · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega)
    iintro ⟨s, c0, t, (⟨%Hv, «$res0», %j, i, %Hj⟩ | ⟨%Hv, «$res0», %Hidx, %iw, i⟩)⟩
    · subst Hv
      try wp_auto
      obtain ⟨HjT, Hjc, Hjmin⟩ := Hj
      have Hj1 : j + 1 < s.length := by omega
      obtain ⟨b1, Hb1⟩ : ∃ b1, s[j + 1]? = some b1 := ⟨_, List.getElem?_eq_getElem Hj1⟩
      simp only [show 0 ≤ sint.Z (W64 (j : Int) + W64 1) by word,
        show sint.nat (W64 (j : Int) + W64 1) = j + 1 by word, ↓reduceIte, Hb1]
      try wp_auto
      wp_join (Q := fun v => iprop(⌜v = #(decide (sep <+: s.drop j))⌝ ∗ s_ptr ↦ s ∗
          i_ptr ↦ W64 (j : Int) ∗ n_ptr ↦ W64 (sep.length : Int) ∗ substr_ptr ↦ sep))
          at (if: #(decide _) then _ else #false) with [s i n substr]
      · wp_if_destruct
        · try wp_auto
          rw [ite_eq_left (by word)]
          rw [show sint.nat (W64 (j : Int) + W64 (sep.length : Int)) - sint.nat (W64 (j : Int)) =
              sep.length by word, show sint.nat (W64 (j : Int)) = j by word]
          try wp_auto
          iframe
          ipureintro
          rw [decide_eq_decide.2 (show List.take sep.length (List.drop j s) = sep ↔
            sep <+: List.drop j s by rw [List.prefix_iff_eq_take]; exact eq_comm)]
        · iframe
          ipureintro
          rw [decide_eq_false (internal.bytealg.not_prefix_drop_of_getElem s sep c1 1 j Hs1
            (by rw [Hb1]; intro h; exact ‹¬b1 = c1› (Option.some.inj h)))]
      iintro ⟨%Hv, s, i, n, substr⟩
      subst Hv
      try wp_auto
      wp_if_destruct
      · -- found at `j`
        try wp_auto
        wp_for_post
        rw [internal.bytealg.index_eq_of s sep j Hif Hjmin]
        iapply HΦ
        ipureintro; exact fun _ => Hsl
      · have Hnf := Hif
        try wp_auto
        rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word]
        wp_join (Q := fun v => iprop(∃ bb : Bool,
            ⌜v = #bb ∧ (bb = true → j + 1 < s.length - sep.length + 1)⌝ ∗
            i_ptr ↦ W64 ((j + 1 : Nat) : Int) ∗
            t_ptr ↦ W64 ((s.length - sep.length + 1 : Nat) : Int)))
            at (if: #(decide _) then _ else #false) with [i t]
        · wp_if_destruct
          · try wp_auto
            iexists _
            iframe
            ipureintro
            refine ⟨rfl, fun h => ?_⟩
            simp only [decide_eq_true_eq] at h
            revert h; word
          · iexists false
            iframe
            ipureintro
            exact ⟨rfl, fun h => absurd h Bool.false_ne_true⟩
        iintro ⟨%bb, ⟨%Hv, %Hbb⟩, i, t⟩
        subst Hv
        try wp_auto
        have Hnomatch : ∀ k < j + 1, ¬ sep <+: s.drop k := fun k hk => by
          rcases Nat.lt_or_ge k j with h | h
          · exact Hjmin k h
          · rw [show k = j by omega]; exact Hnf
        rcases bb
        · -- continue
          try wp_auto
          wp_for_post
          iframe
          iexists j + 1, _
          iframe
          ipureintro
          exact ⟨by omega, Hnomatch⟩
        · -- `IndexRabinKarp(s[i:], substr)`
          have HjT' := Hbb rfl
          try wp_auto
          wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
          try wp_auto
          rw [ite_eq_left (by word)]
          rw [show sint.nat (W64 (s.length : Int)) - sint.nat (W64 ((j + 1 : Nat) : Int)) =
              s.length - (j + 1) by word,
            show sint.nat (W64 ((j + 1 : Nat) : Int)) = j + 1 by word,
            List.take_of_length_le (by simp)]
          try wp_auto
          wp_apply wp_IndexRabinKarp
          · ipureintro; simp only [List.length_drop]; omega
          have Hdrop := internal.bytealg.index_drop s sep (j + 1) Hnomatch
          have Hrb := internal.bytealg.index_bounds (s.drop (j + 1)) sep
          generalize internal.bytealg.index (s.drop (j + 1)) sep = r at Hrb Hdrop ⊢
          have Hr63 : -1 ≤ r ∧ r < 2 ^ 63 := by
            simp only [List.length_drop] at Hrb
            rcases Int.lt_or_le r 0 with h | h
            · omega
            · have := Hrb.2 h; omega
          try wp_auto
          wp_if_destruct
          · try wp_auto
            wp_for_post
            rw [Hdrop, ite_eq_right (by revert Hif; word)]
            iapply HΦ
            ipureintro; exact fun _ => Hsl
          · try wp_auto
            wp_for_post
            rw [Hdrop, ite_eq_left (by revert Hif; word)]
            rw [show W64 ((j + 1 : Nat) : Int) + W64 r = W64 (r + ((j + 1 : Nat) : Int)) by word]
            iapply HΦ
            ipureintro; exact fun _ => Hsl
    · subst Hv
      try wp_auto
      wp_for_post
      rw [Hidx]
      iapply HΦ
      ipureintro; exact fun _ => Hsl
  · -- `i >= t`
    have HiT : s.length - sep.length + 1 ≤ i := by have := Hi.1; revert Hif; word
    rw [internal.bytealg.index_eq_neg s sep (fun k => by
      rcases Nat.lt_or_ge k i with h | h
      · exact Hi.2 k h
      · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega))]
    iapply HΦ
    ipureintro; exact fun _ => Hsl

end proof

end Perennial
