/-
Port of `src/algebra/auth_prop.v`: an authoritative proposition `P` split into
fragments, built from a `ghost_map` of saved-proposition names.

Representation: the set of saved-prop names is a `gmap GName Unit` (= `gmap GName Unit`),
used directly as the ghost map (Rocq `gsetToGmap () gns`), and Rocq's `[∗ set]`
over it is `[∗map] γp ↦ _ ∈ gns, _`.
-/
import Perennial.Ghost.GhostMap
import Perennial.Ghost.SavedProp

noncomputable section

namespace Perennial
open Iris BI OFE CMRA ProofMode
open Iris.Std (PartialMap LawfulPartialMap)

section auth_prop
variable {GF : BundledGFunctors} [AllG GF]

/-- The saved propositions named by `gns` all hold (later). -/
abbrev apropHolds (gns : GMap GName Unit) : IProp GF :=
  iprop([∗map] γp ↦ _u ∈ gns, ∃ Q, savedPropOwn γp .discard Q ∗ ▷ Q)

def ownApropAuth (γ : GName) (P : IProp GF) (n : Nat) : IProp GF :=
  iprop(∃ gns : GMap GName Unit,
    ghostMapAuth γ 1 gns ∗
    □ ([∗map] γp ↦ _u ∈ gns, ∃ Q, savedPropOwn γp .discard Q) ∗
    □ (apropHolds gns ∗-∗ ▷ P) ∗
    ⌜GMap.size gns = n⌝)

def ownApropFrag (γ : GName) (P : IProp GF) (n : Nat) : IProp GF :=
  iprop(∃ gns : GMap GName Unit,
    ([∗map] γp ↦ _u ∈ gns, γp ↪[γ] ()) ∗
    □ (apropHolds gns ∗-∗ ▷ P) ∗
    ⌜GMap.size gns = n⌝)

/-- Rocq notation `ownAprop γ P`. -/
abbrev ownAprop (γ : GName) (P : IProp GF) : IProp GF := ownApropFrag γ P 1

theorem ownApropAuth_alloc : ⊢ |==> ∃ γ, ownApropAuth (GF := GF) γ iprop(True) 0 := by
  imod ghost_map_alloc_empty (GF := GF) (K := GName) (V := Unit) with ⟨%γ, H⟩
  imodintro
  iexists γ
  unfold ownApropAuth
  iexists ∅
  isplitl [H]
  · iexact H
  isplitr
  · imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  isplitr
  · imodintro
    isplit
    · iintro -
      inext
      itrivial
    · iintro -
      iapply BigSepM.bigSepM_empty.2
      itrivial
  · ipureintro
    exact GMap.map_size_empty

theorem ownApropFrag_0 (γ : GName) : ⊢ ownApropFrag (GF := GF) γ iprop(True) 0 := by
  unfold ownApropFrag
  iexists ∅
  isplitr
  · iapply BigSepM.bigSepM_empty.2
    itrivial
  isplitr
  · imodintro
    isplit
    · iintro -
      inext
      itrivial
    · iintro -
      iapply BigSepM.bigSepM_empty.2
      itrivial
  · ipureintro
    exact GMap.map_size_empty


private theorem discard_own_one_invalid : ¬ ✓ (DFrac.discard • DFrac.own (1 : Qp)) := by
  intro h
  have : ((1 : Qp).val < 1) := h
  simp at this

/-- Transfer a saved proposition along agreement of names. -/
private theorem saved_prop_transfer (γp : GName) (dq1 dq2 : DFrac) (Q Q' : IProp GF) :
    ⊢ savedPropOwn γp dq1 Q -∗ savedPropOwn γp dq2 Q' -∗ ▷ Q' -∗ ▷ Q := by
  iintro H1 H2 HQ'
  ihave Heq := saved_prop_agree γp dq1 dq2 Q Q' $$ H1 H2
  haveI : NonExpansive (fun x : IProp GF => x) := ⟨fun _ _ _ h => h⟩
  inext
  irewrite [Heq]
  iexact HQ'

private theorem insert_eq (gns : GMap GName Unit) (k : GName) :
    gns.insert k () = PartialMap.insert gns k () := rfl

theorem ownApropAuth_add (Q : IProp GF) (γ : GName) (P : IProp GF) (n : Nat) :
    ⊢ ownApropAuth γ P n ==∗ ownApropAuth γ iprop(P ∗ Q) (n + 1) ∗ ownAprop γ Q := by
  unfold ownAprop ownApropAuth ownApropFrag
  iintro ⟨%gns, Hgns, #Hused, #Himp, %Hn⟩
  imod saved_prop_alloc Q (.own 1) DFrac.valid_own_one with ⟨%γp, HQ⟩
  cases hγ : gns.lookup γp with
  | some u =>
    ihave Hb := BigSepM.bigSepM_lookup (Φ := fun γp (_ : Unit) =>
      iprop(∃ Q, savedPropOwn (GF := GF) γp .discard Q)) (m := gns) (i := γp) hγ $$ Hused
    icases Hb with ⟨%Q', Hb⟩
    ihave ⟨%Hbad, -⟩ := saved_prop_valid_2 γp _ _ Q' Q $$ Hb HQ
    exact (discard_own_one_invalid Hbad).elim
  | none =>
    imod ghost_map_insert γp () hγ $$ Hgns with ⟨Hgns, Hel⟩
    imod saved_prop_persist γp _ Q $$ HQ with #HQ
    imodintro
    isplitl [Hgns]
    · iexists gns.insert γp ()
      isplitl [Hgns]
      · iexact Hgns
      isplitr
      · imodintro
        rw [insert_eq, (BigSepM.bigSepM_insert (Φ := fun γp (_ : Unit) =>
          iprop(∃ Q, savedPropOwn (GF := GF) γp .discard Q)) (m := gns) hγ).to_eq]
        isplitr
        · iexists Q; iexact HQ
        · iexact Hused
      isplitr
      · imodintro
        unfold apropHolds
        rw [insert_eq, (BigSepM.bigSepM_insert (Φ := fun γp (_ : Unit) =>
          iprop(∃ Q, savedPropOwn (GF := GF) γp .discard Q ∗ ▷ Q)) (m := gns) hγ).to_eq]
        isplit
        · iintro ⟨⟨%Q', HQ', HQf⟩, Hs⟩
          ihave HP := Himp $$ Hs
          ihave HQ'' := saved_prop_transfer γp _ _ Q Q' $$ HQ HQ' HQf
          inext
          isplitl [HP]
          · iexact HP
          · iexact HQ''
        · iintro HPQ
          icases HPQ with ⟨HP, HQf⟩
          isplitl [HQf]
          · iexists Q
            isplitr
            · iexact HQ
            · iexact HQf
          · iapply Himp $$ HP
      · ipureintro
        rw [GMap.map_size_insert_None gns γp () hγ, Hn]
    · iexists PartialMap.insert (∅ : GMap GName Unit) γp ()
      rw [(BigSepM.bigSepM_insert (Φ := fun γp (_ : Unit) =>
          iprop(γp ↪[γ] () : IProp GF)) (m := (∅ : GMap GName Unit)) rfl).to_eq]
      isplitl [Hel]
      · isplitl [Hel]
        · iexact Hel
        · iapply BigSepM.bigSepM_empty.2; itrivial
      isplitr
      · imodintro
        unfold apropHolds
        rw [(BigSepM.bigSepM_insert (Φ := fun γp (_ : Unit) =>
          iprop(∃ Q, savedPropOwn (GF := GF) γp .discard Q ∗ ▷ Q))
          (m := (∅ : GMap GName Unit)) rfl).to_eq]
        isplit
        · iintro ⟨⟨%Q', HQ', HQf⟩, -⟩
          iapply saved_prop_transfer γp _ _ Q Q' $$ HQ HQ' HQf
        · iintro HQf
          isplitl [HQf]
          · iexists Q
            isplitr
            · iexact HQ
            · iexact HQf
          · iapply BigSepM.bigSepM_empty.2; itrivial
      · ipureintro
        exact (GMap.map_size_insert_None (∅ : GMap GName Unit) γp () rfl).trans
          (by rw [GMap.map_size_empty])

/-- Fragments of total size `n` cover the authoritative set of size `n`. -/
private theorem auth_frag_same (γ : GName) (gns gns0 : GMap GName Unit) :
    ⊢ (ghostMapAuth γ 1 gns : IProp GF) -∗ ([∗map] γp ↦ _u ∈ gns0, γp ↪[γ] ()) -∗
      ⌜gns0 ⊆ gns⌝ := by
  iintro H1 H2
  iapply ghost_map_lookup_big gns0 $$ H1 H2

private theorem own_aprop_auth_of_empty (γ : GName) :
    (ghostMapAuth γ 1 (∅ : GMap GName Unit) : IProp GF) ⊢
      iprop(∃ gns : GMap GName Unit,
        ghostMapAuth γ 1 gns ∗
        □ ([∗map] γp ↦ _u ∈ gns, ∃ Q, savedPropOwn γp .discard Q) ∗
        □ (apropHolds gns ∗-∗ ▷ True) ∗
        ⌜GMap.size gns = 0⌝) := by
  iintro H
  iexists ∅
  isplitl [H]
  · iexact H
  isplitr
  · imodintro
    iapply BigSepM.bigSepM_empty.2
    itrivial
  isplitr
  · imodintro
    isplit
    · iintro -
      inext
      itrivial
    · iintro -
      iapply BigSepM.bigSepM_empty.2
      itrivial
  · ipureintro
    exact GMap.map_size_empty

theorem ownApropAuth_reset (γ : GName) (P P' : IProp GF) (n : Nat) :
    ⊢ ownApropAuth γ P n -∗ ownApropFrag γ P' n ==∗ ownApropAuth γ iprop(True) 0 := by
  unfold ownApropAuth ownApropFrag
  iintro ⟨%gns, Hgns, -, -, %Hn⟩ ⟨%gns0, Hgns', -, %Hn'⟩
  ihave %Hsub := ghost_map_lookup_big (GF := GF) (γ := γ) (q := 1) (m := gns) (dq := DFrac.own 1)
    gns0 $$ Hgns [Hgns']
  · iexact Hgns'
  have heq : gns0 = gns := GMap.set_subseteq_size_eq Hsub (by omega)
  subst heq
  imod ghost_map_delete_big gns0 $$ Hgns Hgns' with H
  rw [GMap.map_difference_diag]
  imodintro
  iapply own_aprop_auth_of_empty γ $$ H

private theorem own_aprop_auth_frag_sub (γ : GName) (P P' : IProp GF) (n n' : Nat) :
    ownApropAuth γ P n ∗ ownApropFrag γ P' n' ⊢
      ∃ gns gns0 : GMap GName Unit, ⌜gns0 ⊆ gns ∧ GMap.size gns = n ∧ GMap.size gns0 = n'⌝ ∗
        □ (apropHolds (GF := GF) gns ∗-∗ ▷ P) ∗ □ (apropHolds (GF := GF) gns0 ∗-∗ ▷ P') := by
  unfold ownApropAuth ownApropFrag
  iintro ⟨⟨%gns, Hgns, -, #Himp, %Hn⟩, ⟨%gns0, Hgns', #Himp', %Hn'⟩⟩
  ihave %Hsub := ghost_map_lookup_big (GF := GF) (γ := γ) (q := 1) (m := gns) (dq := DFrac.own 1)
    gns0 $$ Hgns [Hgns']
  · iexact Hgns'
  iexists gns, gns0
  isplitr
  · ipureintro; exact ⟨Hsub, Hn, Hn'⟩
  isplitr
  · iexact Himp
  · iexact Himp'

instance ownApropAuth_agree (γ : GName) (P P' : IProp GF) (n : Nat) :
    CombineSepGives (ownApropAuth γ P n) (ownApropFrag γ P' n) iprop(▷ P ∗-∗ ▷ P') where
  combine_sep_gives := by
    refine (own_aprop_auth_frag_sub γ P P' n n).trans ?_
    iintro ⟨%gns, %gns0, %⟨Hsub, Hn, Hn'⟩, #Himp, #Himp'⟩
    have heq : gns0 = gns := GMap.set_subseteq_size_eq Hsub (by omega)
    subst heq
    imodintro
    isplit
    · iintro HP
      ihave H := Himp $$ HP
      iapply Himp' $$ H
    · iintro HP
      ihave H := Himp' $$ HP
      iapply Himp $$ H

instance ownApropAuth_agree' (γ : GName) (P P' : IProp GF) (n : Nat) :
    CombineSepGives (ownApropFrag γ P' n) (ownApropAuth γ P n) iprop(▷ P' ∗-∗ ▷ P) where
  combine_sep_gives := by
    iintro ⟨H, H'⟩
    icombine H' H gives #Heq
    imodintro
    isplit
    · iintro HP
      iapply Heq $$ HP
    · iintro HP
      iapply Heq $$ HP

/-- Lower priority, to prefer `ownApropAuth_agree`. -/
instance (priority := default - 10) ownApropAuth_le (γ : GName) (P P' : IProp GF) (n n' : Nat) :
    CombineSepGives (ownApropAuth γ P n) (ownApropFrag γ P' n') iprop(⌜n' ≤ n⌝) where
  combine_sep_gives := by
    refine (own_aprop_auth_frag_sub γ P P' n n').trans ?_
    iintro ⟨%gns, %gns0, %⟨Hsub, Hn, Hn'⟩, -, -⟩
    imodintro
    ipureintro
    have := GMap.subseteq_size Hsub
    omega

instance (priority := default - 10) ownApropAuth_le' (γ : GName) (P P' : IProp GF) (n n' : Nat) :
    CombineSepGives (ownApropFrag γ P' n') (ownApropAuth γ P n) iprop(⌜n' ≤ n⌝) where
  combine_sep_gives := by
    iintro ⟨H, H'⟩
    icombine H' H gives %Hle
    imodintro
    ipureintro
    exact Hle

private theorem own_one_own_one_invalid : ¬ ✓ (DFrac.own (1 : Qp) • DFrac.own (1 : Qp)) := by
  intro h
  have : ((1 : Qp) + 1).val ≤ 1 := h
  simp at this
  grind

private theorem bigSepM_union_gset {PROP : Type _} [BI PROP] (Φ : GName → Unit → PROP)
    (gns gns' : GMap GName Unit) (hd : GMap.Disjoint gns gns') :
    ([∗map] k ↦ y ∈ gns ∪ gns', Φ k y) ⊣⊢ ([∗map] k ↦ y ∈ gns, Φ k y) ∗ [∗map] k ↦ y ∈ gns', Φ k y := by
  have h := BigSepM.bigSepM_union (Φ := Φ) (m₁ := gns) (m₂ := gns')
    (fun k ⟨a, b⟩ => hd k a b)
  rw [gmap_union_eq]
  exact h

instance ownApropFrag_combine (γ : GName) (P P' : IProp GF) (n n' : Nat) :
    CombineSepAs (ownApropFrag γ P n) (ownApropFrag γ P' n')
      (ownApropFrag γ iprop(P ∗ P') (n + n')) where
  combine_sep_as := by
    unfold ownApropFrag
    iintro ⟨⟨%gns, Hg, #Himp, %Hn⟩, ⟨%gns', Hg', #Himp', %Hn'⟩⟩
    by_cases hd : GMap.Disjoint gns gns'
    · iexists gns ∪ gns'
      rw [(bigSepM_union_gset (fun γp (_ : Unit) => iprop(γp ↪[γ] () : IProp GF)) gns gns' hd).to_eq]
      isplitl [Hg Hg']
      · isplitl [Hg]
        · iexact Hg
        · iexact Hg'
      isplitr
      · imodintro
        unfold apropHolds
        rw [(bigSepM_union_gset (fun γp (_ : Unit) =>
          iprop(∃ Q, savedPropOwn (GF := GF) γp .discard Q ∗ ▷ Q)) gns gns' hd).to_eq]
        isplit
        · iintro ⟨H1, H2⟩
          ihave HP := Himp $$ H1
          ihave HP' := Himp' $$ H2
          inext
          isplitl [HP]
          · iexact HP
          · iexact HP'
        · iintro HPP
          icases HPP with ⟨HP, HP'⟩
          isplitl [HP]
          · iapply Himp $$ HP
          · iapply Himp' $$ HP'
      · ipureintro
        rw [GMap.size_union hd, Hn, Hn']
    · have : ∃ k, (gns.lookup k).isSome ∧ (gns'.lookup k).isSome := by
        apply Classical.byContradiction
        intro hne
        exact hd fun k h1 h2 => hne ⟨k, h1, h2⟩
      obtain ⟨k, h1, h2⟩ := this
      have e1 : gns.lookup k = some () := by
        revert h1; cases gns.lookup k <;> simp
      have e2 : gns'.lookup k = some () := by
        revert h2; cases gns'.lookup k <;> simp
      ihave E1 := BigSepM.bigSepM_lookup (Φ := fun γp (_ : Unit) => iprop(γp ↪[γ] () : IProp GF))
        (m := gns) (i := k) e1 $$ Hg
      ihave E2 := BigSepM.bigSepM_lookup (Φ := fun γp (_ : Unit) => iprop(γp ↪[γ] () : IProp GF))
        (m := gns') (i := k) e2 $$ Hg'
      ihave ⟨%Hv, -⟩ := ghostMapElem_valid_2 k γ _ _ () () $$ E1 E2
      exact (own_one_own_one_invalid Hv).elim

end auth_prop
end Perennial
