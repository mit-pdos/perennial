/-
A `*bytes.Buffer` read as a stream keeps the reader contract (`io.readerOk`), from the spec of
its `Read` (`bytes.Buffer.Read.spec`).
-/
module

public import Perennial.Spec.bytes.Buffer__Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace bytes

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem take_drop_prefix (r bs : List w8) (k : Nat) (h : r <+: bs) :
    r ++ (bs.drop r.length).take k <+: bs := by
  obtain ⟨t, rfl⟩ := h
  simp only [List.drop_left]
  exact List.prefix_append_right_inj r |>.mpr (List.take_prefix k t)

theorem drop_drop_take (r bs : List w8) (k : Nat) (h : r <+: bs) :
    (bs.drop r.length).drop k = bs.drop (r ++ (bs.drop r.length).take k).length := by
  obtain ⟨t, rfl⟩ := h
  simp only [List.drop_left, List.length_append, List.length_take]
  rw [List.drop_append, Nat.add_sub_cancel_left,
    List.drop_eq_nil_of_le (show r.length ≤ r.length + min k t.length by omega), List.nil_append]
  rcases Nat.le_total k t.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_length, List.drop_eq_nil_of_le h]

/-- **A `*Buffer` `l` holding `bs` keeps the reader contract** when read as a stream of `bs`
(`bufferReadState`, `bufferReadErr`), with any condition on its calls. -/
theorem buffer_readerOk (wp_Read : bytes.Buffer.Read.spec (GF := GF) (hG := hG)) (l : Loc)
    (bs : List w8) (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr io.EOF ↦□ eof ⊢
      io.readerOk ⟨go.GoType.PointerType Buffer.ty, #l⟩ (fun _ _ => True)
        (bufferReadState l bs) (bufferReadErr bs eof) := by
  iintro ⟨#Hinit, #Heof⟩
  ihave HEOF := io.eof_of_init $$ Hinit
  iunfold errors.newVar at HEOF
  icases HEOF with ⟨%xeof, #HEOF, -⟩
  ihave %Heq := typedPointsto_agree_wand _ _ _ _ _ $$ Heof HEOF
  subst Heq
  unfold io.readerOk
  imodintro
  iintro %r %p %xs %Φ
  imodintro
  iintro ⟨-, HS, Hp⟩ HΦ
  unfold bufferReadState
  icases HS with ⟨%Hpre, Hown⟩
  iapply wp_Read l (bs.drop r.length) p xs
    (interface.mkOk (go.GoType.PointerType errors.errorString.ty) #xeof) $$ [Hown Hp]
  · isplitl []
    · iexact Heof
    · iframe
  iintro %n %err !> ⟨%H, Hp, Hown⟩
  iapply HΦ
  iexists ((bs.drop r.length).take xs.length)
  iframe Hp
  isplitr
  · ipureintro; exact ⟨H.1, by simp; omega⟩
  isplitl [Hown]
  · iframe
    rw [drop_drop_take r bs xs.length Hpre]
    iframe Hown
    ipureintro; exact take_drop_prefix r bs xs.length Hpre
  rcases H.2 with h | ⟨rfl, hnil, hxs⟩
  · isplitl
    · unfold io.errAt; ileft; ipureintro; exact h
    · ipureintro; rw [h]; exact io.ptrTyped_nil
  · isplitl
    · unfold io.errAt; iright; imodintro
      unfold bufferReadErr
      ipureintro
      refine ⟨?_, rfl⟩
      obtain ⟨t, rfl⟩ := Hpre
      simp only [List.drop_left] at hnil
      subst hnil
      simp
    · ipureintro
      intro ii T h1 h2
      simp only [interface.mkOk, GoInterface.ok.injEq] at h1
      subst h1
      exact ⟨xeof, rfl⟩

end proof

end bytes

end Perennial
