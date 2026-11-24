/-
The proof of `fmt.Fprint`, from the model's `visitArg` under `%v` (`Perennial/Proof/fmt/PrintArgs.lean`)
and the writer's `writeSpec`.
-/
module

public import Perennial.Spec.fmt.Fprint

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.Fprint.wp_proof :
    fmt.Fprint.spec (GF := GF) (hG := hG) := by
  intro w args_sl xs dq P R Q
  wp_start as ⟨Hsl, #Hok, HR, HP, %ii, %Hw, HW⟩
  subst Hw
  try wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  ihave IH : iprop(∃ (n : w64) (xv : GoInterface),
      "i" ∷ i_ptr ↦ n ∗
      "x" ∷ x_ptr ↦ xv ∗
      "HR" ∷ R ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝) $$ [i x HR]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z args_sl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index args_sl (sint.Z n) xs dq x Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact Hx
    try wp_auto
    ihave #Hx := (show ([∗list] y ∈ xs, fmt.printArgOk (GF := GF) R y) ⊢ fmt.printArgOk R x from
      BigSepL.bigSepL_lookup (Φ := fun _ y => fmt.printArgOk (GF := GF) R y) Hx) $$ Hok
    wp_bind (App (App (App (App (Val fmt.visitArg) (Val #x)) (Val #(W8 118))) (Val #false)) (Val #false))
    iapply (fmt.wp_visitArg_print (GF := GF) x R) $$ [HR]
    · iframe #; iframe
    inext
    iintro HR
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · try wp_auto
    wp_apply fmt.wp_arbitraryString as %s -
    wp_apply (fmt.wp_printerBuf s) as %bsl ⟨Hb, %spare, Hspare⟩
    try wp_auto
    wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #bsl))
    iunfold fmt.writeSpec at HW
    iapply HW $$ HP Hb
    inext
    iintro %n %err Hb HQ
    try wp_auto
    wp_apply (fmt.wp_retire bsl s spare) $$ [$Hb $Hspare]
    try wp_auto
    iapply HΦ
    iframe

end proof

end Perennial
