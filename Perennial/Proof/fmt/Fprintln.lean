/-
The proof of `fmt.Fprintln` (Go's: a printer from `newPrinter`, `pp.doPrintln`, the writer's
`writeSpec` lent the buffer, `pp.free`), with the Go model's `pp.doPrintln`
(`goose/model/overlay/fmt`, the body of `pp.doPrint`'s model): the model's `visitArg` under `%v` of
each argument (`Perennial/Proof/fmt/PrintArgs.lean`), each after an arbitrary string into the
buffer, then an arbitrary string. The proof is `fmt.Fprint`'s (`Perennial/Proof/fmt/Fprint.lean`).
-/
module

public import Perennial.Spec.fmt.Fprintln
public import Perennial.Spec.fmt.newPrinter
public import Perennial.Spec.fmt.buffer__writeString
public import Perennial.Spec.fmt.pp__free

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

/-- The model's `p.doPrintln(a)` (as `p.doPrint(a)`'s): calls of each argument what Go's `printArg` calls under `%v`, each
after appending some string to the printer's buffer, then appends some string to it. -/
theorem fmt.wp_pp_doPrintln
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (p : Loc) (bs : GoString) (args_sl : GoSlice) (xs : List GoInterface) (dq : DFrac)
    (R : IProp GF) :
    {{ fmt.isPrinterAny p bs ∗ args_sl ↦*{dq} xs ∗ ([∗list] x ∈ xs, fmt.printArgOk R x) ∗ R }}
      (App (Val (p @!! go.GoType.PointerType fmt.pp.ty @!! go!"doPrintln")) (Val #args_sl))
    {{ RET #(); ∃ s : GoString, fmt.isPrinterAny p (bs ++ s) ∗ args_sl ↦*{dq} xs ∗ R }} := by
  wp_start as ⟨Hp, Hsl, #Hok, HR⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
  icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
  ihave IH : iprop(∃ (n : w64) (xv : GoInterface) (r : GoString),
      "i" ∷ i_ptr ↦ n ∗
      "x" ∷ x_ptr ↦ xv ∗
      "HR" ∷ R ∗
      "Hb" ∷ fmt.bufferOwn (GF := GF) (p.[fmt.pp, go!"buf"]) (bs ++ r) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝) $$ [i x HR Hb]
  · iexists _, _, []
    simp only [List.append_nil]
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
    wp_apply (fmt.wp_writeArbitrary wp_Choose wp_ChooseUint64 wp_writeString _ (bs ++ r)) $$ Hb
      as ⟨%r', Hb⟩
    try wp_auto
    ihave #Hx := (show ([∗list] y ∈ xs, fmt.printArgOk (GF := GF) R y) ⊢ fmt.printArgOk R x from
      BigSepL.bigSepL_lookup (Φ := fun _ y => fmt.printArgOk (GF := GF) R y) Hx) $$ Hok
    wp_apply (fmt.wp_visitArg_print (GF := GF) x R) $$ [HR] as HR
    · iframe #; iframe
    wp_for_post
    iframe
    iexists _, _, (r ++ r')
    simp only [List.append_assoc]
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · try wp_auto
    wp_apply (fmt.wp_writeArbitrary wp_Choose wp_ChooseUint64 wp_writeString _ (bs ++ r)) $$ Hb
      as ⟨%r', Hb⟩
    try wp_auto
    iapply HΦ
    iexists (r ++ r')
    simp only [List.append_assoc]
    iframe
    ipureintro; exact hnn

theorem fmt.Fprintln.wp_proof
    (wp_newPrinter : fmt.newPrinter.spec (GF := GF) (hG := hG))
    (wp_writeString : fmt.buffer.writeString.spec (GF := GF) (hG := hG))
    (wp_free : fmt.pp.free.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    fmt.Fprintln.spec (GF := GF) (hG := hG) := by
  intro w args_sl xs dq P R Q
  wp_start as ⟨Hsl, #Hok, HR, HP, %ii, %Hw, HW⟩
  subst Hw
  wp_auto
  wp_apply wp_newPrinter as %p Hp
  wp_apply (fmt.wp_pp_doPrintln wp_writeString wp_Choose wp_ChooseUint64 p [] args_sl xs dq R) $$ [$Hp $Hsl $Hok $HR]
    as ⟨%s, Hp, Hsl, HR⟩
  try wp_auto
  unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA
  icases Hp with ⟨%hnn, %F, %wid, %prec, %x', Hb, Hrest⟩
  unfold fmt.bufferOwn
  icases Hb with ⟨%sl, Hb, Hbs, Hcap⟩
  wp_auto
  wp_bind (App (Val #(methods ii.ty go!"Write" ii.v)) (Val #sl))
  iunfold fmt.writeSpec at HW
  iapply HW $$ HP Hbs
  inext
  iintro %n %err Hbs HQ
  wp_auto
  wp_apply wp_free p ([] ++ s) $$ [Hb Hbs Hcap Hrest]
  · iframe
    unfold fmt.isPrinterAny fmt.isPrinter fmt.isPrinterA fmt.bufferOwn
    isplitr
    · ipureintro; exact hnn
    iexists F, wid, prec, x'
    iframe
  try wp_auto
  iapply HΦ
  iframe

end proof

end Perennial
