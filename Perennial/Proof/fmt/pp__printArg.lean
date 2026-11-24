/-
The proof of `fmt.(*pp).printArg`.
-/
module

public import Perennial.Spec.fmt.pp__printArg
public import Perennial.Spec.fmt.pp__fmtBool
public import Perennial.Spec.fmt.pp__fmtInteger
public import Perennial.Spec.fmt.pp__fmtString
public import Perennial.Spec.fmt.pp__fmtBytes
public import Perennial.Spec.fmt.pp__handleMethods
public import Perennial.Spec.fmt.fmt__padString

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! Integer conversions of `printArg`'s type switch (`uint64(f)`). -/

theorem fmt.sint_Z_W64_sint_Z_w8 (n : w8) : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
theorem fmt.sint_Z_W64_sint_Z_w16 (n : w16) : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
theorem fmt.sint_Z_W64_sint_Z_w32 (n : w32) : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
theorem fmt.uint_Z_W64_uint_Z_w8 (n : w8) : uint.Z (W64 (uint.Z n)) = uint.Z n := by word
theorem fmt.uint_Z_W64_uint_Z_w16 (n : w16) : uint.Z (W64 (uint.Z n)) = uint.Z n := by word
theorem fmt.uint_Z_W64_uint_Z_w32 (n : w32) : uint.Z (W64 (uint.Z n)) = uint.Z n := by word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

set_option maxHeartbeats 4000000 in
/-- `printArg`'s spec, given what the semantics lacks for `complex64` and `complex128`: their
underlying types and zero values, without which `arg.(complex64)` (`TypeAssert2 go.complex64`,
`type_assert2_interface_step`) does not step, so the type switch is stuck for every argument
whose case comes after `float64`'s (integers, strings, `[]byte`, methods). Only the failing
assertion is used (the zero value `z64`/`z128` is discarded), so any such rules discharge the
premises. -/
theorem fmt.pp.printArg.wp_proof_of_complex
    [go.IsUnderlying go.complex64 go.complex64] [go.IsUnderlying go.complex128 go.complex128]
    {z64 z128 : val} [go.IsGoStepPureDet (GoZeroVal go.complex64) #() (Val z64)]
    [go.IsGoStepPureDet (GoZeroVal go.complex128) #() (Val z128)]
    (hz64 : z64.isPanic = false) (hz128 : z128.isPanic = false)
    (wp_fmtBool : fmt.pp.fmtBool.spec (GF := GF) (hG := hG))
    (wp_fmtInteger : fmt.pp.fmtInteger.spec (GF := GF) (hG := hG))
    (wp_fmtString : fmt.pp.fmtString.spec (GF := GF) (hG := hG))
    (wp_fmtBytes : fmt.pp.fmtBytes.spec (GF := GF) (hG := hG))
    (wp_handleMethods : fmt.pp.handleMethods.spec (GF := GF) (hG := hG))
    (wp_padString : fmt.fmt.padString.spec (GF := GF) (hG := hG)) :
    fmt.pp.printArg.spec (GF := GF) (hG := hG) :=
    fun p arg a bs zw verb hok => by
  cases a with
  | nil =>
    cases zw with
    | some _ => exact hok.elim
    | none =>
    simp only [DirOk] at hok
    subst hok
    wp_start as ⟨Hp, Ha⟩
    iunfold isArg at Ha
    icases Ha with %Ha
    subst Ha
    iunfold isPrinter at Hp
    icases Hp with ⟨%x0, Hp⟩
    iunfold isPrinterA at Hp
    icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, ⟨%v0, Hval⟩, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
    wp_auto
    rw [show (nilAngleString : val) = #nilAngle from rfl]
    wp_apply (wp_padString _ _ (dirFlags none) (dirWid none) (W64 0) _ nilAngle (Or.inr rfl)) $$ [$Hfmt $Hbuf] as ⟨Hfmt, Hbuf⟩
    iapply HΦ
    iexists nilAngle
    isplitr
    · ipureintro; exact DirOut.nil_v
    unfold isPrinterA
    iframe
    simp only [isArg]
    itrivial
  | bool b =>
    cases zw with
    | some _ => exact hok.elim
    | none =>
    simp only [DirOk] at hok
    subst hok
    wp_start as ⟨Hp, Ha⟩
    iunfold isArg at Ha
    icases Ha with %Ha
    subst Ha
    iunfold isPrinter at Hp
    icases Hp with ⟨%x0, Hp⟩
    iunfold isPrinterA at Hp
    icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, ⟨%v0, Hval⟩, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
    wp_auto
    wp_apply (wp_fmtBool p _ bs (dirWid none) (W64 0) b) $$
      [Hbuf Hfmt Hib Harg Hval Hreo Hgood Hpan Herr Hwrap Hwe] as Hp
    · unfold isPrinterA; iframe
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact DirOut.bool_v b
    iframe
    simp only [isArg]
    itrivial
  | int z =>
    obtain ⟨hverb, hzw⟩ := hok
    have hfi := fun v s => wp_fmtInteger p arg bs zw v s verb hverb hzw
    rcases hverb with rfl | rfl | rfl <;>
    · first
        | rw [show (W32 (uint.nat verb_d : Int) : w32) = W32 100 from rfl] at hfi ⊢
        | rw [show (W32 (uint.nat verb_v : Int) : w32) = W32 118 from rfl] at hfi ⊢
        | rw [show (W32 (uint.nat verb_x : Int) : w32) = W32 120 from rfl] at hfi ⊢
      wp_start as ⟨Hp, Ha⟩
      iunfold isArg at Ha
      icases Ha with %Ha
      iunfold isPrinter at Hp
      icases Hp with ⟨%x0, Hp⟩
      iunfold isPrinterA at Hp
      icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, ⟨%v0, Hval⟩, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
      cases Ha <;>
      · wp_auto
        simp only [signed, unsigned]
        wp_apply (hfi _ _) $$ [Hbuf Hfmt Hib Harg Hval Hreo Hgood Hpan Herr Hwrap Hwe] as Hp
        · unfold isPrinterA; iframe
        iapply HΦ
        iexists _
        iframe Hp
        isplitl
        · ipureintro
          simp only [intOut, fmt.sint_Z_W64_sint_Z_w8, fmt.sint_Z_W64_sint_Z_w16,
            fmt.sint_Z_W64_sint_Z_w32, fmt.uint_Z_W64_uint_Z_w8, fmt.uint_Z_W64_uint_Z_w16,
            fmt.uint_Z_W64_uint_Z_w32]
          first
            | exact DirOut.int_d _ _
            | exact DirOut.int_v _ _
            | exact DirOut.int_x _ _
        simp only [isArg]
        ipureintro
        constructor
  | str t =>
    cases zw with
    | some _ => exact hok.elim
    | none =>
    simp only [DirOk] at hok
    have hverb : verb = verb_s ∨ verb = verb_v ∨ verb = verb_x := by
      rcases hok with h | h | ⟨h, _⟩ <;> simp [h]
    have hlen : verb = verb_x → t.length < 2 ^ 62 := by
      rintro rfl
      rcases hok with h | h | ⟨_, hl⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact hl
    have hfs := wp_fmtString p arg bs (dirWid none) (W64 0) t verb hverb hlen
    rcases hverb with rfl | rfl | rfl <;>
    · first
        | rw [show (W32 (uint.nat verb_s : Int) : w32) = W32 115 from rfl] at hfs ⊢
        | rw [show (W32 (uint.nat verb_v : Int) : w32) = W32 118 from rfl] at hfs ⊢
        | rw [show (W32 (uint.nat verb_x : Int) : w32) = W32 120 from rfl] at hfs ⊢
      rw [show dirFlags none = noFlags from rfl]
      wp_start as ⟨Hp, Ha⟩
      iunfold isArg at Ha
      icases Ha with %Ha
      subst Ha
      iunfold isPrinter at Hp
      icases Hp with ⟨%x0, Hp⟩
      iunfold isPrinterA at Hp
      icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, ⟨%v0, Hval⟩, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
      wp_auto
      wp_apply hfs $$ [Hbuf Hfmt Hib Harg Hval Hreo Hgood Hpan Herr Hwrap Hwe] as Hp
      · unfold isPrinterA; iframe
      iapply HΦ
      iexists _
      iframe Hp
      isplitl
      · ipureintro
        first
          | exact DirOut.str_s _
          | exact DirOut.str_v _
          | exact DirOut.str_x _
      simp only [isArg]
      itrivial
  | bytes ys dq =>
    cases zw with
    | some _ => exact hok.elim
    | none =>
    simp only [DirOk] at hok
    have hverb : verb = verb_s ∨ verb = verb_v ∨ verb = verb_d ∨ verb = verb_x := by
      rcases hok with h | h | h | ⟨h, _⟩ <;> simp [h]
    have hlen : verb = verb_x → ys.length < 2 ^ 62 := by
      rintro rfl
      rcases hok with h | h | h | ⟨_, hl⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact hl
    have hfb := fun sl => wp_fmtBytes p arg bs (dirWid none) (W64 0) sl ys dq verb go!"[]byte" hverb hlen
    rcases hverb with rfl | rfl | rfl | rfl <;>
    · first
        | rw [show (W32 (uint.nat verb_s : Int) : w32) = W32 115 from rfl] at hfb ⊢
        | rw [show (W32 (uint.nat verb_v : Int) : w32) = W32 118 from rfl] at hfb ⊢
        | rw [show (W32 (uint.nat verb_d : Int) : w32) = W32 100 from rfl] at hfb ⊢
        | rw [show (W32 (uint.nat verb_x : Int) : w32) = W32 120 from rfl] at hfb ⊢
      rw [show dirFlags none = noFlags from rfl]
      wp_start as ⟨Hp, Ha⟩
      iunfold isArg at Ha
      icases Ha with ⟨%sl, %Ha, Hsl⟩
      subst Ha
      iunfold isPrinter at Hp
      icases Hp with ⟨%x0, Hp⟩
      iunfold isPrinterA at Hp
      icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, ⟨%v0, Hval⟩, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
      wp_auto
      wp_apply (hfb sl) $$ [Hbuf Hfmt Hib Harg Hval Hreo Hgood Hpan Herr Hwrap Hwe $Hsl] as ⟨Hp, Hsl⟩
      · unfold isPrinterA; iframe
      iapply HΦ
      iexists _
      iframe Hp
      isplitr
      · ipureintro
        first
          | exact DirOut.bytes_s _ _
          | exact DirOut.bytes_v _ _
          | exact DirOut.bytes_d _ _
          | exact DirOut.bytes_x _ _
      simp only [isArg]
      iexists sl
      iframe
      itrivial
  | method P =>
    cases zw with
    | some _ => exact hok.elim
    | none =>
    simp only [DirOk] at hok
    have hverb : verb = verb_s ∨ verb = verb_v ∨ verb = verb_x := by
      rcases hok with h | h | ⟨h, _⟩ <;> simp [h]
    have hlen : verb = verb_x → ∀ s, P s → s.length < 2 ^ 62 := by
      rintro rfl
      rcases hok with h | h | ⟨_, hl⟩
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact hl
    have hhm := fun ii m hx hm =>
      wp_handleMethods p arg ii m P bs (dirWid none) (W64 0) verb hx hm hverb hlen
    rcases hverb with rfl | rfl | rfl <;>
    · first
        | rw [show (W32 (uint.nat verb_s : Int) : w32) = W32 115 from rfl] at hhm ⊢
        | rw [show (W32 (uint.nat verb_v : Int) : w32) = W32 118 from rfl] at hhm ⊢
        | rw [show (W32 (uint.nat verb_x : Int) : w32) = W32 120 from rfl] at hhm ⊢
      rw [show dirFlags none = noFlags from rfl]
      wp_start as ⟨Hp, Ha⟩
      iunfold isArg at Ha
      icases Ha with ⟨%ii, %m, ⟨%hx, %hm⟩, #Hm⟩
      subst hx
      have hsw := hm.1
      simp only [SwitchType, not_or] at hsw
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ := hsw
      iunfold isPrinter at Hp
      icases Hp with ⟨%x0, Hp⟩
      iunfold isPrinterA at Hp
      icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, ⟨%v0, Hval⟩, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
      repeat' (first | wp_auto | simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
        h15, h16, h17, h18, h19, ↓reduceIte, decide_false])
      wp_apply (hhm ii m rfl hm) $$ [Hbuf Hfmt Hib Harg Hval Hreo Hgood Hpan Herr Hwrap Hwe] as ⟨%s, %Hs, Hp⟩
      · unfold isPrinterA; iframe; iexact Hm
      iapply HΦ
      iexists _
      iframe Hp
      isplitr
      · ipureintro
        first
          | exact DirOut.method_s _ _ Hs
          | exact DirOut.method_v _ _ Hs
          | exact DirOut.method_x _ _ Hs
      simp only [isArg]
      iexists ii, m
      isplitr
      · ipureintro; exact ⟨rfl, hm⟩
      iexact Hm

end proof

end Perennial
