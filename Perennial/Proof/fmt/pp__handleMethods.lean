/-
The proof of `fmt.(*pp).handleMethods`.
-/
module

public import Perennial.Spec.fmt.pp__handleMethods
public import Perennial.Spec.fmt.pp__fmtString
public import Perennial.Spec.fmt.pp__catchPanic'deferred

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

theorem fmt.pp.handleMethods.wp_proof
    (wp_fmtString : fmt.pp.fmtString.spec (GF := GF) (hG := hG))
    (wp_catchPanic : fmt.pp.catchPanic'deferred.spec (GF := GF) (hG := hG)) :
    fmt.pp.handleMethods.spec (GF := GF) (hG := hG) :=
    fun p x ii m P bs wid prec verb hx hm hverb hlen => by
  subst hx
  obtain ⟨hsw, hF, hm⟩ := hm
  wp_start as ⟨Hp, #Hm⟩
  iunfold isPrinterA at Hp
  icases Hp with ⟨Hbuf, Hfmt, Hib, Harg, Hval, Hreo, Hgood, Hpan, Herr, Hwrap, Hwe⟩
  iunfold fmtOwn at Hfmt
  icases Hfmt with ⟨Hfbuf, Hflags, Hwid, Hprec⟩
  have hfs := fun s (hs : verb = verb_x → s.length < 2 ^ 62) =>
    wp_fmtString p (GoInterface.ok ii) bs wid prec s verb hverb hs
  iunfold methodSpec at Hm
  rcases hverb with rfl | rfl | rfl <;>
  rcases hm with ⟨rfl, hE⟩ | ⟨rfl, hE, hS⟩ <;>
  · first
      | rw [show (W32 (uint.nat verb_s : Int) : w32) = W32 115 from rfl] at hfs ⊢
      | rw [show (W32 (uint.nat verb_v : Int) : w32) = W32 118 from rfl] at hfs ⊢
      | rw [show (W32 (uint.nat verb_x : Int) : w32) = W32 120 from rfl] at hfs ⊢
    wp_auto
    wp_apply wp_with_defer_recover as %defer %pnc defer pnc
    simp only [hF, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    simp only [hE, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    try (simp only [hS, ↓reduceIte]; wp_auto)
    wp_bind (App (Val #(methods ii.ty _ ii.v)) (Val #()))
    iapply Hm
    inext
    iintro %s %Hs
    wp_auto
    wp_apply (hfs s (fun hv => hlen hv s Hs)) $$
      [Hbuf Hfbuf Hflags Hwid Hprec Hib Harg Hval Hreo Hgood Hpan Herr Hwrap Hwe] as Hp
    · iunfold isPrinterA; iunfold fmtOwn; iframe
    wp_apply wp_catchPanic $$ [$pnc] as pnc
    iapply HΦ
    iexists s
    iframe
    ipureintro
    exact Hs

end proof

end Perennial
