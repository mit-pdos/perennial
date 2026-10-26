/-
Shared definitions of the proofs of the Go model of string/byte-slice conversions
(`github.com/mit-pdos/perennial/goose/model/strings`, used by
`Perennial/Golang/Theory/String.lean`): the spec of the builtin `len` on strings, which
its functions call.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Pre
public import Perennial.Golang.Defn.String
public import Perennial.Code.github_com.mit_pdos.perennial.goose.model.strings
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.model.strings

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.mit_pdos.perennial.goose.model.strings

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_string_len (str : GoString) {t : go.GoType} [t ↓u go.string] :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.len [t])) (Val #str)) @ s; E
    {{ RET #(W64 str.length); ⌜str.length < 2 ^ 63⌝ }} := by
  wp_start
  by_cases h : str.length < 2 ^ 63
  · rw [ite_eq_left h]
    wp_pures
    iapply HΦ
    ipureintro; exact h
  · rw [ite_eq_right h]
    iapply wp_AngelicExit

end wps

end github_com.mit_pdos.perennial.goose.model.strings

end Perennial
