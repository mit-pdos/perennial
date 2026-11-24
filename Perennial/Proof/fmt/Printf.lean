/-
The proof of `fmt.Printf` (the Go model of `goose/model/overlay/fmt`): `Fprintf` to the model's
`os.Stdout`, `stdout{}`, whose `Write` returns whatever it returns, needing nothing.
-/
module

public import Perennial.Spec.fmt.Printf
public import Perennial.Spec.fmt.Fprintf
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64

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

/-- The `Write` of the model's `os.Stdout`, `stdout{}`, needs nothing and gives nothing back but
the bytes. -/
theorem fmt.stdout_writeSpec
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (x : fmt.stdout) :
    isPkgInit (PROP := IProp GF) pkg_id.fmt ⊢
      fmt.writeSpec ⟨fmt.stdout.ty, #x⟩ iprop(True) (fun _ _ _ => iprop(True)) := by
  iintro #Hpkg
  iunfold fmt.writeSpec
  iintro %sl %bs %Φ - Hsl HΦ
  ihave #Hfs : isPkgInit (PROP := IProp GF) pkg_id.io.fs $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hfsi := io.fs.isInit_access $$ Hfs
  icases Hfsi with ⟨-, -, -, -, HEC, -⟩
  iunfold errors.newVar at HEC
  icases HEC with ⟨%xEC, #HEC, -⟩
  ihave #Hpolli := internal.poll.isInit_access $$ Hpoll
  icases Hpolli with ⟨-, ⟨%eDE, #HDE⟩, HNP⟩
  iunfold errors.newVar at HNP
  icases HNP with ⟨%xNP, #HNP, -⟩
  ihave #Hioi := io.isInit_access $$ Hio
  icases Hioi with ⟨-, -, -, -, -, HUE, -⟩
  iunfold errors.newVar at HUE
  icases HUE with ⟨%xUE, #HUE, -⟩
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Choose as %c -
  wp_if_destruct
  all_goals try (iapply HΦ $$ Hsl; itrivial)
  wp_apply wp_ChooseUint64 as %m -
  have Hl0 : ¬ uint.Z (sl.len + W64 1) = 0 := by
    word
  rw [if_neg Hl0]
  try wp_auto
  wp_apply wp_ChooseUint64 as %sw -
  -- the switch on the error, then (on `EPIPE`) the choice to loop for ever (`for {}`, under the
  -- whole context as its invariant), then the `*fs.PathError`
  repeat' (first
    | wp_if_destruct
    | wp_auto
    | wp_apply wp_ChooseUint64 as %e -
    | wp_apply wp_Choose as %c2 -
    | wp_alloc_anon
    | wp_for
    | wp_for_post
    | (iapply HΦ $$ Hsl; itrivial)
    | (iframe; done))

end proof

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : fmt.Assumptions]

theorem fmt.Printf.wp_proof
    (wp_Fprintf : fmt.Fprintf.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG)) :
    fmt.Printf.spec (GF := GF) (hG := hG) := by
  intro format args_sl xs dq
  wp_start as ⟨Hsl, Hok⟩
  wp_auto
  wp_apply (wp_Fprintf _ format args_sl xs dq iprop(True) (fun _ _ _ => iprop(True)))
    $$ [$Hsl $Hok] as %n %err ⟨Hsl, -⟩
  · isplitr
    · itrivial
    iexists _
    isplitr
    · ipureintro; rfl
    iapply (fmt.stdout_writeSpec wp_Choose wp_ChooseUint64) $$ Hpkg
  iapply HΦ
  iframe

end proof

end Perennial
