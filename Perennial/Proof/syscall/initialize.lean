/-
The proof of `syscall.initialize'`: it initializes `sync`, allocates the variables, and runs the
trusted models of `runtime_envs` (an arbitrary `[]string`) and of `init.0` (a no-op).
-/
module

public import Perennial.Spec.syscall.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.sync.OnceFunc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

open syscall in
theorem syscall.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_OnceFunc : sync.OnceFunc.spec (GF := GF) (hG := hG)) :
    syscall.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc as H1
  wp_apply wp_GlobalAlloc as H2
  wp_apply wp_GlobalAlloc as H3
  wp_apply wp_GlobalAlloc as H4
  wp_apply wp_GlobalAlloc as H5
  wp_apply wp_GlobalAlloc as H6
  wp_apply wp_GlobalAlloc as H7
  wp_apply wp_GlobalAlloc as H8
  wp_apply wp_GlobalAlloc as H9
  wp_apply wp_GlobalAlloc as H10
  wp_apply wp_GlobalAlloc as H11
  wp_apply wp_GlobalAlloc as H12
  wp_apply wp_GlobalAlloc as H13
  wp_apply wp_GlobalAlloc as H14
  wp_apply wp_GlobalAlloc as H15
  wp_apply wp_GlobalAlloc as H16
  wp_apply wp_GlobalAlloc as H17
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_func_call
  unfold runtime_envs.impl
  wp_apply syscall.wp_arbitraryStrings as %envsl ⟨%xs, Henvs, Henvscap⟩
  set_option maxRecDepth 20000 in
  wp_apply wp_OnceFunc as %cpe -
  unfold EAGAIN EINVAL ENOENT
  repeat (first
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_map_make1 (K := Loc) (V := GoSlice) as %mref Hm
  -- `init.0`: the trusted no-op model
  wp_func_call
  wp_call
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
