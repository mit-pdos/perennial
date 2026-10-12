/-
Package initialization of `io`: it gives the global `EOF` (a fixed error), which callers compare
errors with (`err == io.EOF`).
-/
module

public import Perennial.Proof.sync_proof.base
public import Perennial.Proof.errors
public import Perennial.Code.io
public import Perennial.GeneratedProof.io

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace io

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : io.Assumptions]

/-- The package-initialized state: the global `EOF` holds a fixed error (Go never writes it
after initialization). -/
abbrev isInit : IProp GF :=
  iprop(∃ (e : GoInterfaceOk), globalAddr EOF ↦□ interface.ok e ∗
    ⌜∃ (t : go.GoType) (p : Loc), e = ⟨go.GoType.PointerType t, #p⟩⌝)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io :=
  build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.io get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.io }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoInterface) EOF go.error as HEOF
    | wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := sync.Pool) blackHolePool sync.Pool.ty as _
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoInterface) EOF go.error as HEOF
    | wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply wp_GlobalAlloc (V := GoInterface) Discard Writer.ty as _
  repeat (first
    | wp_apply wp_GlobalAlloc (V := GoInterface) EOF go.error as HEOF
    | wp_apply wp_GlobalAlloc (V := GoInterface) _ go.error as _)
  wp_apply sync.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Herrors⟩
  repeat (wp_apply errors.wp_New_ptr as %_ ⟨%_, _⟩)
  rw [recv_eq_func_mk BAnon BAnon]
  wp_auto
  ipersist HEOF
  wp_apply errors.wp_New as %_ _
  iframe Hown
  is_pkg_init_finish
  imodintro
  iexists _
  iframe HEOF
  ipureintro
  assumption

end wps

end io

end Perennial
end
