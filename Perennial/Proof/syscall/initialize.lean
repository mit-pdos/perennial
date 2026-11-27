/-
The proof of `syscall.initialize'`: it initializes `internal/gomodel`, `sync/atomic` and `sync`,
allocates the variables, runs the trusted model of `runtime_envs` (`gomodel.ChooseStrings`, an
arbitrary `[]string`), and `init.0` (translated, over the Go model of `prlimit1`).
-/
module

public import Perennial.Spec.syscall.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.sync.OnceFunc
public import Perennial.Spec.sync.atomic.initialize
public import Perennial.Spec.internal.gomodel.initialize
public import Perennial.Spec.internal.gomodel.ChooseStrings
public import Perennial.Spec.internal.gomodel.Choose
public import Perennial.Spec.internal.gomodel.ChooseUint64
public import Perennial.Spec.sync.atomic.Pointer__Store

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

/-- The Go model of `prlimit1` (`goose/model/overlay/syscall/prlimit.go`), as `init.0` calls
it (through `Getrlimit` and `setrlimit`), with the error variables `errnoErr` reads. -/
theorem syscall.wp_prlimit1_init
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (pid res : w64) (nl old : Loc) (ln : syscall.Rlimit) (ea ei en : GoInterface) :
    {{ (globalAddr syscall.errEAGAIN ↦□ ea : IProp GF) ∗ globalAddr syscall.errEINVAL ↦□ ei ∗
       globalAddr syscall.errENOENT ↦□ en ∗
       (⌜nl = null⌝ ∨ (nl ↦ ln : IProp GF)) ∗ (⌜old = null⌝ ∨ ∃ lo : syscall.Rlimit, (old ↦ lo : IProp GF)) }}
      (App (App (App (App (Val (@! syscall.prlimit1)) (Val #pid)) (Val #res)) (Val #nl))
        (Val #old))
    {{ (err : GoInterface), RET #err;
       ((⌜nl = null⌝ ∨ (nl ↦ ln : IProp GF)) ∗ (⌜old = null⌝ ∨ ∃ lo : syscall.Rlimit, (old ↦ lo : IProp GF)) : IProp GF) }} := by
  wp_start as ⟨#Hea, #Hei, #Hen, Hnl, Hold⟩
  wp_auto
  -- `if newlimit != nil { _ = *newlimit }`
  wp_join iprop((⌜nl = null⌝ ∨ (nl ↦ ln : IProp GF)) ∗ newlimit_ptr ↦ nl) at next
    with [Hnl newlimit] as ⟨Hnl, newlimit⟩
  · icases Hnl with (%h | Hnl)
    · subst h
      wp_auto
      wp_join_done
      all_goals (iframe; ileft; ipureintro; rfl)
    · ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hnl
      simp only [Hnn, _root_.decide_false, Bool.not_false]
      wp_auto
      wp_join_done
      all_goals (iframe; iright; iexact Hnl)
  -- `if old != nil && gomodel.Choose() { old.Cur = ...; old.Max = ... }`
  wp_join iprop((⌜old = null⌝ ∨ ∃ lo : syscall.Rlimit, (old ↦ lo : IProp GF)) ∗
      old_ptr ↦ old) at next with [Hold old] as ⟨Hold, old⟩
  · icases Hold with (%h | ⟨%lo, Hold⟩)
    · subst h
      wp_auto
      wp_join_done
      all_goals (iframe; ileft; ipureintro; rfl)
    · ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hold
      simp only [Hnn, _root_.decide_false, Bool.not_false]
      wp_auto
      wp_apply wp_Choose as %c -
      rcases c with _ | _
      · wp_auto
        wp_join_done
        all_goals (iframe; iright; iexists _; iexact Hold)
      · wp_auto
        wp_apply wp_ChooseUint64 as %cur -
        wp_apply wp_ChooseUint64 as %mx -
        wp_join_done
        all_goals (iframe; iright; iexists _; iexact Hold)
  -- `e1 := Errno(gomodel.ChooseUint64()); if e1 != 0 { err = errnoErr(e1) }`
  wp_apply wp_ChooseUint64 as %e -
  wp_if_destruct
  all_goals try (iapply HΦ; iframe; done)
  -- `errnoErr(e1)`
  wp_func_call
  wp_call
  wp_auto
  repeat' wp_if_destruct
  all_goals (iapply HΦ; iframe)

/-- `syscall`'s `init` function (`rlimit.go`), translated, over the model of `prlimit1`. -/
theorem syscall.wp_init0
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (wp_Store : sync.atomic.Pointer.Store.spec (GF := GF) (hG := hG))
    (ea ei en : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync.atomic ∗
       sync.atomic.ownPointer (T' := syscall.Rlimit) (globalAddr syscall.origRlimitNofile) (DFrac.own 1) null ∗
       globalAddr syscall.errEAGAIN ↦□ ea ∗ globalAddr syscall.errEINVAL ↦□ ei ∗
       globalAddr syscall.errENOENT ↦□ en }}
      (App (Val (@! syscall.init.«0»)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨Horig, #Hea, #Hei, #Hen⟩
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ lim
  -- `Getrlimit(RLIMIT_NOFILE, &lim)`: `prlimit1(0, RLIMIT_NOFILE, nil, &lim)`
  wp_func_call
  wp_call
  wp_auto
  wp_apply (syscall.wp_prlimit1_init wp_Choose wp_ChooseUint64 _ _ null lim_ptr
      (zero_val syscall.Rlimit) ea ei en) $$ [lim] as %err ⟨-, Hlim⟩
  · isplitr; · iassumption
    isplitr; · iassumption
    isplitr; · iassumption
    isplitr
    · ileft; ipureintro; rfl
    · iright; iexists _; iexact lim
  icases Hlim with (%h | ⟨%l, lim⟩)
  · exact absurd h Hnn
  -- `if err == nil && lim.Max > 0 && lim.Cur < lim.Max-1 { ... }`
  rcases err with _ | ie
  · wp_auto
    iapply HΦ; itrivial
  wp_auto
  repeat' wp_if_destruct
  all_goals try (iapply HΦ; itrivial; done)
  -- `origRlimitNofile.Store(&lim)`
  wp_apply_core (wp_Store (T' := syscall.Rlimit) syscall.Rlimit.ty
    (globalAddr syscall.origRlimitNofile) lim_ptr) $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists null
  iframe Horig
  iintro Horig
  imod Hmask with _
  imodintro
  wp_auto
  -- `adjustFileLimit(&nlim)`: empty on Linux
  wp_func_call
  wp_call
  wp_auto
  -- `setrlimit(RLIMIT_NOFILE, &nlim)`: `prlimit1(0, RLIMIT_NOFILE, &nlim, nil)`
  wp_func_call
  wp_call
  wp_auto
  wp_apply (syscall.wp_prlimit1_init wp_Choose wp_ChooseUint64 _ _ nlim_ptr null _ ea ei en)
    $$ [nlim] as %err2 -
  · isplitr; · iassumption
    isplitr; · iassumption
    isplitr; · iassumption
    isplitl [nlim]
    · iright; iexact nlim
    · ileft; ipureintro; rfl
  iapply HΦ; itrivial

open syscall in
theorem syscall.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_OnceFunc : sync.OnceFunc.spec (GF := GF) (hG := hG))
    (wp_atomic_initialize : sync.atomic.initialize'.spec (GF := GF) (hG := hG))
    (wp_gomodel_initialize : internal.gomodel.initialize'.spec (GF := GF) (hG := hG))
    (wp_ChooseStrings : internal.gomodel.ChooseStrings.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG))
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (wp_Store : sync.atomic.Pointer.Store.spec (GF := GF) (hG := hG)) :
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
  wp_apply wp_GlobalAlloc as H18
  wp_apply wp_gomodel_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #Hgomodel⟩
  wp_apply wp_atomic_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  wp_func_call
  unfold runtime_envs.impl
  wp_auto
  wp_apply wp_ChooseStrings as %envsl -
  set_option maxRecDepth 20000 in
  wp_apply wp_OnceFunc as %cpe -
  unfold EAGAIN EINVAL ENOENT
  repeat (first
    | (rw [recv_eq_func_mk BAnon BAnon]; wp_auto)
    | wp_auto)
  wp_apply wp_map_make1 (K := Loc) (V := GoSlice) as %mref Hm
  -- `init.0`, translated, over the Go model of `prlimit1`
  ihave Horig : iprop(sync.atomic.ownPointer (T' := syscall.Rlimit)
      (globalAddr syscall.origRlimitNofile) (DFrac.own 1) null) $$ [H10]
  · rw [sync.atomic.ownPointer_unseal]; unfold sync.atomic.ownPointerDef; iexact H10
  ipersist H3
  ipersist H4
  ipersist H5
  wp_apply (syscall.wp_init0 wp_Choose wp_ChooseUint64 wp_Store) $$ [Horig]
  · iframe Horig
    repeat' (first | iassumption | isplitr)
  iframe Hown
  is_pkg_init_finish

end proof

end Perennial
