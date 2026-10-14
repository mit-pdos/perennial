/-
A lock-based stack (`LockedStack`) and an elimination stack built on top of it,
where a `Push` and a `Pop` can exchange a value through an unbuffered channel.

Lean notes:
* The ghost hypotheses `Hsa`/`Hsf` are the auth/frag halves, similarly
  `Hra`/`Hrf`.
* There is no `solve_ndisj`; the mask side conditions are proved with the
  lemmas `mask_diff_ndot` and `mask_ndot_ne'` (`Perennial/Std/Namespaces.lean`).

This file: the package's `isPkgInit` instances, the predicates of the locked
stack and of the elimination stack (with its invariant), and the escrow tokens
`alloc_push_help_token`/`alloc_pop_help_token`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.time.Base
public import Perennial.Ghost.Token
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack :=
  build_get_is_pkg_init_wf

end init

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

-- (declared before the proofs: a command such as `structure`, `macro` or `notation`
-- declared after asynchronously elaborated proofs waits for them)
structure EliminationStackNames where
  specGn : GName
  lsGn : GName
  chGn : ChanNames
  sGn : GName
  rGn : GName

section locked_stack_proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

def ownLockedStack (γ : GName) (σ : List GoString) : IProp GF :=
  ghostVar γ (1 : Qp).half σ

instance ownLockedStack_timeless (γ : GName) (σ : List GoString) :
    Timeless (ownLockedStack (GF := GF) γ σ) := by
  unfold ownLockedStack; infer_instance

def isLockedStack (s : Loc) (γ : GName) : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (s.[LockedStack, go!"mu"])
      iprop(∃ (stack_sl : GoSlice) (stack : List GoString),
        "stack" ∷ s.[LockedStack, go!"stack"] ↦ stack_sl ∗
        "Hsl" ∷ stack_sl ↦* stack ∗
        "Hcap" ∷ ownSliceCap GoString stack_sl (DFrac.own 1) ∗
        "Hauth" ∷ ghostVar γ (1 : Qp).half stack.reverse) ∗
    "_" ∷ True)

instance isLockedStack_persistent (s : Loc) (γ : GName) :
    Persistent (isLockedStack (GF := GF) s γ) := by
  unfold isLockedStack; infer_instance

end locked_stack_proof

section elimination_stack_proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

def ownEliminationStack (γ : EliminationStackNames) (σ : List GoString) : IProp GF :=
  ghostVar γ.specGn (1 : Qp).half σ

/-- Supports atomic updates for Pop and Push that are
allowed to access `⊤ ∖ N`. -/
abbrev ownExchangerInv (γ : EliminationStackNames) (N : Namespace)
    (exstate : ChanState GoString) : IProp GF :=
  iprop(∃ (γs γr : GName),
    "Hsa" ∷ ghostVar γ.sGn (1 : Qp).half γs ∗ "Hra" ∷ ghostVar γ.rGn (1 : Qp).half γr ∗
    "Hexchanger" ∷ (match exstate with
      | .Idle => iprop(ghostVar γ.sGn (1 : Qp).half γs ∗ ghostVar γ.rGn (1 : Qp).half γr)
      | .SndPending v =>
          iprop((|={⊤ \ ↑N,∅}=> ∃ σ, ownEliminationStack γ σ ∗
                  (ownEliminationStack γ (v :: σ) ={∅,⊤ \ ↑N}=∗ token γs)) ∗
                ghostVar γ.rGn (1 : Qp).half γr)
      | .RcvPending =>
          iprop((|={⊤ \ ↑N,∅}=> ∃ σ, ownEliminationStack γ σ ∗
                  (∀ v σ', ⌜σ = v :: σ'⌝ → ownEliminationStack γ σ' ={∅,⊤ \ ↑N}=∗
                    ghostVar γr Qp.threeQuarters v)) ∗
                ghostVar γ.sGn (1 : Qp).half γs)
      | .SndCommit v => iprop(ghostVar γr Qp.threeQuarters v ∗ ghostVar γ.sGn (1 : Qp).half γs)
      | .RcvCommit => iprop(token γs ∗ ghostVar γ.rGn (1 : Qp).half γr)
      | _ => iprop(False)))

abbrev elimInv (γ : EliminationStackNames) (N : Namespace) : IProp GF :=
  iprop(∃ (stack : List GoString) (exstate : ChanState GoString),
    "Hls" ∷ ownLockedStack γ.lsGn stack ∗
    "Hauth" ∷ ghostVar γ.specGn (1 : Qp).half stack ∗
    "exchanger" ∷ ownChan γ.chGn GoString exstate ∗
    "Hexchanger" ∷ ownExchangerInv γ (N.@"inv") exstate)

def isEliminationStack (s : Loc) (γ : EliminationStackNames) (N : Namespace) : IProp GF :=
  iprop(∃ st : EliminationStack,
    "#s" ∷ s ↦□ st ∗
    "#Hbase" ∷ isLockedStack st.base' γ.lsGn ∗
    "#Hch" ∷ isChan st.exchanger' γ.chGn GoString ∗
    "#Hinv" ∷ inv (N.@"inv") (elimInv γ N))

instance isEliminationStack_persistent (s : Loc) (γ : EliminationStackNames) (N : Namespace) :
    Persistent (isEliminationStack (GF := GF) s γ N) := by
  unfold isEliminationStack; infer_instance

theorem alloc_push_help_token {E : CoPset} (N : Namespace) (P : IProp GF) :
    ⊢ |={E}=> ∃ γs, (token γs ={↑N}=∗ ▷ P) ∗ (▷ P ={↑N}=∗ token γs) := by
  imod token_alloc with ⟨%γs, Htok⟩
  imod token_alloc with ⟨%γs2, Htok2⟩
  imod inv_alloc N E iprop(P ∗ token γs2 ∨ token γs) $$ [Htok] with #Hescrow
  · inext; iright; iexact Htok
  imodintro
  iexists γs
  isplitl []
  · iintro Ht
    iinv Hescrow with (⟨HP, Ht2⟩ | >Hbad) Hclose
    · imod Hclose $$ [Ht] with -
      · inext; iright; iexact Ht
      imodintro; iexact HP
    · icombine Ht Hbad gives %h; exact h.elim
  · iintro HP
    iinv Hescrow with (⟨-, >Hbad⟩ | >Htok) Hclose
    · icombine Htok2 Hbad gives %h; exact h.elim
    · imod Hclose $$ [HP Htok2] with -
      · inext; ileft; iframe
      imodintro; iexact Htok

theorem alloc_pop_help_token {E : CoPset} (N : Namespace) (P : GoString → IProp GF) :
    ⊢ |={E}=> ∃ γr, (∀ v : GoString, ghostVar γr Qp.threeQuarters v ={↑N}=∗ ▷ P v) ∗
                   (∀ v, ▷ P v ={↑N}=∗ ghostVar γr Qp.threeQuarters v) := by
  have hq : Qp.threeQuarters + Qp.quarter = 1 := by
    rw [Qp.ext_iff, Qp.val_add, Qp.val_threeQuarters, Qp.val_quarter, Qp.val_one]; grind
  have hbad : ¬ (Qp.threeQuarters + 1 ≤ 1) := by
    rw [Qp.le_iff, Qp.val_add, Qp.val_threeQuarters, Qp.val_one]; grind
  imod ghostVar_alloc (go!"" : GoString) with ⟨%γr, Htok⟩
  imod token_alloc with ⟨%γdone, Hdone⟩
  imod inv_alloc N E iprop(∃ v : GoString,
      (P v ∗ token γdone ∗ ghostVar γr Qp.quarter v) ∨ ghostVar γr 1 v) $$ [Htok] with #Hescrow
  · inext; iexists _; iright; iexact Htok
  imodintro
  iexists γr
  isplitl []
  · iintro %v Ht
    iinv Hescrow with ⟨%v', (⟨HP, Hd, >Ht2⟩ | >Hbad)⟩ Hclose
    · icombine Ht Ht2 gives % ⟨_, Heq⟩
      subst Heq
      ihave Hfull := (ghostVar_fractional γr v).fractional Qp.threeQuarters Qp.quarter |>.2 $$ [Ht Ht2]
      · iframe
      rw [hq]
      imod Hclose $$ [Hfull] with -
      · inext; iexists v; iright; iexact Hfull
      imodintro; iexact HP
    · icombine Ht Hbad gives % ⟨Hq, _⟩
      exact (hbad Hq).elim
  · iintro %v HP
    iinv Hescrow with ⟨%v', (⟨-, >Hbad, -⟩ | >Ht)⟩ Hclose
    · icombine Hdone Hbad gives %h; exact h.elim
    · imod ghostVar_update v γr v' $$ Ht with Ht
      rw [← hq]
      icases (ghostVar_fractional γr v).fractional Qp.threeQuarters Qp.quarter |>.1 $$ Ht
        with ⟨Ht, Ht2⟩
      imod Hclose $$ [HP Hdone Ht2] with -
      · inext; iexists v; ileft; iframe
      imodintro; iexact Ht

end elimination_stack_proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

end Perennial
