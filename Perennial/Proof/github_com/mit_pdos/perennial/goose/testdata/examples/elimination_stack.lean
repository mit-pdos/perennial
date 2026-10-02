/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/elimination_stack.v`:
a lock-based stack (`LockedStack`) and an elimination stack built on top of it,
where a `Push` and a `Pop` can exchange a value through an unbuffered channel.

Lean notes:
* Rocq's ghost names `Hs●`/`Hs◯` are `Hsa`/`Hsf` (auth/frag halves), similarly
  `Hra`/`Hrf`.
* There is no `solve_ndisj`; the mask side conditions are proved with the
  local lemmas `mask_diff_ndot` and `mask_ndot_ne'`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Base
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.strings
import Perennial.Proof.time
import Perennial.Ghost.Token
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

theorem mask_diff_ndot (N : Namespace) (x : String) : (⊤ \ ↑N : CoPset) ⊆ ⊤ \ ↑(N.@x) := by
  intro p hp
  rw [LawfulSet.mem_diff] at hp ⊢
  exact ⟨hp.1, fun h => hp.2 (nclose_subseteq N x p h)⟩

theorem mask_ndot_ne' (N : Namespace) (x y : String) (h : x ≠ y) :
    (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

instance is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack :=
  define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack :=
  build_get_is_pkg_init_wf

end init

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

section locked_stack_proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

def own_LockedStack (γ : GName) (σ : List go_string) : IProp GF :=
  ghost_var γ (1 : Qp).half σ

def is_LockedStack (s : loc) (γ : GName) : IProp GF :=
  iprop("#Hmu" ∷ sync.is_Mutex (s.[LockedStack.t, go!"mu"])
      (∃ (stack_sl : slice.t) (stack : List go_string),
        "stack" ∷ s.[LockedStack.t, go!"stack"] ↦ stack_sl ∗
        "Hsl" ∷ stack_sl ↦* stack ∗
        "Hcap" ∷ own_slice_cap go_string stack_sl (DFrac.own 1) ∗
        "Hauth" ∷ ghost_var γ (1 : Qp).half stack.reverse) ∗
    "_" ∷ True)

instance is_LockedStack_persistent (s : loc) (γ : GName) :
    Persistent (is_LockedStack (GF := GF) s γ) := by
  unfold is_LockedStack; infer_instance

set_option goose.wp.extras true

theorem wp_NewLockedStack :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! NewLockedStack)) (Val #()))
    {{ (s : loc) (γ : GName), RET #s; is_LockedStack s γ ∗ own_LockedStack γ [] }} := by
  wp_start
  sorry -- TODO(port)

theorem wp_LockedStack__Push (v : go_string) (γ : GName) (s : loc) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg ∗ is_LockedStack s γ) -∗
      (|={⊤,∅}=> ∃ σ, own_LockedStack γ σ ∗ (own_LockedStack γ (v :: σ) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.type.PointerType LockedStack @!! go!"Push")) (Val #v)) {{ Φ }} := by
  wp_start as #His
  sorry -- TODO(port)

end locked_stack_proof

section elimination_stack_proof

structure EliminationStack_names where
  spec_gn : GName
  ls_gn : GName
  ch_gn : chan_names
  s_gn : GName
  r_gn : GName

variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

def own_EliminationStack (γ : EliminationStack_names) (σ : List go_string) : IProp GF :=
  ghost_var γ.spec_gn (1 : Qp).half σ

/-- (Rocq `own_exchanger_inv`) Supports atomic updates for Pop and Push that are
allowed to access `⊤ ∖ N`. -/
def own_exchanger_inv (γ : EliminationStack_names) (N : Namespace)
    (exstate : chanstate.t go_string) : IProp GF :=
  iprop(∃ (γs γr : GName),
    "Hsa" ∷ ghost_var γ.s_gn (1 : Qp).half γs ∗ "Hra" ∷ ghost_var γ.r_gn (1 : Qp).half γr ∗
    "Hexchanger" ∷ (match exstate with
      | .Idle => iprop(ghost_var γ.s_gn (1 : Qp).half γs ∗ ghost_var γ.r_gn (1 : Qp).half γr)
      | .SndPending v =>
          iprop((|={⊤ \ ↑N,∅}=> ∃ σ, own_EliminationStack γ σ ∗
                  (own_EliminationStack γ (v :: σ) ={∅,⊤ \ ↑N}=∗ token γs)) ∗
                ghost_var γ.r_gn (1 : Qp).half γr)
      | .RcvPending =>
          iprop((|={⊤ \ ↑N,∅}=> ∃ σ, own_EliminationStack γ σ ∗
                  (∀ v σ', ⌜σ = v :: σ'⌝ → own_EliminationStack γ σ' ={∅,⊤ \ ↑N}=∗
                    ghost_var γr Qp.threeQuarters v)) ∗
                ghost_var γ.s_gn (1 : Qp).half γs)
      | .SndCommit v => iprop(ghost_var γr Qp.threeQuarters v ∗ ghost_var γ.s_gn (1 : Qp).half γs)
      | .RcvCommit => iprop(token γs ∗ ghost_var γ.r_gn (1 : Qp).half γr)
      | _ => iprop(False)))

def elim_inv (γ : EliminationStack_names) (N : Namespace) : IProp GF :=
  iprop(∃ (stack : List go_string) (exstate : chanstate.t go_string),
    "Hls" ∷ own_LockedStack γ.ls_gn stack ∗
    "Hauth" ∷ ghost_var γ.spec_gn (1 : Qp).half stack ∗
    "exchanger" ∷ own_chan γ.ch_gn go_string exstate ∗
    "Hexchanger" ∷ own_exchanger_inv γ (N.@"inv") exstate)

def is_EliminationStack (s : loc) (γ : EliminationStack_names) (N : Namespace) : IProp GF :=
  iprop(∃ st : EliminationStack.t,
    "#s" ∷ s ↦□ st ∗
    "#Hbase" ∷ is_LockedStack st.base' γ.ls_gn ∗
    "#Hch" ∷ is_chan st.exchanger' γ.ch_gn go_string ∗
    "#Hinv" ∷ inv (N.@"inv") (elim_inv γ N))

instance is_EliminationStack_persistent (s : loc) (γ : EliminationStack_names) (N : Namespace) :
    Persistent (is_EliminationStack (GF := GF) s γ N) := by
  unfold is_EliminationStack; infer_instance

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
    · icombine Ht Hbad gives %⟨⟩
  · iintro HP
    iinv Hescrow with (⟨-, >Hbad⟩ | >Htok) Hclose
    · icombine Htok2 Hbad gives %⟨⟩
    · imod Hclose $$ [HP Htok2] with -
      · inext; ileft; iframe
      imodintro; iexact Htok

theorem alloc_pop_help_token {E : CoPset} (N : Namespace) (P : go_string → IProp GF) :
    ⊢ |={E}=> ∃ γr, (∀ v : go_string, ghost_var γr Qp.threeQuarters v ={↑N}=∗ ▷ P v) ∗
                   (∀ v, ▷ P v ={↑N}=∗ ghost_var γr Qp.threeQuarters v) := by
  sorry -- TODO(port)

end elimination_stack_proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

end Perennial
