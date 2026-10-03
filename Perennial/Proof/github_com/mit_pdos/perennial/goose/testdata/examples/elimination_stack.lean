/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/elimination_stack.v`:
a lock-based stack (`LockedStack`) and an elimination stack built on top of it,
where a `Push` and a `Pop` can exchange a value through an unbuffered channel.

Lean notes:
* Rocq's ghost names `Hs●`/`Hs◯` are `Hsa`/`Hsf` (auth/frag halves), similarly
  `Hra`/`Hrf`.
* There is no `solve_ndisj`; the mask side conditions are proved with the
  lemmas `mask_diff_ndot` and `mask_ndot_ne'` (`Perennial/Std/Namespaces.lean`).
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

-- (declared before the proofs: a command such as `structure`, `macro` or `notation`
-- declared after asynchronously elaborated proofs waits for them)
structure EliminationStack_names where
  spec_gn : GName
  ls_gn : GName
  ch_gn : chan_names
  s_gn : GName
  r_gn : GName

section locked_stack_proof
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

def own_LockedStack (γ : GName) (σ : List go_string) : IProp GF :=
  ghost_var γ (1 : Qp).half σ

instance own_LockedStack_timeless (γ : GName) (σ : List go_string) :
    Timeless (own_LockedStack (GF := GF) γ σ) := by
  unfold own_LockedStack; infer_instance

def is_LockedStack (s : loc) (γ : GName) : IProp GF :=
  iprop("#Hmu" ∷ sync.is_Mutex (s.[LockedStack.t, go!"mu"])
      iprop(∃ (stack_sl : slice.t) (stack : List go_string),
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
  wp_apply wp_slice_make2 (V := go_string) (t := go.string) (W64 0) as %stack_sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  wp_alloc s as Hs
  iStructNamed Hs
  imod ghost_var_alloc ([] : List go_string) with ⟨%γ, Hγ⟩
  icases ghost_var_split γ ([] : List go_string) (1 : Qp).half (1 : Qp).half $$ [Hγ] with ⟨Hauth, Hfrag⟩
  · rw [Qp.half_add_half]; iexact Hγ
  imod sync.init_Mutex iprop(∃ (stack_sl : slice.t) (stack : List go_string),
        "stack" ∷ s.[LockedStack.t, go!"stack"] ↦ stack_sl ∗
        "Hsl" ∷ stack_sl ↦* stack ∗
        "Hcap" ∷ own_slice_cap go_string stack_sl (DFrac.own 1) ∗
        "Hauth" ∷ ghost_var γ (1 : Qp).half stack.reverse) ⊤ (s.[LockedStack.t, go!"mu"])
    $$ [mu] [stack Hsl Hcap Hauth] with #Hmu
  · iexact mu
  · inext; iexists stack_sl, []; rw [List.reverse_nil]; iframe
  wp_auto
  iapply HΦ
  unfold is_LockedStack own_LockedStack
  iframe # ∗

theorem wp_LockedStack__Push (v : go_string) (γ : GName) (s : loc) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg ∗ is_LockedStack s γ) -∗
      (|={⊤,∅}=> ∃ σ, own_LockedStack γ σ ∗ (own_LockedStack γ (v :: σ) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.type.PointerType LockedStack @!! go!"Push")) (Val #v)) {{ Φ }} := by
  wp_start as #His
  unfold is_LockedStack
  iNamed His
  wp_auto
  wp_apply sync.wp_Mutex__Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  iNamed Hi
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.type.SliceType go.string)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := go_string) (t := go.string) [v]
  wp_auto
  rw [show go.array_literal_size [KeyedElement none (ElementExpression go.string #v)] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := go_string) (t := go.string) stack_sl stack _ [v] (DFrac.own 1)
    $$ [Hsl Hcap Htmp] with %sl' ⟨Hsl, Hcap, -⟩
  · iframe
  iapply fupd_wp
  imod HΦ with ⟨%σ, Hl, HΦ⟩
  unfold own_LockedStack
  icombine Hl Hauth gives % ⟨_, Heq⟩
  subst Heq
  imod ghost_var_update_halves (v :: stack.reverse) γ _ _ $$ Hl Hauth with ⟨Hl, Hauth⟩
  imod HΦ $$ Hl with HΦ
  imodintro
  wp_apply sync.wp_Mutex__Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
  · inext; iexists sl', stack ++ [v]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    iframe
  iexact HΦ

theorem wp_LockedStack__Pop (γ : GName) (s : loc) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg ∗ is_LockedStack s γ) -∗
      (|={⊤,∅}=> ∃ σ, own_LockedStack γ σ ∗
        (match σ with
         | [] => own_LockedStack γ [] ={∅,⊤}=∗ Φ (PairV #(go!"") #false)
         | v :: σ => own_LockedStack γ σ ={∅,⊤}=∗ Φ (PairV #v #true))) -∗
      WP (App (Val (s @!! go.type.PointerType LockedStack @!! go!"Pop")) (Val #())) {{ Φ }} := by
  wp_start as #His
  unfold is_LockedStack
  iNamed His
  wp_auto
  wp_apply sync.wp_Mutex__Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  iNamed Hi
  wp_auto
  ihave %Hlen := own_slice_len _ _ _ $$ Hsl
  ihave %Hcapwf := own_slice_cap_wf _ _ $$ Hcap
  iapply fupd_wp
  imod HΦ with ⟨%σ, Hl, HΦ⟩
  unfold own_LockedStack
  icombine Hl Hauth gives % ⟨_, Heq⟩
  obtain rfl : stack = σ.reverse := by rw [Heq, List.reverse_reverse]
  rcases σ with _ | ⟨v, σ⟩
  · imod HΦ $$ Hl with HΦ
    imodintro
    wp_if_destruct
    · wp_apply sync.wp_Mutex__Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
      · inext; iexists stack_sl, []; simp only [List.reverse_nil]; iframe
      iexact HΦ
    · exfalso; simp at Hlen; word
  · imod ghost_var_update_halves σ γ _ _ $$ Hl Hauth with ⟨Hl, Hauth⟩
    imod HΦ $$ Hl with HΦ
    imodintro
    simp only [List.reverse_cons, List.length_append, List.length_reverse, List.length_singleton] at Hlen
    wp_if_destruct
    · exfalso; word
    have hpos : 0 ≤ sint.Z (stack_sl.len - W64 1) := by word
    rw [ite_eq_left (show 0 ≤ sint.Z (stack_sl.len - W64 1) ∧ sint.Z (stack_sl.len - W64 1) < sint.Z stack_sl.len by word)]
    rw [List.reverse_cons]
    wp_apply wp_load_slice_index stack_sl (sint.Z (stack_sl.len - W64 1)) (σ.reverse ++ [v]) _ v hpos
      $$ [Hsl] with Hsl
    · iframe; ipureintro
      have hidx : (sint.Z (stack_sl.len - W64 1)).toNat = σ.reverse.length := by
        simp only [List.length_reverse]; word
      rw [hidx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      rfl
    wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (stack_sl.len - W64 1) ∧
      sint.Z (stack_sl.len - W64 1) ≤ sint.Z stack_sl.cap by word)]
    icases own_slice_slice_with_cap (W64 0) (stack_sl.len - W64 1) stack_sl (σ.reverse ++ [v])
      (by word) $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
    · iframe
    wp_auto
    wp_apply sync.wp_Mutex__Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
    · inext; iexists _, σ.reverse
      have hn : sint.nat (stack_sl.len - W64 1) = σ.reverse.length := by
        simp only [List.length_reverse]; word
      rw [List.reverse_reverse, hn, show sint.nat (W64 0) = 0 from rfl]
      simp only [subslice, List.drop_zero, List.take_left']
      iframe
    iexact HΦ

end locked_stack_proof

section elimination_stack_proof

variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

def own_EliminationStack (γ : EliminationStack_names) (σ : List go_string) : IProp GF :=
  ghost_var γ.spec_gn (1 : Qp).half σ

/-- (Rocq `own_exchanger_inv`) Supports atomic updates for Pop and Push that are
allowed to access `⊤ ∖ N`. -/
abbrev own_exchanger_inv (γ : EliminationStack_names) (N : Namespace)
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

abbrev elim_inv (γ : EliminationStack_names) (N : Namespace) : IProp GF :=
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
    · icombine Ht Hbad gives %h; exact h.elim
  · iintro HP
    iinv Hescrow with (⟨-, >Hbad⟩ | >Htok) Hclose
    · icombine Htok2 Hbad gives %h; exact h.elim
    · imod Hclose $$ [HP Htok2] with -
      · inext; ileft; iframe
      imodintro; iexact Htok

theorem alloc_pop_help_token {E : CoPset} (N : Namespace) (P : go_string → IProp GF) :
    ⊢ |={E}=> ∃ γr, (∀ v : go_string, ghost_var γr Qp.threeQuarters v ={↑N}=∗ ▷ P v) ∗
                   (∀ v, ▷ P v ={↑N}=∗ ghost_var γr Qp.threeQuarters v) := by
  have hq : Qp.threeQuarters + Qp.quarter = 1 := by
    rw [Qp.ext_iff, Qp.val_add, Qp.val_threeQuarters, Qp.val_quarter, Qp.val_one]; grind
  have hbad : ¬ (Qp.threeQuarters + 1 ≤ 1) := by
    rw [Qp.le_iff, Qp.val_add, Qp.val_threeQuarters, Qp.val_one]; grind
  imod ghost_var_alloc (go!"" : go_string) with ⟨%γr, Htok⟩
  imod token_alloc with ⟨%γdone, Hdone⟩
  imod inv_alloc N E iprop(∃ v : go_string,
      (P v ∗ token γdone ∗ ghost_var γr Qp.quarter v) ∨ ghost_var γr 1 v) $$ [Htok] with #Hescrow
  · inext; iexists _; iright; iexact Htok
  imodintro
  iexists γr
  isplitl []
  · iintro %v Ht
    iinv Hescrow with ⟨%v', (⟨HP, Hd, >Ht2⟩ | >Hbad)⟩ Hclose
    · icombine Ht Ht2 gives % ⟨_, Heq⟩
      subst Heq
      ihave Hfull := (ghost_var_fractional γr v).fractional Qp.threeQuarters Qp.quarter |>.2 $$ [Ht Ht2]
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
    · imod ghost_var_update v γr v' $$ Ht with Ht
      rw [← hq]
      icases (ghost_var_fractional γr v).fractional Qp.threeQuarters Qp.quarter |>.1 $$ Ht
        with ⟨Ht, Ht2⟩
      imod Hclose $$ [HP Hdone Ht2] with -
      · inext; iexists v; ileft; iframe
      imodintro; iexact Ht

set_option goose.wp.extras true

theorem wp_NewEliminationStack (N : Namespace) :
    {{ is_pkg_init (PROP := IProp GF) pkg }}
      (App (Val (@! NewEliminationStack)) (Val #()))
    {{ (s : loc) (γ : EliminationStack_names), RET #s;
        is_EliminationStack s γ N ∗ own_EliminationStack γ [] }} := by
  wp_start
  wp_apply wp_NewLockedStack as %base %γbase ⟨#Hbase, Hls⟩
  wp_apply chan.wp_make1 (V := go_string) as %ch %γch ⟨#Hch, -, Hc⟩
  wp_alloc s as Hs
  ipersist Hs
  imod ghost_var_alloc ([] : List go_string) with ⟨%γspec, Hspec⟩
  icases ghost_var_split γspec ([] : List go_string) (1 : Qp).half (1 : Qp).half $$ [Hspec]
    with ⟨Hauth, Hes⟩
  · rw [Qp.half_add_half]; iexact Hspec
  imod ghost_var_alloc (0 : GName) with ⟨%γsn, Hsn⟩
  icases ghost_var_split γsn (0 : GName) (1 : Qp).half (1 : Qp).half $$ [Hsn] with ⟨Hsa, Hsf⟩
  · rw [Qp.half_add_half]; iexact Hsn
  imod ghost_var_alloc (0 : GName) with ⟨%γrn, Hrn⟩
  icases ghost_var_split γrn (0 : GName) (1 : Qp).half (1 : Qp).half $$ [Hrn] with ⟨Hra, Hrf⟩
  · rw [Qp.half_add_half]; iexact Hrn
  let γ : EliminationStack_names := ⟨γspec, γbase, γch, γsn, γrn⟩
  imod inv_alloc (N.@"inv") ⊤ (elim_inv γ N) $$ [Hls Hauth Hc Hsa Hsf Hra Hrf] with #Hinv
  · inext
    unfold elim_inv own_exchanger_inv
    iexists [], .Idle
    iframe
    iexists 0, 0
    dsimp only [γ]
    iframe
    isplitl [Hsa]
    · iexact Hsa
    · iexact Hra
  wp_auto
  iapply HΦ $$ %s %γ
  unfold is_EliminationStack own_EliminationStack
  iframe
  iexists _
  iframe # ∗

theorem wp_EliminationStack__Push (v : go_string) (γ : EliminationStack_names) (s : loc)
    (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg ∗ is_EliminationStack s γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ σ, own_EliminationStack γ σ ∗
        (own_EliminationStack γ (v :: σ) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.type.PointerType EliminationStack @!! go!"Push")) (Val #v)) {{ Φ }} := by
  wp_start as #His
  unfold is_EliminationStack
  iNamed His
  irename s => s1
  iStructNamed s1
  wp_auto_lc 2
  wp_apply time.wp_After (W64 10000) as %after_ch %γafter #Hafter
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- elimination occurs
    simp only [chan.blocking_clause_pre]
    iexists go_string, inferInstance, inferInstance, inferInstance, inferInstance, st.exchanger', γ.ch_gn, v
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iframe Hch
    unfold send_au
    iinv Hinv with ⟨%stack, %exstate, Hls, Hauth, exchanger, %γs, %γr, Hsa, Hra, Hexchanger⟩ Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc1 Hexchanger with Hexchanger
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists exstate
    iframe exchanger
    cases exstate
    all_goals dsimp only
    case Idle =>
      icases Hexchanger with ⟨Hsf, Hrf⟩
      iintro exchanger
      imod Hmask with -
      imod alloc_push_help_token (E := ⊤ \ ↑(N.@"inv")) (N.@"escrow") (Φ #()) with ⟨%γs', HΦtok, Htok⟩
      imod ghost_var_update_halves γs' γ.s_gn γs γs $$ Hsf Hsa with ⟨Hsf, Hsa⟩
      imod Hclose $$ [Hls Hauth exchanger Hsa Hra Hrf HΦ Htok] with -
      · inext
        iexists stack, .SndPending v
        iframe Hls Hauth exchanger
        iexists γs', γr
        dsimp only
        isplitl [Hsa]
        · iexact Hsa
        isplitl [Hra]
        · iexact Hra
        isplitr [Hrf]
        · imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
          imod HΦ with ⟨%σ, Hσ, Hau⟩
          imodintro
          iexists σ
          iframe Hσ
          iintro Hσ
          imod Hau $$ Hσ with HP
          imod Hmask with -
          imod fupd_mask_subseteq (mask_ndot_ne' N "escrow" "inv" (by decide)) with Hmask
          imod Htok $$ [HP] with Htok
          · inext; iexact HP
          imod Hmask with -
          imodintro; iexact Htok
        · iexact Hrf
      imodintro
      unfold send_nested_au
      iinv Hinv with ⟨%stack2, %exstate2, Hls, Hauth, exchanger, %γs2, %γr2, Hsa, Hra, Hexchanger⟩ Hclose
      imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc2 Hexchanger with Hexchanger
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists exstate2
      iframe exchanger
      cases exstate2
      all_goals dsimp only
      case RcvCommit =>
        icases Hexchanger with ⟨Htokγ, Hrf⟩
        iintro exchanger
        imod Hmask with -
        icombine Hsa Hsf gives % ⟨_, Heq⟩
        subst Heq
        imod Hclose $$ [Hls Hauth exchanger Hsa Hra Hsf Hrf] with -
        · inext
          iexists stack2, .Idle
          iframe Hls Hauth exchanger
          iexists γs2, γr2
          dsimp only
          isplitl [Hsa]
          · iexact Hsa
          isplitl [Hra]
          · iexact Hra
          isplitl [Hsf]
          · iexact Hsf
          · iexact Hrf
        imod fupd_mask_subseteq (show (↑(N.@"escrow") : CoPset) ⊆ ⊤ from fun _ _ => CoPset.mem_full) with Hmask
        imod HΦtok $$ Htokγ with HP
        imod Hmask with -
        imodintro
        wp_auto
        iexact HP
      all_goals first | itrivial | (iexfalso; iexact Hexchanger)
    case RcvPending =>
      icases Hexchanger with ⟨Hpop_au, Hsf⟩
      iintro exchanger
      imod Hmask with -
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%σ, Hfrag, HΦ⟩
      unfold own_EliminationStack
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghost_var_update_halves (v :: σ) γ.spec_gn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      imod HΦ $$ Hfrag with HP
      imod Hmask with -
      imod Hpop_au with ⟨%σ0, Hfrag, Hpop⟩
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghost_var_update_halves σ γ.spec_gn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      imod Hpop $$ %v %σ [] Hfrag with Hpopwit
      · ipureintro; rfl
      imod Hclose $$ [Hls Hauth exchanger Hsa Hra Hpopwit Hsf] with -
      · inext
        iexists _, .SndCommit v
        iframe Hls Hauth exchanger
        iexists γs, γr
        dsimp only
        isplitl [Hsa]
        · iexact Hsa
        isplitl [Hra]
        · iexact Hra
        isplitl [Hpopwit]
        · iexact Hpopwit
        · iexact Hsf
      imodintro
      wp_auto
      iexact HP
    all_goals first | itrivial | (iexfalso; iexact Hexchanger)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- timeout: push onto the locked stack
    simp only [chan.blocking_clause_pre]
    iexists time.Time.t, inferInstance, inferInstance, inferInstance, inferInstance, after_ch, γafter
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hafter
    iapply bag_recv_au γafter after_ch _ _ $$ [$Hlc1 $Hlc2] Hafter
    inext
    iintro %t -
    wp_auto
    wp_apply wp_LockedStack__Push v γ.ls_gn st.base' $$ [] [HΦ]
    · iframe #
    iinv Hinv with ⟨%stack, %exstate, >Hls, >Hauth, >exchanger, Hexchanger⟩ Hclose
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%σ, Hfrag, HΦ⟩
    unfold own_EliminationStack
    icombine Hfrag Hauth gives % ⟨_, Heq⟩
    subst Heq
    imod ghost_var_update_halves (v :: σ) γ.spec_gn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
    imod HΦ $$ Hfrag with HP
    imod Hmask with -
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists _
    iframe Hls
    iintro Hls
    imod Hmask with -
    imod Hclose $$ [Hls Hauth exchanger Hexchanger] with -
    · inext
      iexists _, exstate
      iframe
    imodintro
    wp_auto
    iexact HP
  iapply BigAndL.bigAndL_nil.2
  itrivial

theorem wp_EliminationStack__Pop (γ : EliminationStack_names) (s : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg ∗ is_EliminationStack s γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ σ, own_EliminationStack γ σ ∗
        (match σ with
         | [] => own_EliminationStack γ [] ={∅,⊤ \ ↑N}=∗ Φ (PairV #(go!"") #false)
         | v :: σ => own_EliminationStack γ σ ={∅,⊤ \ ↑N}=∗ Φ (PairV #v #true))) -∗
      WP (App (Val (s @!! go.type.PointerType EliminationStack @!! go!"Pop")) (Val #())) {{ Φ }} := by
  wp_start as #His
  unfold is_EliminationStack
  iNamed His
  irename s => s1
  iStructNamed s1
  wp_auto_lc 2
  wp_apply time.wp_After (W64 10000) as %after_ch %γafter #Hafter
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- elimination occurs
    simp only [chan.blocking_clause_pre]
    iexists go_string, inferInstance, inferInstance, inferInstance, inferInstance, st.exchanger', γ.ch_gn
    isplitr
    · ipureintro; rfl
    iframe Hch
    unfold recv_au
    iinv Hinv with ⟨%stack, %exstate, Hls, Hauth, exchanger, %γs, %γr, Hsa, Hra, Hexchanger⟩ Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc1 Hexchanger with Hexchanger
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists exstate
    iframe exchanger
    cases exstate
    all_goals dsimp only
    case Idle =>
      icases Hexchanger with ⟨Hsf, Hrf⟩
      iintro exchanger
      imod Hmask with -
      imod alloc_pop_help_token (E := ⊤ \ ↑(N.@"inv")) (N.@"escrow")
        (fun v : go_string => Φ (PairV #v #true)) with ⟨%γr', HΦtok, Htok⟩
      imod ghost_var_update_halves γr' γ.r_gn γr γr $$ Hrf Hra with ⟨Hrf, Hra⟩
      imod Hclose $$ [Hls Hauth exchanger Hsa Hra Hsf HΦ Htok] with -
      · inext
        iexists stack, .RcvPending
        iframe Hls Hauth exchanger
        iexists γs, γr'
        dsimp only
        isplitl [Hsa]
        · iexact Hsa
        isplitl [Hra]
        · iexact Hra
        isplitr [Hsf]
        · imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
          imod HΦ with ⟨%σ, Hσ, Hau⟩
          imodintro
          iexists σ
          iframe Hσ
          iintro %v %σ' %Heq Hσ
          subst Heq
          dsimp only
          imod Hau $$ Hσ with HP
          imod Hmask with -
          imod fupd_mask_subseteq (mask_ndot_ne' N "escrow" "inv" (by decide)) with Hmask
          imod Htok $$ %v [HP] with Htok
          · inext; iexact HP
          imod Hmask with -
          imodintro; iexact Htok
        · iexact Hsf
      imodintro
      unfold recv_nested_au
      iinv Hinv with ⟨%stack2, %exstate2, Hls, Hauth, exchanger, %γs2, %γr2, Hsa, Hra, Hexchanger⟩ Hclose
      imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc2 Hexchanger with Hexchanger
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iexists exstate2
      iframe exchanger
      cases exstate2
      all_goals dsimp only
      case SndCommit v =>
        icases Hexchanger with ⟨Hwit, Hsf⟩
        iintro exchanger
        imod Hmask with -
        icombine Hra Hrf gives % ⟨_, Heq⟩
        subst Heq
        imod Hclose $$ [Hls Hauth exchanger Hsa Hra Hsf Hrf] with -
        · inext
          iexists stack2, .Idle
          iframe Hls Hauth exchanger
          iexists γs2, γr2
          dsimp only
          isplitl [Hsa]
          · iexact Hsa
          isplitl [Hra]
          · iexact Hra
          isplitl [Hsf]
          · iexact Hsf
          · iexact Hrf
        imod fupd_mask_subseteq (show (↑(N.@"escrow") : CoPset) ⊆ ⊤ from fun _ _ => CoPset.mem_full) with Hmask
        imod HΦtok $$ %v Hwit with HP
        imod Hmask with -
        imodintro
        wp_auto
        iexact HP
      all_goals first | itrivial | (iexfalso; iexact Hexchanger)
    case SndPending v =>
      icases Hexchanger with ⟨Hpush_au, Hrf⟩
      iintro exchanger
      imod Hmask with -
      imod Hpush_au with ⟨%σ, Hfrag, Hpush⟩
      unfold own_EliminationStack
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghost_var_update_halves (v :: σ) γ.spec_gn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      imod Hpush $$ Hfrag with Hpushtok
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%σ0, Hfrag, HΦ⟩
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghost_var_update_halves σ γ.spec_gn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      dsimp only
      imod HΦ $$ Hfrag with HP
      imod Hmask with -
      imod Hclose $$ [Hls Hauth exchanger Hsa Hra Hpushtok Hrf] with -
      · inext
        iexists _, .RcvCommit
        iframe Hls Hauth exchanger
        iexists γs, γr
        dsimp only
        isplitl [Hsa]
        · iexact Hsa
        isplitl [Hra]
        · iexact Hra
        isplitl [Hpushtok]
        · iexact Hpushtok
        · iexact Hrf
      imodintro
      wp_auto
      iexact HP
    case Buffered l => rcases l with _ | ⟨_, _⟩ <;> dsimp only <;> first | itrivial | (iexfalso; iexact Hexchanger)
    case Closed l => rcases l with _ | ⟨_, _⟩ <;> dsimp only <;> (iexfalso; iexact Hexchanger)
    all_goals first | itrivial | (iexfalso; iexact Hexchanger)
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- timeout: pop from the locked stack
    simp only [chan.blocking_clause_pre]
    iexists time.Time.t, inferInstance, inferInstance, inferInstance, inferInstance, after_ch, γafter
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hafter
    iapply bag_recv_au γafter after_ch _ _ $$ [$Hlc1 $Hlc2] Hafter
    inext
    iintro %t -
    wp_auto
    wp_apply wp_LockedStack__Pop γ.ls_gn st.base' $$ [] [HΦ]
    · iframe #
    iinv Hinv with ⟨%stack, %exstate, >Hls, >Hauth, >exchanger, Hexchanger⟩ Hclose
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%σ, Hfrag, HΦ⟩
    unfold own_EliminationStack
    icombine Hfrag Hauth gives % ⟨_, Heq⟩
    subst Heq
    rcases σ with _ | ⟨v, σ⟩
    · dsimp only
      imod HΦ $$ Hfrag with HP
      imod Hmask with -
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iexists []
      iframe Hls
      iintro Hls
      imod Hmask with -
      imod Hclose $$ [Hls Hauth exchanger Hexchanger] with -
      · inext
        iexists _, exstate
        iframe
      imodintro
      wp_auto
      iexact HP
    · dsimp only
      imod ghost_var_update_halves σ γ.spec_gn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      imod HΦ $$ Hfrag with HP
      imod Hmask with -
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iexists _
      iframe Hls
      iintro Hls
      imod Hmask with -
      imod Hclose $$ [Hls Hauth exchanger Hexchanger] with -
      · inext
        iexists _, exstate
        iframe
      imodintro
      wp_auto
      iexact HP
  iapply BigAndL.bigAndL_nil.2
  itrivial

end elimination_stack_proof

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

end Perennial
