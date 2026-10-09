/-
A lock-based stack (`LockedStack`) and an elimination stack built on top of it,
where a `Push` and a `Pop` can exchange a value through an unbuffered channel.

Lean notes:
* The ghost hypotheses `Hsa`/`Hsf` are the auth/frag halves, similarly
  `Hra`/`Hrf`.
* There is no `solve_ndisj`; the mask side conditions are proved with the
  lemmas `mask_diff_ndot` and `mask_ndot_ne'` (`Perennial/Std/Namespaces.lean`).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Base
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Proof.sync_proof.mutex
public import Perennial.Proof.strings
public import Perennial.Proof.time
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
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
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
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

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

set_option goose.wp.extras true

theorem wp_NewLockedStack :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! NewLockedStack)) (Val #()))
    {{ (s : Loc) (γ : GName), RET #s; isLockedStack s γ ∗ ownLockedStack γ [] }} := by
  wp_start
  wp_apply wp_slice_make2 (V := GoString) (t := go.string) (W64 0) as %stack_sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  wp_alloc s as Hs
  iStructNamed Hs
  imod ghostVar_alloc ([] : List GoString) with ⟨%γ, Hγ⟩
  icases ghostVar_split γ ([] : List GoString) (1 : Qp).half (1 : Qp).half $$ [Hγ] with ⟨Hauth, Hfrag⟩
  · rw [Qp.half_add_half]; iexact Hγ
  imod sync.init_Mutex iprop(∃ (stack_sl : GoSlice) (stack : List GoString),
        "stack" ∷ s.[LockedStack, go!"stack"] ↦ stack_sl ∗
        "Hsl" ∷ stack_sl ↦* stack ∗
        "Hcap" ∷ ownSliceCap GoString stack_sl (DFrac.own 1) ∗
        "Hauth" ∷ ghostVar γ (1 : Qp).half stack.reverse) ⊤ (s.[LockedStack, go!"mu"])
    $$ [mu] [stack Hsl Hcap Hauth] with #Hmu
  · iexact mu
  · inext; iexists stack_sl, []; rw [List.reverse_nil]; iframe
  wp_auto
  iapply HΦ
  unfold isLockedStack ownLockedStack
  iframe # ∗

theorem LockedStack.wp_Push (v : GoString) (γ : GName) (s : Loc) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isLockedStack s γ) -∗
      (|={⊤,∅}=> ∃ σ, ownLockedStack γ σ ∗ (ownLockedStack γ (v :: σ) ={∅,⊤}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.GoType.PointerType LockedStack.ty @!! go!"Push")) (Val #v)) {{ Φ }} := by
  wp_start as #His
  unfold isLockedStack
  iNamed His
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  iNamed Hi
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) [v]
  wp_auto
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression go.string #v)] = 1 from rfl]
  isplitl []
  · ipureintro; rfl
  iintro %sl_ptr ⟨Htmp, -⟩
  wp_auto
  wp_apply wp_slice_append (V := GoString) (t := go.string) stack_sl stack _ [v] (DFrac.own 1)
    $$ [Hsl Hcap Htmp] with %sl' ⟨Hsl, Hcap, -⟩
  · iframe
  iapply fupd_wp
  imod HΦ with ⟨%σ, Hl, HΦ⟩
  unfold ownLockedStack
  icombine Hl Hauth gives % ⟨_, Heq⟩
  subst Heq
  imod ghostVar_update_halves (v :: stack.reverse) γ _ _ $$ Hl Hauth with ⟨Hl, Hauth⟩
  imod HΦ $$ Hl with HΦ
  imodintro
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
  · inext; iexists sl', stack ++ [v]
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append]
    iframe
  iexact HΦ

theorem LockedStack.wp_Pop (γ : GName) (s : Loc) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isLockedStack s γ) -∗
      (|={⊤,∅}=> ∃ σ, ownLockedStack γ σ ∗
        (match σ with
         | [] => ownLockedStack γ [] ={∅,⊤}=∗ Φ (PairV #(go!"") #false)
         | v :: σ => ownLockedStack γ σ ={∅,⊤}=∗ Φ (PairV #v #true))) -∗
      WP (App (Val (s @!! go.GoType.PointerType LockedStack.ty @!! go!"Pop")) (Val #())) {{ Φ }} := by
  wp_start as #His
  unfold isLockedStack
  iNamed His
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hi⟩
  iNamed Hi
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hcapwf := ownSliceCap_wf _ _ $$ Hcap
  iapply fupd_wp
  imod HΦ with ⟨%σ, Hl, HΦ⟩
  unfold ownLockedStack
  icombine Hl Hauth gives % ⟨_, Heq⟩
  obtain rfl : stack = σ.reverse := by rw [Heq, List.reverse_reverse]
  rcases σ with _ | ⟨v, σ⟩
  · imod HΦ $$ Hl with HΦ
    imodintro
    wp_if_destruct
    · wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
      · inext; iexists stack_sl, []; simp only [List.reverse_nil]; iframe
      iexact HΦ
    · exfalso; simp at Hlen; word
  · imod ghostVar_update_halves σ γ _ _ $$ Hl Hauth with ⟨Hl, Hauth⟩
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
    icases ownSlice_slice_with_cap (W64 0) (stack_sl.len - W64 1) stack_sl (σ.reverse ++ [v])
      (by word) $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
    · iframe
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked stack Hsl Hcap Hauth]
    · inext; iexists _, σ.reverse
      have hn : sint.nat (stack_sl.len - W64 1) = σ.reverse.length := by
        simp only [List.length_reverse]; word
      rw [List.reverse_reverse, hn, show sint.nat (W64 0) = 0 from rfl]
      simp only [subslice, List.drop_zero, List.take_left']
      iframe
    iexact HΦ

end locked_stack_proof

section elimination_stack_proof

variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : elimination_stack.Assumptions]

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

omit sem package_sem in
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
    -- `▷ (P ∗ token γs2)` cannot be split: keep only `▷ P`, dropping the token
    iinv Hescrow with (HPt | >Hbad) Hclose
    · ihave HP : iprop(▷ P) $$ [HPt]
      · inext; icases HPt with ⟨HP, -⟩; iexact HP
      imod Hclose $$ [Ht] with -
      · inext; iright; iexact Ht
      imodintro; iexact HP
    · icombine Ht Hbad gives %h; exact h.elim
  · iintro HP
    iinv Hescrow with (HPt | >Htok) Hclose
    · ihave >Hbad : iprop(▷ token γs2) $$ [HPt]
      · inext; icases HPt with ⟨-, Hbad⟩; iexact Hbad
      icombine Htok2 Hbad gives %h; exact h.elim
    · imod Hclose $$ [HP Htok2] with -
      · inext; ileft; iframe
      imodintro; iexact Htok

omit sem package_sem in
theorem alloc_pop_help_token {E : CoPset} (N : Namespace) (P : GoString → IProp GF) :
    ⊢ |={E}=> ∃ γr, (∀ v : GoString, ghostVar γr Qp.threeQuarters v ={↑N}=∗ ▷ P v) ∗
                   (∀ v, ▷ P v ={↑N}=∗ ghostVar γr Qp.threeQuarters v) := by
  -- Transfinite step indices: `▷ (A ∗ B)` cannot be split into `▷ A ∗ ▷ B`. So when
  -- the escrowed `P v` is taken out, the quarter stored next to it is not recovered;
  -- instead the taker's `3/4` is split into a `1/4` (used under the later to learn the
  -- value) and a `1/2` that goes back into the invariant. The giver starts out owning
  -- the other `1/2`.
  have hq : Qp.threeQuarters = Qp.quarter + (1 : Qp).half := by
    rw [Qp.ext_iff, Qp.val_add, Qp.val_threeQuarters, Qp.val_quarter, Qp.val_half, Qp.val_one]; grind
  have hq2 : (1 : Qp).half + (1 : Qp).half = Qp.quarter + Qp.threeQuarters := by
    rw [Qp.half_add_half, Qp.quarter_add_threeQuarters]
  have hbad : ¬ (Qp.threeQuarters + (1 : Qp).half ≤ 1) := by
    rw [Qp.le_iff, Qp.val_add, Qp.val_threeQuarters, Qp.val_half, Qp.val_one]; grind
  imod ghostVar_alloc (go!"" : GoString) with ⟨%γr, Hγ⟩
  icases ghostVar_split γr (go!"" : GoString) (1 : Qp).half (1 : Qp).half $$ [Hγ] with ⟨Hγi, Hγ2⟩
  · rw [Qp.half_add_half]; iexact Hγ
  imod token_alloc with ⟨%γdone, Hdone⟩
  imod inv_alloc N E iprop((∃ v : GoString, P v ∗ token γdone ∗ ghostVar γr Qp.quarter v) ∨
      (∃ v : GoString, ghostVar γr (1 : Qp).half v)) $$ [Hγi] with #Hescrow
  · inext; iright; iexists _; iexact Hγi
  imodintro
  iexists γr
  isplitl []
  · iintro %v Ht
    iinv Hescrow with (HPt | > ⟨%v', Hbad⟩) Hclose
    · icases ghostVar_split γr v Qp.quarter (1 : Qp).half $$ [Ht] with ⟨Ht1, Ht2⟩
      · rw [← hq]; iexact Ht
      ihave HP : iprop(▷ P v) $$ [HPt Ht1]
      · inext
        icases HPt with ⟨%v', HP, -, Hq⟩
        icombine Ht1 Hq gives % ⟨_, Heq⟩
        subst Heq
        iexact HP
      imod Hclose $$ [Ht2] with -
      · inext; iright; iexists v; iexact Ht2
      imodintro; iexact HP
    · icombine Ht Hbad gives % ⟨Hq, _⟩
      exact (hbad Hq).elim
  · iintro %v HP
    iinv Hescrow with (HPt | > ⟨%v', Ht⟩) Hclose
    · ihave >Hbad : iprop(▷ token γdone) $$ [HPt]
      · inext; icases HPt with ⟨%v', -, Hbad, -⟩; iexact Hbad
      icombine Hdone Hbad gives %h; exact h.elim
    · imod ghostVar_update_2 v γr v' (1 : Qp).half (go!"" : GoString) (1 : Qp).half (Qp.half_add_half 1)
        $$ Ht Hγ2 with ⟨Ht, Hγ2⟩
      icases ghostVar_split γr v Qp.quarter Qp.threeQuarters $$ [Ht Hγ2] with ⟨Ht1, Ht⟩
      · rw [← hq2]; iframe
      imod Hclose $$ [HP Hdone Ht1] with -
      · inext; ileft; iexists v; iframe
      imodintro; iexact Ht

set_option goose.wp.extras true

theorem wp_NewEliminationStack (N : Namespace) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! NewEliminationStack)) (Val #()))
    {{ (s : Loc) (γ : EliminationStackNames), RET #s;
        isEliminationStack s γ N ∗ ownEliminationStack γ [] }} := by
  wp_start
  wp_apply wp_NewLockedStack as %base %γbase ⟨#Hbase, Hls⟩
  wp_apply chan.wp_make1 (V := GoString) as %ch %γch ⟨#Hch, -, Hc⟩
  wp_alloc s as Hs
  ipersist Hs
  imod ghostVar_alloc ([] : List GoString) with ⟨%γspec, Hspec⟩
  icases ghostVar_split γspec ([] : List GoString) (1 : Qp).half (1 : Qp).half $$ [Hspec]
    with ⟨Hauth, Hes⟩
  · rw [Qp.half_add_half]; iexact Hspec
  imod ghostVar_alloc (0 : GName) with ⟨%γsn, Hsn⟩
  icases ghostVar_split γsn (0 : GName) (1 : Qp).half (1 : Qp).half $$ [Hsn] with ⟨Hsa, Hsf⟩
  · rw [Qp.half_add_half]; iexact Hsn
  imod ghostVar_alloc (0 : GName) with ⟨%γrn, Hrn⟩
  icases ghostVar_split γrn (0 : GName) (1 : Qp).half (1 : Qp).half $$ [Hrn] with ⟨Hra, Hrf⟩
  · rw [Qp.half_add_half]; iexact Hrn
  let γ : EliminationStackNames := ⟨γspec, γbase, γch, γsn, γrn⟩
  imod inv_alloc (N.@"inv") ⊤ (elimInv γ N) $$ [Hls Hauth Hc Hsa Hsf Hra Hrf] with #Hinv
  · inext
    unfold elimInv ownExchangerInv
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
  unfold isEliminationStack ownEliminationStack
  iframe
  iexists _
  iframe # ∗

theorem EliminationStack.wp_Push (v : GoString) (γ : EliminationStackNames) (s : Loc)
    (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isEliminationStack s γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ σ, ownEliminationStack γ σ ∗
        (ownEliminationStack γ (v :: σ) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (s @!! go.GoType.PointerType EliminationStack.ty @!! go!"Push")) (Val #v)) {{ Φ }} := by
  wp_start as #His
  unfold isEliminationStack
  iNamed His
  irename s => s1
  iStructNamed s1
  wp_auto_lc 3
  wp_apply time.wp_After (W64 10000) as %after_ch %γafter #Hafter
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- elimination occurs
    simp only [chan.blockingClausePre]
    iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, st.exchanger', γ.chGn, v
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iframe Hch
    unfold sendAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc1 Hi with ⟨%stack, %exstate, Hls, Hauth, exchanger, %γs, %γr, Hsa, Hra, Hexchanger⟩
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
      imod ghostVar_update_halves γs' γ.sGn γs γs $$ Hsf Hsa with ⟨Hsf, Hsa⟩
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
      unfold sendNestedAu
      iinv Hinv with Hi Hclose
      imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc2 Hi with ⟨%stack2, %exstate2, Hls, Hauth, exchanger, %γs2, %γr2, Hsa, Hra, Hexchanger⟩
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
      unfold ownEliminationStack
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghostVar_update_halves (v :: σ) γ.specGn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      imod HΦ $$ Hfrag with HP
      imod Hmask with -
      imod Hpop_au with ⟨%σ0, Hfrag, Hpop⟩
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghostVar_update_halves σ γ.specGn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
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
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, after_ch, γafter
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hafter
    iapply bag_recv_au γafter after_ch _ _ $$ [$Hlc1 $Hlc2] Hafter
    inext
    iintro %t -
    wp_auto
    wp_apply LockedStack.wp_Push v γ.lsGn st.base' $$ [] [HΦ Hlc3]
    · iframe #
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc3 Hi with ⟨%stack, %exstate, Hls, Hauth, exchanger, Hexchanger⟩
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%σ, Hfrag, HΦ⟩
    unfold ownEliminationStack
    icombine Hfrag Hauth gives % ⟨_, Heq⟩
    subst Heq
    imod ghostVar_update_halves (v :: σ) γ.specGn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
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

theorem EliminationStack.wp_Pop (γ : EliminationStackNames) (s : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg ∗ isEliminationStack s γ N) -∗
      (|={⊤ \ ↑N,∅}=> ∃ σ, ownEliminationStack γ σ ∗
        (match σ with
         | [] => ownEliminationStack γ [] ={∅,⊤ \ ↑N}=∗ Φ (PairV #(go!"") #false)
         | v :: σ => ownEliminationStack γ σ ={∅,⊤ \ ↑N}=∗ Φ (PairV #v #true))) -∗
      WP (App (Val (s @!! go.GoType.PointerType EliminationStack.ty @!! go!"Pop")) (Val #())) {{ Φ }} := by
  wp_start as #His
  unfold isEliminationStack
  iNamed His
  irename s => s1
  iStructNamed s1
  wp_auto_lc 3
  wp_apply time.wp_After (W64 10000) as %after_ch %γafter #Hafter
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- elimination occurs
    simp only [chan.blockingClausePre]
    iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, st.exchanger', γ.chGn
    isplitr
    · ipureintro; rfl
    iframe Hch
    unfold recvAu
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc1 Hi with ⟨%stack, %exstate, Hls, Hauth, exchanger, %γs, %γr, Hsa, Hra, Hexchanger⟩
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
        (fun v : GoString => Φ (PairV #v #true)) with ⟨%γr', HΦtok, Htok⟩
      imod ghostVar_update_halves γr' γ.rGn γr γr $$ Hrf Hra with ⟨Hrf, Hra⟩
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
      unfold recvNestedAu
      iinv Hinv with Hi Hclose
      imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc2 Hi with ⟨%stack2, %exstate2, Hls, Hauth, exchanger, %γs2, %γr2, Hsa, Hra, Hexchanger⟩
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
      unfold ownEliminationStack
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghostVar_update_halves (v :: σ) γ.specGn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
      imod Hpush $$ Hfrag with Hpushtok
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%σ0, Hfrag, HΦ⟩
      icombine Hfrag Hauth gives % ⟨_, Heq⟩
      subst Heq
      imod ghostVar_update_halves σ γ.specGn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
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
    simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, after_ch, γafter
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hafter
    iapply bag_recv_au γafter after_ch _ _ $$ [$Hlc1 $Hlc2] Hafter
    inext
    iintro %t -
    wp_auto
    wp_apply LockedStack.wp_Pop γ.lsGn st.base' $$ [] [HΦ Hlc3]
    · iframe #
    iinv Hinv with Hi Hclose
    imod lc_fupd_elim_later (E := ⊤ \ ↑(N.@"inv")) $$ Hlc3 Hi with ⟨%stack, %exstate, Hls, Hauth, exchanger, Hexchanger⟩
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%σ, Hfrag, HΦ⟩
    unfold ownEliminationStack
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
      imod ghostVar_update_halves σ γ.specGn _ _ $$ Hfrag Hauth with ⟨Hfrag, Hauth⟩
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
