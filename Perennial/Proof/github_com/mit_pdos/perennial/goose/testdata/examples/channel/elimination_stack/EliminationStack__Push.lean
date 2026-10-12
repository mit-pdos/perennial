/-
The proof of `elimination_stack.(*EliminationStack).Push`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack__Push
public import Perennial.Spec.time.After
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack__Push

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack

set_option goose.wp.extras true

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack.Push.wp_proof
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_LockedStack_Push :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Push.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack.Push.spec
      (GF := GF) (hG := hG) := fun v γ s N => by
  wp_start as #His
  unfold isEliminationStack
  iNamed His
  irename s => s1
  iStructNamed s1
  wp_auto_lc 2
  wp_apply wp_After (W64 10000) as %after_ch %γafter #Hafter
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
    wp_apply wp_LockedStack_Push v γ.lsGn st.base' $$ [] [HΦ]
    · iframe #
    iinv Hinv with ⟨%stack, %exstate, >Hls, >Hauth, >exchanger, Hexchanger⟩ Hclose
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

end proof

end Perennial
