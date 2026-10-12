/-
The proof of `elimination_stack.(*EliminationStack).Pop`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack__Pop
public import Perennial.Spec.time.After
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack__Pop

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack.Pop.wp_proof
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (wp_LockedStack_Pop :
      github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.LockedStack.Pop.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.elimination_stack.EliminationStack.Pop.spec
      (GF := GF) (hG := hG) := fun γ s N => by
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
    iexists GoString, inferInstance, inferInstance, inferInstance, inferInstance, st.exchanger', γ.chGn
    isplitr
    · ipureintro; rfl
    iframe Hch
    unfold recvAu
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
    wp_apply wp_LockedStack_Pop γ.lsGn st.base' $$ [] [HΦ]
    · iframe #
    iinv Hinv with ⟨%stack, %exstate, >Hls, >Hauth, >exchanger, Hexchanger⟩ Hclose
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

end proof

end Perennial
