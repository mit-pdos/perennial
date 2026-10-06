/-
Port of `new/golang/theory/chan.v`: user-facing specifications of Go channel
operations (`make`, `<-`, `close`, `cap`, `for range`, `select`), in terms of the
atomic-update style specifications of `Perennial/Golang/Theory/Chan/AuSpec/*`.

Lean notes / deviations: see `ChanAuBase.lean` (`[Pos.Countable V]` for ghost state).
The select specifications quantify over the element type `V` and its instances
inside the Iris propositions (as Rocq does).
-/
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuBase
import Perennial.Golang.Theory.Chan.AuSpec.ChanInit
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuSend
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuNew
import Perennial.Golang.Theory.Chan.AuSpec.ChanAuRecv

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.model

namespace chan

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]

instance pure_wp_chan_for_range (c : GoChan) (elem_type : go.GoType) (body : val) :
    PureWp (G := G) (L := L) True (App (App (Val (chan.forRange elem_type)) (Val #c)) (Val body))
      gl(for: (λ: <>, #true : val) ; (λ: <>, #() : val) := (λ: <>,
          let: ("v", "ok") := chan.receive elem_type #c in
          if: "ok" then
            body "v"
          else
            -- channel is closed
            break: #() : val)) where
  pure_wp_wp s E Φ K _ := by
    unfold chan.forRange
    iintro H
    wp_call_lc Hlc
    iapply H $$ Hlc

end proof

section proof2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]
-- (Rocq:) These are carefully ordered so that when the lemmas are applied, typeclass search
-- can fill everything in.
variable {ct : go.GoType} {dir : go.ChanDir} {t : go.GoType} [Hunder : ct ↓u go.ChannelType dir t]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
  [IntoValTyped (GF := GF) V t]

set_option goose.wp.extras true

include Hunder in
theorem wp_make2 (cap : w64) :
    {{ (⌜0 ≤ sint.Z cap⌝ : IProp GF) }}
      (App (Val #(functions go.make2 [ct])) (Val #cap))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChan ch γ V ∗
        ⌜γ.chanCap = cap⌝ ∗
        ownChan γ V (if cap = W64 0 then ChanState.Idle else ChanState.Buffered ([] : List V)) }} := by
  wp_start as %Hle
  wp_apply wp_NewChannel (V := V) cap $$ [] as %ch %γ H
  · ipureintro; exact Hle
  iapply HΦ $$ H

include Hunder in
theorem wp_make1 :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make1 [ct])) (Val #()))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChan ch γ V ∗
        ⌜γ.chanCap = W64 0⌝ ∗
        ownChan γ V ChanState.Idle }} := by
  wp_start
  wp_func_call
  wp_apply wp_NewChannel (V := V) (W64 0) $$ [] as %ch %γ H
  · ipureintro; decide
  iapply HΦ
  iexact H

theorem wp_send (ch : Loc) (v : V) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ sendAu γ v (Φ #())) -∗
      WP (App (App (Val (chan.send t)) (Val #ch)) (Val #v)) {{ Φ }} := by
  iintro %Φ #Hch HΦ
  unfold chan.send
  wp_call
  iapply wp_Send $$ Hch HΦ

include Hunder in
theorem wp_close (ch : Loc) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ closeAu γ V (Φ #())) -∗
      WP (App (Val #(functions go.close [ct])) (Val #ch)) {{ Φ }} := by
  iintro %Φ #Hch HΦ
  wp_func_call
  wp_auto
  iapply wp_Close $$ Hch HΦ

theorem wp_receive (ch : Loc) (γ : ChanNames) :
    ⊢ ∀ Φ : val → IProp GF, isChan ch γ V -∗
      (£ 1 ∗ £ 1 ∗ £ 1 ∗ £ 1 -∗ recvAu γ V (fun v ok => Φ (PairV #v #ok))) -∗
      WP (App (Val (chan.receive t)) (Val #ch)) {{ Φ }} := by
  iintro %Φ #Hch HΦ
  unfold chan.receive
  wp_call
  iapply wp_Receive $$ Hch HΦ

include Hunder in
theorem wp_cap (ch : Loc) (γ : ChanNames) :
    {{ isChan (GF := GF) ch γ V }}
      (App (Val #(functions go.cap [ct])) (Val #ch))
    {{ RET #γ.chanCap; True }} := by
  wp_start as #Hch
  wp_apply wp_Cap (V := V) ch γ $$ Hch
  iapply HΦ
  itrivial

end proof2

/-! ### Select -/

theorem sep_and_persistent {GF : BundledGFunctors} {P Q R : IProp GF} [Persistent P] :
    (P ∗ Q) ∧ R ⊢ P ∗ (Q ∧ R) :=
  (BI.and_intro (BI.and_elim_l.trans (sep_elim_left.trans Persistent.persistent)) .rfl).trans
    (persistently_and_imp_sep.trans
      (sep_mono persistently_elim (and_mono sep_elim_right .rfl)))

section select_proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem_fn : GoSemanticsFunctions] [pre_sem : go.PreSemantics] [sem : go.ChanSemantics]

/-- The precondition for a blocking select case (Rocq inlines this `match`). -/
def blockingClausePre (c : comm_clause) (Ψ : val → IProp GF) : IProp GF :=
  match c with
  | .CommClause (.SendCase t send_chan_expr send_val) send_handler =>
      iprop(∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
          (_ : IntoValTyped (GF := GF) V t) (_ : Pos.Countable V)
          (send_chan : Loc) (γ : ChanNames) (v : V),
        ⌜send_val = Val #v ∧ send_chan_expr = Val #send_chan⌝ ∗
        isChan send_chan γ V ∗
        sendAu γ v (WP send_handler {{ Ψ }}))
  | .CommClause (.RecvCase t recv_chan_expr) recv_handler =>
      iprop(∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
          (_ : IntoValTyped (GF := GF) V t) (_ : Pos.Countable V)
          (recv_chan : Loc) (γ : ChanNames),
        ⌜recv_chan_expr = Val #recv_chan⌝ ∗
        isChan recv_chan γ V ∗
        recvAu γ V (fun v ok => WP (App recv_handler (Val (PairV #v #ok))) {{ Ψ }}))

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
/-- (Rocq:) The lemmas use Ψ because the original client-provided `send/recvAu` will
have some specific postcondition predicate. We don't want to force the caller to
transform that into a `sendAu` of a different. So, these lemmas are written to take a
wand that turns Ψ into Φ. -/
theorem wp_tryCommClause_blocking (c : comm_clause) (Ψ : val → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, (blockingClausePre c Ψ ∧ Φ (PairV #() #false)) -∗
      (∀ retv, Ψ retv -∗ Φ (PairV retv #true)) -∗
      WP (App (Val (chan.tryCommClause c)) (Val #true)) {{ Φ }} := by
  rcases c with ⟨⟨t, ch, e⟩ | ⟨t, ch⟩, body⟩
  · iintro %Φ HΦ Hwand
    simp only [chan.tryCommClause, blockingClausePre]
    wp_call
    icases and_exists_right.1 $$ HΦ with ⟨%V, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hZ, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hT, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hI, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hC, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%send_chan, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%γ, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%v, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨%Heq, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨#Hch, HΦ⟩
    obtain ⟨rfl, rfl⟩ := Heq
    simp only [subst]
    wp_auto
    wp_apply wp_TrySend send_chan v γ true $$ Hch
    simp only [↓reduceIte]
    isplit
    · icases HΦ with ⟨HAU, -⟩
      iapply sendAu_wand $$ HAU
      iintro Hwp
      wp_auto
      wp_bind body
      iapply wp_wand $$ Hwp
      iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr
    · icases HΦ with ⟨-, HΦ⟩
      wp_auto
      iexact HΦ
  · iintro %Φ HΦ Hwand
    simp only [chan.tryCommClause, blockingClausePre]
    wp_call
    icases and_exists_right.1 $$ HΦ with ⟨%V, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hZ, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hT, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hI, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hC, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%recv_chan, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%γ, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨%Heq, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨#Hch, HΦ⟩
    subst Heq
    simp only [subst]
    wp_auto
    wp_apply wp_TryReceive recv_chan γ true $$ Hch
    simp only [↓reduceIte]
    isplit
    · icases HΦ with ⟨HAU, -⟩
      iapply recvAu_wand $$ HAU
      iintro %v %ok Hwp
      wp_auto
      wp_bind (App body _)
      iapply wp_wand $$ Hwp
      iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr
    · icases HΦ with ⟨-, HΦ⟩
      wp_auto
      iexact HΦ

set_option maxHeartbeats 400000 in
theorem wp_trySelect_blocking (clauses : List comm_clause) (Ψ Φ : val → IProp GF) :
    ⊢ (([∧list] c ∈ clauses, blockingClausePre c Ψ) ∧ Φ (PairV #() #false)) -∗
      □ (∀ retv, Ψ retv -∗ Φ (PairV retv #true)) -∗
      WP (chan.trySelect true clauses) {{ Φ }} := by
  induction clauses with
  | nil =>
    iintro HΦ #Hwand
    simp only [chan.trySelect, List.foldr]
    wp_auto
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | cons c cs ih =>
    iintro HΦ #Hwand
    simp only [chan.trySelect, List.foldr] at ih ⊢
    wp_apply wp_tryCommClause_blocking c Ψ $$ [HΦ] []
    · isplit
      · icases HΦ with ⟨H, -⟩
        icases BigAndL.bigAndL_cons.1 $$ H with ⟨H, -⟩
        iexact H
      · wp_auto
        iapply ih $$ [HΦ] []
        · isplit
          · icases HΦ with ⟨H, -⟩
            icases BigAndL.bigAndL_cons.1 $$ H with ⟨-, H⟩
            iexact H
          · icases HΦ with ⟨-, H⟩
            iexact H
        · iexact Hwand
    · iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr

theorem wp_SelectStmt_blocking {s : Stuckness} {E : CoPset} (clauses : List comm_clause)
    (Φ : val → IProp GF) :
    (∀ clauses' : List comm_clause, ⌜clauses'.Perm clauses⌝ -∗
      WP gl(let: ("v", "succeeded") := chan.trySelect true clauses' in
          if: "succeeded" then "v"
          else (λ: <>, SelectStmt (SelectStmtClauses none clauses) : val) #()) @ s; E {{ Φ }}) ⊢
    WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none clauses))) @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_GoInstruction' (s := s) (E := E) SelectStmt (SelectStmtClausesV none clauses) Φ
    (fun gs => by
      have h : ∃ e, is_go_step_pure SelectStmt (SelectStmtClausesV none clauses) e := by
        rw [go.chan_select_blocking]; exact ⟨_, clauses, List.Perm.refl _, rfl⟩
      obtain ⟨e, he⟩ := h
      exact ⟨e, gs, he, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := Hstep
  have Hp' : is_go_step_pure SelectStmt (SelectStmtClausesV none clauses) e' := Hp
  rw [go.chan_select_blocking] at Hp'
  obtain ⟨clauses', Hperm, rfl⟩ := Hp'
  imodintro
  iframe Hctx
  iapply HΦ $$ %clauses' %Hperm

theorem wp_select_blocking (clauses : List comm_clause) (Φ : val → IProp GF) :
    ⊢ ([∧list] c ∈ clauses, blockingClausePre c Φ) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none clauses))) {{ Φ }} := by
  iloeb as IH
  iintro Hcases
  iapply wp_SelectStmt_blocking
  iintro %clauses' %Hperm
  wp_apply wp_trySelect_blocking clauses' Φ $$ [Hcases] []
  · isplit
    · rw [BigAndL.bigAndL_perm (Φ := fun c => blockingClausePre c Φ) Hperm]
      iexact Hcases
    · wp_auto
      iapply IH $$ Hcases
  · imodintro
    iintro %r Hr
    wp_auto
    iexact Hr

/-- The precondition for a nonblocking select case (Rocq inlines this `match`). -/
def nonblockingClausePre (c : comm_clause) (Ψ : val → IProp GF) : IProp GF :=
  match c with
  | .CommClause (.SendCase t send_chan_expr send_val) send_handler =>
      iprop(∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
          (_ : IntoValTyped (GF := GF) V t) (_ : Pos.Countable V)
          (send_chan : Loc) (γ : ChanNames) (v : V),
        ⌜send_val = Val #v ∧ send_chan_expr = Val #send_chan⌝ ∗
        isChan send_chan γ V ∗
        nonblockingSendAu γ v (WP send_handler {{ Ψ }}) iprop(True))
  | .CommClause (.RecvCase t recv_chan_expr) recv_handler =>
      iprop(∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
          (_ : IntoValTyped (GF := GF) V t) (_ : Pos.Countable V)
          (recv_chan : Loc) (γ : ChanNames),
        ⌜recv_chan_expr = Val #recv_chan⌝ ∗
        isChan recv_chan γ V ∗
        nonblockingRecvAu γ V (fun v ok => WP (App recv_handler (Val (PairV #v #ok))) {{ Ψ }})
          iprop(True))

set_option maxHeartbeats 400000 in
theorem wp_tryCommClause_nonblocking (c : comm_clause) (Ψ : val → IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, (nonblockingClausePre c Ψ ∧ Φ (PairV #() #false)) -∗
      (∀ retv, Ψ retv -∗ Φ (PairV retv #true)) -∗
      WP (App (Val (chan.tryCommClause c)) (Val #false)) {{ Φ }} := by
  rcases c with ⟨⟨t, ch, e⟩ | ⟨t, ch⟩, body⟩
  · iintro %Φ HΦ Hwand
    simp only [chan.tryCommClause, nonblockingClausePre]
    wp_call
    icases and_exists_right.1 $$ HΦ with ⟨%V, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hZ, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hT, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hI, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hC, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%send_chan, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%γ, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%v, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨%Heq, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨#Hch, HΦ⟩
    obtain ⟨rfl, rfl⟩ := Heq
    simp only [subst]
    wp_auto
    wp_apply wp_TrySend send_chan v γ false $$ Hch
    simp only [Bool.false_eq_true, ↓reduceIte]
    ileft
    unfold nonblockingSendAu
    isplit
    · icases HΦ with ⟨⟨HAU, -⟩, -⟩
      iapply nonblockingSendAuInner_wand $$ HAU
      iintro Hwp
      wp_auto
      wp_bind body
      iapply wp_wand $$ Hwp
      iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr
    · icases HΦ with ⟨-, HΦ⟩
      wp_auto
      iexact HΦ
  · iintro %Φ HΦ Hwand
    simp only [chan.tryCommClause, nonblockingClausePre]
    wp_call
    icases and_exists_right.1 $$ HΦ with ⟨%V, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hZ, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hT, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hI, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%hC, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%recv_chan, HΦ⟩
    icases and_exists_right.1 $$ HΦ with ⟨%γ, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨%Heq, HΦ⟩
    icases sep_and_persistent $$ HΦ with ⟨#Hch, HΦ⟩
    subst Heq
    simp only [subst]
    wp_auto
    wp_apply wp_TryReceive recv_chan γ false $$ Hch
    simp only [Bool.false_eq_true, ↓reduceIte]
    ileft
    unfold nonblockingRecvAu
    isplit
    · icases HΦ with ⟨⟨HAU, -⟩, -⟩
      iapply nonblockingRecvAuInner_wand $$ HAU
      iintro %v %ok Hwp
      wp_auto
      wp_bind (App body _)
      iapply wp_wand $$ Hwp
      iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr
    · icases HΦ with ⟨-, HΦ⟩
      wp_auto
      iexact HΦ

set_option maxHeartbeats 400000 in
theorem wp_trySelect_nonblocking (clauses : List comm_clause) (Ψ Φ : val → IProp GF) :
    ⊢ (([∧list] c ∈ clauses, nonblockingClausePre c Ψ) ∧ Φ (PairV #() #false)) -∗
      □ (∀ retv, Ψ retv -∗ Φ (PairV retv #true)) -∗
      WP (chan.trySelect false clauses) {{ Φ }} := by
  induction clauses with
  | nil =>
    iintro HΦ #Hwand
    simp only [chan.trySelect, List.foldr]
    wp_auto
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  | cons c cs ih =>
    iintro HΦ #Hwand
    simp only [chan.trySelect, List.foldr] at ih ⊢
    wp_apply wp_tryCommClause_nonblocking c Ψ $$ [HΦ] []
    · isplit
      · icases HΦ with ⟨H, -⟩
        icases BigAndL.bigAndL_cons.1 $$ H with ⟨H, -⟩
        iexact H
      · wp_auto
        iapply ih $$ [HΦ] []
        · isplit
          · icases HΦ with ⟨H, -⟩
            icases BigAndL.bigAndL_cons.1 $$ H with ⟨-, H⟩
            iexact H
          · icases HΦ with ⟨-, H⟩
            iexact H
        · iexact Hwand
    · iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr

theorem wp_SelectStmt_nonblocking {s : Stuckness} {E : CoPset} (dflt : Expr)
    (clauses : List comm_clause) (Φ : val → IProp GF) :
    (∀ clauses' : List comm_clause, ⌜clauses'.Perm clauses⌝ -∗
      WP gl(let: ("v", "succeeded") := chan.trySelect false clauses' in
          if: "succeeded" then "v"
          else (λ: <>, dflt : val) #()) @ s; E {{ Φ }}) ⊢
    WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt) clauses)))
      @ s; E {{ Φ }} := by
  iintro HΦ
  iapply wp_GoInstruction' (s := s) (E := E) SelectStmt (SelectStmtClausesV (some dflt) clauses) Φ
    (fun gs => by
      have h : ∃ e, is_go_step_pure SelectStmt (SelectStmtClausesV (some dflt) clauses) e := by
        rw [go.chan_select_nonblocking]; exact ⟨_, clauses, List.Perm.refl _, rfl⟩
      obtain ⟨e, he⟩ := h
      exact ⟨e, gs, he, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hctx
  obtain ⟨Hp, rfl⟩ := Hstep
  have Hp' : is_go_step_pure SelectStmt (SelectStmtClausesV (some dflt) clauses) e' := Hp
  rw [go.chan_select_nonblocking] at Hp'
  obtain ⟨clauses', Hperm, rfl⟩ := Hp'
  imodintro
  iframe Hctx
  iapply HΦ $$ %clauses' %Hperm

theorem wp_select_nonblocking (clauses : List comm_clause) (dflt : Expr) (Φ : val → IProp GF) :
    ⊢ (([∧list] c ∈ clauses, nonblockingClausePre c Φ) ∧ WP dflt {{ Φ }}) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt) clauses)))
        {{ Φ }} := by
  iintro Hcases
  iapply wp_SelectStmt_nonblocking
  iintro %clauses' %Hperm
  wp_apply wp_trySelect_nonblocking clauses' Φ $$ [Hcases] []
  · isplit
    · rw [BigAndL.bigAndL_perm (Φ := fun c => nonblockingClausePre c Φ) Hperm]
      icases Hcases with ⟨H, -⟩
      iexact H
    · icases Hcases with ⟨-, H⟩
      wp_auto
      iexact H
  · imodintro
    iintro %r Hr
    wp_auto
    iexact Hr

/-- Rocq (stdpp) `permutation_zip`. -/
theorem permutation_zip {A B : Type} {l1 l2 : List A} (h : l1.Perm l2) (l3 : List B)
    (hlen : l1.length = l3.length) :
    ∃ l4 : List B, l3.Perm l4 ∧ (l1.zip l3).Perm (l2.zip l4) := by
  induction h generalizing l3 with
  | nil =>
    cases l3 with
    | nil => exact ⟨[], .nil, .nil⟩
    | cons _ _ => simp at hlen
  | cons x _ ih =>
    cases l3 with
    | nil => simp at hlen
    | cons y l3 =>
      obtain ⟨l4, h1, h2⟩ := ih l3 (by simpa using hlen)
      exact ⟨y :: l4, h1.cons y, by simpa using h2.cons (x, y)⟩
  | swap x y l =>
    match l3, hlen with
    | a :: b :: l3, _ => exact ⟨b :: a :: l3, .swap b a l3, by simpa using .swap (x, b) (y, a) _⟩
  | trans h12 h23 ih1 ih2 =>
    obtain ⟨l4, h1, h2⟩ := ih1 l3 hlen
    obtain ⟨l5, h3, h4⟩ := ih2 l4 (by rw [← h12.length_eq, hlen, h1.length_eq])
    exact ⟨l5, h1.trans h3, h2.trans h4⟩

/-- The precondition for a select case in `wp_select_nonblocking_alt` (Rocq inlines this
`match`). -/
def nonblockingAltClausePre (c : comm_clause) (Ψ : val → IProp GF) (Pnr : IProp GF) :
    IProp GF :=
  match c with
  | .CommClause (.SendCase t send_chan_expr send_val) send_handler =>
      iprop(∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
          (_ : IntoValTyped (GF := GF) V t) (_ : Pos.Countable V)
          (send_chan : Loc) (γ : ChanNames) (v : V),
        ⌜send_val = Val #v ∧ send_chan_expr = Val #send_chan⌝ ∗
        isChan send_chan γ V ∗
        nonblockingSendAuAlt γ v (WP send_handler {{ Ψ }}) Pnr)
  | .CommClause (.RecvCase t recv_chan_expr) recv_handler =>
      iprop(∃ (V : Type) (_ : ZeroVal V) (_ : TypedPointsto (GF := GF) V)
          (_ : IntoValTyped (GF := GF) V t) (_ : Pos.Countable V)
          (recv_chan : Loc) (γ : ChanNames),
        ⌜recv_chan_expr = Val #recv_chan⌝ ∗
        isChan recv_chan γ V ∗
        nonblockingRecvAuAlt γ V
          (fun v ok => WP (App recv_handler (Val (PairV #v #ok))) {{ Ψ }}) Pnr)

set_option maxHeartbeats 400000 in
theorem wp_trySelect_case_nonblocking_alt (c : comm_clause) (Ψ : val → IProp GF)
    (Ψnotready : IProp GF) :
    ⊢ ∀ Φ : val → IProp GF, nonblockingAltClausePre c Ψ Ψnotready -∗
      ((∀ retv, Ψ retv -∗ Φ (PairV retv #true)) ∧ (Ψnotready -∗ Φ (PairV #() #false))) -∗
      WP (App (Val (chan.tryCommClause c)) (Val #false)) {{ Φ }} := by
  rcases c with ⟨⟨t, ch, e⟩ | ⟨t, ch⟩, body⟩
  · iintro %Φ HΦ Hwand
    simp only [chan.tryCommClause, nonblockingAltClausePre]
    wp_call
    icases HΦ with ⟨%V, %hZ, %hT, %hI, %hC, %send_chan, %γ, %v, %Heq, #Hch, Hau⟩
    obtain ⟨rfl, rfl⟩ := Heq
    simp only [subst]
    wp_auto
    wp_apply wp_TrySend send_chan v γ false $$ Hch
    simp only [Bool.false_eq_true, ↓reduceIte]
    iright
    iapply nonblockingSendAuAlt_wand $$ Hau
    isplit
    · icases Hwand with ⟨Hwand, -⟩
      iintro Hwp
      wp_auto
      wp_bind body
      iapply wp_wand $$ Hwp
      iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr
    · icases Hwand with ⟨-, Hwand⟩
      iintro Hnr
      wp_auto
      iapply Hwand $$ Hnr
  · iintro %Φ HΦ Hwand
    simp only [chan.tryCommClause, nonblockingAltClausePre]
    wp_call
    icases HΦ with ⟨%V, %hZ, %hT, %hI, %hC, %recv_chan, %γ, %Heq, #Hch, Hau⟩
    subst Heq
    simp only [subst]
    wp_auto
    wp_apply wp_TryReceive recv_chan γ false $$ Hch
    simp only [Bool.false_eq_true, ↓reduceIte]
    iright
    iapply nonblockingRecvAuAlt_wand $$ Hau
    isplit
    · icases Hwand with ⟨Hwand, -⟩
      iintro %v %ok Hwp
      wp_auto
      wp_bind (App body _)
      iapply wp_wand $$ Hwp
      iintro %r Hr
      wp_auto
      iapply Hwand $$ Hr
    · icases Hwand with ⟨-, Hwand⟩
      iintro Hnr
      wp_auto
      iapply Hwand $$ Hnr

set_option maxHeartbeats 400000 in
theorem wp_trySelect_nonblocking_alt (Φnrs : List (IProp GF)) (clauses : List comm_clause)
    (P : IProp GF) (Ψ Φ : val → IProp GF) :
    ⊢ ([∗list] c;Φnr ∈ clauses;Φnrs, P -∗ nonblockingAltClausePre c Ψ iprop(P ∗ Φnr)) -∗
      P -∗
      (P -∗ ([∗list] Φnr ∈ Φnrs, Φnr) -∗ Φ (PairV #() #false)) -∗
      □ (∀ retv, Ψ retv -∗ Φ (PairV retv #true)) -∗
      WP (chan.trySelect false clauses) {{ Φ }} := by
  induction clauses generalizing Φnrs Φ with
  | nil =>
    iintro HΦ HP Hwandnr #Hwand
    simp only [chan.trySelect, List.foldr]
    wp_auto
    ihave %Heq := BigSepL2.bigSepL2_nil_inv_left (Φ := fun _ c Φnr =>
      iprop(P -∗ nonblockingAltClausePre c Ψ iprop(P ∗ Φnr))) $$ HΦ
    subst Heq
    iapply Hwandnr $$ HP
    iapply BigSepL.bigSepL_nil.2
    iclear HΦ
    iempintro
  | cons c cs ih =>
    iintro HΦ HP Hwandnr #Hwand
    icases (BigSepL2.bigSepL2_cons_inv_left (Φ := fun _ c Φnr =>
      iprop(P -∗ nonblockingAltClausePre c Ψ iprop(P ∗ Φnr)))).1 $$ HΦ
      with ⟨%Φnr, %Φnrs', %Heq, H, HΦ⟩
    subst Heq
    simp only [chan.trySelect, List.foldr] at ih ⊢
    wp_apply wp_trySelect_case_nonblocking_alt c Ψ iprop(P ∗ Φnr) $$ [HP H] [-]
    · iapply H $$ HP
    · isplit
      · iintro %r Hr
        wp_auto
        iapply Hwand $$ Hr
      · iintro ⟨HP, Hnr⟩
        wp_auto
        iapply ih Φnrs' Φ $$ HΦ HP [Hwandnr Hnr] Hwand
        iintro HP Hnrs
        iapply Hwandnr $$ HP
        iapply BigSepL.bigSepL_cons.2
        iframe

/-- (Rocq:) This specification requires proving _separate_ atomic updates for each case,
and requires a proposition `P` to represent the resources that are available to ALL of the
handlers (rather than having to be split up among the cases).

The reason this uses `au1 ∗ au2 ∗ ...` instead of `au1 ∧ au2 ∧ ...` is because in the event
that the default case is chosen, ALL of the case's atomic updates will have to be fired to
produce witnesses that all the cases were not ready (`[∗] Φnrs`). -/
theorem wp_select_nonblocking_alt (Φnrs : List (IProp GF)) (P : IProp GF)
    (clauses : List comm_clause) (dflt : Expr) (Φ : val → IProp GF) :
    ⊢ ([∗list] c;Φnr ∈ clauses;Φnrs, P -∗ nonblockingAltClausePre c Φ iprop(P ∗ Φnr)) -∗
      P -∗
      (P -∗ ([∗list] Φnr ∈ Φnrs, Φnr) -∗ WP dflt {{ Φ }}) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV (some dflt) clauses)))
        {{ Φ }} := by
  iintro Hcases HP Hdef
  iapply wp_SelectStmt_nonblocking
  iintro %clauses' %Hperm
  icases BigSepL2.bigSepL2_alt.1 $$ Hcases with ⟨%Hlen, Hcases⟩
  obtain ⟨Φnrs', Hperm_Φnrs, Hperm_zip⟩ := permutation_zip Hperm.symm Φnrs Hlen
  wp_apply wp_trySelect_nonblocking_alt Φnrs' clauses' P Φ $$ [Hcases] HP [Hdef] []
  · iapply BigSepL2.bigSepL2_alt.2
    isplit
    · ipureintro
      rw [Hperm.length_eq, Hlen, Hperm_Φnrs.length_eq]
    · iapply (BigSepL.bigSepL_perm Hperm_zip).1 $$ Hcases
  · iintro HP Hnrs
    wp_auto
    iapply Hdef $$ HP
    iapply (BigSepL.bigSepL_perm Hperm_Φnrs).2 $$ Hnrs
  · imodintro
    iintro %r Hr
    wp_auto
    iexact Hr

end select_proof

end chan

end Perennial
