From RecordUpdate Require Import RecordSet.

From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import lang lifting slice typing spec_assert.
From Perennial.goose_lang Require ffi.disk.

From iris.algebra Require Import auth agree excl csum.
From Perennial.base_logic Require Import ghost_var.

(* TODO: move this out, it's completely general *)
Section recoverable.
  Context {Σ:Type}.
  Inductive RecoverableState :=
    | UnInit
    | Initing
    | Closed (s:Σ)
    | Opening (s:Σ)
    | Opened (s:Σ) (l:loc)
  .

  Definition recoverable_model : ffi_model :=
    mkFfiModel (RecoverableState) () (populate UnInit) _.

  Local Existing Instance recoverable_model.

  Context {ext:ext_op}.

  Definition openΣ : transition (state*global_state) (Σ*loc) :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | Opened s l => ret (s,l)
                           | _ => undefined
                           end).

  Definition modifyΣ (f:Σ -> Σ) : transition (state*global_state) unit :=
    bind openΣ (λ '(s, l), modify (prod_map (set world (λ _, Opened (f s) l)) id)).

  (* TODO: generalize to a transition to construct the initial value, using a zoom *)
  Definition initTo (init:Σ) (l:loc) : transition (state*global_state) unit :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | UnInit => modify (prod_map (set world (fun _ => Opened init l)) id)
                           | _ => undefined
                           end).

  Definition open (l:loc) : transition (state*global_state) Σ :=
    bind (reads id) (λ '(rs,g), match rs.(world) with
                           | Closed s => bind (modify (prod_map (set world (fun _ => Opened s l)) id))
                                             (fun _ => ret s)
                           | _ => undefined
                           end).

  Definition close : transition (RecoverableState) unit :=
    bind (reads id) (fun s => match s with
                           | Opened s _ | Closed s => modify (fun _ => Closed s)
                           | UnInit => modify (fun _ => UnInit)
                           | _ => undefined
                           end).

  Global Instance Recoverable_inhabited : Inhabited RecoverableState := populate UnInit.
End recoverable.

Arguments RecoverableState Σ : clear implicits.
Arguments recoverable_model Σ : clear implicits.

Definition ty_ := forall (val_ty:val_types), @ty val_ty.
(* TODO: slice should not require an entire ext_ty *)
Definition sliceT_ (t: ty_) : ty_ := λ val_ty, prodT (arrayT (t _)) uint64T.
Definition blockT_: ty_ := sliceT_ (λ val_ty, byteT).


Inductive LogOp :=
  | AppendOp (* log, slice of blocks *)
  | GetOp (* log, index *)
  | ResetOp (* log *)
  | InitOp (* disk size *)
  | OpenOp (* (no arguments) *)
.

Instance eq_LogOp : EqDecision LogOp.
Proof.
  solve_decision.
Defined.

Instance LogOp_fin : Countable LogOp.
Proof.
  solve_countable LogOp_rec 5%nat.
Qed.

Definition log_op : ext_op.
Proof.
  refine (mkExtOp LogOp _ _ Empty_set _ _).
Defined.

Inductive Log_ty := LogT.

Instance log_val_ty: val_types :=
  {| ext_tys := Log_ty; |}.

Section log.
  Existing Instances log_op log_val_ty.

  Inductive log_ext_tys : @val log_op -> (ty * ty) -> Prop :=
  | LogOpType op :
      log_ext_tys (λ: "v", ExternalOp op (Var "v"))%V
                  (match op with
                   | AppendOp => (extT LogT, sliceT_ blockT_ _)
                   | GetOp => (prodT (extT LogT) uint64T, prodT (blockT_ _) boolT)
                   | ResetOp => (extT LogT, unitT)
                   | InitOp => (unitT, prodT (extT LogT) boolT)
                   | OpenOp => (unitT, extT LogT)
                   end).

  Instance log_ty: ext_types log_op :=
    {| val_tys := log_val_ty;
       get_ext_tys := log_ext_tys |}.

  Definition log_state := RecoverableState (list disk.Block).

  Instance log_model : ffi_model := recoverable_model (list disk.Block).

  Existing Instances r_mbind r_fmap.

  Definition read_slice {state} (t:ty) (v:val): transition state (list val) :=
    match v with
    | PairV (#(LitLoc l)) (PairV #(LitInt sz) #(LitInt cap)) =>
      (* TODO: implement *)
      ret []
    | _ => undefined
    end.

  Fixpoint tmapM {Σ A B} (f: A -> transition Σ B) (l: list A) : transition Σ (list B) :=
    match l with
    | [] => ret []
    | x::xs => b ← f x;
             bs ← tmapM f xs;
             ret (b :: bs)
    end.

  (* TODO: implement *)
  Definition to_block (l: list val): option disk.Block := None.

  Definition allocIdent: transition (state*global_state) loc :=
    l ← allocateN 1;
    modify (prod_map (set heap <[l := Free #()]>) id);;
    ret l.

  Definition log_step (op:LogOp) (v:val) : transition (state*global_state) val :=
    match op, v with
    | GetOp, PairV (LitV (LitLoc logPtr)) (LitV (LitInt a)) =>
      openΣ ≫= λ '(log, logPtr_),
      check (logPtr = logPtr_);;
      b ← unwrap (log !! int.nat a);
      l ← allocateN 4096;
      modify (prod_map (state_insert_list l (disk.Block_to_vals b)) id);;
      ret $ #(LitLoc l)
    | ResetOp, LitV (LitLoc logPtr) =>
      openΣ ≫= λ '(_, logPtr_),
      check (logPtr = logPtr_);;
      modifyΣ (fun _ => []);;
      ret $ #()
    | InitOp, LitV LitUnit =>
      logPtr ← allocIdent;
      initTo [] logPtr;;
      ret $ PairV (LitV $ LitLoc logPtr) (LitV $ LitBool true)
    | OpenOp, LitV LitUnit =>
      logPtr ← allocIdent;
      s ← open logPtr;
      ret $ LitV $ LitLoc logPtr
    | AppendOp, PairV (LitV (LitLoc logPtr)) v =>
      openΣ ≫= λ '(_, logPtr_),
      check (logPtr = logPtr_);;
      (* FIXME: append should be non-atomic in the spec because it needs to read
         an input slice (and the slices the input points to). *)
      (* this is absolutely horrendous to reason about *)
      block_slices ← read_slice (slice.T (slice.T byteT)) v;
      block_vals ← tmapM (read_slice (@slice.T _ log_ty byteT)) block_slices;
      new_blocks ← tmapM (unwrap ∘ to_block) block_vals;
      modifyΣ (λ s, s ++ new_blocks);;
      ret $ #()
    | _, _ => undefined
    end.

  Instance log_semantics : ext_semantics log_op log_model :=
    {| ext_step := log_step;
       ext_crash := fun s s' => relation.denote close s s' tt; |}.
End log.

Inductive log_unopen_status := UnInit' | Closed'.
Definition openR := csumR (prodR fracR (agreeR (leibnizO log_unopen_status))) (agreeR (leibnizO loc)).
Definition Log_Opened (l: loc) : openR := Cinr (to_agree l).

Class logG Σ :=
  { logG_open_inG :> inG Σ openR;
    logG_open_name : gname;
    logG_state_inG:> ghost_varG Σ (list disk.Block);
    logG_state_name: gname;
  }.

Class log_preG Σ :=
  { logG_preG_open_inG :> inG Σ openR;
    logG_preG_state_inG:> ghost_varG Σ (list disk.Block);
  }.

Definition logΣ : gFunctors :=
  #[GFunctor openR; ghost_varΣ (list disk.Block)].

Instance subG_logG Σ: subG logΣ Σ → log_preG Σ.
Proof. solve_inG. Qed.

Record log_names :=
  { log_names_open: gname;
    log_names_state: gname; }.

Definition log_get_names {Σ} (lG: logG Σ) :=
  {| log_names_open := logG_open_name; log_names_state := logG_state_name |}.

Definition log_update {Σ} (lG: logG Σ) (names: log_names) :=
  {| logG_open_inG := logG_open_inG;
     logG_open_name := (log_names_open names);
     logG_state_inG := logG_state_inG;
     logG_state_name := (log_names_state names);
  |}.

Definition log_update_pre {Σ} (lG: log_preG Σ) (names: log_names) :=
  {| logG_open_inG := logG_preG_open_inG;
     logG_open_name := (log_names_open names);
     logG_state_inG := logG_preG_state_inG;
     logG_state_name := (log_names_state names);
  |}.

Definition log_open {Σ} {lG :logG Σ} (l: loc) :=
  own (logG_open_name) (Log_Opened l).
Definition log_closed_frag {Σ} {lG :logG Σ} :=
  own (logG_open_name) (Cinl ((1/2)%Qp, to_agree (Closed' : leibnizO log_unopen_status))).
Definition log_closed_auth {Σ} {lG :logG Σ} :=
  own (logG_open_name) (Cinl ((1/2)%Qp, to_agree (Closed' : leibnizO log_unopen_status))).
Definition log_uninit_frag {Σ} {lG :logG Σ} :=
  own (logG_open_name) (Cinl ((1/2)%Qp, to_agree (UnInit' : leibnizO log_unopen_status))).
Definition log_uninit_auth {Σ} {lG :logG Σ} :=
  own (logG_open_name) (Cinl ((1/2)%Qp, to_agree (UnInit' : leibnizO log_unopen_status))).

Definition log_auth {Σ} {lG :logG Σ} (vs: list (disk.Block)) :=
  ghost_var (logG_state_name) (1/2) vs.
Definition log_frag {Σ} {lG :logG Σ} (vs: list (disk.Block)) :=
  ghost_var (logG_state_name) (1/2) vs.

Section log_interp.
  Existing Instances log_op log_model log_val_ty.

  Definition log_ctx {Σ} {lG: logG Σ} (lg: @ffi_state log_model) : iProp Σ :=
    match lg with
    | Opened s l => log_open l ∗ log_auth s
    | Closed s => log_closed_auth ∗ log_auth s
    | UnInit => log_uninit_auth ∗ log_auth []
    | _ => False%I
    end.

  Definition log_start {Σ} {lG: logG Σ} (lg: @ffi_state log_model) : iProp Σ :=
    match lg with
    | Opened s l => log_open l ∗ log_frag s
    | Closed s => log_closed_frag ∗ log_frag s
    | UnInit => log_uninit_frag ∗ log_frag []
    | _ => False%I
    end.

  Definition log_restart {Σ} (lG: logG Σ) (lg: @ffi_state log_model) :=
    match lg with
    | Opened s l => log_open l
    | Closed s => log_closed_frag
    | UnInit => log_uninit_frag
    | _ => False%I
    end.

  Program Instance log_interp : ffi_interp log_model :=
    {| ffiG := logG;
       ffi_local_names := log_names;
       ffi_global_names := unit;
       ffi_get_local_names := @log_get_names;
       ffi_get_global_names := (λ _ _, tt);
       ffi_update_local := @log_update;
       ffi_get_update := _;
       ffi_ctx := @log_ctx;
       ffi_global_ctx _ _ _ := True%I;
       ffi_local_start Σ G w _ := @log_start Σ G w;
       ffi_restart := @log_restart;
       ffi_crash_rel := λ Σ hF1 σ1 hF2 σ2, ⌜ @logG_state_inG _ hF1 = @logG_state_inG _ hF2 ∧
                                           log_names_state (log_get_names hF1) =
                                           log_names_state (log_get_names hF2) ⌝%I;
    |}.
  Next Obligation. intros ? [[]] [] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.
  Next Obligation. intros ? [[]] => //=. Qed.

End log_interp.


Section log_lemmas.
  Context `{lG: logG Σ}.

  Global Instance log_ctx_Timeless lg: Timeless (log_ctx lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance log_start_Timeless lg: Timeless (log_start lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance log_restart_Timeless lg: Timeless (log_restart _ lg).
  Proof. destruct lg; apply _. Qed.

  Global Instance log_open_Persistent (l: loc) : Persistent (log_open l).
  Proof. rewrite /log_open/Log_Opened. apply own_core_persistent. rewrite /CoreId//=. Qed.

  Lemma log_closed_auth_uninit_frag:
    log_closed_auth -∗ log_uninit_frag -∗ False.
  Proof.
    iIntros "Hauth Huninit_frag".
    iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
    inversion Hval as [? Heq%to_agree_op_inv].
    inversion Heq.
  Qed.

  Lemma log_uninit_auth_closed_frag:
    log_uninit_auth -∗ log_closed_frag -∗ False.
  Proof.
    iIntros "Hauth Huninit_frag".
    iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
    inversion Hval as [? Heq%to_agree_op_inv].
    inversion Heq.
  Qed.

  Lemma log_uninit_auth_opened l:
    log_uninit_auth -∗ log_open l -∗ False.
  Proof.
    iIntros "Huninit_auth Hopen".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

  Lemma log_closed_auth_opened l:
    log_closed_auth -∗ log_open l -∗ False.
  Proof.
    iIntros "Huninit_auth Hopen".
    iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
    inversion Hval.
  Qed.

  Lemma log_ctx_unify_closed lg vs:
    log_closed_frag -∗ log_frag vs -∗ log_ctx lg -∗ ⌜ lg = Closed vs ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Hclosed_frag Hstate_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (log_closed_auth_uninit_frag with "[$] [$]") as %[].
    - iDestruct "Hctx" as "(Hclosed_auth&Hstate_auth)".
      rewrite /log_frag/log_auth. unify_ghost_var logG_state_name. done.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hclosed_frag") as %Hval.
      inversion Hval.
  Qed.

  Lemma log_auth_frag_unif vs vs':
    log_auth vs -∗ log_frag vs' -∗ ⌜ vs = vs' ⌝.
  Proof.
    rewrite /log_auth/log_frag. iIntros "H1 H2". by unify_ghost_var logG_state_name.
  Qed.

  Lemma log_open_unif l l':
    log_open l -∗ log_open l' -∗ ⌜ l = l' ⌝.
  Proof.
    rewrite /log_auth/log_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hval.
    rewrite /Log_Opened -Cinr_op in Hval.
    assert (l ≡ l') as Heq.
    { eapply to_agree_op_inv. eauto. }
    inversion Heq. by subst.
  Qed.

  Lemma log_ctx_unify_uninit lg:
    log_uninit_frag -∗ log_ctx lg -∗ ⌜ lg = UnInit ⌝.
  Proof.
    destruct lg; try eauto; iIntros "Huninit_frag Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Huninit_frag") as %Hval.
      inversion Hval as [? Heq%to_agree_op_inv].
      inversion Heq.
    - iDestruct "Hctx" as "(Hauth&Hstate_auth)".
      iDestruct (own_valid_2 with "Hauth Huninit_frag") as %Hval.
      inversion Hval.
  Qed.

  Lemma log_ctx_unify_opened l lg:
    log_open l -∗ log_ctx lg -∗ ⌜ ∃ vs, lg = Opened vs l ⌝.
  Proof.
    destruct lg as [| | |  | vs l']; try eauto; iIntros "Hopen Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (log_open_unif with "[$] [$]") as %Heq.
      subst. iPureIntro; eexists. eauto.
  Qed.

  Lemma log_ctx_unify_opened' l lg vs:
    log_open l -∗ log_frag vs -∗ log_ctx lg -∗ ⌜ lg = Opened vs l ⌝.
  Proof.
    destruct lg as [| | |  | vs' l']; try eauto; iIntros "Hopen Hstate Hctx".
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (own_valid_2 with "Huninit_auth Hopen") as %Hval.
      inversion Hval.
    - iDestruct "Hctx" as "(Huninit_auth&Hstate_auth)".
      iDestruct (log_open_unif with "[$] [$]") as %Heq.
      iDestruct (log_auth_frag_unif with "[$] [$]") as %Heq'.
      subst. eauto.
  Qed.

  Lemma log_uninit_token_open (l: loc):
    log_uninit_auth -∗ log_uninit_frag ==∗ log_open l.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (Log_Opened l) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma log_closed_token_open (l: loc):
    log_closed_auth -∗ log_closed_frag ==∗ log_open l.
  Proof.
    iIntros "Hua Huf".
    iCombine "Hua Huf" as "Huninit".
    rewrite -Cinl_op.
    iMod (own_update _ _ (Log_Opened l) with "Huninit") as "$"; last done.
    { apply: cmra_update_exclusive.
      { apply Cinl_exclusive. rewrite -pair_op frac_op Qp_half_half.
        simpl. apply pair_exclusive_l. apply _.
      }
      { econstructor. }
    }
  Qed.

  Lemma log_state_update vsnew vs1 vs2:
    log_auth vs1 -∗ log_frag vs2 ==∗ log_auth vsnew ∗ log_frag vsnew.
  Proof. apply ghost_var_update_halves. Qed.

End log_lemmas.

From Perennial.goose_lang Require Import adequacy.

Program Instance log_interp_adequacy:
  @ffi_interp_adequacy log_model log_interp log_op log_semantics :=
  {| ffi_preG := log_preG;
     ffiΣ := logΣ;
     subG_ffiPreG := subG_logG;
     ffi_initP := λ σ _, σ = UnInit;
     ffi_update_pre := (λ _ hP names _, @log_update_pre _ hP names);
     ffi_pre_global_start := (λ _ hP names _, True%I);
     ffi_pre_global_ctx := (λ _ hP names _, True%I);
  |}.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. intros ?? [] => //=. Qed.
Next Obligation. rewrite //=. intros ?? [] [] => //=. Qed.
Next Obligation. rewrite //=. Qed.
Next Obligation. rewrite //=. eauto. Qed.
Next Obligation.
  rewrite //=.
  iIntros (Σ hPre σ ?? ->) "_". simpl.
  rewrite /log_uninit_auth/log_uninit_frag/log_frag/log_auth.
  iMod (own_alloc (Cinl (1%Qp, to_agree UnInit') : openR)) as (γ1) "H".
  { repeat econstructor => //=. }
  iMod (ghost_var_alloc ([]: leibnizO (list disk.Block))) as (γ2) "(H2a&H2b)".
  iExists {| log_names_open := γ1; log_names_state := γ2 |}.
  iFrame. iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
Qed.
Next Obligation.
  iIntros (Σ σ σ' g Hcrash Hold) "Hinterp _".
  inversion Hcrash; subst.
  monad_inv. inversion H. subst. inversion H1. subst.
  destruct x; monad_inv.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree UnInit') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| log_names_open := γ1; log_names_state := log_names_state (log_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/log_restart//=.
    iFrame. rewrite left_id. rewrite comm -assoc. iSplitR; first eauto.
    rewrite /log_uninit_auth/log_uninit_frag/log_frag/log_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree Closed') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| log_names_open := γ1; log_names_state := log_names_state (log_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/log_restart//=.
    iFrame. rewrite left_id comm -assoc. iSplitL ""; first eauto.
    rewrite /log_uninit_auth/log_uninit_frag/log_frag/log_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
  - inversion Hcrash. subst. inversion H1. subst. inversion H3. subst.
    inversion H2. subst. inversion H4. subst.
    (* XXX: monad_inv should handle *)
    iMod (own_alloc (Cinl (1%Qp, to_agree Closed') : openR)) as (γ1) "H".
    { repeat econstructor => //=. }
    iExists {| log_names_open := γ1; log_names_state := log_names_state (log_get_names _) |}.
    iDestruct "Hinterp" as "(?&?)". rewrite //=/log_restart//=.
    iFrame. rewrite left_id comm -assoc. iSplitL ""; first eauto.
    rewrite /log_uninit_auth/log_uninit_frag/log_frag/log_auth.
    iModIntro. by rewrite -own_op -Cinl_op -pair_op frac_op Qp_half_half agree_idemp.
Qed.

From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang Require Import refinement_adequacy.
Section spec.

Instance log_spec_ext : spec_ext_op := {| spec_ext_op_field := log_op |}.
Instance log_spec_ffi_model : spec_ffi_model := {| spec_ffi_model_field := log_model |}.
Instance log_spec_ext_semantics : spec_ext_semantics (log_spec_ext) (log_spec_ffi_model) :=
  {| spec_ext_semantics_field := log_semantics |}.
Instance log_spec_ffi_interp : spec_ffi_interp log_spec_ffi_model :=
  {| spec_ffi_interp_field := log_interp |}.
Instance log_spec_ty : ext_types (spec_ext_op_field) := log_ty.
Instance log_spec_interp_adequacy : spec_ffi_interp_adequacy (spec_ffi := log_spec_ffi_interp) :=
  {| spec_ffi_interp_adequacy_field := log_interp_adequacy |}.

Context `{invG Σ}.
Context `{crashG Σ}.
Context `{!refinement_heapG Σ}.

Existing Instance spec_ffi_interp_field.
Existing Instance spec_ext_semantics_field.
Existing Instance spec_ext_op_field.
Existing Instance spec_ffi_model_field.

Implicit Types K: spec_lang.(language.expr) → spec_lang.(language.expr).
Instance logG0 : logG Σ := refinement_spec_ffiG.

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ext_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | [ H1: context[ match world ?σ with | _ => _ end ], Heq: world ?σ = _ |- _ ] =>
          rewrite Heq in H1
        end.

Lemma ghost_step_init_stuck E j K {HCTX: LanguageCtx K} σ g:
  nclose sN_inv ⊆ E →
  (σ.(@world _ log_spec_ffi_model.(@spec_ffi_model_field)) ≠ UnInit) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #()) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ g -∗
  |NC={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    apply head_irreducible_not_atomically; [ by inversion 1 | ].
    intros ??????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)); try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv).
  }
  { solve_ndisj. }
Qed.

Lemma ghost_step_open_stuck E j K {HCTX: LanguageCtx K} σ g:
  nclose sN_inv ⊆ E →
  (∀ vs, σ.(@world _ log_spec_ffi_model.(@spec_ffi_model_field)) ≠ Closed vs) →
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #()) -∗
  source_ctx (CS := spec_crash_lang) -∗
  source_state σ g -∗
  |NC={E}=> False.
Proof.
  iIntros (??) "Hj Hctx H".
  iMod (ghost_step_stuck with "Hj Hctx H") as "[]".
  { eapply stuck_ExternalOp; first (by eauto).
    apply head_irreducible_not_atomically; [ by inversion 1 | ].
    intros ??????.
    repeat (inv_head_step; simpl in *; repeat monad_inv).
    destruct (σ.(world)); try congruence;
    repeat (inv_head_step; simpl in *; repeat monad_inv); eauto.
    eapply H2; eauto.
  }
  { solve_ndisj. }
Qed.

Lemma log_closed_init_false vs E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_closed_frag -∗
  log_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hclosed_frag Hentries Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (log_ctx_unify_closed with "[$] [$] [$]") as %Heq; subst.
  iMod (ghost_step_init_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { congruence. }
Qed.

Lemma log_opened_init_false l E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_open l -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (log_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_init_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma log_init_init_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step_trans. simpl. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** apply fresh_locs_non_null; lia.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** econstructor.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
    }
    { solve_ndisj. }
    iMod (ghost_step_init_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { simpl. congruence. }
  - iMod (ghost_step_init_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_init_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma log_init_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_stuck with "Hj' Hctx H") as "[]".
    { eapply stuck_ExternalOp; first (by eauto).
      apply head_irreducible_not_atomically; [ by inversion 1 | ].
      intros ??????. by repeat (inv_head_step; simpl in H3; repeat monad_inv).
    }
    { solve_ndisj. }
  - iMod (ghost_step_init_stuck with "Hj [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_init_stuck with "Hj [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma ghost_step_log_init E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_uninit_frag -∗
  log_frag [] -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) InitOp #())
  -∗ |NC={E}=>
  ∃ (l: loc), j ⤇ K (#l, #true)%V ∗ log_open l ∗ log_frag [].
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hvals Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (log_ctx_unify_uninit with "[$] [$]") as %Heq.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. simpl. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** apply fresh_locs_non_null; lia.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** econstructor.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (log_uninit_token_open ((fresh_locs (dom _ σ.(heap)))) with "[$] [$]") as "#Hopen".
  iMod (na_heap_alloc _ σ.(heap) (fresh_locs (dom _ σ.(heap))) (#()) (Reading O) with "Hσ") as "(Hσ&?)".
  { rewrite //=. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { auto. }
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _, _. iFrame "H".  iFrame. iFrame "Hopen". rewrite fresh_alloc_equiv_null_non_alloc. iFrame. }
  iModIntro. iExists _. iFrame "Hopen". iFrame.
Qed.

Lemma log_uninit_open_false vs E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_uninit_frag -∗
  log_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hclosed_frag Hentries Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (log_ctx_unify_uninit with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { congruence. }
Qed.

Lemma log_opened_open_false l E j K {HCTX: LanguageCtx K}:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_open l -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hopened Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  simpl.
  iDestruct (log_ctx_unify_opened with "[$] [$]") as %Heq; subst.
  iMod (ghost_step_open_stuck with "[$] [$] [$]") as "[]".
  { solve_ndisj. }
  { destruct Heq as (?&Heq). by rewrite Heq. }
Qed.

Lemma log_open_open_false E j K {HCTX: LanguageCtx K} j' K' {HCTX': LanguageCtx K'}:
  nclose sN ⊆ E →
  spec_ctx -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #()) -∗
  j' ⤇ K' (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #()) -∗ |NC={E}=>
  False.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Hj Hj'".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iEval (simpl) in "Hffi".
  destruct σ.(world) eqn:Heq; rewrite Heq; try (iDestruct "Hffi" as %[]).
  - iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
  - iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
    { apply head_prim_step_trans. simpl. econstructor.
      * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
        ** apply fresh_locs_non_null; lia.
        ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
        ** econstructor.
        ** simpl. rewrite Heq. repeat econstructor.
      * repeat econstructor.
    }
    { solve_ndisj. }
    iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { simpl. congruence. }
  - iMod (ghost_step_open_stuck with "Hj' [$] [$]") as "[]".
    { solve_ndisj. }
    { congruence. }
Qed.

Lemma ghost_step_log_open E j K {HCTX: LanguageCtx K} vs:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_closed_frag -∗
  log_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) OpenOp #())
  -∗ |NC={E}=>
  ∃ (l: loc), j ⤇ K #l%V ∗ log_open l ∗ log_frag vs.
Proof.
  iIntros (?) "(#Hctx&#Hstate) Huninit_frag Hvals Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (log_ctx_unify_closed with "[$] [$] [$]") as %Heq.
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. simpl. econstructor.
    * eexists _ (fresh_locs (dom (gset loc) σ.(heap))); repeat econstructor.
      ** apply fresh_locs_non_null; lia.
      ** hnf; intros. apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh.
      ** econstructor.
      ** simpl. rewrite Heq. repeat econstructor.
    * repeat econstructor.
  }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (log_closed_token_open ((fresh_locs (dom _ σ.(heap)))) with "[$] [$]") as "#Hopen".
  iMod (na_heap_alloc _ σ.(heap) (fresh_locs (dom _ σ.(heap))) (#()) (Reading O) with "Hσ") as "(Hσ&?)".
  { rewrite //=. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { apply (not_elem_of_dom (D := gset loc)). by apply fresh_locs_fresh. }
  { auto. }
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _, _. iFrame "H".  iFrame. iFrame "Hopen". rewrite fresh_alloc_equiv_null_non_alloc. iFrame. }
  iModIntro. iExists _. iFrame "Hopen". iFrame.
Qed.

Lemma ghost_step_log_reset E j K {HCTX: LanguageCtx K} l vs:
  nclose sN ⊆ E →
  spec_ctx -∗
  log_open l -∗
  log_frag vs -∗
  j ⤇ K (ExternalOp (ext := @spec_ext_op_field log_spec_ext) ResetOp #l)
  -∗ |NC={E}=>
  j ⤇ K #()%V ∗log_frag [].
Proof.
  iIntros (?) "(#Hctx&#Hstate) #Hopen Hvals Hj".
  iInv "Hstate" as (σ g) "(>H&Hinterp)" "Hclo".
  iDestruct "Hinterp" as "(>Hσ&>Hffi&Hrest)".
  iDestruct (log_ctx_unify_opened with "[$] [$]") as %Heq.
  destruct Heq as (vs'&Heq).
  iMod (ghost_step_lifting with "Hj Hctx H") as "(Hj&H&_)".
  { apply head_prim_step_trans. repeat (eauto || monad_simpl || rewrite Heq || econstructor || simpl). }
  { solve_ndisj. }
  simpl. rewrite Heq.
  iDestruct "Hffi" as "(Huninit_auth&Hvals_auth)".
  iMod (log_state_update [] with "[$] [$]") as "(Hvals_auth&?)".
  iMod ("Hclo" with "[Hσ Hvals_auth H Hrest]") as "_".
  { iNext. iExists _, _. iFrame "H". iFrame. iFrame "Hopen". }
  iModIntro. iFrame.
Qed.

End spec.
