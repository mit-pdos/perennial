From Perennial.Helpers Require Export List ListLen Fractional NamedProps.
(* Some of these imports (like the helpers) are for files that import postlifting.v *)
From iris.bi.lib Require Import fractional.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.experiments Require Export glob.
From New.golang.theory Require Export proofmode.
From Perennial.Helpers Require Export List.
From RecordUpdate Require Export RecordSet.
From Perennial Require Export base.
Export RecordSetNotations.

Section into_val_defs.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Class TypedPointsto (V : Type) :=
{
  typed_pointsto_def (l : loc) (dq : dfrac) (v : V) : iProp Σ;
  typed_pointsto_def_dfractional l v : DFractional (λ dq, typed_pointsto_def l dq v);
  typed_pointsto_def_timeless l dq v : Timeless (typed_pointsto_def l dq v);
  typed_pointsto_agree : (∀ l dq1 dq2 v1 v2,
                            typed_pointsto_def l dq1 v1 -∗
                            typed_pointsto_def l dq2 v2 -∗
                            ⌜ v1 = v2 ⌝)
}.

Program Definition typed_pointsto := sealed @typed_pointsto_def.
Definition typed_pointsto_unseal : typed_pointsto = _ := seal_eq _.
Global Arguments typed_pointsto {_ _} (l dq v).
Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Global Instance typed_pointsto_dfractional `{TypedPointsto V} l (v : V) :
  DFractional (λ dq, typed_pointsto l dq v).
Proof. rewrite typed_pointsto_unseal. apply typed_pointsto_def_dfractional. Qed.

Global Instance typed_pointsto_timeless `{TypedPointsto V} l dq (v : V) :
  Timeless (typed_pointsto l dq v).
Proof. rewrite typed_pointsto_unseal. apply typed_pointsto_def_timeless. Qed.

Global Instance typed_pointsto_as_dfractional `{TypedPointsto V} l dq (v : V) :
  AsDFractional (typed_pointsto l dq v) (λ dq, typed_pointsto l dq v) dq.
Proof. split; try done. apply _. Qed.

(* TODO: move higher upstream. *)
Global Instance as_dfractional_persistent P Φ `{AsDFractional _ (P : iProp Σ) Φ DfracDiscarded} :
  Persistent P.
Proof.
  erewrite as_dfractional. apply dfractional_persistent.
  unshelve eapply as_dfractional_dfractional; try eassumption.
Qed.

Global Instance typed_pointsto_combine_sep_gives `{TypedPointsto V} l dq1 dq2  (v1 v2 : V) :
  CombineSepGives (typed_pointsto l dq1 v1)
    (typed_pointsto l dq2 v2) (⌜ v1 = v2 ⌝).
Proof.
  rewrite typed_pointsto_unseal /CombineSepGives. iIntros "[H1 H2]".
  iDestruct (typed_pointsto_agree with "H1 H2") as %Heq. by iModIntro.
Qed.

(** [IntoValTyped V t] provides proofs that loading and storing [t] respects
    the typed points-to for `V`.

    [typed_pointsto_def] is in [IntoValProof] rather than here because `l ↦ v`
    not explicitly mention `t`, and there can be multiple `t`s for a single `V`
    (e.g. int64 and uint64 both have w64). *)
Class IntoValTyped (V : Type) (t : go.type) `{!ZeroVal V} `{!TypedPointsto V}
  `{!GoSemanticsFunctions} :=
  {
    wp_alloc : (∀ {s E} (v : V), {{{ True }}}
                           alloc t #v @ s ; E
                         {{{ l, RET #l; l ↦ v }}});
    wp_load : (∀ {s E} l dq (v : V),
                 {{{ l ↦{dq} v }}}
                   load t #l @ s ; E
                 {{{ RET #v; l ↦{dq} v }}});
    wp_store : (∀ {s E} l (v w : V),
                  {{{ l ↦ v }}}
                    store t #l #w @ s ; E
                  {{{ RET #(); l ↦ w }}});
  }.
End into_val_defs.

(* [t] should not be an evar before doing typeclass search *)
Global Hint Mode IntoValTyped - - - - - - - ! - - - : typeclass_instances.

Global Hint Mode TypedPointsto - ! : typeclass_instances.

(* Non-maximally insert the arguments related to [t], [IntoVal], etc., so that
   typeclass search won't be invoked until wp_apply actually unifies the [t]. *)
Global Arguments wp_alloc {_ _ _ _ _ _} [_ _ _ _ _ _ _ _ _] (Φ).
Global Arguments wp_load {_ _ _ _ _ _} [_ _ _ _ _ _ _ _] (l dq v Φ).
Global Arguments wp_store {_ _ _ _ _ _} [_ _ _ _ _ _ _ _] (l v w Φ).

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Section go_wps.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.

Global Instance pure_wp_go_step_det i v e :
  go.IsGoStepPureDet i v e →
  PureWp True (i v) e.
Proof.
  iIntros "% % * _ % HΦ". iApply wp_GoInstruction.
  { intros. repeat econstructor. rewrite go.is_go_step_det go.is_go_step_pure_det //. }
  iNext. iIntros "* %Hstep".
  rewrite go.is_go_step_det go.is_go_step_pure_det in Hstep. inv Hstep.
  iIntros "H"; iIntros "$ !>"; by iApply "HΦ".
Qed.

Global Instance pure_wp_go_expr_eq e e' `{!go.GoExprEq e e'} :
  PureWp True e e'.
Proof.
  rewrite -> go.go_expr_eq. iIntros "% % * _ % HΦ". wp_pure_lc "?". wp_pures. by iApply "HΦ".
Qed.

Lemma wp_GoPrealloc {stk E} :
  {{{ True }}}
    GoPrealloc #() @ stk; E
  {{{ (l : loc), RET #l; ⌜ l ≠ null ⌝ }}}.
Proof.
  iIntros (?) "_ HΦ". wp_apply (wp_GoInstruction []).
  { intros. exists #(Loc 1 1). repeat econstructor. rewrite go.go_prealloc_step.
    repeat econstructor. done. }
  simpl. iIntros "* %Hstep". rewrite go.go_prealloc_step in Hstep.
  destruct Hstep as [[? []]]. subst. iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_AngelicExit Φ s E :
  ⊢ WP AngelicExit #() @ s; E {{ Φ }}.
Proof.
  iLöb as "IH".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. rewrite go.angelic_exit_step //. }
  simpl. iIntros "* %Hstep". rewrite go.angelic_exit_step in Hstep. inv Hstep.
  iIntros "_ $ !>". subst. iApply "IH".
Qed.

Lemma wp_PackageInitCheck {stk E} (pkg : go_string) (s : gmap go_string bool) :
  {{{ own_go_state s }}}
    PackageInitCheck pkg #() @ stk; E
  {{{ RET #(default false (s !! pkg)); own_go_state s }}}.
Proof.
  iIntros (?) "Hown HΦ".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  simpl. iIntros "* %Hstep". intuition. simplify_eq.
  iIntros "_ Hauth". iCombine "Hauth Hown" gives %Heq. subst.
  iModIntro. iFrame. simpl. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_PackageInitStart {stk E} (pkg : go_string) (s : gmap go_string bool) :
  {{{ own_go_state s }}}
    PackageInitStart pkg #() @ stk; E
  {{{ RET #(); own_go_state (<[ pkg := false ]> s) }}}.
Proof.
  iIntros (?) "Hown HΦ".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  simpl. iIntros "* %Hstep". intuition. simplify_eq.
  iIntros "_ Hauth". iCombine "Hauth Hown" gives %Heq. subst.
  iMod (own_go_state_update with "[$] [$]") as "[Hown Hauth]".
  iModIntro. iFrame. simpl. wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_PackageInitFinish {stk E} (pkg : go_string) (s : gmap go_string bool) :
  {{{ own_go_state s }}}
    PackageInitFinish pkg #() @ stk; E
  {{{ RET #(); own_go_state (<[ pkg := true ]> s) }}}.
Proof.
  iIntros (?) "Hown HΦ".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  simpl. iIntros "* %Hstep". intuition. simplify_eq.
  iIntros "_ Hauth". iCombine "Hauth Hown" gives %Heq. subst.
  iMod (own_go_state_update with "[$] [$]") as "[Hown Hauth]".
  iModIntro. iFrame. simpl. wp_pures.
  by iApply "HΦ".
Qed.

Global Instance pure_wp_go_op_equals_comparable t (v1 v2 : val) `{!go.IsComparable t} :
  PureWp True (go_op GoEquals t (v1, v2)%V) (go_eq t v1 v2).
Proof.
  iIntros "%%*%% HΦ". pose proof go.is_comparable.
  wp_pure_lc "?". wp_pures. by iApply "HΦ".
Qed.

Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ #() -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp HΦ".
  wp_apply (lifting.wp_fork with "[$Hwp]").
  replace (LitV LitUnit) with #().
  { iFrame "HΦ". }
  rewrite go.into_val_unfold //.
Qed.

(* use new goose's to_val for the return value *)
Lemma wp_ArbitraryInt s E  :
  {{{ True }}}
    ArbitraryInt @ s; E
  {{{ (x : w64), RET #x; True }}}.
Proof.
  iIntros "% _ HΦ".
  wp_apply (lifting.wp_ArbitraryInt).
  iIntros (x) "_".
  replace (LitV x) with #x.
  { by iApply "HΦ". }
  rewrite go.into_val_unfold //.
Qed.

End go_wps.

Section mem_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.
(* Helper lemmas for establishing [IntoValTyped] *)

Lemma _internal_wp_alloc_untyped stk E v :
  {{{ True }}} go.ref_one (Val v) @ stk; E {{{ l, RET #l; heap_pointsto l (DfracOwn 1) v }}}.
Proof.
  iIntros "% _ HΦ". wp_call. wp_apply wp_alloc_untyped; first done.
  iIntros (?) "Hl". wp_pures.
  wp_call.
  wp_apply (wp_prepare_write with "Hl"). iIntros "[Hl Hl']".
  wp_pures. wp_apply (wp_finish_store with "[$Hl $Hl']"). iIntros "Hl".
  wp_pures. rewrite !go.into_val_unfold. iApply "HΦ". iFrame.
Qed.

Lemma _internal_wp_untyped_atomic_load l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    ! #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof. rewrite !go.into_val_unfold. apply lifting.wp_load. Qed.

Lemma _internal_wp_untyped_start_read l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    StartRead #l @ s; E
  {{{ RET v;
      (∀ Ψ, (heap_pointsto l dq v -∗ Ψ #()) -∗ WP FinishRead #l @ s ; E {{ Ψ }})
    }}}.
Proof.
  rewrite !go.into_val_unfold.
  iIntros "% Hl HΦ".
  wp_apply (wp_start_read with "Hl"). iIntros "[? ?]".
  iApply "HΦ".
  iIntros "% HΨ".
  wp_apply (wp_finish_read with "[$]").
  iIntros "?". wp_pures. by iApply "HΨ".
Qed.

Lemma _internal_wp_untyped_read l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    Read #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof.
  rewrite !go.into_val_unfold.
  iIntros "% Hl HΦ".
  wp_call.
  wp_apply (wp_start_read with "Hl"). iIntros "[? ?]".
  wp_pures.
  wp_apply (wp_finish_read with "[$]").
  iIntros "?". wp_pures. by iApply "HΦ".
Qed.

Lemma _internal_wp_untyped_store l v v' s E :
  {{{ ▷ heap_pointsto l (DfracOwn 1) v }}}
    #l <- v' @ s; E
  {{{ RET #(); heap_pointsto l (DfracOwn 1) v' }}}.
Proof.
  rewrite !go.into_val_unfold. iIntros "% Hl HΦ". wp_call.
  wp_apply (wp_prepare_write with "Hl"). iIntros "[Hl Hl']".
  wp_pures. by iApply (wp_finish_store with "[$Hl $Hl']").
Qed.

End mem_lemmas.
Section typed_pointsto_instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.

Program Global Instance typed_pointsto_loc : TypedPointsto loc :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w64 : TypedPointsto w64 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w32 : TypedPointsto w32 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w16 : TypedPointsto w16 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w8 : TypedPointsto w8 :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_bool : TypedPointsto bool :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_string : TypedPointsto go_string :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_slice : TypedPointsto slice.t :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_func : TypedPointsto func.t :=
  {| typed_pointsto_def l dq v := heap_pointsto l dq #v |}.
Final Obligation.
Proof.
  iIntros "* H1 H2". iCombine "H1 H2" gives %Heq.
  iPureIntro. rewrite !go.into_val_unfold /= in Heq.
  destruct v1, v2. naive_solver.
Qed.

Existing Class go.is_primitive.
#[local] Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.
Existing Class go.is_primitive_zero_val.
#[local] Hint Extern 1 (go.is_primitive_zero_val ?t ?v) => constructor : typeclass_instances.

Ltac solve_wp_alloc :=
  iIntros "* _ HΦ";
  rewrite go.alloc_primitive typed_pointsto_unseal /=;
  wp_pures; by wp_apply _internal_wp_alloc_untyped.

Ltac solve_wp_load :=
  iIntros "* Hl HΦ";
  rewrite go.load_primitive;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_read with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Ltac solve_wp_store :=
  iIntros "* Hl HΦ";
  rewrite go.store_primitive;
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_store with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Ltac solve_into_val_typed := constructor; [solve_wp_alloc|solve_wp_load|solve_wp_store].

Global Instance into_val_typed_loc t : IntoValTyped loc (go.PointerType t).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_func sig : IntoValTyped func.t (go.FunctionType sig).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_slice t : IntoValTyped slice.t (go.SliceType t).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_chan t b : IntoValTyped chan.t (go.ChannelType b t).
Proof. solve_into_val_typed. Qed.

End typed_pointsto_instances.

Tactic Notation "iStructNamed" constr(H) :=
  iEval (typed_pointsto_unseal) in H;
  iNamed H.

Tactic Notation "iStructNamedSuffix" constr(H) constr(suff):=
  iEval (rewrite typed_pointsto_unseal /=) in H;
  iNamedSuffix H suff.

Tactic Notation "iStructNamedPrefix" constr(H) constr(pref) :=
  iEval (rewrite typed_pointsto_unseal /=) in H;
  iNamedPrefix H pref.
