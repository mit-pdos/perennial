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

#[global] Instance countable_interface {ext : ffi_syntax} : Countable interface.t.
Proof.
Admitted.

Section underlying_instances.
Context {ext : ffi_syntax} {go_lctx : GoLocalContext}
  {go_gctx : GoGlobalContext} `{!GoSemanticsFunctions}.

#[global] Instance underlying_eq t : t ≤u t | 100.
Proof. done. Qed.

#[global] Instance unfold_to_underlying_eq `{!t <u t'} : t ≤u t'.
Proof. constructor. rewrite go.underlying_unfold //. Qed.

#[global] Instance is_underlying_unfold `{!t <u t'} `{!t' ↓u tunder} : t ↓u tunder.
Proof. constructor. rewrite go.underlying_unfold. apply go.is_underlying. Qed.

Lemma underlying_trivial t : t ↓u (underlying t).
Proof. done. Qed.
End underlying_instances.
#[global] Hint Extern 0 (go.NotNamed _) => (constructor; refine I) : typeclass_instances.
#[global] Hint Extern 0 (go.NotInterface _) => (constructor; refine I) : typeclass_instances.

Section into_val_defs.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Class TypedPointsto (V : Type) :=
{
  typed_pointsto_def (l : loc) (v : V) (dq : dfrac) : iProp Σ;
  typed_pointsto_def_dfractional l v : DFractional (typed_pointsto_def l v);
  typed_pointsto_def_timeless l v dq : Timeless (typed_pointsto_def l v dq);
  typed_pointsto_agree : (∀ l dq1 dq2 v1 v2,
                            typed_pointsto_def l v1 dq1 -∗
                            typed_pointsto_def l v2 dq2 -∗
                            ⌜ v1 = v2 ⌝)
}.

Program Definition typed_pointsto := sealed @typed_pointsto_def.
Definition typed_pointsto_unseal : typed_pointsto = _ := seal_eq _.
Global Arguments typed_pointsto {_ _} (l v dq).
Notation "l ↦ dq v" := (typed_pointsto l v%V dq)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

(* For empty struct types. *)
Global Instance true_dfractional : DFractional (λ dq, True%I : iProp Σ).
Proof. apply _. Qed.

Global Instance typed_pointsto_dfractional_eta `{!TypedPointsto V} l (v : V) :
  DFractional (λ dq, typed_pointsto l v dq).
Proof. rewrite typed_pointsto_unseal. apply typed_pointsto_def_dfractional. Qed.

Global Instance typed_pointsto_dfractional `{!TypedPointsto V} l (v : V) :
  DFractional (typed_pointsto l v).
Proof. rewrite typed_pointsto_unseal. apply typed_pointsto_def_dfractional. Qed.

Global Instance typed_pointsto_timeless `{!TypedPointsto V} l dq (v : V) :
  Timeless (typed_pointsto l v dq).
Proof. rewrite typed_pointsto_unseal. apply typed_pointsto_def_timeless. Qed.

Global Instance typed_pointsto_as_dfractional `{!TypedPointsto V} l dq (v : V) :
  AsDFractional (typed_pointsto l v dq) (λ dq, typed_pointsto l v dq) dq.
Proof. split; try done. apply _. Qed.

(* TODO: move higher upstream. *)
Global Instance as_dfractional_persistent P Φ `{AsDFractional _ (P : iProp Σ) Φ DfracDiscarded} :
  Persistent P.
Proof.
  erewrite as_dfractional. apply dfractional_persistent.
  unshelve eapply as_dfractional_dfractional; try eassumption.
Qed.

Global Instance typed_pointsto_combine_sep_gives `{!TypedPointsto V} l dq1 dq2 (v1 v2 : V) :
  CombineSepGives (typed_pointsto l v1 dq1) (typed_pointsto l v2 dq2) (⌜ v1 = v2 ⌝).
Proof.
  rewrite typed_pointsto_unseal /CombineSepGives. iIntros "[H1 H2]".
  iDestruct (typed_pointsto_agree with "H1 H2") as %Heq. by iModIntro.
Qed.

Global Instance typed_pointsto_combine_sep_as `{!TypedPointsto V} l dq1 dq2 (v1 v2 : V) :
  CombineSepAs (typed_pointsto l v1 dq1) (typed_pointsto l v2 dq2)
    (typed_pointsto l v1 (dq1 ⋅ dq2)) | 60.
Proof.
  rewrite /CombineSepAs. iIntros "[H1 H2]".
  iCombine "H1 H2" gives %->.
  iCombine "H1 H2" as "$".
Qed.

(** [IntoValTyped V t] provides proofs that loading and storing [t] respects
    the typed points-to for `V`.

    [typed_pointsto_def] is in [IntoValProof] rather than here because `l ↦ v`
    not explicitly mention `t`, and there can be multiple `t`s for a single `V`
    (e.g. int64 and uint64 both have w64). *)
Class IntoValTypedUnderlying (V : Type) (t_under : go.type) `{!ZeroVal V} `{!TypedPointsto V}
                             `{!GoSemanticsFunctions} :=
  {
    wp_alloc_def : (∀ [s E] `[!t ↓u t_under] (v : V),
                      {{{ True }}}
                        GoAlloc t #v @ s ; E
                      {{{ l, RET #l; l ↦ v }}});
    wp_load_def : (∀ [s E] `[!t ↓u t_under] l dq (v : V),
                 {{{ l ↦{dq} v }}}
                    ![t] #l @ s ; E
                 {{{ RET #v; l ↦{dq} v }}});
    wp_store_def : (∀ [s E] `[!t ↓u t_under] l (v w : V),
                  {{{ l ↦ v }}}
                    GoStore t (#l, #w)%V @ s ; E
                  {{{ RET #(); l ↦ w }}});
    type_repr_def : go.TypeReprUnderlying t_under V;
  }.
(* [t] should not be an evar before doing typeclass search *)
Global Hint Mode IntoValTypedUnderlying - + - - -: typeclass_instances.

Class IntoValTyped (V : Type) (t : go.type) `{!ZeroVal V} `{!TypedPointsto V}
  `{!GoSemanticsFunctions} :=
  {
    wp_alloc : (∀ [s E] (v : V),
                      {{{ True }}}
                        GoAlloc t #v @ s ; E
                      {{{ l, RET #l; l ↦ v }}});
    wp_load : (∀ [s E] l dq (v : V),
                 {{{ l ↦{dq} v }}}
                   ![t] #l @ s ; E
                 {{{ RET #v; l ↦{dq} v }}});
    wp_store : (∀ [s E] l (v w : V),
                  {{{ l ↦ v }}}
                    GoStore t (#l, #w)%V @ s ; E
                  {{{ RET #(); l ↦ w }}});
    #[global] type_repr :: TypeRepr t V;
  }.

Global Instance underlying_to_into_val_typed (V : Type) (t_under : go.type) `{!ZeroVal V} `{!TypedPointsto V}
  `{!GoSemanticsFunctions} {pre_sem : go.PreSemantics} t :
  t ↓u t_under →
  IntoValTypedUnderlying V t_under →
  IntoValTyped V t.
Proof.
  constructor.
  { intros. unshelve eapply wp_alloc_def; try tc_solve; tc_solve. }
  { intros. unshelve eapply wp_load_def; try tc_solve; tc_solve. }
  { intros. unshelve eapply wp_store_def; try tc_solve; tc_solve. }
  { pose proof @type_repr_def. tc_solve. }
Qed.

End into_val_defs.

Global Arguments wp_alloc {_ _ _ _ _ _} [_ _ _ _ _ _ _ _ _] (Φ).
Global Arguments wp_load {_ _ _ _ _ _} [_ _ _ _ _ _ _ _] (l dq v Φ).
Global Arguments wp_store {_ _ _ _ _ _} [_ _ _ _ _ _ _ _] (l v w Φ).

Global Hint Mode TypedPointsto - ! : typeclass_instances.

Global Notation "l ↦ dq v" := (typed_pointsto l v%V dq)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Section go_wps.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Global Instance pure_wp_go_step_det i v e :
  ⟦i, v⟧ ⤳ e →
  PureWp True (i v) e.
Proof.
  iIntros "% % * _ % HΦ". iApply wp_GoInstruction.
  { intros. repeat econstructor. rewrite go.is_go_step_det go.is_go_step_pure_det //. }
  iNext. iIntros "* %Hstep".
  rewrite go.is_go_step_det go.is_go_step_pure_det in Hstep. inv Hstep.
  iIntros "H"; iIntros "$ !>"; by iApply "HΦ".
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

Lemma wp_GlobalAlloc v t `[!t ↓u t_under] `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t} :
  {{{ True }}}
    go.GlobalAlloc v t #()
  {{{ RET #(); global_addr v ↦ (zero_val V) }}}.
Proof.
  rewrite go.GlobalAlloc_unseal. iIntros (?) "_ HΦ".
  wp_call. wp_pures.
  wp_apply wp_alloc.
  iIntros (?) "Hl". wp_pures.
  rewrite bool_decide_decide. destruct decide; wp_pures.
  - subst. iApply "HΦ". iFrame.
  - wp_apply wp_AngelicExit.
Qed.

End go_wps.

Section mem_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

(* Helper lemmas for establishing [IntoValTyped] *)
Lemma _internal_wp_untyped_start_read l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    StartRead #l @ s; E
  {{{ RET v;
      (∀ Ψ, (heap_pointsto l dq v -∗ Ψ #()) -∗ WP FinishRead #l @ s ; E {{ Ψ }})
    }}}.
Proof.
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
  iIntros "% Hl HΦ". wp_call.
  wp_apply (wp_prepare_write with "Hl"). iIntros "[Hl Hl']".
  wp_pures. by iApply (wp_finish_store with "[$Hl $Hl']").
Qed.

End mem_lemmas.
Section typed_pointsto_instances.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

Program Global Instance typed_pointsto_unit : TypedPointsto () :=
  {| typed_pointsto_def l v dq := (True%I : iProp Σ) |}.
Final Obligation.
Proof. iIntros "* H1 H2". destruct v1, v2. done. Qed.

Program Global Instance typed_pointsto_loc : TypedPointsto loc :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w64 : TypedPointsto w64 :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w32 : TypedPointsto w32 :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w16 : TypedPointsto w16 :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_w8 : TypedPointsto w8 :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_bool : TypedPointsto bool :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_string : TypedPointsto go_string :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_slice : TypedPointsto slice.t :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_interface : TypedPointsto interface.t :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Program Global Instance typed_pointsto_func : TypedPointsto func.t :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof.
  iIntros "* H1 H2". iCombine "H1 H2" gives %Heq.
  iPureIntro. rewrite !go.into_val_unfold /= in Heq.
  destruct v1, v2. naive_solver.
Qed.

Program Global Instance typed_pointsto_proph_id : TypedPointsto proph_id :=
  {| typed_pointsto_def l v dq := heap_pointsto l dq #v |}.
Final Obligation.
Proof. iIntros "* H1 H2". iCombine "H1 H2" gives %Heq. naive_solver. Qed.

Existing Class go.is_primitive.
#[local] Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.
Existing Class go.is_primitive_zero_val.
#[local] Hint Extern 1 (go.is_primitive_zero_val ?t ?v) => constructor : typeclass_instances.

Ltac solve_wp_alloc :=
  iIntros "* _ HΦ";
  rewrite typed_pointsto_unseal /=;
  wp_pures; by wp_apply wp_alloc_untyped.

Ltac solve_wp_load :=
  iIntros "* Hl HΦ";
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_read with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Ltac solve_wp_store :=
  iIntros "* Hl HΦ";
  wp_pures; rewrite typed_pointsto_unseal /=;
  wp_apply (_internal_wp_untyped_store with "Hl");
  iIntros "Hl"; by iApply "HΦ".

Ltac solve_into_val_typed :=
  pose proof (go.tagged_steps internal);
  constructor; intros; [solve_wp_alloc|solve_wp_load|solve_wp_store|tc_solve].

Global Instance into_val_typed_loc t : IntoValTypedUnderlying loc (go.PointerType t).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_func sig : IntoValTypedUnderlying func.t (go.FunctionType sig).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_slice t : IntoValTypedUnderlying slice.t (go.SliceType t).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_interface elems : IntoValTypedUnderlying interface.t (go.InterfaceType elems).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_chan t b : IntoValTypedUnderlying chan.t (go.ChannelType b t).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_map k v : IntoValTypedUnderlying map.t (go.MapType k v).
Proof. solve_into_val_typed. Qed.

Lemma typed_pointsto_split `{!TypedPointsto V} l (v : V) dq :
  l ↦{dq} v ⊢@{iProp Σ} typed_pointsto_def l v dq.
Proof. rewrite typed_pointsto_unseal //. Qed.

Lemma typed_pointsto_combine `{!TypedPointsto V} l (v : V) dq :
  typed_pointsto_def l v dq ⊢@{iProp Σ} l ↦{dq} v.
Proof. rewrite typed_pointsto_unseal //. Qed.

End typed_pointsto_instances.

Tactic Notation "iStructNamed" constr(H) :=
  iDestruct (typed_pointsto_split with H) as H;
  iNamed H.

Tactic Notation "iStructNamedSuffix" constr(H) constr(suff):=
  iDestruct (typed_pointsto_split with H) as H;
  iNamedSuffix H suff.

Tactic Notation "iStructNamedPrefix" constr(H) constr(pref) :=
  iDestruct (typed_pointsto_split with H) as H;
  iNamedPrefix H pref.

Ltac solve_typed_pointsto_agree :=
  intros; (destruct &v1, &v2); simpl; iIntros "H1 H2";
  let field := (iDestruct "H1" as "[H H1]"; iDestruct "H2" as "[H' H2]";
                iCombine "H H'" gives "->"; iClear "H H'") in
  repeat field; done.
