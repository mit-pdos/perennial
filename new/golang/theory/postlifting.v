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
    wp_alloc : (∀ {s E}, {{{ True }}}
                           alloc t #() @ s ; E
                         {{{ l, RET #l; l ↦ (zero_val V) }}});
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
Global Arguments wp_alloc {_ _ _ _ _ _} [_ _ _ _ _ _ _ _] (Φ).
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

Global Instance pure_wp_is_go_op op t args v `{!go.IsGoOp op t args v} :
  PureWp True (go_op op t args) v.
Proof.
  rewrite go.is_go_op.
  iIntros "% % * _ % HΦ". wp_pure_lc "?". wp_pures. by iApply "HΦ".
Qed.

Lemma wp_GoPrealloc {stk E} :
  {{{ True }}}
    GoPrealloc #() @ stk; E
  {{{ (l : loc), RET #l; True }}}.
Proof.
  iIntros (?) "_ HΦ". wp_apply (wp_GoInstruction []).
  { intros. exists #null. repeat econstructor. rewrite go.go_prealloc_step.
    repeat econstructor. }
  simpl. iIntros "* %Hstep". rewrite go.go_prealloc_step in Hstep.
  destruct Hstep as [[]]. subst. iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
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

Global Instance wp_InternalMapLookup mv k:
  PureWp True (InternalMapLookup (mv, k)%V) (let '(ok, v) := map_lookup mv k in (v, #ok)).
Proof. solve_pure. Qed.

Global Instance wp_InternalMapInsert mv k v:
  PureWp True (InternalMapInsert (mv, k, v)%V) (map_insert mv k v).
Proof. solve_pure. Qed.

Global Instance wp_InternalMapDelete mv k :
  PureWp True (InternalMapDelete (mv, k)%V) (map_delete mv k).
Proof. solve_pure. Qed.

Global Instance wp_InternalMapMake (v : val) :
  PureWp True (InternalMapMake v) (map_empty v).
Proof. solve_pure. Qed.

Global Instance pure_wp_CompositeLiteral t (v : val) :
  PureWp True (CompositeLiteral t v) (composite_literal t v).
Proof. solve_pure. Qed.

Class IsGoEq t v1 v2 (b : bool) : Prop :=
  {
    wp_go_eq stk E Φ : Φ #b -∗ WP (go.go_eq t v1 v2) @ stk; E {{ Φ }}
  }.
Global Arguments wp_go_eq [t].

Global Instance pure_wp_eq_ t v1 v2 b `{!go.IsComparable t} :
  IsGoEq t v1 v2 b → PureWp True (GoEquals t (v1, v2)%V) #b | 0.
Proof.
  iIntros "%%*%% HΦ". wp_pure_lc "?". wp_bind (go.go_eq _ _ _). iApply wp_go_eq. by iApply "HΦ".
Qed.

Global Instance is_go_eq_pointer t (l1 l2 : loc) :
  IsGoEq (go.PointerType t) #l1 #l2 (bool_decide (l1 = l2)).
Proof. constructor. rewrite go.go_eq_pointer. iIntros "* ?". by wp_pures. Qed.

Global Instance is_go_eq_channel t dir (l1 l2 : chan.t) :
  IsGoEq (go.ChannelType t dir) #l1 #l2 (bool_decide (l1 = l2)).
Proof. constructor. rewrite go.go_eq_channel. iIntros "* ?". by wp_pures. Qed.

Global Instance is_go_eq_interface elems t v1 v2 b {Heq : IsGoEq t v1 v2 b}  :
  IsGoEq (go.InterfaceType elems) #(interface.mk t v1) #(interface.mk t v2)
    b.
Proof.
  constructor. rewrite go.go_eq_interface. iIntros "*?". rewrite decide_True //.
  by iApply wp_go_eq.
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
