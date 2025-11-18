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

Section unfolding_defs.
Context {ext : ffi_syntax} {go_ctx : GoContext}.
Class FuncUnfold f type_args f_impl : Prop :=
  {
    func_unfold : #(functions f type_args) = f_impl;
  }.

Hint Mode FuncUnfold ! ! - : typeclass_instances.

Class MethodUnfold t m m_impl : Prop :=
  {
    method_unfold : #(methods t m) = m_impl;
  }.

Hint Mode MethodUnfold ! ! - : typeclass_instances.
End unfolding_defs.

Section into_val_defs.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Class IntoValComparable {go_ctx : GoContext}
                        {core_sem : go.CoreSemantics}
  (V : Type) t `{!IntoVal V} `{!EqDecision V} :=
  {
    into_val_comparable : go.is_comparable t;
    into_val_always_comparable : go.is_always_comparable t V;
  }.

Class TypedPointsto (V : Type) `{!IntoVal V} :=
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
Global Arguments typed_pointsto {_ _ _} (l dq v).
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
Class IntoValTyped (V : Type) (t : go.type) `{TypedPointsto V} :=
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
Global Hint Mode IntoValTyped - - - - - - - ! - - : typeclass_instances.

Global Hint Mode TypedPointsto - - ! - : typeclass_instances.

(* Non-maximally insert the arguments related to [t], [IntoVal], etc., so that
   typeclass search won't be invoked until wp_apply actually unifies the [t]. *)
Global Arguments wp_alloc {_ _ _ _ _ _} [_ _ _ _ _ _ _] (Φ).
Global Arguments wp_load {_ _ _ _ _ _} [_ _ _ _ _ _ _] (l dq v Φ).
Global Arguments wp_store {_ _ _ _ _ _} [_ _ _ _ _ _ _] (l v w Φ).

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.


Section into_val_comparable_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.

Global Instance into_val_loc_inj : Inj eq eq (into_val (V:=loc)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_comparable_loc t : IntoValComparable loc (go.PointerType t).
Proof.
  split.
  - apply go.is_comparable_pointer.
  - apply go.go_eq_pointer.
Qed.

Global Instance into_val_slice_inj : Inj eq eq (into_val (V:=slice.t)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_w64_inj : Inj eq eq (into_val (V:=w64)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_w32_inj : Inj eq eq (into_val (V:=w32)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_w16_inj : Inj eq eq (into_val (V:=w16)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_w8_inj : Inj eq eq (into_val (V:=w8)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_bool_inj : Inj eq eq (into_val (V:=bool)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance into_val_string_inj : Inj eq eq (into_val (V:=go_string)).
Proof. rewrite into_val_unseal; intros ? ?. by inversion 1. Qed.

Global Instance interface_into_val_inj : Inj eq eq (into_val (V:=interface.t)).
Proof. rewrite into_val_unseal; intros ? ?. inversion 1. destruct x, y; naive_solver. Qed.

End into_val_comparable_instances.

Section go_wps.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {core_sem : go.CoreSemantics}.

Local Ltac solve_pure :=
  iIntros "% * _ % HΦ"; iApply wp_GoInstruction;
  [ intros; repeat econstructor | ];
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure;
  iIntros "H"; iIntros "$ !>"; by iApply "HΦ".

Global Instance wp_GoAlloc t :
  PureWp True (GoAlloc t #()) (alloc t #()).
Proof. solve_pure. Qed.

Global Instance wp_GoStore t (l : loc) v :
  PureWp True (GoStore t (#l, v)%V) (store t #l v).
Proof. solve_pure. Qed.

Global Instance wp_GoLoad t (l : loc) :
  PureWp True (GoLoad t #l) (load t #l).
Proof. solve_pure. Qed.

Global Instance wp_FuncResolve f ts :
  PureWp True (FuncResolve f ts #()) #(functions f ts).
Proof. solve_pure. Qed.

Global Instance wp_MethodResolve t f :
  PureWp True (MethodResolve t f #()) #(methods t f).
Proof. solve_pure. Qed.

Global Instance pure_wp_InterfaceGet m t v :
  PureWp True (InterfaceGet m #(interface.mk t v)) (MethodResolve t m #() v).
Proof. solve_pure. Qed.

Global Instance pure_wp_InterfaceMake dt (v : val) :
  PureWp True (InterfaceMake dt v) #(interface.mk dt v).
Proof. solve_pure. Qed.

Global Instance pure_wp_TypeAssert_non_interface t v :
  PureWp (is_interface_type t = false) (TypeAssert t #(interface.mk t v)) v.
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. rewrite Heq. rewrite decide_True //. by iApply "HΦ".
Qed.

Global Instance pure_wp_TypeAssert_interface t dt v :
  PureWp (is_interface_type t = true ∧ type_set_contains dt t = true)
    (TypeAssert t #(interface.mk dt v)) #(interface.mk dt v).
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. destruct Heq as [-> Hcontains]. rewrite Hcontains. by iApply "HΦ".
Qed.

Global Instance pure_wp_TypeAssert2_non_interface t t' `{!IntoVal V}
  `{!TypedPointsto V} `{!IntoValTyped V t} (v : V) :
  PureWp (is_interface_type t = false)
    (TypeAssert2 t #(interface.mk t' #v))
    (if decide (t = t') then (#v, #true)%V else (#(zero_val V), #false)%V).
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. rewrite Heq. destruct decide.
  - by iApply "HΦ".
  - unfold lang.glang_zero_val. wp_pures. wp_apply wp_alloc. iIntros "* Hl".
    wp_pures. wp_apply (wp_load with "[$Hl]"). iIntros "_". wp_pures. by iApply "HΦ".
Qed.

Global Instance pure_wp_TypeAssert2_interface t i :
  PureWp (is_interface_type t = true)
    (TypeAssert2 t #i)
    (match i with
     | interface.mk dt v =>
         if type_set_contains dt t then (# i, # true)%V else (# interface.nil, # false)%V
     | interface.nil => (# interface.nil, # false)%V
     end).
Proof.
  iIntros "% * %Heq % HΦ"; iApply wp_GoInstruction; [ intros; repeat econstructor |  ]; iNext.
  iIntros "* %Hstep Hlc". inv Hstep. inv Hpure. iIntros "$ !>".
  simpl. rewrite Heq. destruct i.
  - by iApply "HΦ".
  - by iApply "HΦ".
Qed.

Global Instance wp_GlobalVarAddr v :
  PureWp True (GlobalVarAddr v #()) #(global_addr v).
Proof. solve_pure. Qed.

Global Instance wp_StructFieldRef t f (l : loc) :
  PureWp True (StructFieldRef t f #l) #(struct_field_ref t f l).
Proof. solve_pure. Qed.

Global Instance wp_StructFieldSet_untyped f m v :
  PureWp True (StructFieldSet f (StructV m, v)%V) (StructV (<[f := v]> m)).
Proof. solve_pure. Qed.

Global Instance wp_InternalLen et s :
  PureWp True (InternalLen (go.SliceType et) #s) #(s.(slice.len)).
Proof. solve_pure. Qed.

Global Instance wp_InternalCap et s :
  PureWp True (InternalCap (go.SliceType et) #s) #(s.(slice.cap)).
Proof. solve_pure. Qed.

Global Instance wp_InternalDynamicArrayAlloc et (n : w64) :
  PureWp True (InternalDynamicArrayAlloc et #n)
    (GoAlloc (go.ArrayType (sint.Z n) et) #()).
Proof. solve_pure. Qed.

Global Instance wp_InternalMakeSlice p l c :
  PureWp True (InternalMakeSlice (#p, #l, #c)%V)
    #(slice.mk p l c).
Proof. solve_pure. Qed.

Global Instance wp_IndexRef t (j : w64) (v : val) :
  PureWp True (IndexRef t (v, #j)%V) (index_ref t (sint.Z j) v).
Proof. solve_pure. Qed.

Global Instance wp_Index t (j : w64) (v : val) :
  PureWp True (Index t (v, #j)%V) (index t (sint.Z j) v).
Proof. solve_pure. Qed.

Global Instance wp_ArrayAppend vs v :
  PureWp True (ArrayAppend (ArrayV vs, v)%V) (ArrayV (vs ++ [v])).
Proof. solve_pure. Qed.

Lemma wp_StructFieldGet_untyped {stk E} f m v :
  m !! f = Some v →
  {{{ True }}}
    StructFieldGet f (StructV m) @ stk; E
  {{{ RET v; £ 1 }}}.
Proof.
  iIntros "% * _ HΦ". iApply (wp_GoInstruction []).
  { intros. repeat econstructor. done. }
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iIntros "? $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

Local Lemma bool_decide_inj `(f : A → B) `{!Inj eq eq f} a a' `{!EqDecision A}
  `{!EqDecision B}
  : bool_decide (f a = f a') = bool_decide (a = a').
Proof.
  case_bool_decide.
  { eapply inj in H; last done. rewrite bool_decide_true //. }
  { rewrite bool_decide_false //.
    intros HR. apply H. subst. done. }
Qed.

Global Instance wp_eq `[!IntoVal V] `[!EqDecision V] `[!IntoValComparable V t] (v1 v2 : V) :
  PureWp True (GoEquals t (#v1, #v2)%V) #(bool_decide (v1 = v2)).
Proof.
  iIntros (?) "* _ * HΦ".
  iApply wp_GoInstruction.
  { intros. repeat econstructor. }
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iIntros "? $ !>". rewrite into_val_comparable. rewrite into_val_always_comparable.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_GoPrealloc {stk E} :
  {{{ True }}}
    GoPrealloc #() @ stk; E
  {{{ (l : loc), RET #l; True }}}.
Proof.
  iIntros (?) "_ HΦ". wp_apply (wp_GoInstruction []).
  { intros. exists #null. repeat econstructor. }
  iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iIntros "_ $ !>". simpl. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_AngelicExit Φ s E :
  ⊢ WP AngelicExit #() @ s; E {{ Φ }}.
Proof.
  iLöb as "IH".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iIntros "_ $ !>". simpl. iApply "IH".
Qed.

Lemma wp_PackageInitCheck {stk E} (pkg : go_string) (s : gmap go_string bool) :
  {{{ own_go_state s }}}
    PackageInitCheck pkg #() @ stk; E
  {{{ RET #(default false (s !! pkg)); own_go_state s }}}.
Proof.
  iIntros (?) "Hown HΦ".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  iIntros "* %Hstep".
  inv Hstep; last by inv Hpure.
  iIntros "_ Hauth". iCombine "Hauth Hown" gives %Heq. subst.
  iModIntro. iFrame. simpl. wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_PackageInitStart {stk E} (pkg : go_string) (s : gmap go_string bool) :
  {{{ own_go_state s }}}
    PackageInitStart pkg #() @ stk; E
  {{{ RET #(); own_go_state (<[ pkg := false ]> s) }}}.
Proof.
  iIntros (?) "Hown HΦ".
  wp_apply (wp_GoInstruction []).
  { intros. repeat econstructor. }
  iIntros "* %Hstep".
  inv Hstep; last by inv Hpure.
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
  iIntros "* %Hstep".
  inv Hstep; last by inv Hpure.
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

Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ #() -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "Hwp HΦ".
  wp_apply (lifting.wp_fork with "[$Hwp]").
  replace (LitV LitUnit) with #().
  { iFrame "HΦ". }
  rewrite into_val_unseal //.
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
  rewrite into_val_unseal //.
Qed.


Definition someStructType : go.type :=
  go.StructType [(go.FieldDecl "a"%go (go.PointerType (go.Named "uint64"%go [])))].

Lemma wp_test  :
  {{{ True }}}
  GoEquals someStructType (StructV {[ "a"%go := #null ]}, StructV {[ "a"%go := #null ]})%V
  {{{ RET #true; True }}}.
Proof.
  iIntros "% _ HΦ".

  (* TODO: abstract into lemma *)
  iApply (wp_GoInstruction [] (GoEquals someStructType)).
  { intros. repeat econstructor. }
  iNext; iIntros "* %Hstep"; inv Hstep; inv Hpure.
  iIntros "? $ !>". simpl.

  (* precondition/typeclass *)
  assert (go.is_comparable someStructType) as Hcomp.
  { rewrite go.is_comparable_struct. repeat constructor. apply into_val_comparable. }
  rewrite Hcomp.

  rewrite go._go_eq_struct. simpl.
  wp_pures.
  wp_apply wp_StructFieldGet_untyped. (* TODO: use struct field get instance *)
  { rewrite lookup_singleton //. }
  iIntros "_".
  wp_apply wp_StructFieldGet_untyped.
  { rewrite lookup_singleton //. }
  iIntros "_".
  wp_pures. by iApply "HΦ".
Qed.

End go_wps.

Section mem_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
(* Helper lemmas for establishing [IntoValTyped] *)
Lemma _internal_wp_untyped_atomic_load l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    ! #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof. rewrite into_val_unseal. apply lifting.wp_load. Qed.

Lemma _internal_wp_untyped_read l dq v s E :
  {{{ ▷ heap_pointsto l dq v }}}
    Read #l @ s; E
  {{{ RET v; heap_pointsto l dq v }}}.
Proof.
  rewrite into_val_unseal.
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
  rewrite into_val_unseal. iIntros "% Hl HΦ". wp_call.
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
  iPureIntro. rewrite into_val_unseal /= in Heq.
  destruct v1, v2. naive_solver.
Qed.

Existing Class go.is_primitive.
#[local] Hint Extern 1 (go.is_primitive ?t) => constructor : typeclass_instances.

Ltac solve_wp_alloc :=
  iIntros "* _ HΦ";
  rewrite go.alloc_primitive typed_pointsto_unseal /= into_val_unseal;
  wp_pures; by wp_apply wp_alloc_untyped.

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
Proof.
  split.
  { apply go.go_zero_val_pointer. }
  {
    rewrite go.go_zero_val_pointer.
    iIntros "* _ HΦ"; rewrite go.alloc_primitive typed_pointsto_unseal /= into_val_unseal; wp_pures.
    wp_apply wp_alloc_untyped.
    2:{ done. }
    rewrite into_val_unseal. done.
    done.
    solve_wp_alloc. }
  solve_into_val_typed. Qed.

Global Instance into_val_typed_func sig : IntoValTyped func.t (go.FunctionType sig).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_slice t : IntoValTyped slice.t (go.SliceType t).
Proof. solve_into_val_typed. Qed.

Global Instance into_val_typed_chan t b : IntoValTyped chan.t (go.ChannelType b t).
Proof. solve_into_val_typed. Qed.

Lemma seqZ_succ start n :
  0 ≤ n →
  seqZ start (Z.succ n) = seqZ start n ++ [start + n].
Proof.
  intros H. rewrite /seqZ Z2Nat.inj_succ; last lia.
  rewrite seq_S fmap_app /=. f_equal. f_equal. lia.
Qed.

End typed_pointsto_instances.
