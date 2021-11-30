From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import refinement.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import metatheory.

Set Default Proof Using "Type".

Lemma val_lit_eq_iff `{spec_op: ffi_syntax} l l' :
  #l = #l' ↔ l = l'.
Proof.
  naive_solver.
Qed.

Lemma val_pair_eq_iff `{spec_op: ffi_syntax} v1 v2 v1' v2' :
  (v1, v2)%V = (v1', v2')%V ↔ v1 = v1' ∧ v2 = v2'.
Proof. naive_solver. Qed.

Lemma val_injl_eq_iff `{spec_op: ffi_syntax} v1 v1' :
  InjLV v1 = InjLV v1' ↔ v1 = v1'.
Proof. naive_solver. Qed.

Lemma val_injr_eq_iff `{spec_op: ffi_syntax} v1 v1' :
  InjRV v1 = InjRV v1' ↔ v1 = v1'.
Proof. naive_solver. Qed.

Section go_refinement.
  (* Records defining spec language extensions *)
  Context {spec_op: ffi_syntax}.
  Context {spec_ffi: ffi_model}.
  Context {spec_semantics: ffi_semantics spec_op spec_ffi}.

  (* Records for the target language *)
  Context {impl_op: ffi_syntax}.
  Context {impl_ffi: ffi_model}.
  Context {impl_semantics: ffi_semantics impl_op impl_ffi}.

  Notation sexpr := (@expr spec_op).
  Notation sectx_item := (@ectx_item spec_op).
  Notation sval := (@val spec_op).
  Notation sstate := (@state spec_op spec_ffi).
  Notation sffi_state := (@ffi_state spec_ffi).
  Notation sffi_global_state := (@ffi_global_state spec_ffi).
  Notation sgstate := (@global_state spec_ffi).
  Notation iexpr := (@expr impl_op).
  Notation iectx_item := (@ectx_item impl_op).
  Notation ival := (@val impl_op).
  Notation istate := (@state impl_op impl_ffi).
  Notation igstate := (@global_state impl_ffi).
  Notation iffi_state := (@ffi_state impl_ffi).
  Notation iffi_global_state := (@ffi_global_state impl_ffi).

  Definition rtc_prim_step' : relation (iexpr * (istate * igstate)) :=
    rtc (λ '(e, (s, g)) '(e', (s', g')), prim_step' e s g [] e' s' g' []).

  Canonical Structure spec_lang : language :=
    @goose_lang (spec_op) (spec_ffi) (spec_semantics).
  Canonical Structure spec_crash_lang : crash_semantics spec_lang :=
    @goose_crash_lang (spec_op) (spec_ffi) (spec_semantics).

  Notation scfg := (@cfg spec_lang).

  Canonical Structure impl_lang : language :=
    @goose_lang (impl_op) (impl_ffi) (impl_semantics).
  Canonical Structure impl_crash_lang : crash_semantics impl_lang :=
    @goose_crash_lang (impl_op) (impl_ffi) (impl_semantics).

  (* op_impl gives a lambda implementing each spec op code *)
  Context (op_impl: @ffi_opcode spec_op → ival).
  Context (ffi_abstraction: sffi_state → sffi_global_state →
                            iffi_state → iffi_global_state → Prop).

  (* wf is a client-selected "well-formedness" predicate on source configurations
     expressions.  This could be a typing relation or other syntactic check on
     source expressions that the client relies upon to prove their simulation
     relation.  The idea is that the refinement theorem will only hold for
     well-formed expressions. *)
  Context (wf : sexpr → scfg → Prop).
  Context (wf_closed : ∀ sr sσ sg stp, wf sr (stp, (sσ, sg)) →
                                       is_closed_expr [] sr ∧ Forall (is_closed_expr []) stp).
  Context (wf_preserved_step : ∀ sr sρ sρ' s,
              wf sr sρ →
              erased_rsteps (CS := spec_crash_lang) sr sρ sρ' s →
              wf sr sρ').

  Definition in_wf_ctxt (se: sexpr) sσ sg :=
    ∃ sr tp1 tp2 K,
      wf sr (tp1 ++ (fill K se) :: tp2, (sσ, sg)).

  Inductive val_relation : sval → ival → Prop :=
  | val_relation_literal : ∀ l,
    (* references are related one-to-one because we maintain a strict
    correspondence between heaps *)
    val_relation (LitV l) (LitV l)
  | val_relation_pair : ∀ sv1 sv2 iv1 iv2,
    val_relation sv1 iv1 →
    val_relation sv2 iv2 →
    val_relation (PairV sv1 sv2) (PairV iv1 iv2)
  | val_relation_injl : ∀ sv iv,
      val_relation sv iv →
      val_relation (InjLV sv) (InjLV iv)
  | val_relation_injr : ∀ sv iv,
      val_relation sv iv →
      val_relation (InjRV sv) (InjRV iv)
  .

  Inductive foval : sval → Prop :=
  | foval_literal : ∀ l, foval (LitV l)
  | foval_pair : ∀ sv1 sv2,
    foval sv1 →
    foval sv2 →
    foval (PairV sv1 sv2)
  | foval_injl : ∀ sv,
      foval sv →
      foval (InjLV sv)
  | foval_injr : ∀ sv,
      foval sv →
      foval (InjRV sv).

  Definition foheap (m: gmap loc (nonAtomic sval)) : Prop :=
    ∀ l n v, m !! l = Some (n, v) → foval v.

  Definition fo_head (e : sexpr) (σ : sstate) (g : sgstate) :=
    ∀ κs e' σ' g' efs',
      head_step_atomic e σ g κs e' σ' g' efs' → foheap (heap σ').

  Definition fo_prim (e : sexpr) (σ : sstate) (g : sgstate) :=
    ∀ κs e' σ' g' efs',
      prim_step e σ g κs e' σ' g' efs' → foheap (heap σ').

  Definition fo_rsteps (r : sexpr) ρ :=
    ∀ t2 σ2 g2 s, erased_rsteps (CS := spec_crash_lang) r ρ (t2, (σ2, g2)) s → foheap (heap σ2).

  Definition naVal_relation : nonAtomic sval → nonAtomic ival → Prop :=
    λ '(m1, sv) '(m2, iv), m1 = m2 ∧ val_relation sv iv.

  Definition heap_relation : gmap loc (nonAtomic sval) → gmap loc (nonAtomic ival) → Prop :=
    λ m1 m2,
      dom (gset _) m1 = dom (gset _) m2 ∧
      (∀ l sv iv, m1 !! l = Some sv →
                  m2 !! l = Some iv →
                  naVal_relation sv iv).

  Definition abstraction (sσ: sstate) (sg: sgstate)
             (iσ: istate) (ig: igstate) :=
    ffi_abstraction (world sσ) sg (world iσ) ig ∧
    heap_relation (heap sσ) (heap iσ) ∧
    trace sσ = trace iσ ∧
    oracle sσ = oracle iσ.

  Inductive expr_impl : sexpr → iexpr → Prop :=
  | expr_impl_val v v' :
    val_impl v v' →
    expr_impl (Val v) (Val v')
  | expr_impl_var x :
    expr_impl (Var x) (Var x)
  | expr_impl_rec f x se ie :
    expr_impl se ie →
    expr_impl (Rec f x se) (Rec f x ie)
  | expr_impl_app f f' x x' :
    expr_impl f f' →
    expr_impl x x' →
    expr_impl (App f x) (App f' x')
  | expr_impl_unop op e e' :
    expr_impl e e' →
    expr_impl (UnOp op e) (UnOp op e')
  | expr_impl_binop op e1 e1' e2 e2' :
    expr_impl e1 e1' →
    expr_impl e2 e2' →
    expr_impl (BinOp op e1 e2) (BinOp op e1' e2')
  | expr_impl_if e1 e1' e2 e2' e3 e3' :
    expr_impl e1 e1' →
    expr_impl e2 e2' →
    expr_impl e3 e3' →
    expr_impl (If e1 e2 e3) (If e1' e2' e3')
  | expr_impl_pair e1 e1' e2 e2' :
    expr_impl e1 e1' →
    expr_impl e2 e2' →
    expr_impl (Pair e1 e2) (Pair e1' e2')
  | expr_impl_fst e e' :
    expr_impl e e' →
    expr_impl (Fst e) (Fst e')
  | expr_impl_snd e e' :
    expr_impl e e' →
    expr_impl (Snd e) (Snd e')
  | expr_impl_injl e e' :
    expr_impl e e' →
    expr_impl (InjL e) (InjL e')
  | expr_impl_injr e e' :
    expr_impl e e' →
    expr_impl (InjR e) (InjR e')
  | expr_impl_case e1 e1' e2 e2' e3 e3' :
    expr_impl e1 e1' →
    expr_impl e2 e2' →
    expr_impl e3 e3' →
    expr_impl (Case e1 e2 e3) (Case e1' e2' e3')
  | expr_impl_fork e e' :
    expr_impl e e' →
    expr_impl (Fork e) (Fork e')
  (* expr atomically: we forbid atomically in the source, even though we don't have to I think *)
  | expr_primitive0 op :
    expr_impl (Primitive0 op) (Primitive0 op)
  | expr_primitive1 op e e' :
    expr_impl e e' →
    expr_impl (Primitive1 op e) (Primitive1 op e')
  | expr_impl_primitive2 op e1 e1' e2 e2' :
    expr_impl e1 e1' →
    expr_impl e2 e2' →
    expr_impl (Primitive2 op e1 e2) (Primitive2 op e1' e2')
  | expr_impl_cmpxchg e0 e0' e1 e1' e2 e2' :
    expr_impl e0 e0' →
    expr_impl e1 e1' →
    expr_impl e2 e2' →
    expr_impl (CmpXchg e0 e1 e2) (CmpXchg e0' e1' e2')
  | expr_impl_external_op_var o x:
    expr_impl (ExternalOp o (Var x))
              (Atomically #() (App (Val (op_impl o)) (Var x)))%E
  | expr_impl_external_op_val o sv iv:
    val_impl sv iv →
    expr_impl (ExternalOp o sv)
              (Atomically #() (App (Val (op_impl o)) iv))%E
  (* TODO: bunch more cases *)
  with val_impl : sval → ival → Prop :=
  (* Just including val_relation is not enough, even though val_relation has all these cases,
     because we need the recursive cases to include val_impl with RecV *)
  (*
  | val_impl_rel sv iv :
    val_relation sv iv → val_impl sv iv *)
  | val_impl_literal : ∀ l,
    (* references are related one-to-one because we maintain a strict
    correspondence between heaps *)
    val_impl (LitV l) (LitV l)
  | val_impl_pair : ∀ sv1 sv2 iv1 iv2,
    val_impl sv1 iv1 →
    val_impl sv2 iv2 →
    val_impl (PairV sv1 sv2) (PairV iv1 iv2)
  | val_impl_injl : ∀ sv iv,
      val_impl sv iv →
      val_impl (InjLV sv) (InjLV iv)
  | val_impl_injr : ∀ sv iv,
      val_impl sv iv →
      val_impl (InjRV sv) (InjRV iv)
  | val_recv f x se ie :
    expr_impl se ie →
    val_impl (RecV f x se) (RecV f x ie)
  .

  Inductive ectx_item_impl : sectx_item → iectx_item → Prop :=
  | ectx_item_impl_appL sv iv :
      val_impl sv iv →
      ectx_item_impl (AppLCtx sv) (AppLCtx iv)
  | ectx_item_impl_appR se ie :
      expr_impl se ie →
      ectx_item_impl (AppRCtx se) (AppRCtx ie)
  | ectx_item_impl_unop op :
      ectx_item_impl (UnOpCtx op) (UnOpCtx op)
  | ectx_item_impl_binopL op se2 ie2 :
      expr_impl se2 ie2 →
      ectx_item_impl (BinOpLCtx op se2) (BinOpLCtx op ie2)
  | ectx_item_impl_binopR op sv1 iv1 :
      val_impl sv1 iv1 →
      ectx_item_impl (BinOpRCtx op sv1) (BinOpRCtx op iv1)
  | ectx_item_impl_if se1 se2 ie1 ie2 :
      expr_impl se1 ie1 →
      expr_impl se2 ie2 →
      ectx_item_impl (IfCtx se1 se2) (IfCtx ie1 ie2)
  | ectx_item_impl_pairL se ie :
      expr_impl se ie →
      ectx_item_impl (PairLCtx se) (PairLCtx ie)
  | ectx_item_impl_pairR sv iv :
      val_impl sv iv →
      ectx_item_impl (PairRCtx sv) (PairRCtx iv)
  | ectx_item_impl_fst :
      ectx_item_impl (FstCtx) (FstCtx)
  | ectx_item_impl_snd :
      ectx_item_impl (SndCtx) (SndCtx)
  | ectx_item_impl_injL :
      ectx_item_impl (InjLCtx) (InjLCtx)
  | ectx_item_impl_injR :
      ectx_item_impl (InjRCtx) (InjRCtx)
  | ectx_item_impl_case se1 se2 ie1 ie2 :
      expr_impl se1 ie1 →
      expr_impl se2 ie2 →
      ectx_item_impl (CaseCtx se1 se2) (CaseCtx ie1 ie2)
  | ectx_item_impl_primitive1 op :
      ectx_item_impl (Primitive1Ctx op) (Primitive1Ctx op)
  | ectx_item_impl_primitive2L op se2 ie2 :
      expr_impl se2 ie2 →
      ectx_item_impl (Primitive2LCtx op se2) (Primitive2LCtx op ie2)
  | ectx_item_impl_primitive2R op sv1 iv1 :
      val_impl sv1 iv1 →
      ectx_item_impl (Primitive2RCtx op sv1) (Primitive2RCtx op iv1)
                     (*
  | ectx_item_impl_external o :
      ectx_item_impl (ExternalOpCtx op)
                     (AppRCtx Atomically #() (App (Val (op_impl o)) (Var x)))
      val_impl sv1 iv1 →
      ectx_item_impl (Primitive2RCtx op sv1) (Primitive2RCtx op iv1)
                      *)
  | ectx_item_impl_cmpxchgL se1 se2 ie1 ie2 :
      expr_impl se1 ie1 →
      expr_impl se2 ie2 →
      ectx_item_impl (CmpXchgLCtx se1 se2) (CmpXchgLCtx ie1 ie2)
  | ectx_item_impl_cmpxchgM sv1 se2 iv1 ie2 :
      val_impl sv1 iv1 →
      expr_impl se2 ie2 →
      ectx_item_impl (CmpXchgMCtx sv1 se2) (CmpXchgMCtx iv1 ie2)
  | ectx_item_impl_cmpxchgR sv1 sv2 iv1 iv2 :
      val_impl sv1 iv1 →
      val_impl sv2 iv2 →
      ectx_item_impl (CmpXchgRCtx sv1 sv2) (CmpXchgRCtx iv1 iv2)
    .

  (* Check to make sure the translation of ExternalOp is not vacuous *)
  Lemma expr_impl_ExternalOp o :
    expr_impl (λ: "x", ExternalOp o (Var "x")) (λ: "x", Atomically #() (App (Val (op_impl o)) (Var "x"))).
  Proof. repeat econstructor. Qed.

  Definition op_simulated_succ (o: @ffi_opcode spec_op) (ie: iexpr) :=
    ∀ iσ ig iσ' ig' (iargv ivret: ival),
    rtc_prim_step' (App ie (Val iargv), (iσ, ig)) (Val ivret, (iσ', ig')) →
    prim_step'_safe (App ie (Val iargv)) iσ ig →
    ∀ sσ sg (sargv: sval),
    val_impl sargv iargv →
    abstraction sσ sg iσ ig →
    in_wf_ctxt (ExternalOp o (Val sargv)) sσ sg →
    ∃ sσ' sg' svret,
      head_step (ExternalOp o (Val sargv)) sσ sg [] (Val svret) sσ' sg' [] ∧
      val_relation svret ivret ∧
      abstraction sσ' sg' iσ' ig'
  .

  Definition op_simulated_abort (o: @ffi_opcode spec_op) (ie: iexpr) :=
    ∀ iσ ig (iargv ivret: ival),
    prim_step'_safe (App ie (Val iargv)) iσ ig →
    ∀ sσ sg (sargv: sval),
    val_impl sargv iargv →
    abstraction sσ sg iσ ig →
    ∃ sσ' sg' svret,
      head_step (ExternalOp o (Val sargv)) sσ sg [] (Val svret) sσ' sg' [] ∧
      val_relation svret (InjLV #()) ∧
      abstraction sσ' sg' iσ ig
  .

  Context (op_impl_succ_ok: ∀ o, op_simulated_succ o (op_impl o)).
  Context (op_impl_abort_ok: ∀ o, op_simulated_abort o (op_impl o)).

  Definition crash_simulated :=
    ∀ iw iw',
    ffi_crash_step iw iw' →
    ∀ ig sw sg,
    ffi_abstraction sw sg iw ig →
    ∃ sw', ffi_crash_step sw sw' ∧
           ffi_abstraction sw' sg iw' ig.

  Context (crash_ok: crash_simulated).

  Ltac inv_head_step :=
    repeat match goal with
        | _ => progress simplify_map_eq/= (* simplify memory stuff *)
        | H : to_val _ = Some _ |- _ => apply of_to_val in H
        | H : head_step ?e _ _ _ _ _ _ _ |- _ =>
          try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
          inversion H; subst; clear H
        | H : ffi_step _ _ _ _ _ |- _ =>
          inversion H; subst; clear H
        | H: relation.denote (unwrap None) _ _ _ |- _ => inversion H; intuition eauto
        end.

  Hint Constructors val_impl expr_impl val_relation ectx_item_impl : core.

  Ltac inv_monad_false :=
    match goal with
    | H: relation.denote (unwrap None) _ _ _ |- _ => inversion H; intuition eauto
    | H: relation.suchThat (λ _ _, False) _ _ _ |- _ => inversion H; intuition eauto
    end.

  Ltac destruct_head :=
    repeat match goal with
           | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] => destruct e; monad_inv; []
           end.

  Ltac destruct_head2 :=
    repeat match goal with
           | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] => destruct e; monad_inv; [|]
           end.

  Lemma expr_impl_un_op_eval op sv iv :
        val_impl sv iv →
        match un_op_eval op iv with
        | Some iv' => ∃ sv', un_op_eval op sv = Some sv' ∧ val_impl sv' iv'
        | None => un_op_eval op sv = None
         end.
  Proof.
    destruct op, iv => //=;
      try (inversion 1; subst; eauto; inversion H0; subst; eauto; done);
      try (destruct l; inversion 1; subst; eauto; inversion H0; subst; eauto).
  Qed.

  Hint Extern 1 (is_comparable _) => simpl : core.

  Lemma val_impl_comparable {sv iv} :
    val_impl sv iv →
    (is_comparable sv ↔ is_comparable iv).
  Proof.
    generalize dependent iv.
    induction sv, iv; simpl; auto;
      try solve [ inversion 1; subst; eauto ].

    inversion 1; subst.
    rewrite IHsv1 //.
    rewrite IHsv2 //.
  Qed.

  Lemma val_impl_bool_iff P1 P2 `{!Decision P1, !Decision P2} :
    (P1 ↔ P2) →
    val_impl #(bool_decide P1) #(bool_decide P2).
  Proof.
    intros.
    rewrite (bool_decide_iff P1 P2) //.
  Qed.

  Lemma val_impl_comparable_to_eq:
    ∀ (iv1 iv2 : ival) (sv1 sv2 : sval),
    is_comparable iv1 → is_comparable iv2 →
    val_impl sv1 iv1 → val_impl sv2 iv2 → sv1 = sv2 ↔ iv1 = iv2.
  Proof using.
    clear.
    induction iv1, iv2; simpl; intros ? ? Hv1 Hv2;
      (* exploit is_comparable *)
      (try contradiction);
      (inversion 1; inversion 1; subst; eauto);
      rewrite ?val_lit_eq_iff ?val_pair_eq_iff ?val_injl_eq_iff ?val_injr_eq_iff //;
      naive_solver.
  Qed.

  Lemma foval_val_impl_relation sv iv :
    foval sv →
    val_impl sv iv →
    val_relation sv iv.
  Proof.
    intros Hfoval.
    induction 1; inversion Hfoval; subst; eauto.
  Qed.

  Lemma expr_impl_bin_op_eval op sv1 sv2 iv1 iv2 :
        val_impl sv1 iv1 →
        val_impl sv2 iv2 →
        match bin_op_eval op iv1 iv2 with
        | Some iv' => ∃ sv', bin_op_eval op sv1 sv2 = Some sv' ∧ val_impl sv' iv'
        | None => bin_op_eval op sv1 sv2 = None
         end.
  Proof.
    clear.
    destruct op;
    try (destruct iv1 => //=; inversion 1; subst; eauto; try inversion H0; subst; eauto;
         try (destruct iv2; inversion 1; subst; eauto; try inversion H2; subst; eauto;
           destruct l => //=; destruct l0 => //=; eauto; done); done).

    rewrite /bin_op_eval /bin_op_eval_eq /=.
    intros Hv1 Hv2.
    pose proof (val_impl_comparable Hv1) as Hv1compare.
    pose proof (val_impl_comparable Hv2) as Hv2compare.
    destruct (decide (is_comparable iv1 ∧ is_comparable iv2));
      [ rewrite decide_True; [ | naive_solver ]
      | rewrite decide_False; [ | naive_solver ] ];
      simpl; auto.

    eexists; split; [ now eauto | ].
    destruct a.
    apply val_impl_bool_iff.
    apply val_impl_comparable_to_eq; auto.
  Qed.

  Lemma expr_impl_subst x sv se iv ie :
    expr_impl se ie →
    val_impl sv iv →
    expr_impl (subst x sv se)
              (subst x iv ie).
  Proof. induction 1 => //=; eauto; intros Hval; destruct (decide _); eauto. Qed.

  Lemma expr_impl_subst' x sv se iv ie :
    expr_impl se ie →
    val_impl sv iv →
    expr_impl (subst' x sv se)
              (subst' x iv ie).
  Proof. destruct x => /=; eauto using expr_impl_subst. Qed.

  Lemma expr_impl_subst'_2 x f sv se iv ie :
    expr_impl se ie →
    val_impl sv iv →
    expr_impl (subst' x sv (subst' f (rec: f x := se) se))
              (subst' x iv (subst' f (rec: f x := ie) ie)).
  Proof. eauto using expr_impl_subst'. Qed.

  Lemma abstraction_heap_lookup sσ sg iσ ig l na iv :
    abstraction sσ sg iσ ig →
    heap iσ !! l = Some (na, iv) →
    ∃ sv, heap sσ !! l = Some (na, sv) ∧ val_relation sv iv.
  Proof.
    intros (?&Hheap&_) Hlook.
    destruct (heap sσ !! l) as [(?&?)|] eqn:Hlook'.
    - destruct Hheap as (?&Hvals). edestruct (Hvals _ _ _ Hlook' Hlook).
      subst; eauto.
    - destruct Hheap as (Hdom&_).
      apply not_elem_of_dom in Hlook'.
      apply elem_of_dom_2 in Hlook. congruence.
  Qed.

  Lemma val_relation_to_val_impl sv iv :
    val_relation sv iv →
    val_impl sv iv.
  Proof. induction 1; eauto. Qed.

  Hint Resolve val_relation_to_val_impl : core.

  Ltac inv_expr_impl :=
     repeat match goal with
        | H : expr_impl ?se ?ie |- _ =>
          try (is_var ie; fail 1);
          is_var se; inversion H; clear H; subst
        | H : val_impl ?se ?ie |- _ =>
          try (is_var ie; fail 1);
          is_var se; inversion H; clear H; subst
     end.

  Ltac inv_expr_implI :=
     repeat match goal with
        | H : expr_impl ?se ?ie |- _ =>
          try (is_var se; fail 1);
          is_var ie; inversion H; clear H; subst
        | H : val_impl ?se ?ie |- _ =>
          try (is_var se; fail 1);
          is_var ie; inversion H; clear H; subst
     end.

  Lemma abstraction_insert l sσ1 sg1 iσ1 ig1 na sv iv :
    val_relation sv iv →
    abstraction sσ1 sg1 iσ1 ig1 →
    abstraction (RecordSet.set heap <[l:=(na, sv)]> sσ1) sg1
                (RecordSet.set heap <[l:=(na, iv)]> iσ1) ig1.
  Proof.
    intros Hval (?&Hheap&?&?).
    split_and!; subst; eauto.
    rewrite /heap_relation.
    destruct Hheap as (Hdom&Hlookup).
    split.
    { rewrite ?dom_insert_L // Hdom //. }
    intros l' ?? => /=.
    destruct (decide (l = l')).
    - subst. rewrite ?lookup_insert.
      inversion 1; subst.
      inversion 1; subst.
      split; auto.
    - rewrite ?lookup_insert_ne //. eapply Hlookup.
  Qed.

  Lemma heap_array_lookup_is_Some : ∀ (V : Type) (l : loc) (vs : list V) (k : loc),
      is_Some (heap_array l vs !! k) ↔ (∃ j : Z, 0 ≤ j ∧ k = addr_plus_off l j ∧ is_Some (vs !! Z.to_nat j)).
  Proof.
    intros. split.
    - intros (v&Heq%heap_array_lookup).
      edestruct Heq as (j&?&?&?). eexists; split_and!; eauto.
    - intros (z&?&?&[? ?]). edestruct (heap_array_lookup) as (_&Hsome). eexists; eapply Hsome.
      eexists; split_and!; eauto.
  Qed.

  Lemma is_Some_free_concat_look {A B} (v1 : list A) (v2 : list B) n m :
    (length v1 = length v2)%nat →
    is_Some ((Free <$> concat_replicate n v1) !! m) →
    is_Some ((Free <$> concat_replicate n v2) !! m).
  Proof.
    intros Hlen.
    rewrite ?list_lookup_fmap ?fmap_is_Some ?lookup_lt_is_Some.
    rewrite ?lifting.concat_replicate_length.
    lia.
  Qed.

  Lemma val_relation_flatten_length sv iv :
    val_relation sv iv →
    length (flatten_struct sv) = length (flatten_struct iv).
  Proof.
    induction 1; eauto.
    { destruct l; auto. }
    { simpl. rewrite ?app_length; congruence. }
  Qed.

  Lemma val_relation_flatten_relation sv iv :
    val_relation sv iv →
    Forall2 val_relation (flatten_struct sv) (flatten_struct iv).
  Proof.
    induction 1; simpl.
    - destruct l; auto.
    - apply Forall2_app; auto.
    - econstructor; auto.
    - econstructor; auto.
  Qed.

  Lemma heap_array_lookup_none2_if {A B} l n (v1 : list A) (v2 : list B) l' :
    length v1 = length v2 →
    heap_array l (Free <$> concat_replicate n v1) !! l' = None →
    heap_array l (Free <$> concat_replicate n v2) !! l' = None.
  Proof.
    intros Hlength.
    destruct (heap_array l (Free <$> concat_replicate n v1) !! l') as [|] eqn:Hlook1; first congruence.
    destruct (heap_array l (Free <$> concat_replicate n v2) !! l') as [|] eqn:Hlook2; auto.
    apply mk_is_Some in Hlook2.
    apply heap_array_lookup_is_Some in Hlook2.
    edestruct Hlook2 as (?&?&?&Hlookfmap).
    symmetry in Hlength.
    eapply (@is_Some_free_concat_look) in Hlookfmap; last by eapply Hlength.
    apply eq_None_not_Some in Hlook1. exfalso. apply Hlook1.
    eapply heap_array_lookup_is_Some; eauto.
  Qed.

  Lemma dom_heap_array_length {A B} (l1 : list A) (l2 : list B) l :
    length l1 = length l2 →
    dom (gset loc) (heap_array l l1) =
    dom (gset loc) (heap_array l l2).
  Proof.
    revert l l2. induction l1 => l l2.
    - destruct l2; last by simpl; congruence.
      intros _. rewrite //= ?dom_empty_L //.
    - destruct l2; first by simpl; congruence.
      inversion 1; subst. simpl. rewrite ?dom_union_L ?dom_singleton_L. f_equal; auto.
  Qed.

   Lemma concat_replicate2_Forall2 {A B} n (l1 : list A) (l2 : list B) R z x y:
     Forall2 R l1 l2 →
     concat_replicate n l1 !! z = Some x →
     concat_replicate n l2 !! z = Some y →
     R x y.
   Proof.
     revert z.
     induction n => //= z.
     intros HFR.
     rewrite ?lifting.concat_replicate_S.
     rewrite ?lookup_app_Some. intros Hl1 Hl2.
     destruct Hl1 as [Hl1|(?&Hl1)].
     - destruct Hl2 as [Hl2|(Hlen&Hl2)]; last first.
       { apply lookup_lt_Some in Hl1. apply Forall2_length in HFR. lia. }
       eapply Forall2_lookup_lr; eauto.
     - destruct Hl2 as [Hl2|(Hlen&Hl2)].
       { apply lookup_lt_Some in Hl2. apply Forall2_length in HFR. lia. }
       eapply IHn; eauto.
       assert (length l1 = length l2) as ->; eauto.
       { eapply Forall2_length; eauto. }
   Qed.

  Lemma abstraction_state_init_heap l z sσ1 sg1 iσ1 ig1 sv iv :
    val_relation sv iv →
    abstraction sσ1 sg1 iσ1 ig1 →
    abstraction (state_init_heap l z sv sσ1) sg1 (state_init_heap l z iv iσ1) ig1.
  Proof.
    intros Hval (?&Hheap&?&?).
    split_and!; subst; eauto.
    rewrite /heap_relation.
    destruct Hheap as (Hdom&Hlookup).
    split.
    { rewrite /state_init_heap//= ?dom_union_L // Hdom //. f_equal.
      apply dom_heap_array_length. rewrite ?fmap_length.
      rewrite ?lifting.concat_replicate_length.
      eapply val_relation_flatten_length in Hval.
      congruence.
    }
    rewrite /state_init_heap/state_insert_list.
    intros l' (na1&sv') (na2&iv') => /= Hlook1 Hlook2.
    apply lookup_union_Some_raw in Hlook1.
    apply lookup_union_Some_raw in Hlook2.
    revert Hlook1 Hlook2.  intros Hlook1 Hlook2.
    destruct Hlook1 as [Hl|Hr].
    { destruct Hlook2 as [Hl2|Hr]; last first.
      { destruct Hr as (Hrbad&_).
        eapply heap_array_lookup_none2_if in Hrbad.
        { erewrite Hl in Hrbad; congruence. }
        symmetry; apply val_relation_flatten_length; auto.
      }
      apply heap_array_lookup in Hl.
      apply heap_array_lookup in Hl2.
      destruct Hl as (j1&?&Heq1&Hl1).
      destruct Hl2 as (j2&?&Heq2&Hl2).
      subst.
      assert (j1 = j2) as ->.
      { inversion Heq2. lia. }
      rewrite list_lookup_fmap in Hl1.
      rewrite list_lookup_fmap in Hl2.
      apply fmap_Some_1 in Hl1 as (?&Heqa1&Hf1).
      apply fmap_Some_1 in Hl2 as (?&Heqa2&Hf2).
      inversion Hf1; inversion Hf2; split; first by congruence.
      eapply concat_replicate2_Forall2; try eassumption.
      apply val_relation_flatten_relation; auto.
    }
    { destruct Hlook2 as [Hl2|Hr2].
      { destruct Hr as (Hrbad&_).
        eapply heap_array_lookup_none2_if in Hrbad.
        { erewrite Hl2 in Hrbad; congruence. }
        apply val_relation_flatten_length; auto.
      }
      destruct Hr as (_&Hsσ1).
      destruct Hr2 as (_&Hiσ1).
      efeed pose proof Hlookup; eauto.
    }
  Qed.

  Lemma isFresh_abstraction sσ1 sg1 iσ1 ig1 l:
    abstraction sσ1 sg1 iσ1 ig1 →
    isFresh (iσ1, ig1) l →
    isFresh (sσ1, sg1) l.
  Proof.
    rewrite /isFresh.
    intros (_&(Hdom&Hlook)&_) (Hfresh1&Hfresh2).
    split; last eauto.
    intros; split; first eapply Hfresh1.
    apply not_elem_of_dom. rewrite Hdom. apply not_elem_of_dom. eapply Hfresh1.
  Qed.

  Lemma is_Writing_abstraction sσ1 sg1 iσ1 ig1 l:
    abstraction sσ1 sg1 iσ1 ig1 →
    is_Writing (heap iσ1 !! l) →
    is_Writing (heap sσ1 !! l).
  Proof.
    rewrite /isFresh.
    intros (_&(Hdom&Hlook)&_) Hwriting1.
    destruct (heap sσ1 !! l) as [(?&?)|] eqn:Hlook2.
    { destruct Hwriting1 as (?&Hwriting). eapply Hlook in Hwriting; eauto. destruct Hwriting as (->&_).
      rewrite /is_Writing. eauto. }
    apply not_elem_of_dom in Hlook2. rewrite Hdom in Hlook2. exfalso.
    apply Hlook2. destruct Hwriting1 as (?&Hlook'). eapply elem_of_dom_2; eauto.
  Qed.

  Lemma fo_flatten_struct_inv v :
    Forall foval (flatten_struct v) →
    foval v.
  Proof.
    induction v; simpl; eauto; try (inversion 1; subst; eauto; done).
    - destruct l; inversion 1; eauto. econstructor.
    - intros [? ?]%Forall_app. econstructor; eauto.
  Qed.

  Lemma foheap_union_inv_l σ1 σ2 :
    foheap (σ1 ∪ σ2) →
    foheap σ1.
  Proof.
    rewrite /foheap. intros Hfo l n v Hin. eapply Hfo; eauto.
    rewrite lookup_union_l; eauto.
  Qed.

  Lemma heap_array_forall {A} (P : A → Prop) l ls :
    (∀ k v, heap_array l ls !! k = Some v → P v) → Forall P ls.
  Proof.
    intros Hall.
    apply Forall_forall.
    intros x Hin.
    apply elem_of_list_lookup_1 in Hin as (i&Hl).
    eapply (Hall (addr_plus_off l (Z.of_nat i))).
    eapply heap_array_lookup. eexists; split_and!; eauto.
    { lia. }
    {rewrite Nat2Z.id //. }
  Qed.

  Lemma Forall_concat_replicate {A} n (l: list A) (P: A → Prop):
    (0 < n)%nat →
    Forall P (concat_replicate n l) →
    Forall P l.
  Proof.
    intros Hlt. destruct n; first lia.
    rewrite lifting.concat_replicate_S Forall_app. intuition.
  Qed.

  Lemma val_impl_compare_safe sv1 sv2 iv1 iv2:
    val_impl sv1 iv1 →
    val_impl sv2 iv2 →
    vals_compare_safe iv1 iv2 →
    vals_compare_safe sv1 sv2.
  Proof.
    intros Hv1 Hv2 Hcs.
    destruct Hcs.
    - rewrite /val_is_unboxed in H.
      destruct iv1; inversion Hv1; subst; try (econstructor; eauto; done).
      { destruct iv1; try intuition; [].
        inv_expr_impl. subst. econstructor. rewrite //=. }
      { destruct iv1; try intuition; [].
        inv_expr_impl. subst. econstructor. rewrite //=. }
    - rewrite /val_is_unboxed in H.
      destruct iv2; inversion Hv2; subst; try (econstructor; eauto; done).
      { destruct iv2; try intuition; [].
        inv_expr_impl. right. eauto. }
      { destruct iv2; try intuition; [].
        inv_expr_impl. right. eauto. }
  Qed.

  Lemma val_relation_val_impl_inj sv1 sv2 iv :
    val_impl sv1 iv →
    val_relation sv2 iv →
    sv1 = sv2.
  Proof.
    intros Hvi Hvr.
    revert sv1 Hvi.
    induction Hvr => ? Hvi; inv_expr_impl; auto; try (f_equal; eauto).
  Qed.

  Lemma val_relation_val_impl_inji sv iv1 iv2 :
    val_impl sv iv1 →
    val_relation sv iv2 →
    iv1 = iv2.
  Proof.
    intros Hvi Hvr.
    revert iv1 Hvi.
    induction Hvr => ? Hvi; inv_expr_implI; auto; try (f_equal; eauto).
  Qed.

  Lemma in_wf_ctxt_closed se sσ sg :
    in_wf_ctxt se sσ sg → is_closed_expr [] se.
  Proof using wf_closed.
    destruct 1 as (?&K&?&?&Hwf).
    apply wf_closed in Hwf as (_&Hin_wf).
    eapply fill_closed.
    eapply Forall_forall in Hin_wf; eauto.
    apply elem_of_app. right. left.
  Qed.

  Hint Resolve isFresh_abstraction is_Writing_abstraction : core.

  Theorem head_step_simulation ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs se1 sσ1 sg1 :
    fo_head se1 sσ1 sg1 →
    head_step ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs →
    expr_impl se1 ie1 →
    abstraction sσ1 sg1 iσ1 ig1 →
    (∃ se2 sσ2 sg2 sefs,
     κ = [] ∧
     head_step_atomic se1 sσ1 sg1 [] se2 sσ2 sg2 sefs ∧
     expr_impl se2 ie2 ∧
     abstraction sσ2 sg2 iσ2 ig2 ∧
     Forall2 expr_impl sefs iefs).
  Proof.
    rewrite /head_step.
    destruct ie1; subst; intros Hfohead Hstep Himpl Habstr; try inversion Hstep; intuition eauto; subst.
    - monad_inv.
      inversion Himpl; subst.
      do 4 eexists. split_and!; eauto.
      econstructor. repeat econstructor.
    - rewrite /head_step//= in Hstep.
      destruct_head. inversion Hstep; subst.
      monad_inv.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      * repeat econstructor.
      * eapply expr_impl_subst'_2; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inv_expr_impl.
      feed pose proof (expr_impl_un_op_eval op _ _ H2) as Heval; eauto.
      destruct (un_op_eval op v).
      * destruct Heval as (sv'&Heval&Hval).
        inv_head_step. monad_inv.
        do 4 eexists. split_and!; eauto.
        econstructor. econstructor; rewrite ?Heval //=.
      * inv_head_step. monad_inv. inversion H.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inv_expr_impl.
      feed pose proof (expr_impl_bin_op_eval op _ _ _ _ H3 H1) as Heval; eauto.
      destruct (bin_op_eval op _ _).
      * destruct Heval as (sv'&Heval&Hval).
        inv_head_step. monad_inv.
        do 4 eexists. split_and!; eauto.
        econstructor. econstructor; rewrite ?Heval //=.
      * inv_head_step. monad_inv. inversion H.
    - rewrite /head_step//= in Hstep.
      destruct_head.
      inversion Hstep; subst.
      monad_inv.
      inversion Himpl. subst.
      destruct b.
      * inv_head_step; monad_inv. do 4 eexists; split_and!; eauto.
        inv_expr_impl. repeat econstructor.
      * inv_head_step; monad_inv. do 4 eexists; split_and!; eauto.
        inv_expr_impl. repeat econstructor.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inversion Hstep; subst; monad_inv.
      inversion Himpl; subst.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inversion Hstep; subst; monad_inv.
      inversion Himpl; subst.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inversion Hstep; subst; monad_inv.
      inversion Himpl; subst.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inversion Hstep; subst; monad_inv.
      inversion Himpl; subst.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inversion Hstep; subst; monad_inv.
      inversion Himpl; subst.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      destruct_head2; monad_inv.
      * inversion Hstep; subst; monad_inv.
        inv_head_step. monad_inv.
        inv_expr_impl.
        do 4 eexists. split_and!; eauto.
        repeat econstructor; eauto; econstructor; eauto.
      * inversion Hstep; subst; monad_inv.
        inv_head_step. monad_inv.
        inv_expr_impl.
        do 4 eexists. split_and!; eauto.
        repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inv_expr_impl.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct_head; monad_inv.
      inv_expr_impl.
      inv_head_step. monad_inv.
      do 4 eexists. split_and!; eauto.
      repeat econstructor; eauto; econstructor; eauto.
    - rewrite /head_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inv_expr_impl; inv_head_step. monad_inv.
        destruct (heap _ !! l) as [(?&?)|] eqn:Heq; subst.
        ** inv_head_step. monad_inv.
           inv_head_step.
           destruct n; inv_head_step; monad_inv; try done; [].
           destruct n; inv_head_step; monad_inv; try done; [].
           eapply abstraction_heap_lookup in Heq as (sv&Hlook&Hrel); eauto.
           do 4 eexists. split_and!; eauto.
           { repeat econstructor; rewrite ?Hlook => //=. repeat econstructor. }
           apply abstraction_insert; auto.
        **  inv_head_step. monad_inv. exfalso; eauto.
      * inv_expr_impl; inv_head_step. monad_inv.
        destruct (heap _ !! l) as [(?&?)|] eqn:Heq; subst.
        ** inv_head_step. monad_inv.
           inv_head_step.
           destruct n; inv_head_step; monad_inv; try done; [].
           eapply abstraction_heap_lookup in Heq as (sv&Hlook&Hrel); eauto.
           do 4 eexists. split_and!; eauto.
           { repeat econstructor; rewrite ?Hlook => //=. repeat econstructor. }
           apply abstraction_insert; auto.
        ** inv_head_step. monad_inv. exfalso; eauto.
      * inv_expr_impl; inv_head_step. monad_inv.
        destruct (heap _ !! l) as [(?&?)|] eqn:Heq; subst.
        ** inv_head_step. monad_inv.
           inv_head_step.
           destruct n; inv_head_step; monad_inv; try done; [].
           destruct n; inv_head_step; monad_inv; try done; [].
           eapply abstraction_heap_lookup in Heq as (sv&Hlook&Hrel); eauto.
           do 4 eexists. split_and!; eauto.
           { repeat econstructor; rewrite ?Hlook => //=. repeat econstructor. }
           apply abstraction_insert; auto.
        ** inv_head_step. monad_inv. exfalso; eauto.
      * inv_expr_impl; inv_head_step. monad_inv.
        destruct (heap _ !! l) as [(?&?)|] eqn:Heq; subst.
        ** inv_head_step. monad_inv.
           inv_head_step.
           destruct n; inv_head_step; monad_inv; try done; [].
           eapply abstraction_heap_lookup in Heq as (sv&Hlook&Hrel); eauto.
           do 4 eexists. split_and!; eauto.
           { repeat econstructor; rewrite ?Hlook => //=. }
        ** inv_head_step. monad_inv. exfalso; eauto.
      * inv_expr_impl; inv_head_step. monad_inv.
        do 4 eexists. split_and!; eauto.
        { repeat econstructor; rewrite ?Hlook => //=.
          destruct Habstr as (?&?&->&->). eauto. }
        rewrite /abstraction in Habstr.
        split_and! => //=; intuition.
        congruence.
      * inv_expr_impl; inv_head_step. monad_inv.
        do 4 eexists. split_and!; eauto.
        { repeat econstructor; rewrite ?Hlook => //=. }
        rewrite /abstraction in Habstr.
        split_and! => //=; intuition.
        congruence.
    - rewrite /head_step//= in Hstep.
      destruct op; monad_inv; destruct_head.
      * inv_expr_impl; inv_head_step. monad_inv.
        destruct (decide (0 < int.Z n)); monad_inv.
        ** let sσ2 := fresh "sσ2" in evar (sσ2:sstate).
           let sg2 := fresh "sg2" in evar (sg2:sgstate).
           let rv := fresh "rv" in evar (rv:sval).
           assert (Hstep: head_step_atomic (AllocN #n v0) sσ1 sg1 [] ?rv ?sσ2 ?sg2 []).
           { econstructor. econstructor; unfold check; rewrite ?ifThenElse_if //.
             econstructor; first done. econstructor.
             { econstructor; eauto. }
             repeat econstructor.
           }
           do 4 eexists; split_and!; eauto.
           apply abstraction_state_init_heap; auto.
           apply foval_val_impl_relation; auto.
           apply Hfohead in Hstep.
           apply fo_flatten_struct_inv.
           simpl in Hstep.
           apply foheap_union_inv_l in Hstep.
           rewrite /foheap in Hstep.
           assert (Hforall: Forall foval (concat_replicate (int.nat n) (flatten_struct v0))).
           { eapply (heap_array_forall _ l0). intros. eapply Hstep.
             rewrite -heap_array_fmap. rewrite lookup_fmap fmap_Some. eauto. }
           apply Forall_concat_replicate in Hforall; auto. lia.
        ** exfalso; eauto.
      * inv_expr_impl; inv_head_step. monad_inv.
        destruct (decide (is_Writing (heap iσ1 !! l))); monad_inv.
        ** let sσ2 := fresh "sσ2" in evar (sσ2:sstate).
           let sg2 := fresh "sg2" in evar (sg2:sgstate).
           assert (Hstep: head_step_atomic (FinishStore #l v0) sσ1 sg1 [] #() ?sσ2 ?sg2 []).
           { econstructor. econstructor; unfold check; rewrite ?ifThenElse_if //.
             econstructor; first done. econstructor.
             { rewrite ?ifThenElse_if //; eauto. }
             repeat econstructor.
           }
           do 4 eexists; split_and!; eauto.
           apply abstraction_insert; auto.
           apply Hfohead in Hstep.
           apply foval_val_impl_relation; auto.
           rewrite /= /foheap in Hstep. eapply Hstep.
           rewrite /Free. apply lookup_insert.
        ** exfalso; eauto.
    - rewrite /head_step//= in Hstep.
      monad_inv; destruct_head.
      inv_head_step. monad_inv. inv_head_step.
      destruct (heap iσ1 !! l) as [(na&vold)|] eqn:Hlook; subst; monad_inv; destruct_head; last first.
      { inv_head_step. monad_inv. exfalso; auto. }
      repeat (inv_head_step; monad_inv). destruct na.
      { inv_head_step. monad_inv. exfalso; auto. }
      repeat (inv_head_step; monad_inv).
      destruct (decide (vals_compare_safe vold v)); monad_inv; try inv_monad_false; last by (exfalso; auto).
      destruct (decide (vold = v)) as [Heqold|Hneqold].
      * subst. inv_head_step; monad_inv.
        destruct (decide (n = O)); inv_head_step; monad_inv; last first.
        { exfalso; eauto. }
        inv_expr_impl.
        let sσ2 := fresh "sσ2" in evar (sσ2:sstate).
        let sg2 := fresh "sg2" in evar (sg2:sgstate).
        eapply abstraction_heap_lookup in Hlook as (sv&Hlook&Hrel); eauto.
        assert (Hstep: head_step_atomic (CmpXchg #l v3 v2) sσ1 sg1 [] (v3, #true)%V ?sσ2 ?sg2 []).
        { econstructor. repeat econstructor => //=.
          { rewrite Hlook => //=. }
          simpl.
          unfold check.
          rewrite ifThenElse_if; last first.
          { eapply val_impl_compare_safe; eauto. }
          assert (Heq: sv = v3).
          { symmetry. eapply val_relation_val_impl_inj; eauto. }
          subst.
          repeat econstructor; eauto.
          { rewrite /when. rewrite ifThenElse_if //. repeat econstructor. }
          { rewrite bool_decide_true //. }
        }
        do 4 eexists.
        split_and!; eauto.
        { rewrite bool_decide_true //. econstructor; eauto. }
        apply abstraction_insert; auto.
        apply Hfohead in Hstep.
        apply foval_val_impl_relation; auto.
        rewrite /= /foheap in Hstep. eapply Hstep.
        rewrite /Free. apply lookup_insert.
      * rewrite ifThenElse_else // in Hstep.
        inv_head_step; monad_inv.
        inv_expr_impl.
        eapply abstraction_heap_lookup in Hlook as (sv&Hlook&Hrel); eauto.
        do 4 eexists.
        split_and!; eauto.
        { econstructor. repeat econstructor => //=.
          { rewrite Hlook => //=. }
          simpl.
          unfold check.
          rewrite ifThenElse_if; last first.
          { eapply val_impl_compare_safe; eauto. }
          assert (Heq: sv ≠ v3).
          { intros Heq. subst. apply Hneqold. symmetry. eapply val_relation_val_impl_inji; eauto. }
          subst.
          repeat econstructor; eauto.
          { rewrite /when. rewrite ifThenElse_else //. }
          { rewrite ?bool_decide_false //. }
        }
    -  inv_expr_impl.
  Qed.

  Theorem head_step_atomic_simulation ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs se1 sσ1 sg1 :
    in_wf_ctxt se1 sσ1 sg1 →
    fo_head se1 sσ1 sg1 →
    head_step_atomic ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs →
    expr_impl se1 ie1 →
    abstraction sσ1 sg1 iσ1 ig1 →
    (∃ se2 sσ2 sg2 sκ sefs,
     head_step_atomic se1 sσ1 sg1 sκ se2 sσ2 sg2 sefs ∧
     expr_impl se2 ie2 ∧
     abstraction sσ2 sg2 iσ2 ig2 ∧
     Forall2 expr_impl sefs iefs).
  Proof using wf_closed op_impl_succ_ok op_impl_abort_ok.
    intros Hwf Hfohead Hstep Himpl Habstr. inversion Hstep; subst.
    - edestruct head_step_simulation as (?&?&?&?&?&?); intuition eauto.
      do 5 eexists; split_and!; eauto.
    - inv_expr_impl.
      * apply in_wf_ctxt_closed in Hwf. inversion Hwf.
      * edestruct (op_impl_succ_ok) as (sσ&sg&svret&Hhead&Hval&Habstr'); eauto.
        do 5 eexists; split_and!; eauto.
        econstructor; eauto.
    - inv_expr_impl.
      * apply in_wf_ctxt_closed in Hwf. inversion Hwf.
      * edestruct (op_impl_abort_ok) as (sσ&sg&svret&Hhead&Hval&Habstr'); eauto.
        do 5 eexists; split_and!; eauto.
        econstructor; eauto.
  Qed.

  Lemma fill_item_impl_inv se iK ie' iσ ig  :
    reducible ie' iσ ig →
    expr_impl se (fill_item iK ie') →
    ∃ sK se', se = fill_item sK se' ∧
              ectx_item_impl sK iK ∧
              expr_impl se' ie'.
  Proof.
    intros Hred.
    induction iK; simpl; intros Himpl;
      inv_expr_impl; try (do 2 eexists; split_and!; eauto; simpl; done).
    - apply reducible_not_val in Hred. inversion Hred.
    - apply reducible_not_val in Hred. inversion Hred.
  Qed.

  Definition ectx_impl sK iK := Forall2 ectx_item_impl sK iK.

  Lemma fill_impl_inv se iK ie' iσ ig  :
    reducible ie' iσ ig →
    expr_impl se (fill iK ie') →
    ∃ sK se', se = fill sK se' ∧
              ectx_impl sK iK ∧
              expr_impl se' ie'.
  Proof.
    revert se ie' iσ ig.
    induction iK => se ie' iσ ig.
    - rewrite //=. intros. eexists [], _. split_and!; eauto. econstructor.
    - intros Hred Himpl. simpl in Himpl.
      eapply IHiK in Himpl as (sK&se'1&Heq&HKimpl'&Himpl'); last first.
      { apply reducible_fill; eauto. }
      subst. eapply fill_item_impl_inv in Himpl' as (a'&?&?&?&?); eauto.
      eexists (a' :: sK), _. split_and!; eauto.
      { subst. rewrite //=. }
      { econstructor; eauto. }
  Qed.

  Lemma fill_item_impl se sK ie iK :
    ectx_item_impl sK iK →
    expr_impl se ie →
    expr_impl (fill_item sK se) (fill_item iK ie).
  Proof.
    induction 1; rewrite //=; eauto.
  Qed.

  Lemma fill_impl se sK ie iK :
    ectx_impl sK iK →
    expr_impl se ie →
    expr_impl (fill sK se) (fill iK ie).
  Proof.
    intros Hectx.
    revert se ie.
    induction Hectx => se ie ?; rewrite //=; eauto.
    apply IHHectx. apply fill_item_impl; eauto.
  Qed.

  Lemma fo_prim_sub K se sσ sg:
    fo_prim (fill K se) sσ sg →
    fo_head se sσ sg.
  Proof.
    rewrite /fo_prim/fo_head.
    intros Hprim Hhead. intros.
    eapply Hprim.
    econstructor; eauto.
  Qed.

  Theorem prim_step_simulation ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs se1 sσ1 sg1 :
    in_wf_ctxt se1 sσ1 sg1 →
    fo_prim se1 sσ1 sg1 →
    prim_step ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs →
    expr_impl se1 ie1 →
    abstraction sσ1 sg1 iσ1 ig1 →
    (∃ se2 sσ2 sg2 sκ sefs,
     prim_step se1 sσ1 sg1 sκ se2 sσ2 sg2 sefs ∧
     expr_impl se2 ie2 ∧
     abstraction sσ2 sg2 iσ2 ig2 ∧
     Forall2 expr_impl sefs iefs).
  Proof using wf_closed op_impl_succ_ok op_impl_abort_ok.
    intros Hwf Hfohead Hstep Himpl Habstr. inversion Hstep; subst.
    simpl in *.
    edestruct (fill_impl_inv) as (sK&se'&HKe'_eq&HKimpl&Heimpl); [| eassumption|].
    { econstructor. do 4 eexists.
      apply head_prim_step; eauto.
    }
    assert (Hwf': in_wf_ctxt se' sσ1 sg1).
    { destruct Hwf as (?&?&?&?&Hwf). do 4 eexists. subst. rewrite -fill_app in Hwf. eauto. }
    edestruct (head_step_atomic_simulation) as (se2'&sσ2&sg2&sκ&sefs&Hsstep&Himpl2&Habstr2&Himplefs);
      try eapply Hwf'; eauto.
    { eapply fo_prim_sub; subst; eauto. }
    eexists (fill sK se2').
    do 4 eexists.
    split_and!.
    { subst. econstructor; eauto. }
    { apply fill_impl; eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Theorem atomic_concurrent_refinement se ie :
    (* se compiles to ie *)
    expr_impl se ie →
    ∀ sσ sg iσ ig,
    abstraction sσ sg iσ ig →
    wf se ([se], (sσ, sg)) →
    trace_refines se se sσ sg ie ie iσ ig.
  Proof.
    induction 1; intros.
    - (* value *)
      admit.
    - (* external op *)
      admit.
      (* more cases *)
  Abort.

End go_refinement.
