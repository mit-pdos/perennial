From Perennial.Helpers Require Import CountableTactics Transitions.
From Perennial.goose_lang Require Import refinement.
From Perennial.goose_lang Require Import notation.

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
  Notation sval := (@val spec_op).
  Notation sstate := (@state spec_op spec_ffi).
  Notation sffi_state := (@ffi_state spec_ffi).
  Notation sffi_global_state := (@ffi_global_state spec_ffi).
  Notation sgstate := (@global_state spec_ffi).
  Notation iexpr := (@expr impl_op).
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

  Canonical Structure impl_lang : language :=
    @goose_lang (impl_op) (impl_ffi) (impl_semantics).
  Canonical Structure impl_crash_lang : crash_semantics impl_lang :=
    @goose_crash_lang (impl_op) (impl_ffi) (impl_semantics).

  (* op_impl gives a lambda implementing each spec op code *)
  Context (op_impl: @ffi_opcode spec_op → ival).
  Context (ffi_abstraction: sffi_state → sffi_global_state →
                            iffi_state → iffi_global_state → Prop).

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

  Definition op_simulated (o: @ffi_opcode spec_op) (ie: iexpr) :=
    ∀ iσ ig iσ' ig' (iargv ivret: ival),
    rtc_prim_step' (App ie (Val iargv), (iσ, ig)) (Val ivret, (iσ', ig')) →
    prim_step'_safe ie iσ ig →
    ∀ sσ sg (sargv svret: sval),
    val_relation sargv iargv →
    abstraction sσ sg iσ ig →
    ∃ sσ' sg',
      head_step (ExternalOp o (Val sargv)) sσ sg [] (Val svret) sσ' sg' [] ∧
      val_relation svret ivret
  .

  Context (op_impl_ok: ∀ o, op_simulated o (op_impl o)).

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

  (* Check to make sure the translation of ExternalOp is not vacuous *)
  Lemma expr_impl_ExternalOp o :
    expr_impl (λ: "x", ExternalOp o (Var "x")) (λ: "x", Atomically #() (App (Val (op_impl o)) (Var "x"))).
  Proof. repeat econstructor. Qed.

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

  Hint Constructors val_impl expr_impl val_relation : core.

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
  Proof.
    induction iv1, iv2; simpl; intros ? ? Hv1 Hv2;
      (* exploit is_comparable *)
      (try contradiction);
      (inversion 1; inversion 1; subst; eauto);
      rewrite ?val_lit_eq_iff ?val_pair_eq_iff ?val_injl_eq_iff ?val_injr_eq_iff //;
      naive_solver.
  Qed.

  Lemma expr_impl_bin_op_eval op sv1 sv2 iv1 iv2 :
        val_impl sv1 iv1 →
        val_impl sv2 iv2 →
        match bin_op_eval op iv1 iv2 with
        | Some iv' => ∃ sv', bin_op_eval op sv1 sv2 = Some sv' ∧ val_impl sv' iv'
        | None => bin_op_eval op sv1 sv2 = None
         end.
  Proof.
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

  Ltac inv_expr_impl :=
     repeat match goal with
        | H : expr_impl ?se ?ie |- _ =>
          try (is_var ie; fail 1);
          is_var se; inversion H; clear H; subst
        | H : val_impl ?se ?ie |- _ =>
          try (is_var ie; fail 1);
          is_var se; inversion H; clear H; subst
     end.

  Theorem head_step_atomic_simulation ie1 iσ1 ig1 κ ie2 iσ2 ig2 iefs se1 sσ1 sg1 :
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
    destruct ie1; subst; intros Hstep Himpl Habstr; try inversion Hstep; intuition eauto; subst.
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
           { apply val_relation_to_val_impl in Hrel.
             repeat econstructor; rewrite ?Hlook => //=.
             repeat econstructor.
           }
           (* This case is ok, but for the next one: *)
           (* TODO: either need to add an assumption that source program
              never tries to write a higher order value -- in which case we can go from
              val_impl to val_relation *)
           (* That or we just switch to doing this in SProp *)
  Abort.


  Theorem atomic_concurrent_refinement se ie :
    (* se compiles to ie *)
    expr_impl se ie →
    ∀ sσ sg iσ ig,
    abstraction sσ sg iσ ig →
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
