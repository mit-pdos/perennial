From stdpp Require Import gmap.
From Perennial.goose_lang Require Export lang.
Require Import Program.

(* This file contains some metatheory about GooseLang,
  which is not needed for verifying programs. *)

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ffi_semantics}.

Definition binder_vars (b: binder) : gset string :=
  match b with
  | BNamed x => {[x]}
  | BAnon => ∅
  end.

(* This returns all variables, bound and free, occurring in an expression *)
Fixpoint expr_vars (e : expr) : gset string :=
  match e with
  | Val v => val_vars v
  | Var x => {[x]}
  | Primitive0 _ => ∅
  | Rec f x e => binder_vars f ∪ binder_vars x ∪ expr_vars e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load e
  | ExternalOp _ e | Primitive1 _ e =>
     expr_vars e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Atomically e1 e2 | Primitive2 _ e1 e2 =>
     expr_vars e1 ∪ expr_vars e2
  | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2 | Resolve e0 e1 e2 =>
     expr_vars e0 ∪ expr_vars e1 ∪ expr_vars e2
  | NewProph => ∅
  end
with val_vars (v : val) : gset string :=
  match v with
  | LitV _ | ExtV _ => ∅
  | RecV f x e => binder_vars f ∪ binder_vars x ∪ expr_vars e
  | PairV v1 v2 => val_vars v1 ∪ val_vars v2
  | InjLV v | InjRV v => val_vars v
  end.

Lemma expr_vars_subst e x es : x ∉ expr_vars e → subst x es e = e.
Proof.
  induction e; rewrite /=; try (destruct op); rewrite ?bool_decide_spec ?andb_True=> ?;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
  set_solver.
Qed.

(* Closed expressions and values. *)
Fixpoint is_closed_expr (X : list string) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val v
  | Var x => bool_decide (x ∈ X)
  | Primitive0 _ => true
  | Rec f x e => is_closed_expr (f :b: x :b: X) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Load e
  | ExternalOp _ e | Primitive1 _ e =>
     is_closed_expr X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Atomically e1 e2 | Primitive2 _ e1 e2 =>
     is_closed_expr X e1 && is_closed_expr X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2 | Resolve e0 e1 e2 =>
     is_closed_expr X e0 && is_closed_expr X e1 && is_closed_expr X e2
  | NewProph => true
  end
with is_closed_val (v : val) : bool :=
  match v with
  | LitV _ | ExtV _ => true
  | RecV f x e => is_closed_expr (f :b: x :b: []) e
  | PairV v1 v2 => is_closed_val v1 && is_closed_val v2
  | InjLV v | InjRV v => is_closed_val v
  end.


Lemma is_closed_expr_prim1_iff X op e:
  is_closed_expr X (Primitive1 op e) <-> is_closed_expr X e.
Proof.
  destruct op; eauto.
Qed.

Lemma is_closed_expr_prim2_iff X op e1 e2:
  is_closed_expr X (Primitive2 op e1 e2) <-> is_closed_expr X e1 && is_closed_expr X e2.
Proof.
  destruct op; eauto.
Qed.

Lemma is_closed_weaken X Y e : is_closed_expr X e → X ⊆ Y → is_closed_expr Y e.
Proof. revert X Y; induction e; try naive_solver (eauto; set_solver).
       - intros. move: H. rewrite ?is_closed_expr_prim1_iff; eauto.
       - intros. move: H. rewrite ?is_closed_expr_prim2_iff; eauto.
         naive_solver.
Qed.

Lemma is_closed_weaken_nil X e : is_closed_expr [] e → is_closed_expr X e.
Proof. intros. by apply is_closed_weaken with [], list_subseteq_nil. Qed.

Lemma is_closed_subst X e x v :
  is_closed_val v → is_closed_expr (x :: X) e → is_closed_expr X (subst x v e).
Proof.
  intros Hv. revert X.
  induction e=> X /= ?; try destruct op; destruct_and?; split_and?; simplify_option_eq;
    try match goal with
    | H : ¬(_ ∧ _) |- _ => apply not_and_l in H as [?%dec_stable|?%dec_stable]
    end; eauto using is_closed_weaken with set_solver.
Qed.
Lemma is_closed_subst' X e x v :
  is_closed_val v → is_closed_expr (x :b: X) e → is_closed_expr X (subst' x v e).
Proof. destruct x; eauto using is_closed_subst. Qed.

(* Substitution *)
Lemma subst_is_closed X e x es : is_closed_expr X e → x ∉ X → subst x es e = e.
Proof.
  revert X. induction e=> X /=; try (destruct op); rewrite ?bool_decide_spec ?andb_True=> ??;
    repeat case_decide; simplify_eq/=; f_equal; intuition eauto with set_solver.
Qed.

Lemma subst_is_closed_nil e x v : is_closed_expr [] e → subst x v e = e.
Proof. intros. apply subst_is_closed with []; set_solver. Qed.

Lemma subst_subst e x v v' :
  subst x v (subst x v' e) = subst x v' e.
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst' e x v v' :
  subst' x v (subst' x v' e) = subst' x v' e.
Proof. destruct x; simpl; auto using subst_subst. Qed.

Lemma subst_subst_ne e x y v v' :
  x ≠ y → subst x v (subst y v' e) = subst y v' (subst x v e).
Proof.
  intros. induction e; simpl; try (f_equal; by auto);
    simplify_option_eq; auto using eq_sym, subst_is_closed_nil with f_equal.
Qed.
Lemma subst_subst_ne' e x y v v' :
  x ≠ y → subst' x v (subst' y v' e) = subst' y v' (subst' x v e).
Proof. destruct x, y; simpl; auto using subst_subst_ne with congruence. Qed.

Lemma subst_rec' f y e x v :
  x = f ∨ x = y ∨ x = BAnon →
  subst' x v (Rec f y e) = Rec f y e.
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.
Lemma subst_rec_ne' f y e x v :
  (x ≠ f ∨ f = BAnon) → (x ≠ y ∨ y = BAnon) →
  subst' x v (Rec f y e) = Rec f y (subst' x v e).
Proof. intros. destruct x; simplify_option_eq; naive_solver. Qed.

Lemma  bin_op_eval_closed op v1 v2 v':
  is_closed_val v1 → is_closed_val v2 → bin_op_eval op v1 v2 = Some v' →
  is_closed_val v'.
Proof.
  rewrite /bin_op_eval /bin_op_eval_bool /bin_op_eval_shift /bin_op_eval_word /bin_op_eval_string /bin_op_eval_eq;
    repeat case_match; try by naive_solver.
Qed.

Lemma heap_closed_alloc σ l n w :
  (0 < n)%Z →
  is_closed_val w →
  map_Forall (λ _ v, is_closed_val (snd v)) (heap σ) →
  (∀ i : Z, (0 ≤ i)%Z → (i < n)%Z → heap σ !! (l +ₗ i) = None) →
  map_Forall (λ _ v, is_closed_val (snd v))
             (heap_array l (replicate (Z.to_nat n) (Free w)) ∪ heap σ).
Proof.
  intros Hn Hw Hσ Hl.
  eapply (map_Forall_ind
            (λ k v, ((heap_array l (fmap Free (replicate (Z.to_nat n) w)) ∪ heap σ)
                       !! k = Some v))).
  - apply map_Forall_empty.
  - intros m i x Hi Hix Hkwm Hm.
    apply map_Forall_insert_2; auto.
    apply lookup_union_Some in Hix; last first.
    { eapply heap_array_map_disjoint. rewrite fmap_replicate.
        rewrite replicate_length Z2Nat.id; auto with lia. }
    destruct Hix as [Hlook|[j Hj]%elem_of_map_to_list%elem_of_list_lookup_1].
    + eapply heap_array_lookup in Hlook as (?&?&?&Hlook).
      rewrite list_lookup_fmap in Hlook.
      eapply fmap_Some_1 in Hlook as (?&Hlook&Hf).
      eapply lookup_replicate_1 in Hlook as [-> Hlt%inj_lt].
      rewrite !Z2Nat.id in Hlt; subst; eauto with lia.
    + apply map_Forall_to_list in Hσ.
      by eapply Forall_lookup in Hσ; eauto; simpl in *.
  - apply map_Forall_to_list, Forall_forall.
    intros [? ?] ?%elem_of_map_to_list.
    by rewrite fmap_replicate.
Qed.

Lemma fill_item_closed X K e :
  is_closed_expr X (fill_item K e) →
  is_closed_expr X e.
Proof.
  revert e. induction K => e //=; try naive_solver; try (destruct op; naive_solver).
Qed.

Lemma fill_closed X K e :
  is_closed_expr X (fill K e) →
  is_closed_expr X e.
Proof.
  revert e. induction K => e; first done.
  rewrite /= => Hclo.  apply IHK in Hclo. eapply fill_item_closed; eauto.
Qed.

(* The stepping relation preserves closedness *)
(*
Lemma head_step_is_closed e1 σ1 obs e2 σ2 es :
  is_closed_expr [] e1 →
  map_Forall (λ _ v, is_closed_val (snd v)) σ1.(heap) →
  head_step e1 σ1 obs e2 σ2 es →

  is_closed_expr [] e2 ∧ Forall (is_closed_expr []) es ∧
  map_Forall (λ _ v, is_closed_val (snd v)) σ2.(heap).
Proof.
  intros Cl1 Clσ1 STEP.
  induction STEP; simpl in *; split_and!.
    try apply map_Forall_insert_2; try by naive_solver.
  - subst. repeat apply is_closed_subst'; naive_solver.
  - unfold un_op_eval in *. repeat case_match; naive_solver.
  - eapply bin_op_eval_closed; eauto; naive_solver.
  - by apply heap_closed_alloc.
  - case_match; try apply map_Forall_insert_2; by naive_solver.
Qed.
*)

(* Parallel substitution with maps of values indexed by strings *)
Definition binder_delete {A} (x : binder) (vs : gmap string A) : gmap string A :=
  if x is BNamed x' then delete x' vs else vs.
Definition binder_insert {A} (x : binder) (v : A) (vs : gmap string A) : gmap string A :=
  if x is BNamed x' then <[x':=v]>vs else vs.

Lemma binder_insert_fmap {A B : Type} (f : A → B) (x : A) b vs :
  f <$> binder_insert b x vs = binder_insert b (f x) (f <$> vs).
Proof. destruct b; rewrite ?fmap_insert //. Qed.
Lemma binder_delete_fmap {A B : Type} (f : A → B) b vs :
  f <$> binder_delete b vs = binder_delete b (f <$> vs).
Proof. destruct b; rewrite ?fmap_delete //. Qed.
Lemma lookup_binder_delete_None {A : Type} (vs : gmap string A) x y :
  binder_delete x vs !! y = None ↔ x = BNamed y ∨ vs !! y = None.
Proof. destruct x; rewrite /= ?lookup_delete_None; naive_solver. Qed.

Fixpoint subst_map (vs : gmap string val) (e : expr) : expr :=
  match e with
  | Val _ => e
  | Var y => if vs !! y is Some v then Val v else Var y
  | Rec f y e => Rec f y (subst_map (binder_delete y (binder_delete f vs)) e)
  | App e1 e2 => App (subst_map vs e1) (subst_map vs e2)
  | UnOp op e => UnOp op (subst_map vs e)
  | BinOp op e1 e2 => BinOp op (subst_map vs e1) (subst_map vs e2)
  | If e0 e1 e2 => If (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Pair e1 e2 => Pair (subst_map vs e1) (subst_map vs e2)
  | Fst e => Fst (subst_map vs e)
  | Snd e => Snd (subst_map vs e)
  | InjL e => InjL (subst_map vs e)
  | InjR e => InjR (subst_map vs e)
  | Case e0 e1 e2 => Case (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | Fork e => Fork (subst_map vs e)
  | Atomically el e => Atomically (subst_map vs el) (subst_map vs e)
  | Primitive0 op => Primitive0 op
  | Primitive1 op e => Primitive1 op (subst_map vs e)
  | Primitive2 op e1 e2 => Primitive2 op (subst_map vs e1) (subst_map vs e2)
  | ExternalOp op e => ExternalOp op (subst_map vs e)
  | CmpXchg e0 e1 e2 => CmpXchg (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  | NewProph => NewProph
  | Resolve e0 e1 e2 => Resolve (subst_map vs e0) (subst_map vs e1) (subst_map vs e2)
  end.

Lemma subst_map_empty e : subst_map ∅ e = e.
Proof.
  assert (∀ x, binder_delete x (∅:gmap _ val) = ∅) as Hdel.
  { intros [|x]; by rewrite /= ?delete_empty. }
  induction e; simplify_map_eq; rewrite ?Hdel; auto with f_equal.
Qed.
Lemma subst_map_insert x v vs e :
  subst_map (<[x:=v]>vs) e = subst x v (subst_map (delete x vs) e).
Proof.
  revert vs. assert (∀ (y : binder) (vs : gmap _ val), y ≠ BNamed x →
    binder_delete y (<[x:=v]> vs) = <[x:=v]> (binder_delete y vs)) as Hins.
  { intros [|y] vs ?; rewrite /= ?delete_insert_ne //; congruence. }
  assert (∀ (y : binder) (vs : gmap _ val),
    binder_delete y (delete x vs) = delete x (binder_delete y vs)) as Hdel.
  { by intros [|y] ?; rewrite /= 1?delete_commute. }
  induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end. by case (vs !! _); simplify_option_eq.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !Hins // !Hdel. eauto with f_equal.
    + by rewrite /= delete_insert_delete delete_idemp.
    + by rewrite /= Hins // delete_insert_delete !Hdel delete_idemp.
Qed.
Lemma subst_map_insert' x v vs e:
    subst_map (<[x:=v]> vs) e = subst_map vs (subst x v e).
Proof.
  revert vs. assert (∀ (y : binder) (vs : gmap _ val), y ≠ BNamed x →
    binder_delete y (<[x:=v]> vs) = <[x:=v]> (binder_delete y vs)) as Hins.
  { intros [|y] vs ?; rewrite /= ?delete_insert_ne //; congruence. }
  induction e=> vs; simplify_map_eq; auto with f_equal.
  - match goal with
    | |- context [ <[?x:=_]> _ !! ?y ] =>
       destruct (decide (x = y)); simplify_map_eq=> //
    end.
  - destruct (decide _) as [[??]|[<-%dec_stable|[<-%dec_stable ?]]%not_and_l_alt].
    + rewrite !Hins // IHe //.
    + by rewrite /= delete_insert_delete.
    + by rewrite /= Hins // delete_insert_delete.
Qed.
Lemma subst_map_subst_comm x v vs e:
  x ∉ dom (gset string) vs →
  subst x v (subst_map vs e) = subst_map vs (subst x v e).
Proof.
  intros Hnin.
  rewrite -subst_map_insert'. rewrite subst_map_insert. f_equal.
  f_equal. rewrite delete_notin //.
  apply not_elem_of_dom; eauto.
Qed.
Lemma subst_map_binder_insert b v vs e :
  subst_map (binder_insert b v vs) e =
  subst' b v (subst_map (binder_delete b vs) e).
Proof. destruct b; rewrite ?subst_map_insert //. Qed.
Lemma subst_map_binder_insert' b v vs e:
  subst_map (binder_insert b v vs) e =
  subst_map vs (subst' b v e).
Proof. destruct b; rewrite ?subst_map_insert' //=. Qed.

Lemma binder_delete_commute b1 b2 (vs: gmap string val):
  binder_delete b1 (binder_delete b2 vs) =
  binder_delete b2 (binder_delete b1 vs).
Proof. destruct b1, b2; rewrite //= delete_commute //. Qed.

(* subst_map on closed expressions *)
Lemma subst_map_is_closed X e vs :
  is_closed_expr X e →
  (∀ x, x ∈ X → vs !! x = None) →
  subst_map vs e = e.
Proof.
  revert X vs. assert (∀ x x1 x2 X (vs : gmap string val),
    (∀ x, x ∈ X → vs !! x = None) →
    x ∈ x2 :b: x1 :b: X →
    binder_delete x1 (binder_delete x2 vs) !! x = None).
  { intros x x1 x2 X vs ??. rewrite !lookup_binder_delete_None. set_solver. }
  induction e=> X vs /= ? HX; try (dependent destruction op); repeat case_match; naive_solver eauto with f_equal.
Qed.

Lemma subst_map_is_closed_nil e vs : is_closed_expr [] e → subst_map vs e = e.
Proof. intros. apply subst_map_is_closed with []; set_solver. Qed.

End goose_lang.
