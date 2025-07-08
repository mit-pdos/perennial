From Perennial.goose_lang Require Import notation.
From Coq Require Import ssreflect.
From New.golang.defn Require Import typing.
From New.golang.theory Require Import proofmode globals pkg loop chan.
From New.golang.theory Require Import mem.
From Perennial Require Import base.

From New.proof Require Import std.

From lithium Require Import hooks all.

Set Default Proof Using "Type".

(* copy of lithium tutorial, applied to GooseLang *)

(** * Definitions of Lithium functions *)
(** First, we define the Lithium functions that we will use later. *)
Section definitions.
  Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

  Definition expr_ok (e : expr) (G : val → iProp Σ) : iProp Σ :=
    WP e {{ G }}.

  Definition binop_ok (op : bin_op) (v1 v2 : val) (G : val → iProp Σ) : iProp Σ :=
    WP BinOp op v1 v2 {{ G }}.

  Definition unop_ok (op : un_op) (v : val) (G : val → iProp Σ) : iProp Σ :=
    WP UnOp op v {{ G }}.

  Definition if_ok `{!goGlobalsGS Σ} (v : val) (G1 G2 : iProp Σ) : iProp Σ :=
    ∃ b : bool, ⌜v = #b⌝ ∗ if b then G1 else G2.
End definitions.

(** * Boilerplate for setup *)
(** The following code is necessary to register the Lithium functions.
You can ignore it for the purposes of this tutorial. *)
Section setup.
  Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

  Class ExprOk (e : expr) : Type :=
    expr_ok_proof G : iProp_to_Prop (expr_ok e G).
  Class BinopOk (op : bin_op) (v1 v2 : val) : Type :=
    binop_ok_proof G : iProp_to_Prop (binop_ok op v1 v2 G).
  Class UnopOk (op : un_op) (v : val) : Type :=
    unop_ok_proof G : iProp_to_Prop (unop_ok op v G).
  Class IfOk (v : val) : Type :=
    if_ok_proof G1 G2 : iProp_to_Prop (if_ok v G1 G2).
End setup.

Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | expr_ok ?x1 => constr:(ExprOk x1)
  | binop_ok ?x1 ?x2 ?x3 => constr:(BinopOk x1 x2 x3)
  | unop_ok ?x1 ?x2 => constr:(UnopOk x1 x2)
  | if_ok ?x1 => constr:(IfOk x1)
  end.
Ltac liExtensible_to_i2p_hook P bind cont ::=
  lazymatch P with
  | expr_ok ?e ?G =>
      cont uconstr:(((_ : ExprOk _) _))
  | binop_ok ?op ?v1 ?v2 ?G =>
      cont uconstr:(((_ : BinopOk _ _ _) _))
  | unop_ok ?op ?v ?G =>
      cont uconstr:(((_ : UnopOk _ _) _))
  | if_ok ?v ?G1 ?G2 =>
      cont uconstr:(((_ : IfOk _) _ _))
  end.

Ltac liToSyntax_hook ::=
  change (expr_ok ?x1) with (li.bind1 (expr_ok x1));
  change (binop_ok ?x1 ?x2 ?x3) with (li.bind1 (binop_ok x1 x2 x3));
  change (unop_ok ?x1 ?x2) with (li.bind1 (unop_ok x1 x2)).

Ltac can_solve_hook ::= done.

Ltac liTStep :=
 liEnsureInvariant;
 first [
 liStep
]; liSimpl.

Ltac liTUnfold :=
  liFromSyntax; unfold expr_ok, binop_ok, unop_ok, if_ok.


(** * Tutorial *)
(** This is the start of the actual tutorial. *)
Section proofs.
  Context `{hG: heapGS Σ, !ffi_semantics _ _} `{!goGlobalsGS Σ}.

  (** For explanation, see the corresponding sections of the "Lithium
  by Example" chapter in Michael Sammler's dissertation. *)

  (** ** 1. Lithium basics *)
  Definition assert_two : expr :=
    let: "x" := #(W64 1) in
    let: "y" := "x" + #(W64 1) in
    std.Assert ("y" = #(W64 2)).

  Lemma assert_two_correct :
    ⊢ [{
      _ ← {expr_ok assert_two};
      done
    }  ].
  Proof.
    (** Prepare goal and unfold assert_two. *)
    iStartProof. unfold assert_two.
    (** Run Lithium. *)
    repeat liTStep; liShow.
    (** No progress since we have not defined the Lithium function [expr_ok] yet. *)
  Abort.

  (** Basic rules for [expr_ok] and [binop_ok]. *)
  Lemma expr_let x e1 e2 G :
    expr_ok (Let x e1 e2) G :-
      v1 ← {expr_ok e1};
      v2 ← {expr_ok (subst' x v1 e2)};
      return G v2.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e1).
    iApply (wp_wand with "HWP"). iIntros (?) "HWP".
    by wp_pures.
  Qed.
  Definition expr_let_inst := [instance expr_let].
  Global Existing Instance expr_let_inst | 2.

  Lemma expr_val v G :
    expr_ok (Val v) G :- return G v.
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition expr_val_inst := [instance expr_val].
  Global Existing Instance expr_val_inst.

  Lemma expr_binop op e1 e2 G :
    expr_ok (BinOp op e1 e2) G :-
      v1 ← {expr_ok e1};
      v2 ← {expr_ok e2};
      v  ← {binop_ok op v1 v2};
      return G v.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e1).
    iApply (wp_wand with "HWP"). iIntros (?) "HWP".
    wp_bind (e2).
    iApply (wp_wand with "HWP"). by iIntros (?) "HWP".
  Qed.
  Definition expr_binop_inst := [instance expr_binop].
  Global Existing Instance expr_binop_inst.

  Lemma binop_plus_int_int (n1 n2 : w64) G :
    binop_ok PlusOp #n1 #n2 G :-
      return G #(word.add n1 n2).
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_plus_int_int_inst := [instance binop_plus_int_int].
  Global Existing Instance binop_plus_int_int_inst.
  Lemma binop_minus_int_int (n1 n2 : w64) G :
    binop_ok MinusOp #n1 #n2 G :-
      return G #(word.sub n1 n2).
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_minus_int_int_inst := [instance binop_minus_int_int].
  Global Existing Instance binop_minus_int_int_inst.
  Lemma binop_eq_int_int (n1 n2 : w64) G :
    binop_ok EqOp #n1 #n2 G :-
      return G #(bool_decide (n1 = n2)).
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_eq_int_int_inst := [instance binop_eq_int_int].
  Global Existing Instance binop_eq_int_int_inst.

  Lemma expr_assert e G :
    expr_ok (std.Assert e) G :-
      v ← {expr_ok e};
      exhale ⌜v = #true⌝;
      return G #().
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e).
    iApply (wp_wand with "HWP"). iIntros (?) "[-> HWP]".
  Admitted.
  Definition expr_assert_inst := [instance expr_assert].
  Global Existing Instance expr_assert_inst.

  (** Now Lithium automatically verifies [assert_two]! *)
  Lemma assert_two_correct :
    ⊢ [{
      _ ← {expr_ok assert_two};
      done
    } ].
  Proof.
    iStartProof. unfold assert_two.
    repeat liTStep; liShow.
  Qed.

  (** ** 2. Operational model *)
  (** The operational semantics of Lithium are given by the [liTStep]
  tactic that executes one step of the Lithium interpreter. The state
  of the Lithium interpreter is of the form:

                           Γ; Δ |- ∃ x, G(x)

  where Γ is the Coq context, Δ is the Iris context, x is a tuple of
  existential quantifiers and G is the current Lithium program. Each
  step of the Lithium interpreter (i.e., each [liTStep]) transforms
  the state into a new state, i.e. it can be described mathematically
  as a transition

       Γ1; Δ1 |- ∃ x1, G1(x1) => Γ2; Δ2 |- ∃ x2, G2(x2)

  The execution ends when Lithium reaches [done]. A mathematical
  description of the steps of the Lithium interpreter can be found in
  Michael Sammler's dissertation. *)

  (** ** 3. Modular verification via inhale, exhale and quantifiers *)
  Definition add1 : val := λ: "v", "v" + #(W64 1).

  Definition fn_ok (v : val) (X : Type)
    (pre : X → val → iProp Σ) (post : X → val → iProp Σ) : iProp Σ :=
    □ ∃ f b e, ⌜v = RecV f b e⌝ ∗
    ∀ x va, pre x va -∗ ▷ WP subst' b va (subst' f v e) {{ vr, post x vr}}.
  Global Typeclasses Opaque fn_ok.

  Global Instance fn_ok_pers X v pre post :
    Persistent (fn_ok v X pre post).
  Proof. unfold fn_ok. apply _. Qed.

  Global Instance fn_ok_intro_pers X v pre post :
    IntroPersistent (fn_ok v X pre post) (fn_ok v X pre post).
  Proof. constructor. by iIntros "#?". Qed.

  Lemma prove_fn_ok X f a e pre post :
    fn_ok (RecV f a e) X pre post :-
      drop_spatial;
      ∀ (x : X) v vr,
      inhale pre x v;
      inhale fn_ok vr X pre post;
      v' ← {expr_ok (subst' a v (subst' f vr e))};
      exhale post x v';
      done.
  Proof.
    liTUnfold. unfold fn_ok. iIntros "#HWP !>".
    iExists _, _, _. iSplit; [done|].
    iIntros (x va) "Hpre". iModIntro.
    iLöb as "IH" forall (x va).
    iApply (wp_wand with "[-]").
    - iApply ("HWP" with "Hpre").
      iModIntro. iExists _, _, _. iSplit; [done|].
      iIntros (??) "?". iModIntro. by iApply "IH".
    - iIntros (?) "[$ _]".
  Qed.

  Lemma add1_correct :
    ⊢ fn_ok add1 w64
        (λ (n: w64) (v: val), ⌜v = #n⌝)
        (λ (n: w64) (v: val), ⌜v = #(word.add n (W64 1))⌝).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Qed.

  Definition assert_two_modular (add1 : val) : expr :=
    let: "x" := #(W64 1) in
    let: "y" := add1 "x" in
    std.Assert ("y" = #(W64 2)).

  (** These find functions are explained in 5. *)
  Definition FindFnOk (v : val) :=
  {| fic_A := sigT (λ X, (X → val → iProp Σ) * (X → val → iProp Σ))%type;
    fic_Prop '(existT X (pre, post)) := fn_ok v X pre post |}.
  Global Typeclasses Opaque FindFnOk.
  Lemma find_in_context_find_fn_ok v G:
    find_in_context (FindFnOk v) G :-
      pattern: X pre post, fn_ok v X pre post; return G (existT X (pre, post)).
  Proof. iDestruct 1 as (X pre post) "[Hv HT]". iExists _. by iFrame. Qed.
  Definition find_in_context_find_fn_ok_inst :=
    [instance find_in_context_find_fn_ok with FICSyntactic].
  Global Existing Instance find_in_context_find_fn_ok_inst | 1.

  Lemma expr_app e1 e2 G :
    expr_ok (App e1 e2) G  :-
      v2 ← {expr_ok e2};
      v1 ← {expr_ok e1};
      '(existT X (pre, post)) ← find_in_context (FindFnOk v1);
      ∃ x,
      exhale (pre x v2);
      ∀ v',
      inhale (post x v');
      return G v'.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e2). iApply (wp_wand with "HWP").
    iIntros (?) "HWP". wp_bind (e1). iApply (wp_wand with "HWP").
    iIntros (?) "[%a HWP]". destruct a as [?[??]] => /=. unfold fn_ok.
    iDestruct "HWP" as "[#(%&%&%&->&Hf) [% [Hpre HG]]]".
    iDestruct ("Hf" with "[$]") as "HWP".
    wp_pures. by iApply (wp_wand with "HWP").
  Qed.
  Definition expr_app_inst := [instance expr_app].
  Global Existing Instance expr_app_inst | 50.


  Lemma assert_two_modular_correct add1 :
    ⊢ [{
      inhale fn_ok add1 w64 (λ n v, ⌜v = #n⌝) (λ n v, ⌜v = #(word.add n 1)⌝);
      _ ← {expr_ok (assert_two_modular add1)};
      done
    } ].
  Proof.
    iStartProof. unfold assert_two_modular.
    repeat liTStep; liShow.
  Qed.

  (** ** 4. Continuations *)
  Definition fib : val := rec: "f" "x" :=
      if: "x" = #(W64 0) then
        #(W64 0)
      else if: "x" = #(W64 1) then
        #(W64 1)
      else
         "f" ("x" - #(W64 1)) + "f" ("x" - #(W64 2)).

  Lemma expr_if e0 e1 e2 G :
    expr_ok (If e0 e1 e2) G :-
      v ← {expr_ok e0};
      {if_ok v (expr_ok e1 G) (expr_ok e2 G)}.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e0).
    iApply (wp_wand with "HWP"). iIntros (?) "[%b [-> HWP]]".
    by destruct b; wp_pures.
  Qed.
  Definition expr_if_inst := [instance expr_if].
  Global Existing Instance expr_if_inst.

  Lemma if_bool (b : bool) (G1 G2: iProp Σ) :
    if_ok #b G1 G2 :-
      if: b
      | return G1
      | return G2.
  Proof.
    liTUnfold. iIntros "Hif".
    iExists _. iSplit; [done|].
    destruct b.
    - iDestruct "Hif" as "[HG _]". by iApply "HG".
    - iDestruct "Hif" as "[_ HG]". iApply "HG". naive_solver.
  Qed.
  Definition if_bool_inst := [instance if_bool].
  Global Existing Instance if_bool_inst | 10.

  (* Without this being transparent, there's a step that tries to run
     `liExInst` which requires unifying:
    eunify (@to_val ext (@word.rep (Zpos (xO (xO (xO (xO (xO (xO xH))))))) w64_word_instance)
              (@into_val_w64 ext)
              (@word.sub (Zpos (xO (xO (xO (xO (xO (xO xH))))))) w64_word_instance n (W64 (Zpos xH))))
      (@to_val ext w64 (@into_val_w64 ext) _).

     The following unification fails because the LHS has `word.rep
     w64_word_instance` while the RHS has `w64`
     ```
     lazymatch goal with |- ?a = ?b => unify a b with solve_protected_eq_db end;
     ```
     because `solve_protected_eq_db` marks constants as opaque by default.
 *)
  Global Hint Transparent w64 : solve_protected_eq_db.

  Lemma fib_correct :
    ⊢ fn_ok fib unit (λ _ v, ∃ n : w64, ⌜v = #n⌝ ∗ ⌜(0 ≤ uint.Z n)%Z⌝)
        (λ _ v, ∃ n' : w64, ⌜v = #n'⌝ ∗ ⌜(0 ≤ uint.Z n')%Z⌝).
  Proof using goGlobalsGS0.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep.
    Unshelve. all: unshelve_sidecond.
    - word.
    - word.
    - word.
  Qed.

  (** ** 5. Separation logic *)
  Lemma expr_alloc `{!IntoVal V} (v: V) G :
    expr_ok (mem.alloc #v) G :-
      ∀ (l: loc),
      inhale (l ↦ v);
      return G #l.
  Proof. liTUnfold. iIntros "HG". by iApply wp_alloc. Qed.
  Definition expr_alloc_inst := [instance @expr_alloc].
  Global Existing Instance expr_alloc_inst.

  Definition FindPointsTo (l : loc) :=
  {| fic_A := sigT (fun (V: Type) => (IntoVal V * V)%type);
     fic_Prop '(existT V (_, v)) := (l ↦ v)%I; |}.
  Global Typeclasses Opaque FindPointsTo.

  (* Questions:

  Why are these lemmas for Store e1 e2 (arbitrary expressions) and not values?
  Can we make them values and add wp_pures automation in between?

  How do we deal with the fact that functions take only argument?

  *)

  Lemma expr_store e1 e2 G :
    expr_ok (Store e1 e2) G :-
      v2 ← {expr_ok e2};
      ∀ (V2: Type) (H: IntoVal V2) (v2': V2),
      exhale ⌜v2 = #v2'⌝;
      v1 ← {expr_ok e1};
      ∀ (l1: loc),
      exhale ⌜v1 = #l1⌝;
      (* TODO: we can actually do a FindPointsTo with a fixed value type of V2 *)
      _ ← find_in_context (FindPointsTo l1);
      inhale (l1 ↦ v2');
      return G v2.
  Proof.
    (*
    liTUnfold. iIntros "HWP". wp_bind (e2).
    iApply (wp_wand with "HWP"). iIntros (?) "HWP".
    wp_bind (e1). iApply (wp_wand with "HWP"). iIntros (?) "[% [? HWP]]/=".
    by iApply (wp_store with "[$]").
    *)
  Abort.

  (* rest of tutorial *)

  (*
  Definition expr_store_inst := [instance expr_store].
  Global Existing Instance expr_store_inst.

  Lemma expr_load e G :
    expr_ok (Load e) G :-
      v ← {expr_ok e};
      vl ← find_in_context (FindPointsTo v);
      inhale (v ↦ vl);
      return G vl.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e).
    iApply (wp_wand with "HWP"). iIntros (?) "[% [? HWP]]/=".
    by iApply (wp_load with "[$]").
  Qed.
  Definition expr_load_inst := [instance expr_load].
  Global Existing Instance expr_load_inst.


  Lemma find_points_to v1 G:
    find_in_context (FindPointsTo v1) G :-
      pattern: v, v1 ↦ v; return G v.
  Proof. iDestruct 1 as (v) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Definition find_points_to_inst :=
    [instance find_points_to with FICSyntactic].
  Global Existing Instance find_points_to_inst | 1.

  Global Instance related_to_points_to A vl v : RelatedTo (λ x : A, vl ↦ v x)%I | 100 :=
    {| rt_fic := FindPointsTo vl |}.

  Lemma expr_load_alt e G :
    expr_ok (Load e) G :-
      v ← {expr_ok e};
      ∃ vl, exhale (v ↦ vl);
      inhale (v ↦ vl);
      return G vl.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e).
    iApply (wp_wand with "HWP"). iIntros (?) "[% [? HWP]]/=".
    by iApply (wp_load with "[$]").
  Qed.
  Definition expr_load_alt_inst := [instance expr_load_alt].

  Lemma subsume_points_to_points_to A vl v1 v2 G :
    subsume (vl ↦ v1) (λ x : A, vl ↦ (v2 x)) G :-
     ∃ x, exhale ⌜v1 = v2 x⌝;
     return G x.
  Proof. liTUnfold. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_points_to_points_to_inst := [instance subsume_points_to_points_to].
  Global Existing Instance subsume_points_to_points_to_inst.

  Definition points_to_test : val := λ: <>,
      let: "l" := Alloc in
      "l" <- !"l";;
      "l".

  Lemma points_to_test_correct :
    ⊢ fn_ok points_to_test unit (λ _ _, True) (λ _ v, ∃ z : Z, v ↦ #z ∗ ⌜0 ≤ z⌝).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Qed.

  Section alt.
    Local Existing Instance expr_load_alt_inst | 0.
    Lemma points_to_test_correct_alt :
      ⊢ fn_ok points_to_test unit (λ _ _, True) (λ _ v, ∃ z : Z, v ↦ #z ∗ ⌜0 ≤ z⌝).
    Proof.
      iStartProof. iApply prove_fn_ok. simpl.
      repeat liTStep; liShow.
    Qed.
  End alt.

  (** ** 6. Reasoning about abstract predicates  *)

  Fixpoint is_list (v : val) (xs : list val) : iProp Σ :=
    match xs with
    | [] => ⌜v = #NULL⌝
    | x :: xs => ∃ vnext, v ↦ (x, vnext)%V ∗ is_list vnext xs
  end.
  Global Typeclasses Opaque is_list.
  Global Opaque is_list.

  Lemma is_list_cons v x xs :
    is_list v (x::xs) = (∃ vnext, v ↦ (x, vnext)%V ∗ is_list vnext xs)%I.
  Proof. done. Qed.
  Lemma is_list_NULL v xs :
    is_list v xs -∗ ⌜xs = [] ↔ v = #NULL⌝.
  Proof.
    destruct xs. { unfold_opaque is_list. naive_solver. }
    rewrite is_list_cons. iDestruct 1 as (?) "[Hv _]".
    unfold val_pointsto. iDestruct "Hv" as (? ->) "?". naive_solver.
  Qed.

  (** *** Lithium rules for pairs *)
  (** These rules are used by the functions on lists. *)
  Lemma expr_unop op e G :
    expr_ok (UnOp op e) G :-
      v  ← {expr_ok e};
      vr ← {unop_ok op v};
      return G vr.
  Proof.
    liTUnfold. iIntros "HWP". wp_bind (e).
    iApply (wp_wand with "HWP"). by iIntros (?) "HWP".
  Qed.
  Definition expr_unop_inst := [instance expr_unop].
  Global Existing Instance expr_unop_inst.

  Lemma unop_fst v1 v2 G :
    unop_ok FstOp (v1, v2) G :- return G v1.
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition unop_fst_inst := [instance unop_fst].
  Global Existing Instance unop_fst_inst.
  Lemma unop_snd v1 v2 G :
    unop_ok SndOp (v1, v2) G :- return G v2.
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition unop_snd_inst := [instance unop_snd].
  Global Existing Instance unop_snd_inst.

  Lemma binop_pair v1 v2 G :
    binop_ok PairOp v1 v2 G :- return G (v1, v2)%V.
  Proof. liTUnfold. iIntros "HG". by wp_pures. Qed.
  Definition binop_pair_inst := [instance binop_pair].
  Global Existing Instance binop_pair_inst.

  (** *** Constructing linked lists *)
  Definition empty_code : val := λ: <>, #NULL.
  Definition cons_code : val := λ: "a",
      let: "v" := Fst "a" in
      let: "l" := Snd "a" in
      let: "new_l" := Alloc in
      "new_l" <- ("v", "l");;
      "new_l".

  Definition mklist_code (empty cons : val) : val := λ: <>,
    let: "l" := empty #0 in
    let: "l" := cons (#1, "l") in
    let: "l" := cons (#2, "l") in
    "l".


  Lemma empty_code_correct :
    ⊢ fn_ok empty_code unit (λ _ _, True) (λ _ v, is_list v []).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma simpl_list_empty xs G :
    simplify_goal (is_list #NULL xs) G :- exhale ⌜xs = []⌝; return G.
  Proof. liTUnfold. iIntros "[-> $]". by unfold_opaque is_list. Qed.
  Definition simpl_list_empty_inst := [instance simpl_list_empty with 50%N].
  Global Existing Instance simpl_list_empty_inst.

  Lemma empty_code_correct :
    ⊢ fn_ok empty_code unit (λ _ _, True) (λ _ v, is_list v []).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Qed.


  Lemma cons_correct :
    ⊢ fn_ok cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (x, v)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Abort.

  Definition FindList (v : val) :=
  {| fic_A := iProp Σ; fic_Prop P := P; |}.
  Global Typeclasses Opaque FindList.
  Global Instance related_to_list A v xs : RelatedTo (λ x : A, is_list v (xs x)) | 100
    := {| rt_fic := FindList v |}.

  Lemma find_list v G:
    find_in_context (FindList v) G :-
      pattern: xs, is_list v xs; return G (is_list v xs).
  Proof. iDestruct 1 as (xs) "[Hl HT]". iExists _. by iFrame. Qed.
  Definition find_list_inst :=
    [instance find_list with FICSyntactic].
  Global Existing Instance find_list_inst | 1.

  Lemma find_list_points_to v G:
    find_in_context (FindList v) G :-
      pattern: v2, v ↦ v2; return G (v ↦ v2).
  Proof. iDestruct 1 as (?) "[Hl HT]". iExists _. by iFrame. Qed.
  Definition find_list_points_to_inst :=
    [instance find_list_points_to with FICSyntactic].
  Global Existing Instance find_list_points_to_inst | 10.

  Lemma subsume_list_list A v xs1 xs2 G :
    subsume (is_list v xs1) (λ x : A, is_list v (xs2 x)) G :-
     ∃ x, exhale ⌜xs1 = xs2 x⌝;
     return G x.
  Proof. liTUnfold. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_list_list_inst := [instance subsume_list_list].
  Global Existing Instance subsume_list_list_inst.

  Lemma subsume_points_to_list A vl v xs G :
    subsume (vl ↦ v) (λ x : A, is_list vl (xs x)) G :-
     ∃ x v1 v2 xs',
     exhale ⌜v = (v1, v2)%V⌝ ∗ is_list v2 xs' ∗ ⌜xs x = v1 :: xs'⌝;
     return G x.
  Proof.
    liTUnfold. iIntros "[% [% [% [% [[-> [Hl %Hxs]] ?]]]]] ?".
    iExists _. iFrame. rewrite Hxs is_list_cons. iExists _. iFrame.
  Qed.
  Definition subsume_points_to_list_inst := [instance subsume_points_to_list].
  Global Existing Instance subsume_points_to_list_inst.


  Lemma cons_correct :
    ⊢ fn_ok cons_code (val * list val)
      (λ '(x, xs) a, ∃ v, ⌜a = (x, v)%V⌝ ∗ is_list v xs)
      (λ '(x, xs) r, is_list r (x :: xs)).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Qed.

  Lemma mklist_correct empty cons :
    fn_ok empty unit (λ _ _, True) (λ _ v, is_list v []) -∗
    fn_ok cons (val * list val) (λ '(x, xs) a, ∃ v, ⌜a = (x, v)%V⌝ ∗ is_list v xs) (λ '(x, xs) r, is_list r (x :: xs)) -∗
    fn_ok (mklist_code empty cons) unit (λ _ _, True) (λ _ v, is_list v [ #2; #1 ]).
  Proof.
    iStartProof. iIntros "#? #?". iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Qed.

  (** *** Destructing linked lists *)
  Definition head_code : val := λ: "l", Fst (! "l").

  Lemma head_correct :
    ⊢ fn_ok head_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs ∗ ⌜0 < length xs⌝)
      (λ '(va, xs) r, ⌜head xs = Some r⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Abort.

  Lemma find_points_to_list v G:
    find_in_context (FindPointsTo v) G :-
      pattern: xs, is_list v xs;
      exhale ⌜0 < length xs⌝;
      ∀ v' x xs',
      inhale ⌜xs = x::xs'⌝ ∗ is_list v' xs';
      return G (x, v')%V.
  Proof.
    liTUnfold. iIntros "[% [Hl [% HG]]]".
    destruct xs => //=. rewrite is_list_cons.
    iDestruct "Hl" as (?) "[??]". iExists _ => /=. iFrame.
    iApply "HG". by iFrame.
  Qed.
  Definition find_points_to_list_inst :=
    [instance find_points_to_list with FICSyntactic].
  Global Existing Instance find_points_to_list_inst | 10.

  Lemma head_correct :
    ⊢ fn_ok head_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs ∗ ⌜0 < length xs⌝)
      (λ '(va, xs) r, ⌜head xs = Some r⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
  Qed.

  (** This tests that using [expr_load_alt] instead of [expr_load] works as well. *)
  Section alt.
    Local Existing Instance expr_load_alt_inst | 0.

    Lemma head_correct_alt :
      ⊢ fn_ok head_code (val * list val)
        (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs ∗ ⌜0 < length xs⌝)
        (λ '(va, xs) r, ⌜head xs = Some r⌝ ∗ is_list va xs).
    Proof.
      iStartProof. iApply prove_fn_ok. simpl.
      repeat liTStep; liShow.
    Qed.
  End alt.

  Definition length_code : val := rec: "f" "l" :=
      if: "l" = #NULL then
        #0
      else
        let: "r" := "f" (Snd (! "l")) in
        "r" + #1.

  Definition FindIsNULL (v : val) :=
  {| fic_A := bool; fic_Prop b := (⌜b ↔ v = #NULL⌝ : iProp Σ)%I |}.
  Global Typeclasses Opaque FindIsNULL.

  Lemma binop_eq_NULL v G :
    binop_ok EqOp v #NULL G :-
      b ← find_in_context (FindIsNULL v);
      return G #b.
  Proof.
    liTUnfold. iIntros "[% [Hb HG]]". simpl. iDestruct "Hb" as %?.
    wp_pure _. 2: by iFrame.
    simpl. repeat case_match; destruct b; naive_solver.
  Qed.
  Definition binop_eq_NULL_inst := [instance binop_eq_NULL].
  Global Existing Instance binop_eq_NULL_inst.

  Lemma find_null_points_to v G:
    find_in_context (FindIsNULL v) G :-
      pattern: v2, v ↦ v2;
      inhale v ↦ v2;
      return G false.
  Proof.
    liTUnfold.
    iDestruct 1 as (?) "[Hl HG]".
    unfold val_pointsto. iDestruct "Hl" as (? ->) "?".
    iExists false => /=. iSplit; [naive_solver|]. iApply "HG".
    iExists _. by iFrame.
  Qed.
  Definition find_null_points_to_inst :=
    [instance find_null_points_to with FICSyntactic].
  Global Existing Instance find_null_points_to_inst | 10.

  Lemma find_null_list v G:
    find_in_context (FindIsNULL v) G :-
      pattern: xs, is_list v xs;
      inhale is_list v xs;
      return G (bool_decide (xs = [])).
  Proof.
    liTUnfold.
    iDestruct 1 as (?) "[Hl HG]".
    iDestruct (is_list_NULL with "Hl") as %?.
    iExists _. iDestruct ("HG" with "Hl") as "$".
    simpl. iPureIntro. naive_solver.
  Qed.
  Definition find_null_list_inst :=
    [instance find_null_list with FICSyntactic].
  Global Existing Instance find_null_list_inst | 10.

  Lemma length_correct :
    ⊢ fn_ok length_code (val * list val)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list v xs)
      (λ '(va, xs) r, ⌜r = #(length xs)⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
    Unshelve. all: unshelve_sidecond.
    - by destruct x0.
    - do 2 f_equal. lia.
  Qed.

  (** ** 7. Verifying higher-order functions using Lithium *)

  Definition contains_code : val := rec: "f" "x" :=
      let: "l" := Fst "x" in
      let: "cb" := Snd "x" in
      if: "l" = #NULL then
        #false
      else if: "cb" (Fst (! "l")) then
        #true
      else
        "f" (Snd (! "l"), "cb").

  Global Instance related_to_fn_ok A v X pre post : RelatedTo (λ x : A, fn_ok v X (pre x) (post x)) | 100
    := {| rt_fic := FindFnOk v |}.

  Lemma subsume_fn A v X pre1 pre2 post1 post2 G :
    subsume (fn_ok v X pre1 post1) (λ x : A, fn_ok v X pre2 post2) G :-
     and:
     | drop_spatial;
       ∀ x v, inhale pre2 x v;
       ∃ x', exhale pre1 x' v;
       ∀ v', inhale post1 x' v';
       exhale post2 x v';
       done
     | ∃ x, return G x.
  Proof.
    liTUnfold. iIntros "[#Hsub [% ?]] Hfn". iExists _. iFrame. unfold fn_ok.
    iDestruct "Hfn" as "#[%[%[%[-> Hwp]]]]".
    iModIntro. iExists _, _, _. iSplit; [done|].
    iIntros (??) "?". iDestruct ("Hsub" with "[$]") as (?) "[Hpre1 HWP]".
    iSpecialize ("Hwp" with "Hpre1"). iModIntro.
    iApply (wp_wand with "Hwp"). iIntros (?) "Hpost1".
    iDestruct ("HWP" with "Hpost1") as "[$ _]".
  Qed.
  Definition subsume_fn_inst := [instance subsume_fn].
  Global Existing Instance subsume_fn_inst.

  Lemma contains_correct (P : val → bool) :
    ⊢ fn_ok contains_code (val * list val)
      (λ '(va, xs) v, ∃ cb, ⌜v = (va, cb)%V⌝ ∗ is_list va xs ∗ fn_ok cb val (λ va v, ⌜v = va⌝ ∗ ⌜v ∈ xs⌝) (λ va v, ⌜v = #(P va)⌝))
      (λ '(va, xs) r, ⌜r = #(bool_decide (Exists P xs))⌝ ∗ is_list va xs).
  Proof.
    iStartProof. iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
    Unshelve. all: unshelve_sidecond.
    - by destruct x0.
    - set_solver.
    - do 2 f_equal. normalize_and_simpl_goal. constructor. naive_solver.
    - set_solver.
    - do 2 f_equal. apply bool_decide_ext. rewrite Exists_cons H0. naive_solver.
  Qed.

  Definition contains_one (contains : val) : val := λ: "x",
      contains ("x", (λ: "y", "y" = #1)%V).

  Lemma simpl_fn X f a e pre post G :
    simplify_goal (fn_ok (RecV f a e) X pre post) G :-
      and:
      | drop_spatial;
        ∀ (x : X) v vr,
        inhale pre x v;
        inhale fn_ok vr X pre post;
        v' ← {expr_ok (subst' a v (subst' f vr e))};
        exhale post x v';
        done
      | return G.
  Proof. liTUnfold. iIntros "[Hsub $]". by iApply prove_fn_ok. Qed.
  Definition simpl_fn_inst := [instance simpl_fn with 50%N].
  Global Existing Instance simpl_fn_inst.

  (* TODO: upstream? *)
  Global Instance simpl_fmap_elem_of {A B} x (xs : list A) (f : A → B) :
    SimplBoth (x ∈ f <$> xs) (∃ y, x = f y ∧ y ∈ xs).
  Proof. constructor. by set_unfold. Qed.

  Lemma contains_one_correct contains :
    fn_ok contains (val * list val)
      (λ '(va, xs) v, ∃ cb, ⌜v = (va, cb)%V⌝ ∗ is_list va xs ∗ fn_ok cb val (λ va v, ⌜v = va⌝ ∗ ⌜v ∈ xs⌝) (λ va v, ⌜v = #(bool_decide (va = #1))⌝))
      (λ '(va, xs) r, ⌜r = #(bool_decide (Exists (λ x, (bool_decide (x = #1))) xs))⌝ ∗ is_list va xs)
    -∗
       fn_ok (contains_one contains) (val * list Z)
      (λ '(va, xs) v, ⌜v = va⌝ ∗ is_list va (LitV <$> (LitInt <$> xs)))
      (λ '(va, xs) r, ⌜r = #(bool_decide (1 ∈ xs))⌝ ∗ is_list va (LitV <$> (LitInt <$> xs))).
  Proof.
    iStartProof. iIntros "#?". iApply prove_fn_ok. simpl.
    repeat liTStep; liShow.
    Unshelve. all: unshelve_sidecond.
    - repeat case_bool_decide; naive_solver.
    - do 2 f_equal. apply bool_decide_ext. rewrite !Exists_fmap. rewrite Exists_exists. naive_solver.
  Qed.
  *)

End proofs.
