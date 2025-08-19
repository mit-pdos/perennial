From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import exception mem typing list assume.
From New.golang.defn Require Export pkg.
From Perennial Require Import base.
Import Ltac2.
Set Default Proof Mode "Classic".

Set Default Proof Using "Type".

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Global Instance wp_unwrap (v : val) :
  PureWp True (option.unwrap $ InjRV v) v.
Proof.
  rewrite option.unwrap_unseal /option.unwrap_def.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.
End wps.

(** [GoContext] contains the global state of a node running Go code. It is a
    typeclass so that [global_addr] can be conveniently used in proofs that have
    a section variable of type [GoContext]. A new [global_addr] is (angelically)
    nondeterministically chosen on reboot. This choice is angelic in the sense
    that future code (package.alloc) will actually allocate on the heap and
    angelically assumes that the allocated location matches the [global_addr]
    map.
 *)
Class GoContext {ext : ffi_syntax} :=
  {
    global_addr_def : go_string → loc;
    __function : go_string → option (list go_type → val);
    __method : go_string → option (list (go_string * val));
  }.

(* NOTE: To avoid printing the [GoContext] instance when printing [global_addr].
   See https://github.com/rocq-prover/rocq/issues/9814 *)
#[global] Notation global_addr := global_addr_def.

Section globals.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!GoContext}.

Definition is_init (σ : state) : Prop :=
  (∀ var_name, σ.(globals) ("V" ++ var_name)%go = Some #(global_addr var_name)) ∧
  (∀ func_name, σ.(globals) ("F" ++ func_name)%go = (__function func_name)) ∧
  (∀ type_id, σ.(globals) ("M" ++ type_id)%go = (alist_val <$> __method type_id)) ∧
  (∀ pkg_name, σ.(globals) ("P" ++ pkg_name)%go = None).

(** Proof of initialization must refer to a [get_is_pkg_init] mapping that
    covers all packages. This specified what an init function must establish
    when returning, and what one gets to assume when calling other init
    functions. *)
Definition is_initialization get_is_pkg_init : iProp Σ :=
  inv nroot (
      ∃ g package_started package_inited,
        "Hg" ∷ own_globals (DfracOwn (1/2)) g ∗
        (* NOTE: could own an auth that has precisely the "started" keys, and
           the exclusive pointstos can be given to program proofs to help escrow
           resources into initialization. *)
        "#Hinit" ∷ □([∗ set] pkg_name ∈ package_inited, get_is_pkg_init pkg_name) ∗
        "%Hglobal_addr" ∷ (⌜ ∀ var_name, g ("V" ++ var_name)%go = Some #(global_addr var_name) ⌝) ∗
        "%Hfunction" ∷ (⌜ ∀ func_name, g ("F" ++ func_name)%go = (__function func_name) ⌝) ∗
        "%Hmethod" ∷ (⌜ ∀ type_id, g ("M" ++ type_id)%go = (alist_val <$> __method type_id) ⌝) ∗

        "%Hpackage_inited" ∷ (⌜ ∀ pkg_name, g ("P" ++ pkg_name)%go =
                                # <$> ((gset_to_gmap "initialized"%go package_inited) ∪
                                   (gset_to_gmap "started"%go package_started)) !! pkg_name
                                  ⌝)
    ).
#[global] Opaque is_initialization.
#[local] Transparent is_initialization.
#[global] Instance is_initialization_pers a : Persistent (is_initialization a).
Proof. apply _. Qed.

(** This asserts that the implicit [GoContext] matches the execution state of
    the current Go program. *)
Definition is_go_context : iProp Σ :=
  ∃ get_is_pkg_init, is_initialization get_is_pkg_init.

Definition own_initializing : iProp Σ :=
  ∃ g, own_globals (DfracOwn (1/2)) g.

Lemma alist_lookup_f_fmap {A B} n (l: list (go_string * A)) (f : A → B) :
  alist_lookup_f n ((λ '(name, a), (name, f a)) <$> l) =
  f <$> (alist_lookup_f n l).
Proof.
  induction l as [|[]]; first done; simpl.
  destruct (ByteString.eqb g n); first done.
  rewrite IHl //.
Qed.

Definition func_callv_def (func_name : go_string) : func.t :=
  {|
    func.f := <>;
                func.x := "firstArg";
    func.e := option.unwrap (GlobalGet (# "F"%go + # func_name)) "firstArg"
  |}.
Program Definition func_callv := sealed @func_callv_def.
Definition func_callv_unseal : func_callv = _ := seal_eq _.

Global Instance wp_func_callv (func_name : go_string) :
  PureWp True (func_call #func_name)%E #(func_callv func_name)%E.
Proof.
  rewrite func_call_unseal /func_call_def func_callv_unseal.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.

Definition method_callv_def (type_id method_name : go_string) (receiver : val) : func.t :=
  {|
    func.f := <>;
                func.x := "firstArg";
    func.e :=
      let: "method_set" := option.unwrap (GlobalGet (# "M"%go + # type_id)) in
      option.unwrap (alist_lookup (# method_name) "method_set") receiver "firstArg"
  |}.
Program Definition method_callv := sealed @method_callv_def.
Definition method_callv_unseal : method_callv = _ := seal_eq _.

Global Instance wp_method_callv (type_id method_name : go_string) (receiver : val) :
  PureWp True (method_call #type_id #method_name receiver) #(method_callv type_id method_name receiver).
Proof.
  rewrite method_call_unseal /method_call_def method_callv_unseal.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.

(** Internal-ish to Goose. Users should never manually define instances of this.
    The [P] predicate will generally be a package's [is_pkg_defined]. *)
Class WpFuncCall func_name (f : val) (P : iProp Σ) :=
  wp_func_call :
    (∀ (first_arg : val) Φ,
       P -∗ (WP (f first_arg) {{ Φ }}) -∗
       WP #(func_callv func_name) first_arg {{ Φ }}).

(** Same as [WpFuncCall]. *)
Class WpMethodCall (type_id : go_string) (func_name : go_string) (m : val)
                   (P : iProp Σ)
  := wp_method_call :
    (∀ (first_arg receiver : val) Φ,
         P -∗ (WP (m receiver first_arg) {{ Φ }}) -∗
         WP #(method_callv type_id func_name receiver) first_arg {{ Φ }}).

(** Pure predicate asserting that the declarations in the Go package [pkg_name]
    are part of the implicit [GoContext]. Top-level closed theorems can assume
    this about the starting state/[GoContext]. *)
Definition is_pkg_defined_pure pkg_name `{!PkgInfo pkg_name} : Prop :=
  (∀ func_name func,
     alist_lookup_f func_name (pkg_functions pkg_name) = Some func →
     __function func_name = Some func) ∧
  (∀ type_id method_name m,
     (alist_lookup_f type_id (pkg_msets pkg_name)) ≫=
     (alist_lookup_f method_name) = Some m →
     (__method type_id) ≫= (alist_lookup_f method_name) = Some m).

(** This says that the package's declarations are accessible (including
    functions, methods, and variables). *)
Definition is_pkg_defined_def pkg_name `{!PkgInfo pkg_name} : iProp Σ :=
  "#Hctx" ∷ is_go_context ∗
  "%Hdefined" ∷ ⌜ is_pkg_defined_pure pkg_name ⌝.
Program Definition is_pkg_defined := sealed @is_pkg_defined_def.
Definition is_pkg_defined_unseal : is_pkg_defined = _ := seal_eq _.
#[global] Arguments is_pkg_defined (pkg_name) {_}.
#[global] Instance is_pkg_defined_persistent pkg_name `{!PkgInfo pkg_name} : Persistent (is_pkg_defined pkg_name).
Proof. rewrite is_pkg_defined_unseal. apply _. Qed.

(** Any package's [is_pkg_defined] suffices as precondition. *)
Lemma wp_globals_get pkg_name `{!PkgInfo pkg_name} var_name :
  {{{ is_pkg_defined pkg_name }}} (globals.get #var_name) {{{ RET #(global_addr var_name); True }}}.
Proof.
  iIntros (?) "#Hdef HΦ". rewrite globals.get_unseal.
  rewrite is_pkg_defined_unseal. iNamed "Hdef". clear Hdefined PkgInfo0. iNamed "Hctx".
  wp_call_lc "Hlc". wp_bind.
  iInv "Hctx" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  rewrite [in # (_::_)]to_val_unseal.
  wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg]").
  { iFrame "∗#%". }
  iModIntro. wp_pures. rewrite Hglobal_addr. wp_pures. by iApply "HΦ".
Qed.

(** Internal to Goose. Used in generatedproofs to establish [WpFuncCall]. *)
Lemma wp_func_call' {func_name func} `{!PkgInfo pkg_name} :
  alist_lookup_f func_name (pkg_functions pkg_name) = Some func →
  WpFuncCall func_name func (is_pkg_defined pkg_name).
Proof.
  intros Hlookup. rewrite /WpFuncCall. iIntros "* Hdef HΦ". rewrite func_callv_unseal.
  wp_pure_lc "Hlc". wp_pures. wp_bind. rewrite is_pkg_defined_unseal. iNamed "Hdef". iNamed "Hctx".
  iInv "Hctx" as "Hi" "Hclose". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi". rewrite [in # (_::_)]to_val_unseal. wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg Hinit]"). { iFrame "∗#%". }
  iModIntro. rewrite Hfunction. destruct Hdefined as (Hfunction_def & _).
  erewrite Hfunction_def; try done. wp_pures. wp_pures. iApply "HΦ".
Qed.

(** Internal to Goose. Used in generatedproofs to establish [WpMethodCall]. *)
Lemma wp_method_call' {type_id method_name m} `{!PkgInfo pkg_name} :
  (alist_lookup_f type_id (pkg_msets pkg_name)) ≫= (alist_lookup_f method_name) = (Some m) →
  WpMethodCall type_id method_name m (is_pkg_defined pkg_name).
Proof.
  intros Hlookup. rewrite /WpMethodCall. iIntros "* Hdef HΦ". rewrite method_callv_unseal.
  wp_pure_lc "Hlc". wp_pures. wp_bind. rewrite is_pkg_defined_unseal. iNamed "Hdef".
  iNamed "Hctx". iInv "Hctx" as "Hi" "Hclose". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi". rewrite [in #(_::_)]to_val_unseal. wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg Hinit]"). { iFrame "∗#%". }
  iModIntro. destruct Hdefined as (Hfunction_def & Hmethod_def).
  rewrite Hmethod. specialize (Hmethod_def type_id method_name). rewrite Hlookup in Hmethod_def.
  specialize (Hmethod_def _ ltac:(done)).
  destruct (__method type_id) eqn:Hm; last by exfalso.
  wp_pures. simpl in Hmethod_def. rewrite Hmethod_def. wp_pures. iApply "HΦ".
Qed.

Lemma go_init get_is_pkg_init σ :
  is_init σ →
  own_globals (DfracOwn 1) σ.(globals) ={⊤}=∗
  is_initialization get_is_pkg_init ∗ own_initializing ∗ is_go_context.
Proof.
  intros (? & ? & ? & ?).
  iIntros "[Hg Hg2]".
  iFrame. iMod (inv_alloc with "[-]") as "#H".
  2:{ by iFrame "H". }
  iExists _, ∅, ∅. iFrame. rewrite big_sepS_empty. iFrame "#%". done.
Qed.

End globals.

Global Hint Mode WpMethodCall - - - - - - + + - - : typeclass_instances.
Global Hint Mode WpFuncCall - - - - - - + - - : typeclass_instances.

(* TODO: better error messages if tc_solve fails to find a val for the name. *)
Tactic Notation "wp_globals_get_core" :=
  wp_bind (globals.get _ _);
  unshelve iApply (wp_globals_get with "[]").

Tactic Notation "wp_func_call_core" :=
  (wp_bind (#(func_callv _) _);
   unshelve iApply (wp_func_call with "[]");
   [| | (tc_solve || fail "could not find mapping from function name to val") | | ]).

Tactic Notation "wp_method_call_core" :=
  (wp_bind (#(method_callv _ _ _) _);
   unshelve iApply (wp_method_call with "[]");
   [| | (tc_solve || fail "could not find mapping from method to val") | |]).

#[global]
Notation "@! func" :=
  #(func_callv func) (at level 1, no associativity, format "@! func") : expr_scope.

#[global]
Notation "rcvr @ type @ method" :=
  #(method_callv type method #rcvr)
    (at level 1, type at next level, no associativity) : expr_scope.


(** [IsPkgInit] is used to record a mapping from pkg names to an
initialization predicate, which is the postcondition for after the package has
been initialized. This should include the package being "defined", a technicality of
Goose where function names are associated with their bodies. Defining the
package occurs prior to initializing global variables according to their
initialization expressions, as well as running init() functions.

This typeclass associates a single initialization predicate to each package,
reflecting common practice, but strictly speaking proofs could choose different
postconditions for initialization. This is similar to how almost all functions
have a canonical specification, even though they could potentially have several
incomparable ones.
*)
Class IsPkgInit (pkg_name: go_string) {PROP: bi} :=
  {
    is_pkg_init_def : PROP;
    is_pkg_init_deps : PROP;
  }.

#[global] Arguments is_pkg_init_def (pkg_name) {_ _}.
#[global] Arguments is_pkg_init_deps (pkg_name) {_ _}.
#[global] Typeclasses Opaque is_pkg_init_def.

Section is_pkg_init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!GoContext}.

Definition is_pkg_init (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInit pkg_name} : iProp Σ :=
  "#Hdefined" ∷ is_pkg_defined pkg_name ∗
  "#Hdeps" ∷ □ is_pkg_init_deps pkg_name ∗
  "#Hinit" ∷ □ is_pkg_init_def pkg_name.
#[global] Opaque is_pkg_init.
#[local] Transparent is_pkg_init.
#[global] Instance is_pkg_init_pers (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInit pkg_name} :
  Persistent (is_pkg_init pkg_name).
Proof. apply _. Qed.

Lemma is_pkg_init_unfold (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInit pkg_name} :
  is_pkg_init pkg_name =
  ("#Hdefined" ∷ is_pkg_defined pkg_name ∗
  "#Hdeps" ∷ □ is_pkg_init_deps pkg_name ∗
  "#Hinit" ∷ □ is_pkg_init_def pkg_name)%I.
Proof. done. Qed.

Lemma is_pkg_init_def_unfold (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInit pkg_name} :
  is_pkg_init pkg_name -∗
  is_pkg_init_def pkg_name.
Proof. iNamed 1. done. Qed.

Lemma is_pkg_init_unfold_deps (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInit pkg_name} :
  is_pkg_init pkg_name -∗
  is_pkg_init_deps pkg_name.
Proof. iNamed 1. done. Qed.

End is_pkg_init.

#[global]
Hint Mode IsPkgInit + - : typeclass_instances.

Ltac2 build_pkg_init_deps name :=
  Control.refine
    (fun () =>
       lazy_match! goal with
       | [ |- iProp _ ] =>
           let deps := Std.eval_hnf constr:(pkg_imported_pkgs $name) in
           let rec build_iprop deps :=
             lazy_match! deps with
             | cons ?pkg ?deps =>
                 let rest := build_iprop deps in
                 constr:((is_pkg_init $pkg ∗ $rest)%I)
             | nil => constr:(is_pkg_defined $name)
             | _ =>
                 Message.print (Message.of_constr deps);
                 Control.backtrack_tactic_failure "build_pkg_init: unable to match deps list"
             end in
           build_iprop deps
       | [ |- _ ] => Control.backtrack_tactic_failure "build_pkg_init: goal is not (iProp _)"
       end
    ).

(* FIXME: better implementation using PkgInfo to direct the search. Could try lithium even. *)
(* solve a goal which is just [is_pkg_init] or [is_pkg_defined] *)
Ltac solve_pkg_init :=
  unfold named;
  lazymatch goal with
  | |- environments.envs_entails ?env (is_pkg_init _) => idtac
  | |- environments.envs_entails ?env (is_pkg_defined _) => idtac
  | _ => fail "not a is_pkg_init or is_pkg_defined goal"
  end;
  try iAssumption;
  iClear "∗";
  iEval (rewrite ?is_pkg_init_unfold; simpl is_pkg_init_deps; unfold named) in "#";
  repeat
    lazymatch goal with
    | |- environments.envs_entails ?env _ =>
        lazymatch env with
        | context[environments.Esnoc _ ?i (_ ∗ _)%I] =>
            iDestruct i as "[? ?]"
        | context[environments.Esnoc _ ?i (□ _)%I] =>
            iDestruct i as "#?"
        end
    end;
  solve [ iFrame "#" ].

(* Attempt to solve [is_pkg_init] at the front of the goal.

NOTE: The automation here is limited to match what we expect in goals and to make the
implementation simple. It is possible that the shape of expected goals changes,
for example to have multiple [is_pkg_init] conjuncts, in which case this
automation will need improvement.
*)
Ltac iPkgInit :=
  progress (
      try solve_pkg_init;
      repeat (iSplitR; [ solve_pkg_init | ])
    ).

Section package_init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.
Context `{!GoContext}.
#[local] Transparent is_initialization.

Lemma wp_package_init (pkg_name : go_string) `{!PkgInfo pkg_name} (init_func : val) get_is_pkg_init :
  ∀ Φ,
  (is_initialization get_is_pkg_init ∗ own_initializing ∗ (own_initializing -∗ WP init_func #() {{ _, □ get_is_pkg_init pkg_name ∗ own_initializing }})) -∗
  (own_initializing ∗ get_is_pkg_init pkg_name -∗ Φ #()) -∗
  WP package.init pkg_name init_func #() {{ Φ }}.
Proof.
  iIntros (?) "(#Hctx & Hown & Hpre) HΦ". rewrite package.init_unseal.
  wp_call. wp_call_lc "Hlc".
  wp_bind. unfold is_initialization. iInv "Hctx" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  rewrite [in #(_::_)]to_val_unseal.
  wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg".
  iNamed "Hown". iCombine "Hown Hg" gives %[_ Heq]. subst.
  iMod ("Hclose" with "[Hg Hinit]") as "_". { iFrame "∗#%". }
  iModIntro. rewrite Hpackage_inited. wp_pures.
  destruct (lookup) eqn:Hstatus.
  - simpl. wp_pures. wp_apply wp_assume. iIntros "%Hstarted_ne".
    rewrite bool_decide_decide in Hstarted_ne; try done.
    destruct decide as [|] in Hstarted_ne; try done.
    wp_pures. iApply "HΦ".
    iFrame. iDestruct (big_sepS_elem_of_acc with "Hinit") as "[$ _]".
    specialize (Hpackage_inited pkg_name).
    rewrite lookup_union in Hstatus.
    destruct lookup eqn:Hlookup in Hstatus.
    { rewrite lookup_gset_to_gmap_Some in Hlookup. set_solver. }
    rewrite left_id in Hstatus.
    symmetry in Hpackage_inited. rewrite lookup_gset_to_gmap_Some in Hstatus.
    naive_solver.
  - simpl. wp_pure_lc "Hlc". wp_pures. wp_bind.
    iInv "Hctx" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iAssert (∃ g, own_globals (DfracOwn (1/2)) g)%I with "[Hi]" as "[% Hg]".
    { iNamedSuffix "Hi" "_tmp". iFrame. }
    iCombine "Hown Hg" gives %[_ Heq]. subst.
    iCombine "Hown Hg" as "Hg".
    wp_apply (wp_GlobalPut with "[$]").
    iIntros "[Hown Hg]".
    iMod ("Hclose" with "[Hg]") as "_".
    {
      iFrame "∗#%".
      iExists ({[ pkg_name ]} ∪ package_started). iPureIntro.
      rewrite lookup_union union_None in Hstatus. destruct Hstatus as [Hinit Hstarted].
      intros pkg_name'. rewrite /globals_insert lookup_union gset_to_gmap_union_singleton.
      destruct decide as [Heq|Hneq].
      { simplify_eq. rewrite lookup_insert_eq Hinit //. }
      { rewrite Hpackage_inited lookup_union. rewrite lookup_insert_ne //. congruence. }
    }
    iModIntro. wp_pures. wp_bind.
    wp_apply (wp_wand with "[Hpre Hown]").
    { iApply ("Hpre" with "[$Hown]"). }
    iClear "Hinit". iIntros (?) "[#? Hown]". iNamed "Hown". wp_pures.
    wp_call_lc "Hlc". wp_bind. iInv "Hctx" as "Hi" "Hclose".
    clear dependent package_started package_inited.
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
    rewrite [in #(_::_)]to_val_unseal.
    iCombine "Hown Hg" gives %[_ Heq]. subst.
    iCombine "Hown Hg" as "Hg".
    wp_apply (wp_GlobalPut with "[$]"). iIntros "[Hg Hown]".
    iMod ("Hclose" with "[Hg]").
    {
      iExists _, package_started, ({[ pkg_name ]} ∪ package_inited).
      iFrame "∗#%". iSplit.
      { iModIntro. iModIntro. iApply big_sepS_insert_2; done. }
      iPureIntro. intros pkg_name'. rewrite /globals_insert lookup_union gset_to_gmap_union_singleton.
      destruct decide.
      { simplify_eq. rewrite lookup_insert_eq union_Some_l //. }
      { rewrite Hpackage_inited lookup_union lookup_insert_ne //. congruence. }
    }
    rewrite to_val_unseal.
    iApply "HΦ". iFrame "∗#". done.
Qed.

End package_init.
