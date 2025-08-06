From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import exception mem typing list.
From New.golang.defn Require Export pkg.
From Perennial Require Import base.

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

    TODO: not sure if having [is_pkg_init] makes sense in here. The other three
    fields are directly related to execution state, but the [is_pkg_init]
    consists of predicates chosen by the proof developer.
 *)
Class GoContext {ext : ffi_syntax} Σ :=
  {
    global_addr : go_string → loc;
    is_pkg_init : go_string → iProp Σ;
    __function : list (go_string * val);
    __method : list (go_string * (list (go_string * val)));
  }.

Section globals.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!GoContext Σ}.

Definition is_go_context : iProp Σ :=
    inv nroot (
        ∃ (global_addr_val : list (_ * loc)) package_inited,
        "Hg" ∷ own_globals 1 (
            <["__global_vars"%go := alist_val ((λ '(a, b), (a, #b)) <$> global_addr_val)]>
              (<["__functions"%go := alist_val __function]>
                 (<["__msets"%go := alist_val ((λ '(a, b), (a, alist_val b)) <$> __method)]>
                    package_inited))) ∗
        "#Hinit" ∷ □([∗ map] pkg_name ↦ _ ∈ package_inited, is_pkg_init pkg_name) ∗
        "%Hglobal_addr" ∷ ⌜ ∀ var_name, default null (alist_lookup_f var_name global_addr_val) = global_addr var_name ⌝
      ).

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
    func.f := <>; func.x := "firstArg";
    func.e :=
      option.unwrap (alist_lookup (# func_name) (option.unwrap (GlobalGet (# "__functions"%go))))
        "firstArg"
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

Definition method_callv_def (type_name method_name : go_string) (receiver : val) : func.t :=
  {|
    func.f := <>; func.x := "firstArg";
    func.e :=
      let: "method_set" := option.unwrap
                             (alist_lookup (# type_name) (option.unwrap (GlobalGet #"__msets"))) in
      option.unwrap (alist_lookup (# method_name) "method_set") receiver "firstArg"
  |}.

Program Definition method_callv := sealed @method_callv_def.
Definition method_callv_unseal : method_callv = _ := seal_eq _.

Global Instance wp_method_callv (type_name method_name : go_string) (receiver : val) :
  PureWp True (method_call #type_name #method_name receiver) #(method_callv type_name method_name receiver).
Proof.
  rewrite method_call_unseal /method_call_def method_callv_unseal.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.

(** Internal-ish to Goose. Users should never manually define instances of this.
    The [P] predicate will generally be a package's [is_defined]. *)
Class WpFuncCall func_name (f : val) (P : iProp Σ) :=
  wp_func_call :
    (∀ (first_arg : val) Φ,
       P -∗ (WP (f first_arg) {{ Φ }}) -∗
       WP #(func_callv func_name) first_arg {{ Φ }}).

(** Same as [WpFuncCall]. *)
Class WpMethodCall (type_name : go_string) (func_name : go_string) (m : val)
                   (P : iProp Σ)
  := wp_method_call :
    (∀ (first_arg receiver : val) Φ,
         P -∗ (WP (m receiver first_arg) {{ Φ }}) -∗
         WP #(method_callv type_name func_name receiver) first_arg {{ Φ }}).

(** This says that the package's declarations are accessible (including
    functions, methods, and variables). *)
Definition is_defined_def pkg_name `{!PkgInfo pkg_name} : iProp Σ :=
  "#Hctx" ∷ is_go_context ∗
  "%Hfunction" ∷ ⌜ (∀ func_name func,
                      (alist_lookup_f func_name (pkg_functions pkg_name)) = Some func →
                      (alist_lookup_f func_name __function) = Some func) ⌝ ∗
  "%Hmethod" ∷ ⌜ (∀ type_name method_name m,
                      (alist_lookup_f type_name (pkg_msets pkg_name)) ≫=
                      (alist_lookup_f method_name) = Some m →
                      (alist_lookup_f type_name __method) ≫=
                      (alist_lookup_f method_name) = Some m) ⌝.
Program Definition is_defined := sealed @is_defined_def.
Definition is_defined_unseal : is_defined = _ := seal_eq _.
#[global] Arguments is_defined (pkg_name) {_}.
#[global] Instance is_defined_persistent pkg_name `{!PkgInfo pkg_name} : Persistent (is_defined pkg_name).
Proof. rewrite is_defined_unseal. apply _. Qed.

(** Any package's [is_defined] suffices as precondition. *)
Lemma wp_globals_get pkg_name `{!PkgInfo pkg_name} var_name :
  {{{ is_defined pkg_name }}} (globals.get #var_name) {{{ RET #(global_addr var_name); True }}}.
Proof.
  iIntros (?) "#Hdef HΦ". rewrite globals.get_unseal.
  rewrite is_defined_unseal. iNamed "Hdef". clear Hfunction Hmethod PkgInfo0. iNamed "Hctx".
  wp_call_lc "Hlc". wp_bind.
  iInv "Hctx" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  rewrite [in # "__global_vars"]to_val_unseal.
  wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg".
  iMod ("Hclose" with "[Hg Hinit]").
  { iFrame "∗#%". }
  iModIntro.
  rewrite lookup_insert_eq.
  wp_pures. specialize (Hglobal_addr var_name).
  rewrite alist_lookup_f_fmap.
  destruct alist_lookup_f.
  { simpl in *. subst. wp_pures. by iApply "HΦ". }
  { simpl in *. wp_pures. rewrite <-Hglobal_addr. by iApply "HΦ". }
Qed.

(** Internal to Goose. Used in generatedproofs to establish [WpFuncCall]. *)
Lemma wp_func_call' {func_name func} `{!PkgInfo pkg_name} :
  alist_lookup_f func_name (pkg_functions pkg_name) = Some func →
  WpFuncCall func_name func (is_defined pkg_name).
Proof.
  intros Hlookup. rewrite /WpFuncCall. iIntros "* Hdef HΦ". rewrite func_callv_unseal.
  wp_pure_lc "Hlc". wp_bind. iNamed "Hdef". rewrite is_defined_unseal.
  iNamed "Hdef". iInv "Hctx" as "Hi" "Hclose". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi". rewrite [in # "__functions"]to_val_unseal. wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg Hinit]"). { iFrame "∗#%". }
  iModIntro. rewrite lookup_insert_ne // lookup_insert_eq.
  wp_pures. erewrite Hfunction; last done. wp_pures. iApply "HΦ".
Qed.

(** Internal to Goose. Used in generatedproofs to establish [WpMethodCall]. *)
Lemma wp_method_call' {type_name method_name m} `{!PkgInfo pkg_name} :
  (alist_lookup_f type_name (pkg_msets pkg_name)) ≫= (alist_lookup_f method_name) = (Some m) →
  WpMethodCall type_name method_name m (is_defined pkg_name).
Proof.
  intros Hlookup. rewrite /WpMethodCall. iIntros "* Hdef HΦ". rewrite method_callv_unseal.
  wp_pure_lc "Hlc". wp_bind. iNamed "Hdef". rewrite is_defined_unseal.
  iNamed "Hdef". iInv "Hctx" as "Hi" "Hclose". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi". rewrite [in # "__msets"]to_val_unseal. wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg Hinit]"). { iFrame "∗#%". }
  iModIntro. do 2 rewrite lookup_insert_ne //. rewrite lookup_insert_eq.
  wp_pures. rewrite alist_lookup_f_fmap. specialize (Hmethod _ _ _ Hlookup).
  destruct (alist_lookup_f type_name __method); last by exfalso.
  wp_pures. simpl in *. destruct (alist_lookup_f method_name l); last by exfalso.
  wp_pures. simplify_eq. iApply "HΦ".
Qed.

End globals.

Global Hint Mode WpMethodCall - - - - - - + + - - : typeclass_instances.
Global Hint Mode WpFuncCall - - - - - - + - - : typeclass_instances.

(* TODO: better error messages if tc_solve fails to find a val for the name. *)
Tactic Notation "wp_globals_get_core" :=
  wp_bind (globals.get _ _);
  unshelve iApply (wp_globals_get with "[]").

Tactic Notation "wp_func_call_core" :=
  (wp_bind (#(func_callv _ _) _);
   unshelve iApply (wp_func_call with "[]");
   [| | (tc_solve || fail "could not find mapping from function name to val") | | ]).

Tactic Notation "wp_method_call_core" :=
  (wp_bind (#(method_callv _ _ _ _) _);
   unshelve iApply (wp_method_call with "[]");
   [| | (tc_solve || fail "could not find mapping from method to val") | |]).

#[global]
Notation "pkg @ func" :=
  #(func_callv pkg func) (at level 1, no associativity) : expr_scope.

#[global]
Notation "rcvr @ pkg @ type @ method" :=
  #(method_callv pkg type method #rcvr)
    (at level 1, pkg at next level, type at next level, no associativity) : expr_scope.


(** [IsPkgInit] is used to record a mapping from pkg names to an
initialization predicate, which is the postcondition for after the package has
been initialized. This includes the package being "defined", a technicality of
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
    is_pkg_init_def : PROP ; (* user-specified *)
    is_pkg_init_deps : PROP ; (* autogenerated *)
    #[global]
    is_pkg_init_persistent :: Persistent is_pkg_init_def;
  }.

#[global]
Arguments is_pkg_init_def (pkg_name) {_ _}.
#[global]
Typeclasses Opaque is_pkg_init_def.

Section is_pkg_init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!GoContext Σ}.
Definition is_pkg_init_aux `{!PkgInfo pkg_name} `{!IsPkgInit pkg_name} : iProp Σ :=
  "#Hdefined" ∷ is_defined pkg_name ∗
  "#Hdeps" ∷ □ is_pkg_init_deps ∗
  "#Hinit" ∷ is_pkg_init_def pkg_name.

End is_pkg_init.

#[global]
Hint Mode IsPkgInit + - : typeclass_instances.

Ltac prove_is_pkg_init :=
  constructor; refine _.

Import Ltac2.
Ltac2 build_pkg_init () :=
  Control.refine
    (fun () =>
       lazy_match! goal with
       | [ |- IsPkgInit ?name ] =>
           let deps := Std.eval_hnf constr:(pkg_imported_pkgs $name) in
           let rec build_iprop deps :=
             lazy_match! deps with
             | cons ?pkg ?deps =>
                 let rest := build_iprop deps in
                 constr:((is_pkg_init $pkg ∗ $rest)%I)
             | nil => constr:(is_defined_def $name)
             | _ =>
                 Message.print (Message.of_constr deps);
                 Control.backtrack_tactic_failure "build_pkg_init: unable to match deps list"
             end in
           let p := build_iprop deps in
           let p := constr:(Build_IsPkgInit $name _ $p) in
           (* Intentionally leaving the `Persistent` goal unsolved so the instance can Qed it *)
           open_constr:($p _)
       | [ |- _ ] => Control.backtrack_tactic_failure "build_pkg_init: goal is not (IsPkgInit _)"
       end
    ).

(* solve a goal which is just [is_pkg_init] or [is_pkg_defined] *)
Ltac solve_pkg_init :=
  unfold named;
  lazymatch goal with
  | |- environments.envs_entails ?env (is_pkg_init _) => idtac
  | |- environments.envs_entails ?env (is_defined _) => idtac
  | _ => fail "not a is_pkg_init or is_defined goal"
  end;
  iClear "∗";
  simpl is_pkg_init;
  repeat
    lazymatch goal with
    | |- environments.envs_entails ?env _ =>
        lazymatch env with
        | context[environments.Esnoc _ ?i (_ ∗ _)%I] =>
            iDestruct i as "[? ?]"
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

Lemma wp_package_init
  pending
  (postconds : gmap go_string (iProp Σ))
  (pkg_name : go_string) `{!PkgInfo pkg_name} (init_func : val)

  `{!WpGlobalsAlloc (pkg_vars pkg_name) GlobalAddrs var_addrs own_allocated}
  (is_initialized : GlobalAddrs → iProp Σ)
  (is_defined : GlobalAddrs → iProp Σ)
  :
  postconds !! pkg_name = Some (∃ d, is_defined d ∗ is_initialized d)%I →
  pkg_name ∉ pending →
  (∀ (d : GlobalAddrs),
     is_global_definitions pkg_name (var_addrs d) -∗
     own_allocated d -∗
     own_globals_tok ({[ pkg_name ]} ∪ pending) postconds -∗
     WP init_func #()
       {{ v, ⌜ v = #tt ⌝ ∗
             □ (is_defined d ∗ is_initialized d) ∗
             own_globals_tok ({[ pkg_name ]} ∪ pending) postconds
       }}
  ) →
  {{{ own_globals_tok pending postconds }}}
    globals.package_init pkg_name init_func
  {{{ (d : GlobalAddrs), RET #(); is_defined d ∗ is_initialized d ∗ own_globals_tok pending postconds }}}.
Proof.
  unseal.
  intros Hpost Hnot_pending Hwp_init.
  iIntros (?) "Htok HΦ".
  rewrite globals.package_init_unseal.
  wp_call.
  iNamed "Htok".
  wp_bind (GlobalGet _).
  iApply (wp_GlobalGet_full with "[$]").
  iNext. iIntros "Hglobals".
  destruct (lookup _ g) eqn:Hlookup.
  { (* don't run init because the package has already been initialized *)
    wp_pures.
    apply elem_of_dom_2 in Hlookup.
    rewrite Hpkg elem_of_union or_r // in Hlookup.
    iDestruct (big_sepS_elem_of with "Hinited") as "H".
    { done. }
    rewrite Hpost /=.
    iDestruct "H" as (?) "#[? ?]".
    iApply ("HΦ" with "[-]").
    iFrame "∗#%".
  }
  (* actually run init *)
  wp_pures.
  wp_apply wp_globals_alloc.
  iIntros "* Halloc".
  wp_pures.
  wp_bind (GlobalPut _ _).
  iApply (wp_GlobalPut with "[$]").
  { done. }
  iNext. iIntros "[Hg #Hdef]".
  wp_pures.
  iDestruct (Hwp_init with "[$Hdef] [$Halloc] [Hg]") as "Hinit".
  { iFrame "∗#%". iPureIntro. set_solver. }
  wp_apply (wp_wand with "Hinit").
  iIntros (?) "H".
  iDestruct "H" as (?) "[#[? ?] Htok]". subst.
  iApply ("HΦ" with "[-]").
  iClear "Hinited".
  clear Hpkg.
  iNamed "Htok".
  iDestruct (big_sepS_insert_2 pkg_name with "[] Hinited") as "Hinited2".
  { simpl. rewrite Hpost. iFrame "#". }
  iFrame "∗#%".
  iPureIntro. set_solver.
Qed.

End package_init.
