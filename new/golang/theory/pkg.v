From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import exception mem typing list assume.
From New.golang.defn Require Export pkg.
From Perennial Require Import base.
Import Ltac2. Import Printf.
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
    __function : list (go_string * val);
    __method : list (go_string * (list (go_string * val)));
  }.

(* NOTE: To avoid printing the [GoContext] instance when printing [global_addr].
   See https://github.com/rocq-prover/rocq/issues/9814 *)
#[global] Notation global_addr := global_addr_def.

Section init_defns.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {go_ctx : GoContext}.

(** [is_init] holds when a node boots up and is used as an assumption in closed theorems. *)
Definition is_init (σ : state) : Prop :=
  ∃ (global_addr_val : list (_ * loc)),
  (∀ var_name, default null (alist_lookup_f var_name global_addr_val) = global_addr var_name) ∧
  σ.(globals) = {[ "__global_vars"%go := alist_val ((λ '(a, b), (a, #b)) <$> global_addr_val);
     "__functions"%go := alist_val __function;
     "__msets"%go := alist_val ((λ '(a, b), (a, alist_val b)) <$> __method);
     "__packages"%go := alist_val [] ]}.
#[global] Opaque is_init.
#[local] Opaque is_init.

Local Definition is_init_inv get_is_pkg_init : iProp Σ :=
  inv nroot (
      ∃ (global_addr_val : list (_ * loc)) (package_inited_val : list (_ * go_string))
        package_started package_inited,
        "Hg" ∷ own_globals (DfracOwn (1/2))
          {[ "__global_vars"%go := alist_val ((λ '(a, b), (a, #b)) <$> global_addr_val);
             "__functions"%go := alist_val __function;
             "__msets"%go := alist_val ((λ '(a, b), (a, alist_val b)) <$> __method);
             "__packages"%go := alist_val ((λ '(a, b), (a, #b)) <$> package_inited_val) ]} ∗
        "#Hinit" ∷ □([∗ set] pkg_name ∈ package_inited, get_is_pkg_init pkg_name) ∗
        (* NOTE: could own an auth that has precisely the "started" keys, and
           the exclusive pointstos can be given to program proofs to help escrow
           resources into initialization. *)
        "%Hglobal_addr" ∷ (⌜ ∀ var_name, default null (alist_lookup_f var_name global_addr_val) = global_addr var_name ⌝) ∗
        "%Hpackage_inited" ∷ (⌜ ∀ pkg_name,
                                alist_lookup_f pkg_name package_inited_val =
                                ((gset_to_gmap "initialized"%go package_inited) ∪
                                   (gset_to_gmap "started"%go package_started)) !! pkg_name
                                  ⌝)
    ).

(** [is_go_context] asserts that the implicit [GoContext] matches the execution
    state of the current Go program. *)
Definition is_go_context : iProp Σ :=
  ∃ get_is_pkg_init, is_init_inv get_is_pkg_init.
#[global] Opaque is_go_context.
#[local] Transparent is_go_context.
#[global] Instance : Persistent is_go_context.
Proof. apply _. Qed.

(** [own_initializing] denotes permission to run [package.init]. This is
    exclusive because go packages are initialized sequentially, in a single
    thread. The [get_is_pkg_init] mapping contains the agreed-upon post-init
    predicate for every package. Making sure that [get_is_pkg_init] has the
    appropriate user-defined predicates is facilitated by [GetIsPkgInitWf]
    below. *)
Definition own_initializing (get_is_pkg_init : go_string → iProp Σ) : iProp Σ :=
  ∃ g, "#Hinv" ∷ is_init_inv get_is_pkg_init ∗ "Hg" ∷ own_globals (DfracOwn (1/2)) g.
#[global] Opaque own_initializing.
#[local] Transparent own_initializing.

Lemma go_init get_is_pkg_init σ :
  is_init σ →
  own_globals (DfracOwn 1) σ.(globals) ={⊤}=∗
  own_initializing get_is_pkg_init ∗ is_go_context.
Proof.
  intros (? & Haddrs & ->).
  iIntros "[Hg Hg2]".
  iFrame. iMod (inv_alloc with "[-]") as "#H".
  2:{ by iFrame "H". }
  iExists _, [], ∅, ∅. iFrame. rewrite big_sepS_empty. iFrame "#%".
  iSplit; first done. iPureIntro. done.
Qed.

End init_defns.

Section package_init_and_defined.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} {go_ctx : GoContext}.

(** XXX: there are a lof of design questions around [is_pkg_defined].
    - construct using ltac2 or Goose?
    - have an Iris version of [is_pkg_defined] or only a pure version?
    - should WpFuncCall/MethodCall take a transitive version of
      [is_pkg_defined], or just a single package's?
    - if pure, should there be new automation for solving [is_pkg_defined_pure]?
      Use typeclasses? Would be annoying to maintain automation for this given
      that there's already Iris automation for [is_pkg_init].
    - If not pure, should one unfold [is_pkg_defined] to get access to the
    - Should the transitive [is_pkg_defined] be kept sealed? Use [Opaque], and
      locally make it [Transparent] where needed in program proofs?
    - and more.
    Moreover, many of these questions do not make a big difference to the
    resulting user experience.

    So, this implementation makes design decisions arbitrarily around these
    questions. For instance, rather than using ltac2 to generate predicates (as
    is done for [is_pkg_init]), the predicate is generated in Goose.
 *)

(** Used as a parameter of the below so that this pure predicate can be referred
    without needing a [heapGS]. *)
Class IsPkgDefinedPure (pkg_name : go_string) :=
  {
    is_pkg_defined_pure_def : ∀ {go_ctx : GoContext}, Prop;
  }.

(** [IsPkgDefined] connects package names to a predicate which asserts that all
    functions/methods from the package and all of its dependencies are
    available.

    The pure predicate is used as an assumption in closed theorems. The Iris
    predicate is used as a precondition in specs for [<PACKAGE NAME>.initialize']. *)
Class IsPkgDefined (pkg_name : go_string) `{!IsPkgDefinedPure pkg_name} :=
  {
    is_pkg_defined_def : ∀ {go_ctx : GoContext}, iProp Σ;
    is_pkg_defined_boot : ∀ {go_ctx : GoContext},
      is_pkg_defined_pure_def → is_go_context -∗ is_pkg_defined_def
  }.
Notation is_pkg_defined_pure := is_pkg_defined_pure_def.
#[global] Arguments is_pkg_defined_pure (pkg_name) {_} {go_ctx}.
#[global] Opaque is_pkg_defined_pure.

Notation is_pkg_defined := is_pkg_defined_def.
#[global] Arguments is_pkg_defined (pkg_name) {_ _} {go_ctx}.
#[global] Opaque is_pkg_defined.

(** Internal to Goose. Pure predicate asserting that the declarations in the Go
    package [pkg_name] are part of the implicit [GoContext]. *)
Definition is_pkg_defined_pure_single_def pkg_name `{!PkgInfo pkg_name} : Prop :=
  (∀ func_name func,
     (alist_lookup_f func_name (pkg_functions pkg_name)) = Some func →
     (alist_lookup_f func_name __function) = Some func) ∧
  (∀ type_name method_name m,
     (alist_lookup_f type_name (pkg_msets pkg_name)) ≫=
     (alist_lookup_f method_name) = Some m →
     (alist_lookup_f type_name __method) ≫=
     (alist_lookup_f method_name) = Some m).
(* XXX: sealing because of a unification problem *)
Program Definition is_pkg_defined_pure_single := sealed is_pkg_defined_pure_single_def.
Definition is_pkg_defined_pure_single_unseal : is_pkg_defined_pure_single = _ := seal_eq _.
#[global] Arguments is_pkg_defined_pure_single (pkg_name) {_}.

(** Internal to Goose. This says that the package's declarations are accessible
    (including functions, methods, and variables). This does not cover any
    dependencies.  This should only be referring to by definitions in
    generatedproof; do not use this manually in proofs. *)
Definition is_pkg_defined_single pkg_name `{!PkgInfo pkg_name} : iProp Σ :=
  "#Hctx" ∷ is_go_context ∗
  "%Hdefined" ∷ ⌜ is_pkg_defined_pure_single pkg_name ⌝.
#[global] Opaque is_pkg_defined_single.
#[local] Transparent is_pkg_defined_single.

(** [IsPkgInit] connects pkg names (really the full package path) to their
    post-initialization predicate. There should only be one instance for each
    package name (i.e. each package is meant to have a canonical init
    predicate).

    This also contains the init predicate of all of the dependencies; it is a
    separate field so that the user-specified part can be extracted with lemmas. *)
Class IsPkgInit (pkg_name : go_string) :=
  {
    is_pkg_init_deps : iProp Σ; (* autogenerated; includes [is_pkg_defined] *)
    is_pkg_init_def : iProp Σ; (* user-specified *)
  }.

#[global] Arguments is_pkg_init_deps (pkg_name) {_}.
#[global] Arguments is_pkg_init_def (pkg_name) {_}.

(** [is_pkg_init] asserts the predicate specified in the [IsPkgInit] instance. *)
Definition is_pkg_init (pkg_name : go_string) `{!IsPkgInit pkg_name} : iProp Σ :=
  "#Hdeps" ∷ □ is_pkg_init_deps pkg_name ∗
  "#Hinit" ∷ □ is_pkg_init_def pkg_name.
#[global] Opaque is_pkg_init.
#[local] Transparent is_pkg_init.
#[global] Instance is_pkg_init_pers (pkg_name : go_string) `{!IsPkgInit pkg_name} :
  Persistent (is_pkg_init pkg_name).
Proof. apply _. Qed.

Lemma is_pkg_init_unfold (pkg_name : go_string) `{!IsPkgInit pkg_name} :
  is_pkg_init pkg_name =
  ("#Hdeps" ∷ □ is_pkg_init_deps pkg_name ∗
  "#Hinit" ∷ □ is_pkg_init_def pkg_name)%I.
Proof. done. Qed.

(* access user-defined init predicate. *)
Lemma is_pkg_init_access (pkg_name : go_string) `{!IsPkgInit pkg_name} :
  is_pkg_init pkg_name -∗
  is_pkg_init_def pkg_name.
Proof. iNamed 1. done. Qed.

Lemma is_pkg_init_unfold_deps (pkg_name : go_string) `{!IsPkgInit pkg_name} :
  is_pkg_init pkg_name -∗
  is_pkg_init_deps pkg_name.
Proof. iNamed 1. done. Qed.

(** Maps [pkg_name] to a pure predicate that constrains [get_is_pkg_init] to
    have all of the init predicates for [pkg_name] and its transitive
    dependencies. *)
Class GetIsPkgInitWf (pkg_name : go_string) {PROP} :=
  {
    get_is_pkg_init_prop_def (get_is_pkg_init : go_string → PROP) : Prop
  }.
Notation get_is_pkg_init_prop := get_is_pkg_init_prop_def.
Global Arguments get_is_pkg_init_prop (pkg_name) {_} {_} (get_is_pkg_init).

End package_init_and_defined.

#[global] Hint Mode IsPkgInit - + : typeclass_instances.
#[global] Hint Mode IsPkgDefined - - - - - - + - : typeclass_instances.
#[global] Hint Mode GetIsPkgInitWf + - : typeclass_instances.

Notation is_pkg_defined_pure := is_pkg_defined_pure_def.
Notation is_pkg_defined := is_pkg_defined_def.
Notation get_is_pkg_init_prop := get_is_pkg_init_prop_def.

Ltac2 fail m := Control.throw (Tactic_failure (Some m)).

Local Ltac2 build_pkg_init_deps name :=
  Control.refine
    (fun () =>
       let deps := Std.eval_hnf constr:(pkg_imported_pkgs $name) in
       let rec build_iprop deps :=
         lazy_match! deps with
         | cons ?pkg ?deps =>
             let rest := build_iprop deps in
             constr:((is_pkg_init $pkg ∗ $rest)%I)
         | nil => constr:((is_pkg_defined $name ∗ is_go_context)%I)
         | _ =>
             Message.print (Message.of_constr deps);
             fail (fprintf "build_pkg_init_deps: unable to match deps list")
         end in
       build_iprop deps
    ).

Local Ltac2 build_is_pkg_init (is_pkg_init_def : preterm) :=
  Control.refine
    (fun () =>
       lazy_match! goal with
       | [ |- IsPkgInit ?pkg_name ] =>
           constr:(Build_IsPkgInit $pkg_name ltac2:(build_pkg_init_deps pkg_name) $preterm:is_pkg_init_def)
       | [ |- ?x ] => fail (fprintf "build_pkg_init: goal is [%t] instead of [IsPkgInit]" x)
       end
    ).
Reserved Notation "'define_is_pkg_init' is_pkg_init" (at level 100).
Notation "'define_is_pkg_init' is_pkg_init" :=
  (ltac2:(build_is_pkg_init is_pkg_init)) (only parsing, is_pkg_init in scope bi_scope).

Ltac2 build_get_is_pkg_init_wf () :=
  Control.refine
    (fun () =>
       lazy_match! goal with
       | [ |- @GetIsPkgInitWf ?name ?prop] =>
           let deps := Std.eval_hnf constr:(pkg_imported_pkgs $name) in
           let p :=
             constr:(λ (get_is_pkg_init : go_string → $prop),
                       (&get_is_pkg_init $name = is_pkg_init $name) ∧
                       ltac2:(Control.refine
                                (fun () =>
                                   let rec build deps :=
                                     lazy_match! deps with
                                     | cons ?pkg ?deps =>
                                         let rest := build deps in
                                         constr:(get_is_pkg_init_prop $pkg &get_is_pkg_init ∧ $rest)
                                     | nil => constr:(True)
                                     | _ =>
                                         Message.print (Message.of_constr deps);
                                         fail (fprintf "build_get_is_pkg_init_wf: unable to match deps list")
                                     end in
                                   build deps
                                )
                    )) in
           constr:(Build_GetIsPkgInitWf $name $prop $p)
       | [ |- _ ] => fail (fprintf "build_get_is_pkg_init_wf: goal is not (GetIsPkgInitWf _)")
       end
    ).

Notation "'build_get_is_pkg_init_wf'" := (ltac2:(build_get_is_pkg_init_wf ())) (only parsing).

Section calls.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} `{!GoContext}.

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
    The [P] predicate will generally be a package's [is_pkg_defined]. *)
Class WpFuncCall func_name (f : val) (P : iProp Σ) :=
  wp_func_call :
    (∀ (first_arg : val) Φ,
       P -∗ (WP (f first_arg) {{ Φ }}) -∗
       WP #(func_callv func_name) first_arg {{ Φ }}).

(** Same as [WpFuncCall]. *)
Class WpMethodCall (type_name : go_string) (func_name : go_string) (m : val) (P : iProp Σ)
  := wp_method_call :
    (∀ (first_arg receiver : val) Φ,
         P -∗ (WP (m receiver first_arg) {{ Φ }}) -∗
         WP #(method_callv type_name func_name receiver) first_arg {{ Φ }}).

Lemma alist_lookup_f_fmap {A B} n (l: list (go_string * A)) (f : A → B) :
  alist_lookup_f n ((λ '(name, a), (name, f a)) <$> l) =
  f <$> (alist_lookup_f n l).
Proof.
  induction l as [|[]]; first done; simpl.
  destruct (ByteString.eqb g n); first done.
  rewrite IHl //.
Qed.

#[local] Transparent is_go_context.

Lemma wp_globals_get var_name :
  {{{ is_go_context }}} (globals.get #var_name) {{{ RET #(global_addr var_name); True }}}.
Proof.
  iIntros (?) "#Hctx HΦ". rewrite globals.get_unseal.
  iNamed "Hctx". wp_call_lc "Hlc". wp_bind. iNamed "Hctx".
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

#[local] Transparent is_pkg_defined_single.

(** Internal to Goose. Used in generatedproofs to establish [WpFuncCall]. *)
Lemma wp_func_call' {func_name func} `{!PkgInfo pkg_name} P :
  alist_lookup_f func_name (pkg_functions pkg_name) = Some func →
  (P -∗ is_pkg_defined_single pkg_name) →
  WpFuncCall func_name func P.
Proof.
  intros Hlookup HP. rewrite /WpFuncCall. iIntros "* Hdef HΦ". rewrite func_callv_unseal.
  wp_pure_lc "Hlc". wp_bind. iDestruct (HP with "Hdef") as "Hdef". iNamed "Hdef". iNamed "Hctx".
  iInv "Hctx" as "Hi" "Hclose". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi". rewrite [in # "__functions"]to_val_unseal. wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg Hinit]"). { iFrame "∗#%". }
  iModIntro. rewrite lookup_insert_ne // lookup_insert_eq. wp_pures.
  rewrite is_pkg_defined_pure_single_unseal in Hdefined.
  destruct Hdefined as [Hfunction Hmethod]. erewrite Hfunction; last done. wp_pures. iApply "HΦ".
Qed.

(** Internal to Goose. Used in generatedproofs to establish [WpMethodCall]. *)
Lemma wp_method_call' {type_name method_name m} `{!PkgInfo pkg_name} P :
  (alist_lookup_f type_name (pkg_msets pkg_name)) ≫= (alist_lookup_f method_name) = (Some m) →
  (P -∗ is_pkg_defined_single pkg_name) →
  WpMethodCall type_name method_name m P.
Proof.
  intros Hlookup HP. rewrite /WpMethodCall. iIntros "* Hdef HΦ". rewrite method_callv_unseal.
  wp_pure_lc "Hlc". wp_bind. iDestruct (HP with "Hdef") as "Hdef". iNamed "Hdef".
  iNamed "Hctx". iInv "Hctx" as "Hi" "Hclose". iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
  iNamed "Hi". rewrite [in # "__msets"]to_val_unseal. wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg". iMod ("Hclose" with "[Hg Hinit]"). { iFrame "∗#%". }
  iModIntro. do 2 rewrite lookup_insert_ne //. rewrite lookup_insert_eq.
  wp_pures. rewrite alist_lookup_f_fmap. rewrite is_pkg_defined_pure_single_unseal in Hdefined.
  destruct Hdefined as [Hfunction Hmethod].
  specialize (Hmethod _ _ _ Hlookup). destruct (alist_lookup_f type_name __method); last by exfalso.
  wp_pures. simpl in *. destruct (alist_lookup_f method_name l); last by exfalso.
  wp_pures. simplify_eq. iApply "HΦ".
Qed.

End calls.

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

Ltac solve_wp_func_call :=
  lazymatch goal with
  | |- WpFuncCall _ _ (is_pkg_defined ?pkg_name) =>
      apply (wp_func_call' (pkg_name:=pkg_name)); [reflexivity| iIntros "H"; try iDestruct "H" as "[H _]"; iFrame "H"]
  | _ => fail "solve_wp_func_call: not a WpFuncCall goal"
  end.

Ltac solve_wp_method_call :=
  lazymatch goal with
  | |- WpMethodCall _ _ _ (is_pkg_defined ?pkg_name) =>
      apply (wp_method_call' (pkg_name:=pkg_name)); [reflexivity | iIntros "H"; try iDestruct "H" as "[H _]"; iFrame "H"]
  | _ => fail "solve_wp_method_call: not a WpMethodCall goal"
  end.

(* FIXME: better implementation using PkgInfo to direct the search. Could try lithium even. *)
(* solve a goal which is just [is_pkg_init] or [is_pkg_defined] *)
Ltac solve_pkg_init :=
  unfold named;
  lazymatch goal with
  | |- environments.envs_entails ?env (is_pkg_init _) => idtac
  | |- environments.envs_entails ?env (is_pkg_defined _) => idtac
  | |- environments.envs_entails ?env (is_go_context) => idtac
  | _ => fail "not a is_pkg_init, is_pkg_defined, or is_go_context goal"
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

#[local] Transparent own_initializing.
Lemma wp_package_init (pkg_name : go_string) `{!PkgInfo pkg_name} (init_func : val) get_is_pkg_init is_pkg_init :
  ∀ Φ,
  get_is_pkg_init pkg_name = is_pkg_init →
  (own_initializing get_is_pkg_init ∗ (own_initializing get_is_pkg_init -∗ WP init_func #() {{ _, □ is_pkg_init ∗ own_initializing get_is_pkg_init }})) -∗
  (own_initializing get_is_pkg_init ∗ is_pkg_init -∗ Φ #()) -∗
  WP package.init #pkg_name init_func {{ Φ }}.
Proof.
  intros ? Heq. subst. iIntros "(Hown & Hpre) HΦ". rewrite package.init_unseal.
  wp_call. wp_call_lc "Hlc".
  wp_bind. iNamed "Hown". iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iRename "Hg" into "Hg2". iNamed "Hi".
  rewrite [in #"__packages"]to_val_unseal.
  wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg".
  iCombine "Hg Hg2" gives %[_ Heq]. subst.
  iMod ("Hclose" with "[Hg Hinit]") as "_". { iFrame "∗#%". }
  iModIntro. do 3 rewrite lookup_insert_ne //. rewrite lookup_insert_eq.
  wp_pures. rewrite alist_lookup_f_fmap /=.
  destruct (alist_lookup_f pkg_name) eqn:Hstatus.
  - simpl. wp_pures. wp_apply wp_assume. iIntros "%Hstarted_ne".
    rewrite bool_decide_decide in Hstarted_ne; try done.
    destruct decide as [|] in Hstarted_ne; try done.
    wp_pures. iApply "HΦ".
    iFrame "∗#". iDestruct (big_sepS_elem_of_acc with "Hinit") as "[$ _]".
    specialize (Hpackage_inited pkg_name).
    rewrite Hstatus lookup_union in Hpackage_inited.
    destruct lookup eqn:Hlookup in Hpackage_inited.
    { rewrite lookup_gset_to_gmap_Some in Hlookup. set_solver. }
    rewrite left_id in Hpackage_inited.
    symmetry in Hpackage_inited. rewrite lookup_gset_to_gmap_Some in Hpackage_inited.
    naive_solver.
  - simpl. wp_pure_lc "Hlc". wp_pures. wp_bind.
    iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iAssert (∃ g, own_globals (DfracOwn (1/2)) g)%I with "[Hi]" as "[% Hg]".
    { iNamedSuffix "Hi" "_tmp". iFrame. }
    iCombine "Hg2 Hg" gives %[_ Heq]. subst.
    iCombine "Hg2 Hg" as "Hg".
    wp_apply (wp_GlobalPut with "[$]").
    iIntros "[Hown Hg]".
    iMod ("Hclose" with "[Hg]") as "_".
    {
      do 3 rewrite (insert_insert_ne _ "__packages"%go) //.
      rewrite insert_insert_eq. rewrite insert_empty.
      iNext. repeat iExists _, ((_, _) :: _), _, _.
      rewrite fmap_cons. iFrame "Hg".
      iFrame "#%". iPureIntro.
      instantiate (1:=({[pkg_name]} ∪ package_started)).
      intros pkg_name'. specialize (Hpackage_inited pkg_name').
      rewrite gset_to_gmap_union_singleton !lookup_union.
      destruct (decide (pkg_name = pkg_name')).
      { subst. rewrite lookup_insert_eq. rewrite /= ByteString.eqb_refl.
        symmetry in Hpackage_inited. rewrite Hstatus lookup_union_None in Hpackage_inited.
        by destruct Hpackage_inited as [-> ?]. }
      rewrite lookup_insert_ne //.
      rewrite !lookup_union in Hpackage_inited.
      simpl. rewrite ByteString.eqb_ne //.
    }
    iModIntro. wp_pures. wp_bind.
    wp_apply (wp_wand with "[Hpre Hown]").
    { iApply ("Hpre" with "[$Hown $Hinv]"). }
    iClear "Hinit". iIntros (?) "[#? Hown]". iClear "Hinv". iNamed "Hown". wp_pures.
    wp_call_lc "Hlc". wp_bind. iInv "Hinv" as "Hi" "Hclose".
    clear dependent package_started package_inited package_inited_val global_addr_val.
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iRename "Hg" into "Hg2". iNamed "Hi".
    rewrite [in #"__packages"]to_val_unseal.
    wp_apply (wp_GlobalGet with "[$]"). iIntros "Hg".
    iCombine "Hg Hg2" gives %[_ Heq]. subst.
    do 3 rewrite lookup_insert_ne //. rewrite lookup_insert_eq.
    iMod ("Hclose" with "[Hg]") as "_".
    { iFrame "∗#%". }
    iModIntro. wp_pure_lc "Hlc". wp_pures. wp_bind. iInv "Hinv" as "Hi" "Hclose".
    iMod (lc_fupd_elim_later with "[$] Hi") as "Hi".
    iAssert (∃ g, own_globals (DfracOwn (1/2)) g)%I with "[Hi]" as "[% Hg]".
    { iNamedSuffix "Hi" "_tmp". iFrame. }
    iCombine "Hg Hg2" gives %[_ Heq]. subst.
    iCombine "Hg Hg2" as "Hg".
    wp_apply (wp_GlobalPut with "[$]"). iIntros "[Hown Hg]".
    iMod ("Hclose" with "[Hg]") as "_".
    {
      do 3 rewrite (insert_insert_ne _ "__packages"%go) //.
      rewrite insert_insert_eq. rewrite insert_empty.
      iNext. repeat iExists _, ((_, _) :: _), package_started, ({[pkg_name]} ∪ package_inited). iFrame.
      iSplit. { iModIntro. iApply big_sepS_insert_2; iFrame "#". }
      iFrame "%". iPureIntro. intros pkg_name'. specialize (Hpackage_inited pkg_name').
      simpl. rewrite gset_to_gmap_union_singleton !lookup_union.
      destruct (decide (pkg_name = pkg_name')).
      { subst. rewrite ByteString.eqb_refl lookup_insert_eq //.
        erewrite left_absorb; try done.
        rewrite /LeftAbsorb. by intros []. }
      rewrite ByteString.eqb_ne //. rewrite lookup_insert_ne //.
      rewrite !lookup_union // in Hpackage_inited.
    }
    rewrite to_val_unseal.
    iApply "HΦ". iFrame "∗#". done.
Qed.

End package_init.

(* Uses [cbv] to unfold [is_pkg_defined] despite it being [Opaque]. *)
Ltac simpl_is_pkg_defined := (cbv delta [is_pkg_defined]; simpl).
