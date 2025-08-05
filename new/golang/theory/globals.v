From New.golang.theory Require Import exception mem typing list.
From New.golang.defn Require Import pkg.
From New.golang.defn Require Export globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii Equality.
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

Section ghost_map_lemmas.
  Context `{ghost_mapG Σ K V}.
  (* FIXME: upstream. *)
  Global Instance ghost_map_auth_combines_gives {γ q1 q2 m1 m2} :
    CombineSepGives (ghost_map_auth γ q1 m1) (ghost_map_auth γ q2 m2) ⌜ ((q1 + q2) ≤ 1)%Qp ∧ m1 = m2 ⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %?. eauto.
  Qed.
End ghost_map_lemmas.

Class goGlobals_preG `{ffi_syntax} (Σ: gFunctors) : Set :=
  {
    #[global] go_globals_inG :: ghost_mapG Σ go_string val ;
  }.

Class goGlobalsGS `{ffi_syntax} Σ : Set :=
  GoGlobalsGS {
      #[global] go_globals_pre_inG :: goGlobals_preG Σ ;
      go_globals_name : gname ;
    }.

Definition goGlobalsΣ `{ffi_syntax} : gFunctors :=
  #[ghost_mapΣ go_string val; ghost_mapΣ go_string ()].

Global Instance subG_goGlobalsG `{ffi_syntax} {Σ} : subG goGlobalsΣ Σ → goGlobals_preG Σ.
Proof. solve_inG. Qed.

Class GoContext {ext : ffi_syntax} Σ :=
  {
    global_addr : go_string → loc;
    function : go_string → option val;
    method : go_string → go_string → option val;
    is_pkg_init : go_string → iProp Σ;
  }.

Section globals.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.
Context `{!GoContext Σ}.

Definition is_go_context : iProp Σ :=
    inv nroot (
        ∃ (global_addr_val : list (_ * loc)) function_val method_val package_inited,
        "Hg" ∷ own_globals 1 (
            <["__global_vars"%go := alist_val ((λ '(a, b), (a, #b)) <$> global_addr_val)]>
              (<["__functions"%go := alist_val function_val]>
                 (<["__msets"%go := alist_val ((λ '(a, b), (a, alist_val b)) <$> method_val)]>
                    package_inited))) ∗
        "#Hinit" ∷ □([∗ map] pkg_name ↦ _ ∈ package_inited, is_pkg_init pkg_name) ∗
        "%Hglobal_addr" ∷ ⌜ ∀ var_name, default null (alist_lookup_f var_name global_addr_val) = global_addr var_name ⌝ ∗
        "%Hfunction" ∷ ⌜ ∀ func_name, (alist_lookup_f func_name function_val) = function func_name ⌝ ∗
        "%Hmethod" ∷ ⌜ ∀ type_name method_name,
          (alist_lookup_f type_name method_val) ≫= (alist_lookup_f method_name) =
          method type_name method_name ⌝
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
  PureWp True (func_call #func_name)%E
    #(func_callv func_name)%E.
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
  PureWp True (method_call #type_name #method_name receiver)%E
    #(method_callv type_name method_name receiver)%E.
Proof.
  rewrite method_call_unseal /method_call_def method_callv_unseal.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.

Class WpMethodCall (type_name : go_string) (func_name : go_string) (m : val)
                   (P : iProp Σ)
  := wp_method_call :
    ⊢ (∀ (first_arg receiver : val) Φ,
         P -∗ (WP (m receiver first_arg) {{ Φ }}) -∗
         WP #(method_callv type_name func_name receiver) first_arg {{ Φ }}).

Lemma wp_globals_get var_name :
  {{{ is_go_context }}} (globals.get #var_name) {{{ RET #(global_addr var_name); True }}}.
Proof.
  iIntros (?) "#Hctx HΦ". rewrite globals.get_unseal.
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

Local Lemma wp_func_call_aux func_name m :
  (∀ (first_arg : val) Φ,
     function func_name = Some m →
     is_go_context -∗
     ▷ (WP (m first_arg) {{ Φ }}) -∗
     WP #(func_callv func_name) first_arg {{ Φ }}).
Proof.
  iIntros "* %Hf Hctx HΦ".
  rewrite func_callv_unseal /func_callv_def.
  wp_pure_lc "Hlc". wp_bind.
  iInv "Hctx" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "[$] Hi") as "Hi". iNamed "Hi".
  rewrite [in # "__functions"]to_val_unseal.
  wp_apply (wp_GlobalGet with "[$]").
  iIntros "Hg".
  iMod ("Hclose" with "[Hg Hinit]").
  { iFrame "∗#%". }
  iModIntro. rewrite lookup_insert_ne // lookup_insert_eq.
  wp_pures. rewrite Hfunction. rewrite Hf. wp_pures. iApply "HΦ".
Qed.

Definition is_defined pkg_name `{!PkgInfo pkg_name} : Prop :=
  (∀ func_name func, (alist_lookup_f func_name (pkg_functions pkg_name)) = Some func →
             function func_name = Some func).

(** [IsPkgInitDefinition] is used to record the user-defined initialization
    predicate. Each proof of a package should define a new instances of this. *)
Class IsPkgInitDefinition (pkg_name : go_string) :=
  is_pkg_init_def : iProp Σ.

Local Definition is_pkg_init_aux (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInitDefinition pkg_name}
  : iProp Σ :=
  "#Hg" ∷ is_go_context ∗
  "%Hdef" ∷ ⌜ is_defined pkg_name ⌝ ∗ (* this has [is_go_context] inside it. *)
  "#Hdeps" ∷ □([∗ list] pkg_name ∈ (pkg_imported_pkgs pkg_name), is_pkg_init pkg_name) ∗
  "#Hinit" ∷ □ is_pkg_init_def.

(** [IsPkgInit] asserts that the global configuration for all initialization
    predicates actually matches the user-defined predicate for [pkg_name]. This
    is a precondition to [wp_func_call] and [wp_method_call] for [pkg_name]. *)
Class IsPkgInit (pkg_name : go_string) `{!PkgInfo pkg_name} `{!IsPkgInitDefinition pkg_name} : Prop :=
  is_pkg_init_eq : (is_pkg_init pkg_name = is_pkg_init_aux pkg_name).

Class WpFuncCall func_name f :=
  wp_func_call : (∀ (first_arg : val) Φ,
     function func_name = Some f →
     is_go_context -∗
     ▷ (WP (f first_arg) {{ Φ }}) -∗
     WP #(func_callv func_name) first_arg {{ Φ }}).

Context `{IsPkgInit foo}.

TODO: iPkgInit should solve goals like `is_go_context`, `is_pkg_init`, and `is_defined`

is_pkg_init foo :=
  is_defined foo ∗ (* this has [is_go_context] inside it. *)
  is_go_context

  (* Should always be autogenerated, but can't be done in `generatedproof` bc it depends on non-autogenerated stuff. *)
  is_pkg_deps_init_foo ∗

  (* user-chosen predicate *)
  is_pkg_init_foo.



function foo = fooⁱᵐᵖˡ ∧
function bar = barⁱᵐᵖˡ ∧
...
function zzz = zzzⁱᵐᵖˡ

Lemma wp_func_call' {pkg_name func_name var_addrs func} `{!PkgInfo pkg_name} :
  alist_lookup_f func_name (pkg_functions pkg_name) = Some func →
  WpFuncCall pkg_name func_name func is_go_context.
Proof.
  intros Hlookup. rewrite /WpFuncCall.
  iIntros "* #Hctx HΦ".
  rewrite func_callv_unseal /func_callv_def.
  wp_pures.
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplified to [{| Naive.unsigned := 118; ... |} :: ...] *)
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "_".
  wp_pures.
  rewrite Hlookup.
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_method_call' {pkg_name type_name method_name var_addrs m} `{!PkgInfo pkg_name} :
  ((alist_lookup_f method_name) <$> (alist_lookup_f type_name (pkg_msets pkg_name))) = Some (Some m) →
  WpMethodCall pkg_name type_name method_name m (is_global_definitions pkg_name var_addrs).
Proof.
  intros Hlookup. rewrite /WpMethodCall.
  iIntros "* #Hctx HΦ".
  rewrite method_callv_unseal /method_callv_def.
  wp_pures.
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplifid to [{| Naive.unsigned := 118; ... |} :: ...] *)
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "_".
  wp_pures.
  rewrite fmap_Some in Hlookup.
  destruct Hlookup as (? & Heq1 & Heq2).
  rewrite alist_lookup_f_fmap.
  rewrite Heq1.
  wp_pures.
  rewrite -Heq2.
  wp_pures. by iApply "HΦ".
Qed.

End globals.

Local Ltac unseal :=
  rewrite ?own_globals_tok_unseal.

Section init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Lemma go_global_init (posts : ∀ {H : goGlobalsGS Σ}, gmap go_string (iProp Σ))
  {hT: goGlobals_preG Σ}
  :
  ⊢ lifting.own_globals (DfracOwn 1) ∅ ={⊤}=∗ ∃ (H : goGlobalsGS Σ),
      own_globals_tok ∅ posts.
Proof.
  iMod (ghost_map_alloc (∅ : gmap go_string val)) as (new_globals_name) "[[Haddrs Haddrs2] _]".
  iIntros "Hg".
  iExists (GoGlobalsGS _ _ _ new_globals_name).
  rewrite own_globals_tok_unseal.
  iMod (inv_alloc with "[Hg Haddrs]") as "#Hinv".
  2:{
    iModIntro.
    iFrame "#∗".
    repeat iExists _.
    instantiate (1:=∅).
    iSplit.
    { iPureIntro. done. }
    iModIntro.
    by iApply big_sepS_empty.
  }
  iNext.
  iFrame.
Qed.

End init.

Global Hint Mode WpGlobalsGet - - - - - - + + - - : typeclass_instances.
Global Hint Mode WpMethodCall - - - - - - + + + - - : typeclass_instances.
Global Hint Mode WpFuncCall - - - - - - + + - - : typeclass_instances.

(* TODO: better error messages if tc_solve fails to find a val for the name. *)
Tactic Notation "wp_globals_get_core" :=
  (wp_bind (globals.get _ _);
   unshelve wp_apply (wp_globals_get with "[]"); [| | tc_solve | |]).

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
