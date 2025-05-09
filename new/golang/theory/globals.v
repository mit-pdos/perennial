From New.golang.theory Require Import exception mem typing list.
From New.golang.defn Require Import pkg.
From New.golang.defn Require Export globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii Equality.
From Perennial Require Import base.

Set Default Proof Using "Type".

Class GoContext `{ffi_syntax} :=
  {
    global_addrs : go_string → go_string → loc;
    func_table : go_string → go_string → val;
    method_table : go_string → go_string → go_string → val;
  }.

Class pkgG `{ffi_syntax} {Γ : GoContext} (pkg_name : go_string) {info : PkgInfo pkg_name} :=
  {
    func_table_lookup : ∀ func_name,
      default #() (alist_lookup_f func_name (pkg_functions pkg_name)) = func_table pkg_name func_name;
    method_table_lookup : ∀ type_name method_name,
      default #() ((alist_lookup_f method_name) <$> (alist_lookup_f type_name (pkg_msets pkg_name))) =
      method_table pkg_name type_name method_name;
  }.

Section wps.
Context `{sem : ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {Γ : GoContext}.

Definition is_go_context : iProp Σ :=
  ∃ (go_context_decoded : list (go_string * (list (go_string * loc) *
                                               list (go_string * val) *
                                               list (go_string * (list (go_string * val)))))),
  let go_context_encoded :=
    alist_val ((λ '(name, (var_addrs, functions, msets)),
                  let var_addrs_val := alist_val ((λ '(name, addr), (name, #addr)) <$> var_addrs) in
                  let functions_val := alist_val functions in
                  let msets_val := alist_val (list_fmap _ _ (λ '(name, mset), (name, alist_val mset)) msets) in
                  (name, (var_addrs_val, functions_val, msets_val)%V)
               ) <$> go_context_decoded) in
  "#Hg" ∷ own_globals DfracDiscarded {[ "$go"%go := go_context_encoded ]} ∗
  "%Hfunc" ∷
    (⌜ ∀ pkg_name func_name func,
       (alist_lookup_f func_name) <$>
         (snd <$> (fst <$> (alist_lookup_f pkg_name go_context_decoded))) = Some func →
       func_table pkg_name func_name = func
       ⌝)
  "%Hmethods" ∷
    (⌜ ∀ pkg_name type_name method_name method,
       (alist_lookup_f func_name) <$>
         (snd <$> (fst <$> (alist_lookup_f pkg_name go_context_decoded))) = Some func ⌝)
.

  is_global pkg_name (var_addrs_val, functions_val, msets_val).

Lemma alist_lookup_f_fmap {A B} n (l: list (go_string * A)) (f : A → B) :
  alist_lookup_f n ((λ '(name, a), (name, f a)) <$> l) =
  f <$> (alist_lookup_f n l).
Proof.
  induction l.
  { done. }
  simpl.
  destruct a.
  destruct (ByteString.eqb g n).
  { done. }
  rewrite IHl //.
Qed.

Class WpGlobalsGet (pkg_name : go_string) (var_name : go_string) (addr : loc)
                   (P : iProp Σ)
  := wp_globals_get : ⊢ {{{ P }}} (globals.get #pkg_name #var_name) {{{ RET #addr; True }}}.

Definition func_callv_def (pkg_name func_name : go_string) : func.t :=
  {|
    func.f := <>;
    func.x := "firstArg";
    func.e :=
      let: "__p" := globals.unwrap (GlobalGet (# pkg_name)) in
      let: "varAddrs" := Fst (Fst "__p") in
      let: "functions" := Snd (Fst "__p") in
      let: "typeToMethodSets" := Snd "__p" in
      globals.unwrap (alist_lookup (# func_name) "functions") "firstArg"
  |}.
Program Definition func_callv := sealed @func_callv_def.
Definition func_callv_unseal : func_callv = _ := seal_eq _.

Global Instance wp_func_callv (pkg_name func_name : go_string) :
  PureWp True (func_call #pkg_name #func_name)%E
    #(func_callv pkg_name func_name)%E.
Proof.
  rewrite func_call_unseal /func_call_def func_callv_unseal.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.

Class WpFuncCall (pkg_name : go_string) (func_name : go_string) (m : val)
                   (P : iProp Σ)
  := wp_func_call :
    ⊢ (∀ (first_arg : val) Φ,
         P -∗ (WP (m first_arg) {{ Φ }}) -∗
         WP #(func_callv pkg_name func_name) first_arg {{ Φ }}).

Definition method_callv_def (pkg_name type_name method_name : go_string) (receiver : val) : func.t :=
  {|
    func.f := <>;
    func.x := "firstArg";
    func.e :=
      let: "__p" := globals.unwrap (GlobalGet (# pkg_name)) in
      let: "varAddrs" := Fst (Fst "__p") in
      let: "functions" := Snd (Fst "__p") in
      let: "typeToMethodSets" := Snd "__p" in
      let: "methodSet" := globals.unwrap (alist_lookup (# type_name) "typeToMethodSets") in
      globals.unwrap (alist_lookup (# method_name) "methodSet") receiver "firstArg"
  |}.
Program Definition method_callv := sealed @method_callv_def.
Definition method_callv_unseal : method_callv = _ := seal_eq _.

Global Instance wp_method_callv (pkg_name type_name method_name : go_string) (receiver : val) :
  PureWp True (method_call #pkg_name #type_name #method_name receiver)%E
    #(method_callv pkg_name type_name method_name receiver)%E.
Proof.
  rewrite method_call_unseal /method_call_def method_callv_unseal.
  intros ?????. iIntros "Hwp". wp_pure_lc "?".
  wp_pures. by iApply "Hwp".
Qed.

Class WpMethodCall (pkg_name : go_string) (type_name : go_string) (func_name : go_string) (m : val)
                   (P : iProp Σ)
  := wp_method_call :
    ⊢ (∀ (first_arg receiver : val) Φ,
         P -∗ (WP (m receiver first_arg) {{ Φ }}) -∗
         WP #(method_callv pkg_name type_name func_name receiver) first_arg {{ Φ }}).

Class WpGlobalsAlloc (vars : list (go_string * go_type)) (GlobalAddrs : Type)
                     (var_addrs : GlobalAddrs → list (go_string * loc))
                     (own_allocated : GlobalAddrs → iProp Σ)
  := wp_globals_alloc :
    ⊢ {{{ True }}}
        (globals.alloc vars #())
      {{{ (d : GlobalAddrs),
            RET (alist_val $ (λ '(pair name addr), (pair name #addr)) <$> var_addrs d);
          own_allocated d
      }}}.

Lemma wp_globals_get' {pkg_name var_name var_addrs addr} `{!PkgInfo pkg_name} :
  alist_lookup_f var_name var_addrs = Some addr →
  WpGlobalsGet pkg_name var_name addr (is_global_definitions pkg_name var_addrs).
Proof.
  intros Hlookup. rewrite /WpGlobalsGet.
  iStartProof.
  iIntros (?) "!# #Hctx HΦ".
  rewrite globals.get_unseal.
  wp_call.
  wp_pures.
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplifid to [{| Naive.unsigned := 118; ... |} :: ...] *)
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "_".
  wp_pures.
  rewrite alist_lookup_f_fmap Hlookup.
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_func_call' {pkg_name func_name var_addrs func} `{!PkgInfo pkg_name} :
  alist_lookup_f func_name (pkg_functions pkg_name) = Some func →
  WpFuncCall pkg_name func_name func (is_global_definitions pkg_name var_addrs).
Proof.
  intros Hlookup. rewrite /WpFuncCall.
  iIntros "* #Hctx HΦ".
  rewrite func_callv_unseal /func_callv_def.
  wp_pures.
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplifid to [{| Naive.unsigned := 118; ... |} :: ...] *)
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

Ltac solve_wp_globals_alloc :=
  rewrite /WpGlobalsAlloc;
  iIntros (?) "!# _ HΦ";
  wp_call;
  repeat (let x := fresh "l" in wp_alloc x as "?"; wp_pures);
  unshelve iSpecialize ("HΦ" $! _); first (econstructor; shelve);
  iApply "HΦ"; iFrame.

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
