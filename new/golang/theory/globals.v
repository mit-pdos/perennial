From New.golang.theory Require Import exception mem typing list.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii Equality.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Global Instance wp_unwrap (v : val) :
  PureWp True (globals.unwrap $ InjRV v) v.
Proof.
  rewrite globals.unwrap_unseal /globals.unwrap_def.
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

Section definitions_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

(* Internal specs for primitive global that only allows for inserting a new key into
   the globals map and reading existing keys. *)
Local Definition own_globals_inv : iProp Σ :=
  ∃ (g : gmap go_string val),
    "Hauth" ∷ ghost_map_auth go_globals_name (1/2)%Qp g ∗
    "Hg" ∷ own_globals (DfracOwn 1) g.

Local Definition is_globals_inv : iProp Σ :=
  inv nroot own_globals_inv.

Definition is_global (k : go_string) (v : val) : iProp Σ :=
  "#Hinv" ∷ is_globals_inv ∗
  "#Hptsto" ∷ k ↪[go_globals_name]□ v.

Definition own_globals (g : gmap go_string val) : iProp Σ :=
  "#Hinv" ∷ is_globals_inv ∗
  "Hauth2" ∷ ghost_map_auth go_globals_name (1/2)%Qp g.

Lemma wp_GlobalPut k v g :
  g !! k = None →
  {{{ own_globals g }}}
    GlobalPut #k v
  {{{ RET #();
      own_globals (<[ k := v ]> g) ∗
      is_global k v
  }}}.
Proof.
  intros Hlookup.
  iIntros (?) "Hg HΦ".
  iNamed "Hg".
  iInv "Hinv" as ">Hi".
  iNamed "Hi".
  rewrite to_val_unseal.
  iApply (wp_GlobalPut with "[$]").
  iIntros " !> Hg".
  iCombine "Hauth Hauth2" gives %[_ ->].
  iCombine "Hauth Hauth2" as "Hauth".
  iMod (ghost_map_insert_persist with "[$]") as "[[Hauth1 Hauth2] #Hptsto]"; first done.
  iSpecialize ("HΦ" with "[$]").
  by iFrame.
Qed.

Lemma wp_GlobalGet k v :
  {{{ is_global k v }}}
    GlobalGet #k
  {{{ RET (SOMEV v); True }}}.
Proof.
  iIntros (?) "Hg HΦ".
  iNamed "Hg".
  iInv "Hinv" as ">Hi".
  iNamed "Hi".
  rewrite to_val_unseal.
  iApply (wp_GlobalGet with "[$]").
  iIntros " !> Hg".
  iCombine "Hauth Hptsto" gives %Hlookup.
  rewrite Hlookup.
  iSpecialize ("HΦ" with "[$]").
  by iFrame.
Qed.

Lemma wp_GlobalGet_full k m :
  {{{ own_globals m }}}
    GlobalGet #k
  {{{ RET (match (m !! k) with
           | None => InjLV #()
           | Some v => InjRV v
           end); own_globals m  }}}.
Proof.
  iIntros (?) "Hg HΦ".
  iNamed "Hg".
  iInv "Hinv" as ">Hi".
  iNamed "Hi".
  rewrite to_val_unseal.
  iApply (lifting.wp_GlobalGet with "[$]").
  iIntros " !> Hg".
  iCombine "Hauth Hauth2" gives %[_ ->].
  iSpecialize ("HΦ" with "[$]").
  by iFrame.
Qed.

(* This must be owned by the `init` thread. *)
Definition own_globals_tok_def (pending_packages : gset go_string)
  (pkg_postconds : gmap go_string (iProp Σ)): iProp Σ :=
  ∃ g (pkg_initialized : gset go_string),
  "Hglobals" ∷ own_globals g ∗
  "%Hpkg" ∷ (⌜ dom g = pending_packages ∪ pkg_initialized ⌝) ∗
  "#Hinited" ∷ □ ([∗ set] pkg_name ∈ pkg_initialized,
                  default False (pkg_postconds !! pkg_name)
    ).
Program Definition own_globals_tok := unseal (_:seal (@own_globals_tok_def)). Obligation 1. by eexists. Qed.
Definition own_globals_tok_unseal : own_globals_tok = _ := seal_eq _.

End definitions_and_lemmas.

Section globals.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition is_global_definitions (pkg_name : go_string)
  (var_addrs : list (go_string * loc))
  (functions : list (go_string * val))
  (msets: list (go_string * (list (go_string * val))))
  : iProp Σ :=
  let var_addrs_val := alist_val ((λ '(name, addr), (name, #addr)) <$> var_addrs) in
  let functions_val := alist_val functions in
  let msets_val := alist_val ((λ '(name, mset), (name, alist_val mset)) <$> msets) in
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
  := wp_globals_get : ⊢ ∀ Φ, P -∗ (▷ Φ #addr) -∗
                             WP (globals.get #pkg_name #var_name) {{ Φ }}.

Class WpFuncCall (pkg_name : go_string) (func_name : go_string) (func : val)
                   (P : iProp Σ)
  := wp_func_call : ⊢ ∀ Φ, P -∗ (▷ Φ func) -∗
                           WP (func_call #pkg_name #func_name) {{ Φ }}.

Class WpMethodCall (pkg_name : go_string) (type_name : go_string) (func_name : go_string) (m : val)
                   (P : iProp Σ)
  := wp_method_call : ⊢ ∀ Φ, P -∗ (▷ Φ m) -∗
                           WP (method_call #pkg_name #type_name #func_name) {{ Φ }}.

Lemma wp_global_get' {pkg_name var_name var_addrs functions msets addr} :
  alist_lookup_f var_name var_addrs = Some addr →
  WpGlobalsGet pkg_name var_name addr (is_global_definitions pkg_name var_addrs functions msets).
Proof.
  intros Hlookup. rewrite /WpGlobalsGet.
  iIntros (?) "#Hctx HΦ".
  rewrite globals.get_unseal.
  wp_call.
  wp_pures.
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplifid to [{| Naive.unsigned := 118; ... |} :: ...] *)
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "_".
  wp_pures.
  rewrite alist_lookup_f_fmap Hlookup.
  wp_pures. iApply "HΦ".
Qed.

Lemma wp_func_call' {pkg_name func_name var_addrs functions msets func} :
  alist_lookup_f func_name functions = Some func →
  WpFuncCall pkg_name func_name func (is_global_definitions pkg_name var_addrs functions msets).
Proof.
  intros Hlookup. rewrite /WpFuncCall.
  iIntros (?) "#Hctx HΦ".
  rewrite func_call_unseal.
  wp_call.
  wp_pures.
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplifid to [{| Naive.unsigned := 118; ... |} :: ...] *)
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "_".
  wp_pures.
  rewrite Hlookup.
  wp_pures. iApply "HΦ".
Qed.

Lemma wp_method_call' {pkg_name type_name method_name var_addrs functions msets m} :
  ((alist_lookup_f method_name) <$> (alist_lookup_f type_name msets)) = Some (Some m) →
  WpMethodCall pkg_name type_name method_name m (is_global_definitions pkg_name var_addrs functions msets).
Proof.
  intros Hlookup. rewrite /WpMethodCall.
  iIntros (?) "#Hctx HΦ".
  rewrite method_call_unseal.
  wp_call.
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
  wp_pures. iApply "HΦ".
Qed.

(* No generic globals.alloc lemma. WPs for [globals.alloc vars] get proved for
   each package individually. This is here so something useful shows up from
   [Search]. *)
Lemma there_is_no_generic_lemma_for_globals_alloc_and_define:
  ∀ Φ pkg_name vars functions msets,
  False -∗ WP (globals.alloc_and_define pkg_name vars functions msets #()) {{ Φ }}.
Proof. iIntros. done. Qed.

End globals.

Local Ltac unseal :=
  rewrite ?own_globals_tok_unseal.

Section package_init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Lemma wp_package_init
  pending Φ
  (postconds : gmap go_string (iProp Σ))
  (pkg_name : go_string) (init_func : val)
  vars functions msets
  (GoDefns : Type)
  (is_defined : GoDefns → iProp Σ)
  (is_initialized : GoDefns → iProp Σ)
  :
  (∀ g,
     g !! pkg_name = None →
     {{{ own_globals g }}}
       globals.alloc_and_define pkg_name vars functions msets #()
     {{{ (d : GoDefns) v, RET #();
         is_defined d ∗
         own_globals (<[pkg_name := v]> g)
     }}}
  ) →
  (∀ (d : GoDefns),
     is_defined d -∗
     own_globals_tok ({[ pkg_name ]} ∪ pending) postconds -∗
     WP init_func #()
       {{ v, ⌜ v = #tt ⌝ ∗
             □ is_initialized d ∗
             own_globals_tok ({[ pkg_name ]} ∪ pending) postconds
       }}
  ) →
  postconds !! pkg_name = Some (∃ d, is_initialized d)%I →
  pkg_name ∉ pending →
  own_globals_tok pending postconds -∗
  (∀ (d : GoDefns), is_initialized d -∗ own_globals_tok pending postconds -∗ Φ #()) -∗
  WP (globals.package_init pkg_name vars functions msets init_func) {{ Φ }}.
Proof.
  unseal.
  intros Hwp_alloc Hwp_init Hpost Hnot_pending.
  iIntros "Htok HΦ".
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
    iDestruct "H" as (?) "Hinit".
    iApply ("HΦ" with "[$]").
    iFrame "∗#%".
  }
  (* actually run init *)
  wp_pures.
  wp_apply (Hwp_alloc with "[$]").
  { done. }
  iIntros "* [Hdef Hglobals]".
  wp_pures.
  iDestruct (Hwp_init with "[$Hdef] [Hglobals]") as "Hinit".
  { iFrame "∗#%". iPureIntro. set_solver. }
  wp_apply (wp_wand with "Hinit").
  iIntros (?) "H".
  iDestruct "H" as (?) "[#Hinit Htok]". subst.
  iApply ("HΦ" with "[$]").
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

Tactic Notation "wp_func_call" :=
  (wp_bind (func_call _ _);
   unshelve wp_apply (wp_func_call with "[]"); [| | tc_solve | | ]; try iFrame "#").

Tactic Notation "wp_method_call" :=
  (wp_bind (method_call _ _ _);
   unshelve wp_apply (wp_method_call with "[]"); [| | tc_solve | |]; try iFrame "#").
