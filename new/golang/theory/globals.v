From New.golang.theory Require Import exception mem typing list.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii Equality.

Section context.
Context {PROP:bi}.
Class BiContextRoot := { is_bi_context : PROP ; bi_context_pers :: Persistent is_bi_context }.
Class BiContext `{BiContextRoot} (P : PROP) := { contains : is_bi_context -∗ P }.
Global Arguments contains {_ _} (_).
End context.

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Global Instance wp_unwrap (v : val) :
  PureWp True (globals.unwrap $ InjRV v) v.
Proof.
  rewrite /globals.unwrap.
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
  (pkg_postconds : gmap go_string (∀ `(!BiContextRoot (PROP:=iProp Σ)), Type)): iProp Σ :=
  ∃ g (pkg_initialized : gmap go_string ()),
  "Hglobals" ∷ own_globals g ∗
  "%Hpkg" ∷ (⌜ ∀ (pkg_name : go_string),
               is_Some (g !! ("pkg:"%go ++ pkg_name)) ↔
               is_Some (((gset_to_gmap tt pending_packages) ∪ pkg_initialized) !! pkg_name)
               ⌝) ∗
  "#Hinited" ∷ □ ([∗ map] pkg_name ↦ _ ∈ pkg_initialized,
                  match (pkg_postconds !! pkg_name) with
                  | None => False
                  | Some InitializedContext => (∃ (root:BiContextRoot (PROP:=iProp Σ))
                                                 (H:InitializedContext root), is_bi_context)
                  end
    ).
Program Definition own_globals_tok := unseal (_:seal (@own_globals_tok_def)). Obligation 1. by eexists. Qed.
Definition own_globals_tok_unseal : own_globals_tok = _ := seal_eq _.

End definitions_and_lemmas.


Section global_vars.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!BiContextRoot (PROP:=iProp Σ)}.
Context `{!goGlobalsGS Σ}.

Class WpGlobalsGet (pkg_var_name : go_string * go_string) (addr : loc)
  := wp_globals_get : ⊢ ∀ Φ, is_bi_context -∗ (▷ Φ #addr) -∗
                             WP (globals.get pkg_var_name #()) {{ Φ }}.

Definition is_global_definitions (pkg_name : go_string)
  (var_addrs : list (go_string * loc))
  (functions : list (go_string * val))
  (msets: list (go_string * (list (go_string * val))))
  : iProp Σ :=
  let var_addrs_val := alist_val ((λ '(name, addr), (name, #addr)) <$> var_addrs) in
  let functions_val := alist_val functions in
  let msets_val := alist_val ((λ '(name, mset), (name, alist_val mset)) <$> msets) in
  is_global ("pkg:"%go ++ pkg_name) (var_addrs_val, functions_val, msets_val).

Lemma alist_lookup_f_loc n (var_addrs : list (go_string * loc)) :
  alist_lookup_f n ((λ '(name, addr), (name, #addr)) <$> var_addrs) =
  # <$> (alist_lookup_f n var_addrs).
Proof.
  induction var_addrs.
  { done. }
  simpl.
  destruct a.
  destruct (ByteString.eqb g n).
  { done. }
  rewrite IHvar_addrs //.
Qed.

Lemma wp_global_get' {pkg_name var_name var_addrs functions msets addr}
  {Hdefined : BiContext (is_global_definitions pkg_name var_addrs functions msets)} :
  alist_lookup_f var_name var_addrs = Some addr →
  WpGlobalsGet (pkg_name, var_name) addr.
Proof.
  intros Hlookup. rewrite /WpGlobalsGet.
  iIntros (?) "#Hctx HΦ".
  wp_call.
  wp_pures.
  iDestruct (Hdefined.(contains) with "[$]") as "#Hdefined".
  wp_bind (GlobalGet _).
  (* FIXME: go_string is getting simplifid to [{| Naive.unsigned := 118; ... |} :: ...] *)
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "_".
  wp_pures.
  rewrite alist_lookup_f_loc Hlookup.
  wp_pures. iApply "HΦ".
Qed.

(* No generic globals.alloc lemma. WPs for [globals.alloc vars] get proved for
   each package individually. This is here so something useful shows up from
   [Search]. *)
Lemma there_is_no_generic_lemma_for_globals_alloc_and_define:
  ∀ Φ pkg_name vars functions msets,
  False -∗ WP (globals.alloc_and_define pkg_name vars functions msets #()) {{ Φ }}.
Proof. iIntros. done. Qed.

End global_vars.

Local Ltac unseal :=
  rewrite ?own_globals_tok_unseal.

Section package_init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Lemma wp_package_init
  pending Φ
  (postconds : gmap go_string (∀ `{!BiContextRoot (PROP:=iProp Σ)}, Type))
  (pkg_name : go_string) (init_func : val)
  vars functions msets
  (GoDefinedContext : ∀ `{!BiContextRoot (PROP:=iProp Σ)}, Type)
  (GoInitializedContext : (∀ `{!BiContextRoot (PROP:=iProp Σ)}, Type))
  :
  (∀ g,
     g !! ("pkg:"%go ++ pkg_name) = None →
     {{{ own_globals g }}}
       globals.alloc_and_define pkg_name vars functions msets (# ())
     {{{ `(!BiContextRoot) `(!GoDefinedContext) v, RET #();
         is_bi_context ∗
         own_globals (<[("pkg:"%go ++ pkg_name) := v]> g)
     }}}
  ) →
  (∀ `(!BiContextRoot) `(!GoDefinedContext),
     own_globals_tok ({[ pkg_name ]} ∪ pending) postconds -∗
     WP init_func #()
       {{ v, ⌜ v = #tt ⌝ ∗ ∃ (r: BiContextRoot) `(!GoInitializedContext),
             is_bi_context ∗
             own_globals_tok ({[ pkg_name ]} ∪ pending) postconds
       }}
  ) →
  postconds !! pkg_name = Some (@GoInitializedContext) →
  pkg_name ∉ pending →
  own_globals_tok pending postconds -∗
  (∀ `(!BiContextRoot) `(!GoInitializedContext),
     is_bi_context -∗ own_globals_tok pending postconds -∗ Φ #()) -∗
  WP (globals.package_init pkg_name vars functions msets init_func) {{ Φ }}.
Proof.
  unseal.
  intros Hwp_alloc Hwp_init Hpost Hnot_pending.
  iIntros "Htok HΦ".
  wp_call.
  iNamed "Htok".
  wp_bind (GlobalGet _).
  iApply (wp_GlobalGet_full with "[$]").
  iNext. iIntros "Hglobals".
  destruct (lookup _ g) eqn:Hlookup.
  { (* don't run init because the package has already been initialized *)
    wp_pures.
    pose proof (Hpkg pkg_name) as Hpkg'.
    rewrite Hlookup /= in Hpkg'.
    symmetry in Hpkg'.
    rewrite lookup_union in Hpkg'.
    rewrite lookup_gset_to_gmap option_guard_False //=
      left_id in Hpkg'.
    destruct Hpkg' as [_ Hpkg'].
    specialize (Hpkg' ltac:(done)).
    destruct Hpkg'.
    iDestruct (big_sepM_lookup with "Hinited") as "H".
    { done. }
    rewrite Hpost /=.
    iDestruct "H" as (? ?) "Hctx".
    unshelve iApply ("HΦ" $! _ ltac:(done) with "[$]").
    iFrame "∗#%".
  }
  (* actually run init *)
  wp_pures.
  wp_apply (Hwp_alloc with "[$]").
  { done. }
  iIntros "* [#Hctx Hglobals]".
  wp_pures.
  iDestruct (Hwp_init with "[Hglobals]") as "Hinit".
  { done. }
  { iFrame "∗#%". iPureIntro.
    intros pkg_name'.
    specialize (Hpkg pkg_name').
    destruct (decide (pkg_name = pkg_name')).
    - subst. rewrite lookup_insert. rewrite lookup_union.
      rewrite lookup_gset_to_gmap option_guard_True //.
      2:{ set_solver. }
      rewrite union_Some_l //.
    - rewrite lookup_insert_ne //.
      2:{ naive_solver. }
      rewrite Hpkg gset_to_gmap_union_singleton lookup_union lookup_union lookup_insert_ne //.
  }
  wp_apply (wp_wand with "Hinit").
  iIntros (?) "H".
  iClear "Hctx". clear H H0.
  iDestruct "H" as (???) "[#Hctx Htok]". subst.
  unshelve iApply ("HΦ" $! _ _ with "[$]").
  { done. }
  clear Hpkg.
  iClear "Hinited".
  iNamed "Htok".
  iDestruct (big_sepM_insert_2 _ _ pkg_name () with "[] Hinited") as "Hinited2".
  { simpl. rewrite Hpost. iFrame "#". done. }
  iFrame "∗#%".
  iPureIntro.
  intros pkg_name'.
  specialize (Hpkg pkg_name').
  rewrite Hpkg gset_to_gmap_union_singleton -insert_union_l
          -insert_union_r // lookup_gset_to_gmap option_guard_False //.
Qed.

End package_init.

Section init.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Lemma go_global_init (posts : ∀ {H : goGlobalsGS Σ}, gmap go_string (iProp Σ))
  {hT: goGlobals_preG Σ}
  :
  ⊢
    own_globals (DfracOwn 1) ∅ ={⊤}=∗ ∃ (H : goGlobalsGS Σ),
      own_package_post_toks ∅ ∗ own_globals_tok ∅ posts.
Proof.
  iMod (ghost_map_alloc (∅ : gmap (go_string * go_string) loc)) as (new_globals_name) "[Haddrs _]".
  iMod (ghost_map_alloc (∅ : gmap go_string ())) as (new_package_postcond_name) "[Hpost _]".
  iMod (ghost_var_alloc None) as (new_access_prev_state_name) "Hacc".
  iIntros "[Hg Hg2]".
  iExists (GoGlobalsGS _ _ _ _ _ _).
  rewrite own_globals_tok_unseal.
  iMod (inv_alloc with "[Hg2 Haddrs]") as "#Hinv".
  2:{
    iModIntro.
    rewrite own_package_post_toks_unseal.
    iFrame "#∗".
    repeat iExists _.
    instantiate (1:=∅).
    iSplit.
    { iPureIntro. intros. right. rewrite lookup_empty //. }
    by iApply big_sepM_empty.
  }
  iNext.
  iFrame.
  iPureIntro. intros.
  rewrite kmap_empty fmap_empty //.
Qed.

End init.
