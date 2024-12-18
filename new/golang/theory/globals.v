From New.golang.theory Require Import exception mem typing.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii.

Class goGlobals_preG `{ffi_syntax} (Σ: gFunctors) : Set :=
  {
    #[global] go_globals_inG :: ghost_mapG Σ (go_string * go_string) loc ;
    #[global] go_package_initialized_inG :: ghost_mapG Σ go_string () ;
    #[global] go_access_prev_inG :: ghost_varG Σ (option (gmap go_string val)) ;
  }.

Class goGlobalsGS `{ffi_syntax} Σ : Set :=
  GoGlobalsGS {
      #[global] go_globals_pre_inG :: goGlobals_preG Σ ;
      go_globals_name : gname ;
      go_package_postcond_tok_name : gname ;
      go_access_prev_state_name : gname ;
    }.

Definition goGlobalsΣ `{ffi_syntax} : gFunctors :=
  #[ghost_mapΣ (go_string * go_string) loc ; ghost_mapΣ go_string (); ghost_varΣ (option (gmap go_string val))].

Global Instance subG_goGlobalsG `{ffi_syntax} {Σ} : subG goGlobalsΣ Σ → goGlobals_preG Σ.
Proof. solve_inG. Qed.

Section definitions_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Fixpoint is_valid_package_name (pkg_name : go_string) : bool :=
  match pkg_name with
  | [] => true
  | {| Naive.unsigned := 32; Naive._unsigned_in_range := eq_refl |} :: _ => false
    (* Check " "%go. *)
  | _ :: pkg_name => is_valid_package_name pkg_name
  end.

Local Notation encode_var_name := (globals.globals.encode_var_name).

(* The only concurrent access to globals is to read the address of global
   variables, so that's the only thing this invariant is concerned with. *)
Local Definition own_globals_inv : iProp Σ :=
  ∃ g (addrs : gmap (go_string * go_string) loc),
  "Hglobals_i" ∷ own_globals (DfracOwn (1/2)) g ∗
  "Haddrs" ∷ ghost_map_auth go_globals_name 1%Qp addrs ∗
  "%Hvars" ∷ (⌜ ∀ pkg_name var_name,
                is_valid_package_name pkg_name →
                # <$> addrs !! (pkg_name, var_name) = g !! (encode_var_name pkg_name var_name) ⌝).

Local Definition is_globals_inv : iProp Σ :=
  inv nroot own_globals_inv.

(* This must be owned by the `init` thread. *)
Definition own_globals_tok_def (pending_packages : gset go_string)
  (pkg_postconds : gmap go_string (iProp Σ)): iProp Σ :=
  ∃ g (pkg_initialized : gmap go_string ()),
  "Hglobals" ∷ own_globals (DfracOwn (1/2)) g ∗
  "Hacc" ∷ ghost_var go_access_prev_state_name 1%Qp None ∗
  "%Hpkg" ∷ (⌜ ∀ pkg_name,
               is_valid_package_name pkg_name →
               pkg_name ∈ pending_packages ∨
                 (match pkg_initialized !! pkg_name with
                  | Some _ => g !! pkg_name = Some #()%V
                  | None => g !! pkg_name = None ∧
                           ∀ var_name, g !! (encode_var_name pkg_name var_name) = None
                  end) ⌝) ∗
  "#Hinv" ∷ is_globals_inv ∗
  "#Hinited" ∷ ([∗ map] pkg_name ↦ _ ∈ pkg_initialized,
                  match (pkg_postconds !! pkg_name) with
                  | None => False
                  | Some P => inv nroot (pkg_name ↪[go_package_postcond_tok_name] () ∨ P)
                  end
    ).
Program Definition own_globals_tok := unseal (_:seal (@own_globals_tok_def)). Obligation 1. by eexists. Qed.
Definition own_globals_tok_unseal : own_globals_tok = _ := seal_eq _.

Definition own_package_post_toks_def (used_pkgs : gset go_string) : iProp Σ :=
  ghost_map_auth go_package_postcond_tok_name 1%Qp (gset_to_gmap () used_pkgs).
Program Definition own_package_post_toks := unseal (_:seal (@own_package_post_toks_def)). Obligation 1. by eexists. Qed.
Definition own_package_post_toks_unseal : own_package_post_toks = _ := seal_eq _.

Definition own_package_post_tok_def (pkg_name : go_string) : iProp Σ :=
  pkg_name ↪[go_package_postcond_tok_name] ().
Program Definition own_package_post_tok := unseal (_:seal (@own_package_post_tok_def)). Obligation 1. by eexists. Qed.
Definition own_package_post_tok_unseal : own_package_post_tok = _ := seal_eq _.

Definition is_initialized_def (pkg_name : go_string) (P : iProp Σ) : iProp Σ :=
  inv nroot (pkg_name ↪[go_package_postcond_tok_name] () ∨ P).
Program Definition is_initialized := unseal (_:seal (@is_initialized_def)). Obligation 1. by eexists. Qed.
Definition is_initialized_unseal : is_initialized = _ := seal_eq _.

Definition is_global_addr_def (var_id : go_string * go_string) (addr : loc) : iProp Σ :=
  is_globals_inv ∗ var_id ↪[go_globals_name]□ addr ∗ ⌜ is_valid_package_name var_id.1 ⌝.
Program Definition is_global_addr := unseal (_:seal (@is_global_addr_def)). Obligation 1. by eexists. Qed.
Definition is_global_addr_unseal : is_global_addr = _ := seal_eq _.

Definition own_unused_vars_def (pkg_name : go_string) (used_var_names : gset go_string) : iProp Σ :=
  ∃ g_old var_addrs,
  "Hglobals" ∷ own_globals (DfracOwn (1/2)) ((kmap (encode_var_name pkg_name) var_addrs) ∪ g_old) ∗
  "Hacc" ∷ ghost_var go_access_prev_state_name (1/2)%Qp (Some g_old) ∗
  "#Hinv" ∷ is_globals_inv ∗
  "%Hused_vars_dom" ∷ (⌜ dom var_addrs = used_var_names ⌝) ∗
  "%Hvalid" ∷ ⌜ is_valid_package_name pkg_name ⌝ ∗
  "%Hold_unused" ∷ (⌜ ∀ var_name, g_old !! (encode_var_name pkg_name var_name) = None ⌝).
Program Definition own_unused_vars := unseal (_:seal (@own_unused_vars_def)). Obligation 1. by eexists. Qed.
Definition own_unused_vars_unseal : own_unused_vars = _ := seal_eq _.

Local Ltac unseal :=
  rewrite ?own_globals_tok_unseal
    ?is_global_addr_unseal
    ?is_initialized_unseal
    ?own_package_post_toks_unseal
    ?own_package_post_tok_unseal
    ?own_unused_vars_unseal.

Global Instance is_global_addr_persistent x a:
  Persistent (is_global_addr x a).
Proof. unseal. apply _. Qed.

Global Instance is_initialized_persistent a b:
  Persistent (is_initialized a b).
Proof. unseal. apply _. Qed.

Lemma own_package_post_toks_get (pkg_name : go_string) (used_pkgs : gset go_string) :
  pkg_name ∉ used_pkgs →
  own_package_post_toks used_pkgs ==∗
  own_package_post_tok pkg_name ∗
  own_package_post_toks ({[ pkg_name ]} ∪ used_pkgs).
Proof.
  unseal.
  iIntros (?) "Hpkg".
  iMod (ghost_map_insert with "Hpkg") as "[H H2]".
  { by rewrite lookup_gset_to_gmap_None. }
  iFrame.
  rewrite -gset_to_gmap_union_singleton.
  by iFrame.
Qed.

Lemma is_initialized_get_post pkg_name P :
  own_package_post_tok pkg_name -∗
  is_initialized pkg_name P ={⊤}=∗
  ▷ P.
Proof.
  unseal.
  iIntros "Htok #Hinv".
  iInv "Hinv" as "Hi" "Hclose".
  iDestruct "Hi" as "[>Hbad|$]".
  { iCombine "Hbad Htok" gives %Hbad. exfalso. naive_solver. }
  by iMod ("Hclose" with "[$Htok]").
Qed.

Lemma encode_var_name_inj pkg_name1 pkg_name2 var_name1 var_name2 :
  is_valid_package_name pkg_name1 →
  is_valid_package_name pkg_name2 →
  encode_var_name pkg_name1 var_name1 = encode_var_name pkg_name2 var_name2 →
  pkg_name1 = pkg_name2 ∧ var_name1 = var_name2.
Proof.
Admitted.

Lemma encode_var_name_package_name_ne pkg_name' pkg_name var_name :
  is_valid_package_name pkg_name' →
  pkg_name' ≠ encode_var_name pkg_name var_name.
Proof.
Admitted.

Lemma wp_globals_put var_id used_var_names (addr : loc) :
  var_id.2 ∉ used_var_names →
  {{{ own_unused_vars var_id.1 used_var_names }}}
    globals.put var_id #addr
  {{{ RET #();
      own_unused_vars var_id.1 ({[ var_id.2 ]} ∪ used_var_names) ∗
      is_global_addr var_id addr
  }}}.
Proof.
  iIntros (??) "Hu HΦ".
  wp_call_lc "Hlc".
  rewrite to_val_unseal.
  simpl.
  unseal.
  iNamed "Hu".
  unseal.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  iCombine "Hglobals Hglobals_i" gives %[_ <-].
  iCombine "Hglobals Hglobals_i" as "Hglobals".
  iApply (wp_GlobalPut with "[$]").
  iNext. iIntros "Hglobals".
  iMod (ghost_map_insert_persist var_id with "Haddrs") as "[Haddrs #Hptsto]".
  {
    subst.
    specialize (Hvars var_id.1 var_id.2 ltac:(assumption)).
    rewrite lookup_union lookup_kmap (not_elem_of_dom_1 var_addrs)
      //= left_id Hold_unused fmap_None in Hvars.
    by destruct var_id.
  }
  iDestruct "Hglobals" as "[Hglobals Hglobals_i]".
  iMod ("Hclose" with "[-HΦ Hglobals Hacc]") as "_".
  {
    iFrame "∗#%". iPureIntro.
    intros.
    destruct (decide ((pkg_name, var_name) = var_id)).
    {
      subst.
      rewrite !lookup_insert /=.
      rewrite to_val_unseal //.
    }
    {
      rewrite lookup_insert_ne //.
      rewrite lookup_insert_ne //.
      2:{
        intros Hbad.
        apply n.
        apply encode_var_name_inj in Hbad; try done.
        intuition; subst.
        by destruct var_id.
      }
      by apply Hvars.
    }
  }
  iApply "HΦ".
  rewrite insert_union_l -kmap_insert.
  iFrame "∗#%".
  iPureIntro.
  set_solver.
Qed.

Lemma wp_globals_get var_id (addr : loc) :
  {{{ is_global_addr var_id addr }}}
    globals.get var_id #()
  {{{ RET #addr; True }}}.
Proof.
  unseal.
  iIntros (?) "Hu HΦ".
  destruct var_id as [pkg_name var_name].
  iDestruct "Hu" as "(#Hinv & #Haddr & %Hvalid)".
  wp_call_lc "Hlc".
  wp_bind (GlobalGet _).
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  rewrite [in (GlobalGet _)]to_val_unseal.
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros.
  iCombine "Haddrs Haddr" gives %Hlookup.
  rewrite -Hvars // Hlookup.
  iMod ("Hclose" with "[-HΦ]").
  { iFrame "∗#%". }
  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_package_init pending postconds (pkg_name : go_string) (init_func : val) P Φ :
  is_valid_package_name pkg_name →
  postconds !! pkg_name = Some P →
  pkg_name ∉ pending →
  own_globals_tok pending postconds -∗
  (own_unused_vars pkg_name ∅ -∗
   (∀ vars, own_unused_vars pkg_name vars ==∗ own_globals_tok ({[ pkg_name ]} ∪ pending) postconds) -∗
   WP init_func #()
     {{ _, P ∗
           own_globals_tok ({[ pkg_name ]} ∪ pending) postconds
     }}
  ) -∗
  (is_initialized pkg_name P -∗ own_globals_tok pending postconds -∗ Φ #()) -∗
  WP (globals.package_init pkg_name init_func) {{ Φ }}.
Proof.
  unseal.
  intros Hvalid Hpost Hnot_pending.
  iIntros "Htok Hinit HΦ".
  wp_call.
  iNamed "Htok".
  wp_bind (GlobalGet _).
  rewrite [in GlobalGet _]to_val_unseal.
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "Hglobals".
  destruct (lookup pkg_name g) eqn:Hlookup; rewrite Hlookup.
  { (* don't bother running init *)
    wp_pures.
    pose proof (Hpkg pkg_name ltac:(done)) as Hpkg'.
    rewrite Hlookup /= in Hpkg'.
    destruct Hpkg' as [|Hpkg']; first done.
    destruct (pkg_initialized !! pkg_name) as [[]|] eqn:Hpkg_lookup; last naive_solver.
    inversion_clear Hpkg'.
    iDestruct (big_sepM_lookup with "Hinited") as "H".
    { done. }
    rewrite Hpost /=.
    wp_pures.
    iApply "HΦ".
    { iFrame "#". }
    iFrame "∗#%".
  }
  (* actually run init *)
  iMod (ghost_var_update (Some g) with "Hacc") as "[Hacc Hacc2]".
  wp_pures.
  wp_bind (init_func _).
  iSpecialize ("Hinit" with "[Hglobals Hacc2]").
  {
    iFrame "∗#%".
    iExists ∅.
    rewrite kmap_empty left_id.
    iFrame.
    iPureIntro.
    split; first done.
    specialize (Hpkg pkg_name ltac:(done)).
    destruct Hpkg as [|Hpkg]; first done.
    destruct (pkg_initialized !! pkg_name); first naive_solver.
    destruct Hpkg as [_ Hnone].
    done.
  }
  iSpecialize ("Hinit" with "[Hacc]").
  {
    iRename "Hacc" into "Hacc2".
    rename g into g_old.
    clear Hvalid. iClear "Hinv".
    iIntros (?). iNamed 1.
    iCombine "Hacc Hacc2" gives %[_ Heq].
    inversion_clear Heq.
    iCombine "Hacc Hacc2" as "Hacc".
    iMod (ghost_var_update None with "Hacc") as "Hacc".
    iModIntro.
    iFrame "∗#%".
    iPureIntro.
    intros pkg_name' Hvalid'.
    destruct (decide (pkg_name' ∈ {[pkg_name]} ∪ pending)).
    { by left. }
    right.
    specialize (Hpkg pkg_name' ltac:(done)).
    destruct Hpkg as [|Hpkg].
    { set_solver. }
    destruct (pkg_initialized !! pkg_name').
    {
      rewrite lookup_union_r // lookup_kmap_None.
      intros. exfalso.
      by eapply encode_var_name_package_name_ne.
    }
    {
      destruct Hpkg as [? Hpkg].
      split.
      { rewrite lookup_union_r // lookup_kmap_None.
        intros. exfalso.
        by eapply encode_var_name_package_name_ne. }
      {
        intros.
        rewrite lookup_union_r //.
        rewrite lookup_kmap_None.
        intros. exfalso. apply encode_var_name_inj in H0; try done.
        set_solver.
      }
    }
  }
  iApply (wp_wand with "Hinit").
  iIntros (?) "[HP Htok]".
  wp_pure_lc "Hlc".
  clear Hpkg. iClear "Hinv Hinited".
  iNamed "Htok".
  wp_pures.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  iCombine "Hglobals Hglobals_i" gives %[_ Heq]. subst.
  iCombine "Hglobals Hglobals_i" as "H".
  rewrite to_val_unseal.
  iApply (wp_GlobalPut with "[$]").
  iNext. iIntros "[Hglobals Hglobals_i]".
  iMod ("Hclose" with "[Hglobals_i Haddrs]").
  {
    iFrame "∗#%". iPureIntro.
    setoid_rewrite lookup_insert_ne.
    { done. }
    by apply encode_var_name_package_name_ne.
  }
  iMod (inv_alloc with "[HP]") as "#Hinit";
    last iSpecialize ("HΦ" with "Hinit").
  { iFrame. }
  iApply "HΦ".
  iDestruct (big_sepM_insert_2 _ _ pkg_name () with "[] Hinited") as "Hinited2".
  { simpl. rewrite Hpost. iFrame "#". }
  iFrame "∗#%".
  iPureIntro.
  intros pkg_name' ?.
  specialize (Hpkg pkg_name' ltac:(done)).
  destruct (decide (pkg_name' = pkg_name)).
  {
    subst. right.
    rewrite !lookup_insert to_val_unseal //.
  }
  destruct Hpkg as [|Hpkg].
  { set_solver. }
  right.
  rewrite lookup_insert_ne //.
  destruct (_ !! pkg_name').
  { rewrite lookup_insert_ne //. }
  rewrite lookup_insert_ne //.
  destruct Hpkg as [? ?].
  split; first done.
  setoid_rewrite lookup_insert_ne.
  { done. }
  by apply encode_var_name_package_name_ne.
Qed.

End definitions_and_lemmas.

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
  rewrite !lookup_empty //.
Qed.

End init.
