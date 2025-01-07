From New.golang.theory Require Import exception mem typing hex.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii Equality.

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
    #[global] go_postcond_tok_inG :: ghost_mapG Σ go_string () ;
  }.

Class goGlobalsGS `{ffi_syntax} Σ : Set :=
  GoGlobalsGS {
      #[global] go_globals_pre_inG :: goGlobals_preG Σ ;
      go_globals_name : gname ;
      go_package_postcond_tok_name : gname ;
      (* go_access_prev_state_name : gname ; *)
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

(* This must be owned by the `init` thread. *)
Definition own_globals_tok_def (pending_packages : gset go_string)
  (pkg_postconds : gmap go_string (iProp Σ)): iProp Σ :=
  ∃ g (pkg_initialized : gmap go_string ()),
  "Hglobals" ∷ own_globals g ∗
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

End definitions_and_lemmas.

Section context.
Context {PROP:bi}.
Class BiContextRoot := { is_bi_context : PROP ; bi_context_pers :: Persistent is_bi_context }.
Class BiContext `{BiContextRoot} (P : PROP) :=
  {
    contains : □ is_bi_context ⊢ P
  }.
End context.

Class WpGlobalsGet
  `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  `{!BiContextRoot} (pkg_var_name : go_string * go_string) (addr : loc)
  :=
  wp_globals_get : ⊢@{iProp Σ}
                      ∀ Φ, is_bi_context -∗ (▷ Φ #addr) -∗
                           WP (globals.get pkg_var_name #()) {{ Φ }}
.

Class IsDefined :=
  {
    h : list (string * (list (string * loc))) ;
  }.

(* Definition is_defined `{IsDefined} : iProp Σ :=
  is_global pkg_name #globalA *)

Module bar.
Section bar.
Class GlobalAddrs :=
  {
    globalX: loc;
  }.

(* XXX: defined in a different module. *)
Definition globalX'name := ("bar", "globalX")%go.

Context {addrs : GlobalAddrs}.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.
Context `{!BiContextRoot (PROP:=iProp Σ)}.
Definition is_defined : iProp Σ :=
  is_global "bar"%go #globalX.
Context {His_defined : BiContext is_defined}.

Instance wp_global_get_globalX : WpGlobalsGet globalX'name globalX.
Proof.
  rewrite /WpGlobalsGet.
  iIntros (?) "#Hdef HΦ".
  iDestruct (His_defined.(contains) with "[$]") as "#H".
Admitted.
End bar.
End bar.

Module foo.
Section defs.
Class GlobalAddrs :=
  {
    globalA: loc;
    globalB: loc;
    to_bar' : bar.GlobalAddrs
  }.
Existing Instance to_bar'.

Context {addrs : GlobalAddrs}.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.
Definition is_defined : iProp Σ :=
  is_global "foo"%go #globalA.

Definition globalA'name := ("foo", "globalA")%go.

Context `{!BiContextRoot (PROP:=iProp Σ)}.
Context {Hbar_def : BiContext (bar.is_defined)}.
Context {Hdef : BiContext (is_defined)}.

Existing Instance bar.wp_global_get_globalX.

Lemma bar :
  {{{ is_bi_context }}}
    globals.get bar.globalX'name #()
  {{{ RET #bar.globalX; True }}}.
Proof.
  iIntros (?) "#Hctx HΦ".
  wp_apply (wp_globals_get with "[$]").
  by iApply "HΦ".
Qed.

Instance wp_global_get_globalA : WpGlobalsGet globalA'name globalA.
Proof.
  rewrite /WpGlobalsGet.
  iIntros (?) "#Hdef HΦ".
Admitted.

Context `{IrisContextRoot}.
Context `{!IrisContext (bar.is_defined)}.
Context `{!IrisContext (is_defined)}.

Ltac iContext := (iStopProof; apply contains).


About globals.get.
Lemma foo :
  {{{ is_defined }}}
    globals.get globalA'name #()
  {{{ RET #globalA; True }}}.
Proof.
  iIntros (?) "#Hpre HΦ".
  wp_apply (wp_globals_get); first iFrame "#".
  by iApply "HΦ".
Qed.
Instance wp_global_get_globalA.

Instance wp_global_get_globalB.

Definition foo.is_defined

globals_contains Γ (pkg_name : string) (record_type : )

Definition is_global_vars_inv : iProp Σ :=
.

Definition is_global_addr_def (pkg_var_name : go_string * go_string) (addr : loc) : iProp Σ :=
  is_globals_inv ∗ pkg_var_name ↪[go_globals_name]□ addr.
Program Definition is_global_addr := unseal (_:seal (@is_global_addr_def)). Obligation 1. by eexists. Qed.
Definition is_global_addr_unseal : is_global_addr = _ := seal_eq _.

Local Ltac unseal :=
  rewrite ?own_globals_tok_unseal
    ?is_global_addr_unseal
    ?is_initialized_unseal
    ?own_package_post_toks_unseal
    ?own_package_post_tok_unseal.

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

Lemma encode_package_inj pkg_name1 pkg_name2 :
  globals.encode_package pkg_name1 = globals.encode_package pkg_name2 →
  pkg_name1 = pkg_name2.
Proof.
  intros Heq.
  apply app_inv_head in Heq.
  by apply hex_encode_inj.
Qed.

Local Instance encode_var_inj : Inj (=) (=) globals.encode_var.
Proof.
  intros pkg_name pkg_name' Heq.
  apply app_inv_head in Heq.
  apply hex_encode_app_inj in Heq. destruct pkg_name, pkg_name'.
  simpl in Heq. intuition. by subst.
Qed.

Lemma encode_var_name_package_name_ne pkg_name pkg_var_name :
  globals.encode_package pkg_name ≠ globals.encode_var pkg_var_name.
Proof. done. Qed.

Lemma wp_globals_put pkg_var_name used_pkg_vars (addr : loc) :
  pkg_var_name ∉ used_pkg_vars →
  {{{ own_unused_vars pkg_var_name.1 used_pkg_vars }}}
    globals.put pkg_var_name #addr
  {{{ RET #();
      own_unused_vars pkg_var_name.1 ({[ pkg_var_name ]} ∪ used_pkg_vars) ∗
      is_global_addr pkg_var_name addr
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
  iCombine "Hglobals Hglobals_i" gives %[_ Heq]. subst.
  iCombine "Hglobals Hglobals_i" as "Hglobals".
  iApply (wp_GlobalPut with "[$]").
  iNext. iIntros "Hglobals".
  iMod (ghost_map_insert_persist pkg_var_name addr with "Haddrs")
    as "[Haddrs #Hptsto]".
  {
    eapply lookup_weaken_None in Hvars.
    { rewrite lookup_fmap fmap_None // in Hvars.
      erewrite lookup_kmap in Hvars.
      - done.
      - apply _.
    }
    rewrite lookup_union lookup_kmap Hold_unused.
    rewrite (not_elem_of_dom_1 var_addrs) //.
  }
  iDestruct "Hglobals" as "[Hglobals Hglobals_i]".
  iMod ("Hclose" with "[-HΦ Hglobals Hacc]") as "_".
  {
    iFrame "∗#%". iPureIntro.
    rewrite kmap_insert fmap_insert [in #addr]to_val_unseal /=.
    by apply insert_mono.
  }
  iApply "HΦ".
  rewrite insert_union_l -kmap_insert.
  iFrame "∗#%".
  iPureIntro.
  set_solver.
Qed.

Lemma wp_globals_get pkg_var_name (addr : loc) :
  {{{ is_global_addr pkg_var_name addr }}}
    globals.get pkg_var_name #()
  {{{ RET #addr; True }}}.
Proof.
  unseal.
  iIntros (?) "Hu HΦ".
  iDestruct "Hu" as "(#Hinv & #Haddr)".
  wp_call_lc "Hlc".
  wp_bind (GlobalGet _).
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  rewrite [in (GlobalGet _)]to_val_unseal.
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros.
  iCombine "Haddrs Haddr" gives %Hlookup.
  erewrite lookup_weaken; try eassumption.
  2:{ rewrite lookup_fmap lookup_kmap Hlookup //. }
  iMod ("Hclose" with "[-HΦ]").
  { iFrame "∗#%". }
  iModIntro. wp_pures. by iApply "HΦ".
Qed.

Lemma wp_package_init pending postconds (pkg_name : go_string) (init_func : val) P Φ :
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
  intros Hpost Hnot_pending.
  iIntros "Htok Hinit HΦ".
  wp_call.
  iNamed "Htok".
  wp_bind (GlobalGet _).
  rewrite [in GlobalGet _]to_val_unseal.
  iApply (wp_GlobalGet with "[$]").
  iNext. iIntros "Hglobals".
  destruct (lookup (globals.encode_package pkg_name) g) eqn:Hlookup; rewrite Hlookup.
  { (* don't bother running init *)
    wp_pures.
    pose proof (Hpkg pkg_name) as Hpkg'.
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
    specialize (Hpkg pkg_name).
    destruct Hpkg as [|Hpkg]; first done.
    destruct (pkg_initialized !! pkg_name); first naive_solver.
    destruct Hpkg as [_ Hnone].
    done.
  }
  iSpecialize ("Hinit" with "[Hacc]").
  {
    iRename "Hacc" into "Hacc2".
    rename g into g_old.
    iClear "Hinv".
    iIntros (?). iNamed 1.
    iCombine "Hacc Hacc2" gives %[_ [=Heq]].
    subst.
    iCombine "Hacc Hacc2" as "Hacc".
    iMod (ghost_var_update None with "Hacc") as "Hacc".
    iModIntro.
    iFrame "∗#%".
    iPureIntro.
    intros pkg_name'.
    destruct (decide (pkg_name' ∈ {[pkg_name]} ∪ pending)).
    { by left. }
    right.
    specialize (Hpkg pkg_name').
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
        rewrite lookup_kmap.
        rewrite -not_elem_of_dom.
        intros Hin.
        specialize (Hused_pkg (pkg_name', var_name) ltac:(done)).
        subst. set_solver.
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
    apply insert_subseteq_r; try done.
    rewrite lookup_fmap fmap_None lookup_kmap_None.
    intros. exfalso. by eapply encode_var_name_package_name_ne.
  }
  iMod (inv_alloc with "[HP]") as "#Hinit";
    last iSpecialize ("HΦ" with "Hinit").
  { iFrame. }
  iApply "HΦ".
  iDestruct (big_sepM_insert_2 _ _ pkg_name () with "[] Hinited") as "Hinited2".
  { simpl. rewrite Hpost. iFrame "#". }
  iFrame "∗#%".
  iPureIntro.
  intros pkg_name'.
  specialize (Hpkg pkg_name').
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
  { rewrite lookup_insert_ne //. intros H. eapply encode_package_inj in H. done. }
  rewrite lookup_insert_ne //.
  2:{ intros H. eapply encode_package_inj in H. done. }
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
  rewrite kmap_empty fmap_empty //.
Qed.

End init.
