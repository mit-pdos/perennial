From New.golang.theory Require Import exception mem typing.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.

From Coq Require Import Ascii.

Class goGlobals_preG (Σ: gFunctors) : Set :=
  {
    #[global] go_globals_inG :: ghost_mapG Σ string loc ;
    #[global] go_package_gname_inG :: ghost_mapG Σ string gname ;
  }.

Class goGlobalsGS Σ : Set :=
  GoGlobalsGS {
      #[global] go_globals_pre_inG :: goGlobals_preG Σ ;
      go_globals_name : gname ;
      go_package_gname_name : gname ;
    }.

Section definitions.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Definition is_global_addr_def (pkg_name var_name : string) (addr : loc) : iProp Σ :=
  ∃ γpkg,
  pkg_name ↪[go_package_gname_name]□ γpkg ∗
  var_name ↪[γpkg]□ addr.

Definition own_unused_packages_def (used_package_names : gset string) : iProp Σ :=
  ∃ m,
    ghost_map_auth go_package_gname_name 1%Qp m ∗
    ⌜ dom m = used_package_names ⌝.

Definition own_unused_vars_def (pkg_name : string) (used_var_names : gset string) : iProp Σ :=
  ∃ γpkg (m : gmap string loc),
  "#Hγpkg" ∷ pkg_name ↪[go_package_gname_name]□ γpkg ∗
  "Hpkg_auth" ∷ ghost_map_auth γpkg (1/2)%Qp m ∗
  "%Hused_vars_dom" ∷ ⌜ dom m = used_var_names ⌝.

Local Definition encode_var_name (pkg_name var_name : string) : string :=
  pkg_name +:+ " " +:+ var_name.

Local Definition is_valid_package_name (pkg_name : string) : Prop :=
  " "%char ∉ (String.list_ascii_of_string pkg_name).

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

Definition own_globals_inv : iProp Σ :=
  ∃ g (package_gnames : gmap string gname),
  "Hglobals" ∷ own_globals (DfracOwn 1) g ∗
  "Hpkg_gnames" ∷ ghost_map_auth go_package_gname_name 1%Qp package_gnames ∗
  "Hglobal_addrs" ∷ ([∗ map] pkg_name ↦ γpkg ∈ package_gnames,
                       ∃ (addrs : gmap string loc),
                         ghost_map_auth γpkg (1/2)%Qp addrs ∗
                         ⌜ is_valid_package_name pkg_name ⌝ ∗
                         ⌜ ∀ var_name,
                            match (addrs !! var_name) with
                            | None => g !! (encode_var_name pkg_name var_name) = None
                            | Some addr => g !! (encode_var_name pkg_name var_name) = Some #addr
                            end ⌝

    ) ∗
  "%Hpackage_ids" ∷ ⌜ ∀ pkg_name, is_valid_package_name pkg_name →
                                    match package_gnames !! pkg_name with
                                    | None =>
                                        g !! pkg_name = None ∧
                                        (∀ var_name, g !! (encode_var_name pkg_name var_name) = None)
                                    | Some _ => g !! pkg_name = Some #()%V
                                    end ⌝
.

Definition is_globals_inv : iProp Σ :=
  inv nroot own_globals_inv.

Lemma wp_globals_put pkg_name var_name used_var_names (addr : loc) :
  var_name ∉ used_var_names →
  is_valid_package_name pkg_name →
  {{{ is_globals_inv ∗ own_unused_vars_def pkg_name used_var_names }}}
    globals.put #(encode_var_name pkg_name var_name) #addr
  {{{ RET #();
      own_unused_vars_def pkg_name ({[ var_name ]} ∪ used_var_names) ∗
      is_global_addr_def pkg_name var_name addr
  }}}.
Proof.
  iIntros (???) "Hpre HΦ".
  iDestruct "Hpre" as "[#Hinv Hu]".
  unfold globals.put.
  wp_call_lc "Hlc".
  rewrite to_val_unseal.
  simpl.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  iNamed "Hu".
  iCombine "Hγpkg Hpkg_gnames" gives %Hlookup.
  iDestruct (big_sepM_delete with "Hglobal_addrs") as "[Hauth2 Hglobal_addrs]".
  { done. }
  iDestruct "Hauth2" as (?) "[Hauth2 %Hg]".
  iDestruct (ghost_map_auth_agree with "Hpkg_auth Hauth2") as %Heq. subst.
  iCombine "Hpkg_auth Hauth2" as "Hpkg_auth".
  iApply (wp_GlobalPut with "[$]").
  iNext.
  iIntros "Hglobals".
  iMod (ghost_map_insert var_name addr with "Hpkg_auth") as "[Hpkg_auth Hptsto]".
  { by apply not_elem_of_dom. }
  iMod (ghost_map_elem_persist with "Hptsto") as "#?".
  iDestruct "Hpkg_auth" as "[Hpkg_auth Hpkg_auth2]".
  iMod ("Hclose" with "[-HΦ Hpkg_auth2]").
  {
    iNext. repeat iExists _.
    iFrame.
    iSplitL.
    {
      iApply (big_sepM_delete _ _ pkg_name).
      { done. }
      iSplitL "Hpkg_auth".
      - iExists _; iFrame.
        iPureIntro.
        destruct Hg as [Hvalid Hg].
        split; first done.
        intros var_name'.
        destruct (decide (var_name' = var_name)) as [|Hneq].
        + subst. rewrite !lookup_insert to_val_unseal //.
        + rewrite lookup_insert_ne //.
          rewrite lookup_insert_ne //.
          2:{ intros Hbad.
              apply Hneq.
              apply String.app_inj in Hbad.
              by apply String.app_inj in Hbad.
          }
          apply Hg.
      - iApply (big_sepM_impl with "[$]").
        iIntros "!# %pkg_name' %γpkg' %Hlookup' H".
        clear Hg.
        iDestruct "H" as (?) "[$ %Hg]".
        iPureIntro.
        destruct Hg as [Hvalid Hg].
        split; first done.
        intros ?.
        rewrite -> lookup_insert_ne.
        2:{
          intros Hbad.
          apply encode_var_name_inj in Hbad as [-> ->]; try assumption.
          rewrite lookup_delete_Some in Hlookup'. naive_solver.
        }
        apply Hg.
    }
    iPureIntro.
    intros pkg_name' Hvalid.
    rewrite [in <[_ := _]> g !! pkg_name']lookup_insert_ne.
    2:{ intros Hbad.
        subst. by eapply encode_var_name_package_name_ne. }
    specialize (Hpackage_ids pkg_name' Hvalid).
    destruct (package_gnames !! pkg_name') eqn:Hlookup'; try done.
    split; first naive_solver.
    intros.
    rewrite lookup_insert_ne.
    2:{
      intros Hbad.
      apply encode_var_name_inj in Hbad as [-> ->]; try assumption.
      naive_solver.
    }
    naive_solver.
  }
  iApply "HΦ".
  iFrame "∗#%".
  iPureIntro.
  by rewrite dom_insert_L.
Qed.

Lemma wp_globals_get pkg_name var_name (addr : loc) :
  is_valid_package_name pkg_name →
  {{{ is_globals_inv ∗ is_global_addr_def pkg_name var_name addr }}}
    globals.get #(encode_var_name pkg_name var_name)
  {{{ RET #addr; True }}}.
Proof.
  iIntros (??) "Hpre HΦ".
  iDestruct "Hpre" as "[#Hinv Hu]".
  unfold globals.put.
  wp_call_lc "Hlc".
  rewrite to_val_unseal.
  simpl.
  wp_bind (GlobalGet _).
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
  iDestruct "Hu" as (?) "[#Hpkg #Hvar]".
  iCombine "Hpkg Hpkg_gnames" gives %Hlookup.
  iApply (wp_GlobalGet with "[$]").
  iIntros "!> Hglobals".
  iDestruct (big_sepM_lookup_acc with "Hglobal_addrs") as "[H Hglobal_addrs]".
  { done. }
  iDestruct "H" as (?) "(Hpkg_auth & %Hvalid & %Hg)".
  iCombine "Hpkg_auth Hvar" gives %Haddrs.
  pose proof (Hg var_name) as Hvar. rewrite Haddrs /= in Hvar.
  iSpecialize ("Hglobal_addrs" with "[Hpkg_auth]").
  { iFrame "∗#%". }
  iMod ("Hclose" with "[-HΦ]").
  { iExists _; iFrame "∗#%". }
  iModIntro.
  rewrite Hvar.
  wp_pures.
  rewrite to_val_unseal.
  by iApply "HΦ".
Qed.

End definitions.
