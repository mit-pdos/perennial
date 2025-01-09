From New.golang.theory Require Import exception mem typing.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii Equality.

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
  #[ghost_mapΣ (go_string * go_string) loc ; ghost_mapΣ go_string ();
    ghost_varΣ (option (gmap go_string val))].

Global Instance subG_goGlobalsG `{ffi_syntax} {Σ} : subG goGlobalsΣ Σ → goGlobals_preG Σ.
Proof. solve_inG. Qed.

Section definitions_and_lemmas.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

(* The only concurrent access to globals is to read the address of global
   variables, so that's the only thing this invariant is concerned with. *)
Local Definition own_globals_inv : iProp Σ :=
  ∃ g (addrs : gmap (go_string * go_string) loc),
  "Hglobals_i" ∷ own_globals (DfracOwn (1/2)) g ∗
  "Haddrs" ∷ ghost_map_auth go_globals_name 1%Qp addrs ∗
  "%Hvars" ∷ (⌜ # <$> kmap globals.encode_var addrs ⊆ g ⌝)
.

Local Definition is_globals_inv : iProp Σ :=
  inv nroot own_globals_inv.

(* This must be owned by the `init` thread. *)
Definition own_globals_tok_def (pending_packages : gset go_string)
  (pkg_postconds : gmap go_string (iProp Σ)): iProp Σ :=
  ∃ g (pkg_initialized : gmap go_string ()),
  "Hglobals" ∷ own_globals (DfracOwn (1/2)) g ∗
  "Hacc" ∷ ghost_var go_access_prev_state_name 1%Qp None ∗
  "%Hpkg" ∷ (⌜ ∀ pkg_name,
               pkg_name ∈ pending_packages ∨
                 (match pkg_initialized !! pkg_name with
                  | Some _ => g !! globals.encode_package pkg_name = Some #()%V
                  | None => g !! globals.encode_package pkg_name = None ∧
                           ∀ var_name, g !! (globals.encode_var (pkg_name, var_name)) = None
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

Definition is_global_addr_def (pkg_var_name : go_string * go_string) (addr : loc) : iProp Σ :=
  is_globals_inv ∗ pkg_var_name ↪[go_globals_name]□ addr.
Program Definition is_global_addr := unseal (_:seal (@is_global_addr_def)). Obligation 1. by eexists. Qed.
Definition is_global_addr_unseal : is_global_addr = _ := seal_eq _.

Definition own_unused_vars_def (pkg_name : go_string) (used_pkg_vars : gset (go_string * go_string)) :
  iProp Σ :=
  ∃ g_old var_addrs,
  "Hglobals" ∷ own_globals (DfracOwn (1/2)) ((kmap globals.encode_var var_addrs) ∪ g_old) ∗
  "Hacc" ∷ ghost_var go_access_prev_state_name (1/2)%Qp (Some g_old) ∗
  "#Hinv" ∷ is_globals_inv ∗
  "%Hused_vars_dom" ∷ (⌜ dom var_addrs = used_pkg_vars ⌝) ∗
  "%Hused_pkg" ∷ (⌜ ∀ pkg_var_name, pkg_var_name ∈ used_pkg_vars → pkg_var_name.1 = pkg_name ⌝) ∗
  "%Hold_unused" ∷ (⌜ ∀ var_name, g_old !! (globals.encode_var (pkg_name, var_name)) = None ⌝).
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

Lemma hex_encode_length (w : w8) :
  length (globals.hex_encode_w8 w) = 2%nat.
Proof.
  rewrite -(ByteString.w8_to_byte_to_w8 w).
  generalize (w8_to_byte w). clear.
  by intros [].
Qed.

Local Definition hex := ["00";"01";"02";"03";"04";"05";"06";"07";"08";"09";"0a";"0b";"0c";"0d";"0e";"0f";"10";"11";"12";"13";"14";"15";"16";"17";"18";"19";"1a";"1b";"1c";"1d";"1e";"1f";"20";"21";"22";"23";"24";"25";"26";"27";"28";"29";"2a";"2b";"2c";"2d";"2e";"2f";"30";"31";"32";"33";"34";"35";"36";"37";"38";"39";"3a";"3b";"3c";"3d";"3e";"3f";"40";"41";"42";"43";"44";"45";"46";"47";"48";"49";"4a";"4b";"4c";"4d";"4e";"4f";"50";"51";"52";"53";"54";"55";"56";"57";"58";"59";"5a";"5b";"5c";"5d";"5e";"5f";"60";"61";"62";"63";"64";"65";"66";"67";"68";"69";"6a";"6b";"6c";"6d";"6e";"6f";"70";"71";"72";"73";"74";"75";"76";"77";"78";"79";"7a";"7b";"7c";"7d";"7e";"7f";"80";"81";"82";"83";"84";"85";"86";"87";"88";"89";"8a";"8b";"8c";"8d";"8e";"8f";"90";"91";"92";"93";"94";"95";"96";"97";"98";"99";"9a";"9b";"9c";"9d";"9e";"9f";"a0";"a1";"a2";"a3";"a4";"a5";"a6";"a7";"a8";"a9";"aa";"ab";"ac";"ad";"ae";"af";"b0";"b1";"b2";"b3";"b4";"b5";"b6";"b7";"b8";"b9";"ba";"bb";"bc";"bd";"be";"bf";"c0";"c1";"c2";"c3";"c4";"c5";"c6";"c7";"c8";"c9";"ca";"cb";"cc";"cd";"ce";"cf";"d0";"d1";"d2";"d3";"d4";"d5";"d6";"d7";"d8";"d9";"da";"db";"dc";"dd";"de";"df";"e0";"e1";"e2";"e3";"e4";"e5";"e6";"e7";"e8";"e9";"ea";"eb";"ec";"ed";"ee";"ef";"f0";"f1";"f2";"f3";"f4";"f5";"f6";"f7";"f8";"f9";"fa";"fb";"fc";"fd";"fe";"ff"]%go.
Local Lemma hex_NoDup_helper : hex = remove_dups hex.
Proof. reflexivity. Qed.
Local Lemma hex_NoDup : NoDup hex.
Proof. rewrite hex_NoDup_helper. apply NoDup_remove_dups. Qed.
Local Definition hex_encode_w8' (x : w8) := default "00"%go (hex !! uint.nat x).
Local Lemma hex_encode_eq (x : w8) : hex_encode_w8' x = globals.hex_encode_w8 x.
Proof.
  rewrite -(ByteString.w8_to_byte_to_w8 x).
  generalize (w8_to_byte x) as x'. clear. by intros [].
Qed.
Local Lemma hex_lookup (x : w8) :
  ∃ y, hex !! (uint.nat x) = Some y.
Proof.
  destruct (hex !! _) eqn:Hbad.
  { by eexists. }
  exfalso.
  rewrite lookup_ge_None /= in Hbad.
  word.
Qed.

Delimit Scope byte_char_scope with go_byte.

Local Definition hex_chars :=
  ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"; "a"; "b"; "c"; "d"; "e"; "f" ]%go_byte.

Lemma hex_encode_subseteq x : (globals.hex_encode x ⊆ hex_chars).
Proof.
  induction x.
  { set_solver. }
  simpl.
  rewrite -hex_encode_eq.
  rewrite list_subseteq_app_iff_l.
  split; try done.
  rewrite -(ByteString.w8_to_byte_to_w8 a).
  generalize (w8_to_byte a) as x'. clear.
  intros [].
  1-50: set_solver.
  1-50: set_solver.
  1-50: set_solver.
  1-50: set_solver.
  1-50: set_solver.
  all: set_solver.
Qed.

Instance hex_encode_w8_inj : Inj (=) (=) globals.hex_encode_w8.
Proof.
  hnf. intros x y.
  rewrite -!hex_encode_eq.
  intros Heq.
  rewrite /hex_encode_w8' in Heq.
  pose proof (hex_lookup x) as [? Hl1].
  pose proof (hex_lookup y) as [? Hl2].
  rewrite Hl1 Hl2 /= in Heq. subst.
  apply word.unsigned_inj.
  apply Z2Nat.inj; try word.
  eapply NoDup_lookup; try done.
  apply hex_NoDup.
Qed.

Lemma hex_encode_w8_length x : length (globals.hex_encode_w8 x) = 2.
Proof.
  rewrite -(ByteString.w8_to_byte_to_w8 x).
  generalize (w8_to_byte x) as x'. clear. by intros [].
Qed.

Instance hex_encode_inj : Inj (=) (=) globals.hex_encode.
Proof.
  hnf. intros.
  move x after y.
  dependent induction x generalizing y.
  { destruct y; first done.
    exfalso. apply (f_equal length) in H.
    rewrite /= length_app hex_encode_length in H. lia.
  }
  destruct y.
  { exfalso. apply (f_equal length) in H.
    rewrite /= length_app hex_encode_length in H. lia. }
  simpl in H.
  apply app_inj_1 in H.
  2:{ rewrite !hex_encode_w8_length //. }
  intuition.
  f_equal.
  - by apply hex_encode_w8_inj.
  - by apply IHx.
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
  change (" "%go) with ([" "%go_byte]) in Heq.
  rewrite -!cons_middle in Heq.
  apply app_inj_pivot in Heq as [Hbad|Heq].
  {
    exfalso.
    rewrite -!elem_of_list_In in Hbad.
    pose proof (hex_encode_subseteq pkg_name.1).
    pose proof (hex_encode_subseteq pkg_name.2).
    set_solver.
  }
  intuition.
  repeat match goal with
  | [ H : context [globals.hex_encode] |- _] => apply (hex_encode_inj) in H
  end. destruct pkg_name, pkg_name'.
  simpl in *. subst. done.
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
