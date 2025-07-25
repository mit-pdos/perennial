From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.tuple Require Import res.

(* FIXME: ugly proofs; clean this up *)

(* spec_find_ver_step *)
Definition find_version_forward_step (ts : nat) (res : option dbpver) (ver : dbpver) :=
  match res with
  | Some _ => res
  | None => if decide (uint.Z ver.1 ≤ ts) then Some ver else None
  end.

(* spec_find_ver_reverse *)
Definition find_version_forward (vers : list dbpver) (ts : nat) :=
  foldl (find_version_forward_step ts) None vers.

(* spec_find_ver *)
Definition find_version (vers : list dbpver) (ts : nat) :=
  find_version_forward (reverse vers) ts.

(* spec_lookup *)
Definition lookup_with_versions (vers : list dbpver) (ts : nat) :=
  match find_version vers ts with
  | Some ver => ver.2
  | None => None
  end.

(* spec_find_ver_step_Some_noop *)
Lemma foldl_find_version_forward_step_Some vers ts ver :
  foldl (find_version_forward_step ts) (Some ver) vers = Some ver.
Proof. by induction vers. Qed.

(* spec_find_ver_lt_Some *)
Lemma find_version_le_is_Some vers (ts : nat) ver :
  ver ∈ vers ->
  uint.Z ver.1 ≤ ts ->
  is_Some (find_version vers ts).
Proof.
  intros Hin Hlt.
  apply elem_of_reverse, list_elem_of_lookup_1 in Hin as [idx Hlookup].
  rewrite /find_version /find_version_forward.
  rewrite -(take_drop_middle _ _ _ Hlookup) foldl_app.
  destruct (foldl _ None _) as [ver' |].
  - exists ver'.
    by rewrite foldl_find_version_forward_step_Some.
  - exists ver.
    simpl.
    case_decide; last word.
    by rewrite foldl_find_version_forward_step_Some.
Qed.

(* spec_find_ver_reverse_match *)
Lemma find_version_forward_match vers tid :
  ∀ vers_take vers_drop ver,
    vers_take ++ ver :: vers_drop = vers ->
    find_version_forward vers_take tid = None ->
    uint.Z ver.1 ≤ uint.Z tid ->
    find_version_forward vers tid = Some ver.
Proof.
  intros vers_take vers_drop ver Hvers Htake Hver.
  rewrite -Hvers.
  unfold find_version_forward in *.
  rewrite foldl_app.
  rewrite Htake.
  simpl.
  case_decide.
  - induction vers_drop.
    + done.
    + by rewrite foldl_find_version_forward_step_Some.
  - word.
Qed.

(* spec_find_ver_reverse_not_match *)
Lemma find_version_forward_not_match vers tid :
  ∀ vers_take ver,
    vers_take ++ [ver] = vers ->
    find_version_forward vers_take tid = None ->
    tid < uint.Z ver.1 ->
    find_version_forward vers tid = None.
Proof.
  intros vers_take ver Hvers Htake Hver.
  unfold find_version_forward in *.
  rewrite -Hvers foldl_app Htake /=.
  case_decide; [lia | done].
Qed.

(* spec_find_ver_extensible *)
Lemma find_version_extensible vers (tidlast tid1 tid2 : nat) :
  (tidlast ≤ tid1)%nat ->
  (tidlast ≤ tid2)%nat ->
  Forall (λ ver, (uint.nat ver.1 ≤ tidlast)%nat) vers ->
  find_version vers tid1 = find_version vers tid2.
Proof.
  intros Htid1 Htid2 Hlast.
  rewrite /find_version /find_version_forward.
  destruct (reverse _) as [| ver versl] eqn:Hversl; first done.
  rewrite Forall_forall in Hlast.
  assert (Hin : ver ∈ vers).
  { apply elem_of_reverse. rewrite Hversl. apply list_elem_of_here. }
  simpl.
  specialize (Hlast _ Hin).
  do 2 (case_decide; last word).
  by do 2 rewrite foldl_find_version_forward_step_Some.
Qed.

(* spec_lookup_snoc_l *)
Lemma lookup_with_versions_snoc_l vers ver (tid tidx : nat) :
  uint.Z ver.1 = tidx ->
  tid < tidx ->
  lookup_with_versions (vers ++ [ver]) tid = lookup_with_versions vers tid.
Proof.
  intros Heq Hle.
  unfold lookup_with_versions, find_version, find_version_forward.
  rewrite reverse_snoc.
  simpl.
  case_decide; last done.
  rewrite Heq in H. lia.
Qed.

(* spec_lookup_snoc_r *)
Lemma lookup_with_versions_snoc_r vers ver (tid tidx : nat) :
  uint.Z ver.1 = tidx ->
  tidx ≤ tid ->
  lookup_with_versions (vers ++ [ver]) tid = ver.2.
Proof.
  intros Heq Hle.
  unfold lookup_with_versions, find_version, find_version_forward.
  rewrite reverse_snoc.
  simpl.
  case_decide.
  - by rewrite foldl_find_version_forward_step_Some.
  - rewrite Heq in H. word.
Qed.

(* spec_lookup_extensible *)
Lemma lookup_with_versions_extensible vers (tidlast tid1 tid2 : nat) :
  (tidlast ≤ tid1)%nat ->
  (tidlast ≤ tid2)%nat ->
  Forall (λ ver, (uint.nat ver.1 ≤ tidlast)%nat) vers ->
  lookup_with_versions vers tid1 = lookup_with_versions vers tid2.
Proof.
  intros Htid1 Htid2 Hlast.
  unfold lookup_with_versions.
  by rewrite (find_version_extensible _ _ _ _ Htid1 Htid2); last done.
Qed.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  (*@ type Tuple struct {                                                     @*)
  (*@     // Mutex protecting the fields below.                               @*)
  (*@     mu     *sync.Mutex                                                  @*)
  (*@     // Timestamp of fast-read optimization. Currently not used.         @*)
  (*@     tssafe uint64                                                       @*)
  (*@     // List of versions.                                                @*)
  (*@     vers   []tulip.Version                                              @*)
  (*@ }                                                                       @*)
  Definition own_tuple tuple key γ α : iProp Σ :=
    ∃ (tssafe : u64) (versS : Slice.t) (vers : list dbpver) (verlast : dbpver) (hist : dbhist),
      "HtssafeP"   ∷ tuple ↦[Tuple :: "tssafe"] #tssafe ∗
      "HversP"     ∷ tuple ↦[Tuple :: "vers"] (to_val versS) ∗
      "Hvers"      ∷ own_slice versS (struct.t Version) (DfracOwn 1) vers ∗
      "Hphys"      ∷ own_phys_hist_half α key hist ∗
      "#Hrepl"     ∷ is_repl_hist_lb γ key hist ∗
      "%Habs"      ∷ ⌜(∀ t, (t < length hist)%nat -> hist !! t = Some (lookup_with_versions vers t))⌝ ∗
      "%Hverlast"  ∷ ⌜last vers = Some verlast⌝ ∗
      "%Hlenhist"  ∷ ⌜length hist = S (uint.nat verlast.1)⌝ ∗
      "%Hlelast"   ∷ ⌜Forall (λ v, (uint.nat v.1 ≤ uint.nat verlast.1)%nat) vers⌝ ∗
      "%Hfirst"    ∷ ⌜vers !! O = Some (W64 0, None)⌝ ∗
      "%Hlasthist" ∷ ⌜last hist = Some verlast.2⌝.

  Definition is_tuple tuple key γ α : iProp Σ :=
    ∃ (muP : loc),
      "#Hmu"   ∷ readonly (tuple ↦[Tuple :: "mu"] #muP) ∗
      "#Hlock" ∷ is_lock tulipNS #muP (own_tuple tuple key γ α).

  Theorem wp_Tuple__AppendVersion (tuple : loc) (tsW : u64) (value : byte_string) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [Some value] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple key γ α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__AppendVersion #tuple #tsW #(LitString value)
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
    iIntros (ts hist' Hts) "#Hlb #Htpl".
    iIntros (Φ) "!> HphysX HΦ".
    wp_rec.

    (*@ func (tuple *Tuple) AppendVersion(ts uint64, value string) {            @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Htpl]".

    (*@     // Create a new version and add it to the version chain.            @*)
    (*@     ver := tulip.Version{                                               @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Value : tulip.Value{                                            @*)
    (*@             Present : true,                                             @*)
    (*@             Content : value,                                            @*)
    (*@         },                                                              @*)
    (*@     }                                                                   @*)
    (*@     tuple.vers = append(tuple.vers, ver)                                @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    iDestruct (phys_hist_agree with "HphysX Hphys") as %->.
    iApply fupd_wp.
    iMod (phys_hist_update hist' with "HphysX Hphys") as "[HphysX Hphys]".
    iModIntro.
    wp_loadField.
    (* somehow wp_SliceAppend doesn't work. *)
    wp_apply (wp_SliceAppend' with "Hvers").
    { done. }
    { by auto 10. }
    iIntros (versS') "Hvers".
    iAssert (own_slice versS' (struct.t Version) (DfracOwn 1) (vers ++ [(tsW, Some value)]))%I
      with "[Hvers]" as "Hvers".
    { by rewrite /own_slice {2}/list.untype fmap_app. }
    wp_storeField.

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HphysX]").
    { iFrame "Hlock Hlocked ∗ #".
      iModIntro.
      iExists (tsW, Some value).
      iPureIntro.
      assert (Hnnil : hist ≠ []).
      { by intros ->. }
      split.
      { intros t Ht.
        destruct (decide (t < ts)%nat) as [Hprevrext | Hwext].
        { (* Case: previous + read-extension *)
          rewrite (lookup_with_versions_snoc_l _ _ _ ts); last first.
          { clear -Hprevrext. lia. }
          { simpl. lia. }
          rewrite lookup_app_l; last first.
          { rewrite last_extend_length; last apply Hnnil.
            clear -Hprevrext Hts. lia.
          }
          destruct (decide (t < length hist)%nat) as [Hprev | Hrext].
          { (* Case: previous *)
            rewrite lookup_last_extend_l; last apply Hprev.
            by apply Habs.
          }
          (* Case: read-extension *)
          rewrite lookup_last_extend_r; last first.
          { apply Hprevrext. }
          { apply Nat.nlt_ge in Hrext.
            clear -Hrext.
            (* why couldn't lia solve this... *)
            trans t; [done | lia].
          }
          specialize (Habs (pred (length hist))).
          rewrite last_lookup Habs; last first.
          { apply length_not_nil in Hnnil. clear -Hnnil.
            set x := length _. lia.
          }
          f_equal.
          eapply lookup_with_versions_extensible; last first.
          { apply Hlelast. }
          { rewrite Hlenhist in Hrext. lia. }
          { rewrite Hlenhist. lia. }
        }
        (* Case: write-extension *)
        rewrite (lookup_with_versions_snoc_r _ _ _ ts); last first.
        { clear -Hwext. lia. }
        { simpl. word. }
        rewrite lookup_snoc_length'; last first.
        { rewrite last_extend_length_eq_n; last first.
          { apply Hts. }
          { apply Hnnil. }
          rewrite length_app last_extend_length_eq_n in Ht; last first.
          { apply Hts. }
          { apply Hnnil. }
          simpl in Ht.
          clear -Hwext Ht. lia.
        }
        done.
      }
      split.
      { by rewrite last_snoc. }
      split.
      { rewrite length_app last_extend_length_eq_n; last first.
        { apply Hts. }
        { intros Hnil. by rewrite Hnil in Hlasthist. }
        simpl.
        lia.
      }
      split.
      { apply Forall_app.
        split.
        { apply (Forall_impl _ _ _ Hlelast).
          intros x Hx.
          simpl.
          rewrite Hlenhist in Hts.
          clear -Hx Hts. lia.
        }
        by rewrite Forall_singleton.
      }
      split.
      { rewrite lookup_app_l; first done.
        by apply lookup_lt_Some in Hfirst.
      }
      { by rewrite last_snoc. }
    }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_Tuple__KillVersion (tuple : loc) (tsW : u64) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [None] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple key γ α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__KillVersion #tuple #tsW
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
    iIntros (ts hist' Hts) "#Hlb #Htpl".
    iIntros (Φ) "!> HphysX HΦ".
    wp_rec.

    (*@ func (tuple *Tuple) KillVersion(ts uint64) {                            @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Htpl]".

    (*@     // Create a new version and add it to the version chain.            @*)
    (*@     ver := tulip.Version{                                               @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Value : tulip.Value{ Present : false },                         @*)
    (*@     }                                                                   @*)
    (*@     tuple.vers = append(tuple.vers, ver)                                @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    iDestruct (phys_hist_agree with "HphysX Hphys") as %->.
    iApply fupd_wp.
    iMod (phys_hist_update hist' with "HphysX Hphys") as "[HphysX Hphys]".
    iModIntro.
    wp_loadField.
    (* somehow wp_SliceAppend doesn't work. *)
    wp_apply (wp_SliceAppend' with "Hvers").
    { done. }
    { by auto 10. }
    iIntros (versS') "Hvers".
    iAssert (own_slice versS' (struct.t Version) (DfracOwn 1) (vers ++ [(tsW, None)]))%I
      with "[Hvers]" as "Hvers".
    { by rewrite /own_slice {2}/list.untype fmap_app. }
    wp_storeField.

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@ }                                                                       @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HphysX]").
    { iFrame "Hlock Hlocked ∗ #".
      iModIntro.
      iExists (tsW, None).
      iPureIntro.
      assert (Hnnil : hist ≠ []).
      { by intros ->. }
      split.
      { intros t Ht.
        destruct (decide (t < ts)%nat) as [Hprevrext | Hwext].
        { (* Case: previous + read-extension *)
          rewrite (lookup_with_versions_snoc_l _ _ _ ts); last first.
          { clear -Hprevrext. lia. }
          { simpl. lia. }
          rewrite lookup_app_l; last first.
          { rewrite last_extend_length; last apply Hnnil.
            clear -Hprevrext Hts. lia.
          }
          destruct (decide (t < length hist)%nat) as [Hprev | Hrext].
          { (* Case: previous *)
            rewrite lookup_last_extend_l; last apply Hprev.
            by apply Habs.
          }
          (* Case: read-extension *)
          rewrite lookup_last_extend_r; last first.
          { apply Hprevrext. }
          { apply Nat.nlt_ge in Hrext.
            clear -Hrext.
            (* why couldn't lia solve this... *)
            trans t; [done | lia].
          }
          specialize (Habs (pred (length hist))).
          rewrite last_lookup Habs; last first.
          { apply length_not_nil in Hnnil. clear -Hnnil.
            set x := length _. lia.
          }
          f_equal.
          eapply lookup_with_versions_extensible; last first.
          { apply Hlelast. }
          { rewrite Hlenhist in Hrext. lia. }
          { rewrite Hlenhist. lia. }
        }
        (* Case: write-extension *)
        rewrite (lookup_with_versions_snoc_r _ _ _ ts); last first.
        { clear -Hwext. lia. }
        { simpl. word. }
        rewrite lookup_snoc_length'; last first.
        { rewrite last_extend_length_eq_n; last first.
          { apply Hts. }
          { apply Hnnil. }
          rewrite length_app last_extend_length_eq_n in Ht; last first.
          { apply Hts. }
          { apply Hnnil. }
          simpl in Ht.
          clear -Hwext Ht. lia.
        }
        done.
      }
      split.
      { by rewrite last_snoc. }
      split.
      { rewrite length_app last_extend_length_eq_n; last first.
        { apply Hts. }
        { intros Hnil. by rewrite Hnil in Hlasthist. }
        simpl.
        lia.
      }
      split.
      { apply Forall_app.
        split.
        { apply (Forall_impl _ _ _ Hlelast).
          intros x Hx.
          simpl.
          rewrite Hlenhist in Hts.
          clear -Hx Hts. lia.
        }
        by rewrite Forall_singleton.
      }
      split.
      { rewrite lookup_app_l; first done.
        by apply lookup_lt_Some in Hfirst.
      }
      { by rewrite last_snoc. }
    }
    wp_pures.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_findVersion (tsW : u64) (versS : Slice.t) (vers : list dbpver) :
    let ts := uint.nat tsW in
    Exists (λ v, uint.Z v.1 ≤ ts) vers ->
    {{{ own_slice versS (struct.t Version) (DfracOwn 1) vers }}}
      findVersion #tsW (to_val versS)
    {{{ (ver : dbpver) (slow : bool), RET (dbpver_to_val ver, #slow); 
        own_slice versS (struct.t Version) (DfracOwn 1) vers ∗
        ⌜find_version vers ts = Some ver⌝ ∗
        ⌜if slow
         then last vers = Some ver ∧ (uint.nat ver.1 < ts)%nat
         else Exists (λ v, (ts ≤ uint.nat v.1)%nat) vers⌝
    }}}.
  Proof.
    iIntros (ts Hexists Φ) "Hvers HΦ".
    wp_rec.
    rewrite Exists_exists in Hexists.
    destruct Hexists as [ver'' [Hin Hle]].
    destruct (nil_or_length_pos vers) as [| Hnonempty].
    { rewrite H in Hin. by destruct (not_elem_of_nil ver''). }
    iDestruct (own_slice_small_acc with "Hvers") as "[Hvers HversC]".
    iDestruct (own_slice_small_sz with "Hvers") as %Hlenvers.

    (*@ func findVersion(ts uint64, vers []tulip.Version) (tulip.Version, bool) { @*)
    (*@     var ver tulip.Version                                               @*)
    (*@     length := uint64(len(vers))                                         @*)
    (*@     var idx uint64 = 0                                                  @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first by auto.
    iIntros (verP) "HverP".
    wp_apply wp_slice_len.
    wp_apply wp_ref_to; first auto.
    iIntros (idxP) "HidxP".
    wp_pures.

    (*@     for idx < length {                                                  @*)
    (*@         ver = vers[length - idx - 1]                                    @*)
    (*@         if ver.Timestamp <= ts {                                        @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         idx++                                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := λ (cont : bool), (∃ (ver : dbpver) (idx : u64),
             "HverP"  ∷ (verP ↦[struct.t Version] (dbpver_to_val ver)) ∗
             "HidxP"  ∷ (idxP ↦[uint64T] #idx) ∗
             "Hvers"  ∷ own_slice_small versS (struct.t Version) (DfracOwn 1) vers ∗
             "%Hge"   ∷ ⌜(if cont
                          then True
                          else (uint.nat ver.1 ≤ ts)%nat)⌝ ∗
             "%Hlt"   ∷ ⌜(if decide (idx = W64 0)
                          then True
                          else Exists (λ v, (ts < uint.nat v.1)%nat) vers)⌝ ∗
             "%Hver"  ∷ ⌜(if cont
                          then True
                          else vers !! (length vers - uint.nat idx - 1)%nat = Some ver)⌝ ∗
             "%Hspec" ∷ ⌜(if cont
                          then find_version_forward (take (uint.nat idx) (reverse vers)) ts = None
                          else find_version_forward (reverse vers) ts = Some ver)⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [-HΦ HversC]"); last first; first 1 last.
    { (* Loop entry. *)
      iExists (W64 0, None).
      iFrame.
      iPureIntro.
      change (uint.nat 0) with 0%nat.
      by rewrite take_0.
    }
    { (* Loop body. *)
      clear Φ.
      iIntros (Φ).
      iModIntro.
      iIntros "Hloop HΦ".
      iNamed "Hloop".
      wp_pures.
      wp_load.
      wp_pures.
      wp_if_destruct; last first.
      { (* Loop condition. *)
        iModIntro.
        iApply "HΦ".
        unfold P.
        replace (take (uint.nat idx) _) with (reverse vers) in Hspec; last first.
        { symmetry.
          pose proof (length_reverse vers) as HversRevLen.
          rewrite take_ge; first done.
          rewrite HversRevLen Hlenvers.
          word.
        }
        destruct (find_version_le_is_Some _ _ _ Hin Hle).
        unfold find_version in H.
        by rewrite H in Hspec.
      }
      wp_load.
      wp_pures.
      destruct (list_lookup_lt vers (length vers - S (uint.nat idx))%nat) as [ver' Hver']; first word.
      wp_apply (wp_SliceGet with "[Hvers]").
      { iFrame.
        iPureIntro.
        set x := versS.(Slice.sz).
        assert (H : Z.ge (uint.Z (word.sub x idx)) 1).
        { subst x. word. }
        replace (uint.Z (word.sub _ (W64 1))) with (uint.Z versS.(Slice.sz) - uint.Z idx - 1); last first.
        { subst x. word. }
        replace (Z.to_nat _) with ((length vers) - (S (uint.nat idx)))%nat; last first.
        { rewrite Hlenvers. word. }
        rewrite Hver'.
        done.
      }
      iIntros "Hvers".
      wp_apply (wp_StoreAt with "HverP").
      { rewrite /dbpver_to_val /=. by destruct ver'.2; auto 10. }
      iIntros "HverP".
      wp_load.
      wp_pures.
      wp_if_destruct.
      { iModIntro.
        iApply "HΦ".
        unfold P.
        do 2 iExists _.
        iFrame "∗ %".
        iPureIntro.
        pose proof Hver' as Hlookup.
        rewrite -reverse_lookup in Hver'; last first.
        { rewrite Hlenvers. word. }
        apply take_drop_middle in Hver'.
        split; first word.
        split.
        { rewrite -Hlookup. f_equal. lia. }
        apply (find_version_forward_match _ _ _ _ _ Hver'); [done | word].
      }
      wp_load.
      wp_store.
      iModIntro.
      iApply "HΦ".
      unfold P.
      do 2 iExists _.
      iFrame.
      iPureIntro.
      replace (uint.nat (word.add _ _)) with (S (uint.nat idx)); last word.
      rewrite -reverse_lookup in Hver'; last first.
      { rewrite Hlenvers. word. }
      rewrite (take_S_r _ _ ver'); last done.
      set vers_take := take _ _.
      set vers' := vers_take ++ _.
      split; first done.
      split.
      { clear Hlt.
        case_decide; first done.
        rewrite Exists_exists.
        exists ver'.
        split.
        { apply list_elem_of_lookup_2 in Hver'.
          by rewrite elem_of_reverse in Hver'.
        }
        clear -Heqb0. word.
      }
      split; first done.
      apply (find_version_forward_not_match vers' _ vers_take ver'); [auto | auto | word].
    }
    iNamed 1. subst P.
    wp_pures.

    (*@     return ver, (idx == 0) && (ts != ver.Timestamp)                     @*)
    (*@ }                                                                       @*)
    do 2 wp_load.
    iDestruct ("HversC" with "Hvers") as "Hvers".
    wp_pures.
    case_bool_decide as Hidx; wp_pures.
    { wp_load. wp_pures.
      inv Hidx.
      case_bool_decide as Heq; last first.
      { (* Case: Slow-path *)
        iApply "HΦ".
        iFrame "Hvers".
        iPureIntro.
        split; first done.
        simpl.
        split.
        { rewrite last_lookup -Hver. f_equal. word. }
        { apply u64_val_ne in Heq. clear-Hge Heq. word. }
      }
      { (* Case: Fast-path hitting the last version. *)
        iApply "HΦ".
        iFrame "Hvers".
        iPureIntro.
        split; first done.
        rewrite /= Exists_exists.
        exists ver. subst ts.
        inv Heq.
        split; last done.
        by apply list_elem_of_lookup_2 in Hver.
      }
    }
    (* Case: Fast-path hitting a non-last version. *)
    iApply "HΦ".
    iFrame "Hvers".
    iPureIntro.
    split; first done.
    apply u64_val_ne in Hidx.
    case_decide; first word.
    apply (Exists_impl _ _ _ Hlt).
    intros v Hvgt.
    word.
  Qed.

  Theorem wp_Tuple__ReadVersion_xphys (tuple : loc) (tsW : u64) key γ α :
    let ts := uint.nat tsW in
    ts ≠ O ->
    is_tuple tuple key γ α -∗
    {{{ True }}}
      Tuple__ReadVersion #tuple #tsW
    {{{ (ver : dbpver) (slow : bool), RET (dbpver_to_val ver, #slow);
        if slow then True else is_repl_hist_at γ key (pred ts) ver.2
    }}}.
  Proof.
    iIntros (ts Htsnz) "#Htpl".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (tuple *Tuple) ReadVersion(ts uint64) (tulip.Version, bool) {      @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Htpl]".

    (*@     ver, slow := findVersion(ts - 1, tuple.vers)                        @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_loadField.
    wp_apply (wp_findVersion with "Hvers").
    { rewrite Exists_exists.
      exists (W64 0, None). simpl.
      split; last word.
      by apply list_elem_of_lookup_2 in Hfirst.
    }
    iIntros (ver slow) "[Hvers %Hfind]".
    destruct Hfind as [Hfind Hlast].
    replace (uint.nat _) with (pred ts) in Hfind, Hlast; last first.
    { word. }
    wp_pures.

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗ # %". }
    wp_pures.
    iApply "HΦ".

    (*@     return ver, slow                                                    @*)
    (*@ }                                                                       @*)
    destruct slow; first done.
    iFrame "Hrepl".
    iPureIntro.
    specialize (Habs (pred ts)).
    rewrite /lookup_with_versions Hfind in Habs.
    apply Habs.
    rewrite Exists_exists in Hlast.
    destruct Hlast as (v & Hv & Hle).
    rewrite Forall_forall in Hlelast.
    specialize (Hlelast _ Hv).
    clear -Hle Hlelast Hlenhist. lia.
  Qed.

  Theorem wp_Tuple__ReadVersion (tuple : loc) (tsW : u64) key hist γ α :
    let ts := uint.nat tsW in
    ts ≠ O ->
    is_tuple tuple key γ α -∗
    {{{ own_phys_hist_half α key hist }}}
      Tuple__ReadVersion #tuple #tsW
    {{{ (ver : dbpver) (slow : bool), RET (dbpver_to_val ver, #slow);
        own_phys_hist_half α key hist ∗
        if slow
        then is_repl_hist_lb γ key hist ∗
             ⌜last hist = Some ver.2⌝ ∗
             ⌜uint.nat ver.1 = pred (length hist)⌝ ∗
             ⌜(length hist < ts)%nat⌝
        else is_repl_hist_at γ key (pred ts) ver.2
    }}}.
  Proof.
    iIntros (ts Htsnz) "#Htpl".
    iIntros (Φ) "!> HphysX HΦ".
    wp_rec.

    (*@ func (tuple *Tuple) ReadVersion(ts uint64) (tulip.Version, bool) {      @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Htpl]".

    (*@     ver, slow := findVersion(ts - 1, tuple.vers)                        @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    iDestruct (phys_hist_agree with "HphysX Hphys") as %->.
    wp_loadField.
    wp_apply (wp_findVersion with "Hvers").
    { rewrite Exists_exists.
      exists (W64 0, None). simpl.
      split; last word.
      by apply list_elem_of_lookup_2 in Hfirst.
    }
    iIntros (ver slow) "[Hvers %Hfind]".
    destruct Hfind as [Hfind Hlast].
    replace (uint.nat _) with (pred ts) in Hfind, Hlast; last first.
    { word. }
    wp_pures.

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@                                                                         @*)
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[-HΦ HphysX]").
    { by iFrame "Hlock Hlocked ∗ # %". }
    wp_pures.
    iApply "HΦ".
    iFrame "HphysX".

    (*@     return ver, slow                                                    @*)
    (*@ }                                                                       @*)
    destruct slow; last first.
    { (* Case: fast-path. *)
      iFrame "Hrepl".
      iPureIntro.
      specialize (Habs (pred ts)).
      rewrite /lookup_with_versions Hfind in Habs.
      apply Habs.
      rewrite Exists_exists in Hlast.
      destruct Hlast as (v & Hv & Hle).
      rewrite Forall_forall in Hlelast.
      specialize (Hlelast _ Hv).
      clear -Hle Hlelast Hlenhist. lia.
    }
    (* Case: slow-path. *)
    iFrame "Hrepl".
    iPureIntro.
    destruct Hlast as [Hlast Hlt].
    rewrite Hverlast in Hlast. inv Hlast.
    split; first apply Hlasthist.
    split; first by rewrite Hlenhist.
    word.
  Qed.

  Theorem wp_MkTuple key γ α :
    is_repl_hist_lb γ key [None] -∗
    {{{ own_phys_hist_half α key [None] }}}
      MkTuple #()
    {{{ (tuple : loc), RET #tuple; is_tuple tuple key γ α }}}.
  Proof.
    iIntros "#Hrepl" (Φ) "!> Hphys HΦ".
    wp_rec.

    (*@ func MkTuple() *Tuple {                                                 @*)
    (*@     tuple := new(Tuple)                                                 @*)
    (*@     tuple.mu = new(sync.Mutex)                                          @*)
    (*@     vers := make([]tulip.Version, 1, 1)                                 @*)
    (*@     vers[0] = tulip.Version{                                            @*)
    (*@         Timestamp : 0,                                                  @*)
    (*@         Value     : tulip.Value{ Present : false },                     @*)
    (*@     }                                                                   @*)
    (*@     tuple.vers = vers                                                   @*)
    (*@     return tuple                                                        @*)
    (*@ }                                                                       @*)
    wp_apply wp_allocStruct; first by auto.
    iIntros (tupleP) "Htuple".
    iDestruct (struct_fields_split with "Htuple") as "Htuple".
    iNamed "Htuple". simpl.
    wp_apply wp_new_free_lock.
    iIntros (muP) "Hfree".
    wp_storeField.
    wp_apply (wp_NewSliceWithCap); first word.
    iIntros (versPP).
    iIntros "Hvers".
    wp_pures.
    iDestruct (own_slice_small_acc with "Hvers") as "[Hvers HversC]".
    wp_apply (slice.wp_SliceSet with "[$Hvers]").
    { iPureIntro.
      split.
      { by rewrite /list.untype fmap_replicate lookup_replicate_2; last word. }
      { by auto 10. }
    }
    iIntros "Hvers".
    set versP := Slice.mk _ _ _.
    set verinit : dbpver := (W64 0, None).
    iAssert (own_slice_small versP (struct.t Version) (DfracOwn 1) [verinit])%I
      with "Hvers" as "Hvers".
    iDestruct ("HversC" with "Hvers") as "Hvers".
    wp_storeField.
    iMod (alloc_lock _ _ _ (own_tuple tupleP key γ α) with "Hfree [-HΦ mu]") as "#Hlock".
    { iFrame "∗ #".
      iPureIntro.
      exists verinit.
      split.
      { intros t Ht. simpl in Ht. assert (t = O) as -> by lia.
        simpl.
        rewrite -(app_nil_l [verinit]).
        by rewrite (lookup_with_versions_snoc_r _ _ _ O).
      }
      by rewrite Forall_singleton.
    }
    iMod (readonly_alloc_1 with "mu") as "#HmuP".
    iApply "HΦ".
    by iFrame "#".
  Qed.

End program.
