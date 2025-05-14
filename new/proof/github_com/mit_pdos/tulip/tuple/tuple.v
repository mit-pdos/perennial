From stdpp Require Import list.
From New.proof.github_com.mit_pdos.tulip.tuple Require Import res.

From New.proof.github_com.mit_pdos.tulip Require Import program_prelude.

From New.proof.github_com.mit_pdos.tulip Require Import tulip.
From New.proof.github_com.mit_pdos.gokv Require Import grove_ffi.
From New.proof Require Import sync.

From New.proof Require Import grove_prelude.
From New.generatedproof.github_com.mit_pdos.tulip Require Import tuple.

(* FIXME: ugly proofs; clean this up *)

Unset Printing Projections.

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
  apply elem_of_reverse, elem_of_list_lookup_1 in Hin as [idx Hlookup].
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
  rewrite list.Forall_forall in Hlast.
  assert (Hin : ver ∈ vers).
  { apply elem_of_reverse. rewrite Hversl. apply elem_of_list_here. }
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
  Context `{!heapGS Σ, !tulip_ghostG Σ} `{!goGlobalsGS Σ}.

  #[global] Program Instance : IsPkgInit tuple :=
    ltac2:(build_pkg_init ()).

  (*@ type Tuple struct {                                                     @*)
  (*@     // Mutex protecting the fields below.                               @*)
  (*@     mu     *sync.Mutex                                                  @*)
  (*@     // Timestamp of fast-read optimization. Currently not used.         @*)
  (*@     tssafe uint64                                                       @*)
  (*@     // List of versions.                                                @*)
  (*@     vers   []tulip.Version                                              @*)
  (*@ }                                                                       @*)
  Definition own_tuple tuple key γ α : iProp Σ :=
    ∃ (tssafe : u64) (versS : slice.t) (vers : list dbpver) (verlast : dbpver) (hist : dbhist),
      "HtssafeP"   ∷ tuple ↦s[tuple.Tuple :: "tssafe"] tssafe ∗
      "HversP"     ∷ tuple ↦s[tuple.Tuple :: "vers"] versS ∗
      "Hvers"      ∷ own_slice versS (DfracOwn 1) (dbpver_to_t <$> vers) ∗
      "Hvers_cap"  ∷ own_slice_cap tulip.Version.t versS ∗
      "Hphys"      ∷ own_phys_hist_half α key hist ∗
      "#Hrepl"     ∷ is_repl_hist_lb γ key hist ∗
      "%Habs"      ∷ ⌜(∀ t, (t < length hist)%nat -> hist !! t = Some (lookup_with_versions vers t))⌝ ∗
      "%Hverlast"  ∷ ⌜list.last vers = Some verlast⌝ ∗
      "%Hlenhist"  ∷ ⌜length hist = S (uint.nat verlast.1)⌝ ∗
      "%Hlelast"   ∷ ⌜Forall (λ v, (uint.nat v.1 ≤ uint.nat verlast.1)%nat) vers⌝ ∗
      "%Hfirst"    ∷ ⌜vers !! O = Some (W64 0, None)⌝ ∗
      "%Hlasthist" ∷ ⌜list.last hist = Some verlast.2⌝.

  Definition is_tuple tuple key γ α : iProp Σ :=
    ∃ (muP : loc),
      "#Hmu"   ∷ tuple ↦s[tuple.Tuple :: "mu"]□ muP ∗
      "#Hlock" ∷ is_Mutex muP (own_tuple tuple key γ α).

  Theorem wp_Tuple__AppendVersion (tuple_l : loc) (tsW : u64) (value : byte_string) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [Some value] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple_l key γ α -∗
    {{{ is_pkg_init tuple ∗ own_phys_hist_half α key hist }}}
      tuple_l @ tuple @ "Tuple'ptr" @ "AppendVersion" #tsW #value
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
    iIntros (ts hist' Hts) "#Hlb #Htpl".
    wp_start as "HphysX".

    (*@ func (tuple *Tuple) AppendVersion(ts uint64, value string) {            @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Htpl]".

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
    wp_auto.
    iDestruct (phys_hist_agree with "HphysX Hphys") as %->.
    iApply fupd_wp.
    iMod (phys_hist_update hist' with "HphysX Hphys") as "[HphysX Hphys]".
    iModIntro.
    wp_apply wp_slice_literal as "%sl Hvers_s".
    wp_apply (wp_slice_append with "[$Hvers $Hvers_cap $Hvers_s]") as "%versS' (Hvers & Hvers_cap & _)".
    iAssert (own_slice versS' (DfracOwn 1) (dbpver_to_t <$> (vers ++ [(tsW, Some value)])))%I
      with "[Hvers]" as "Hvers".
    {
      iExactEq "Hvers".
      rewrite fmap_app //=.
    }

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@ }                                                                       @*)
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
      { apply list.Forall_app.
        split.
        { apply (list.Forall_impl _ _ _ Hlelast).
          intros x Hx.
          simpl.
          rewrite Hlenhist in Hts.
          clear -Hx Hts. lia.
        }
        by rewrite list.Forall_singleton.
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

  Theorem wp_Tuple__KillVersion (tuple_l : loc) (tsW : u64) key hist γ α :
    let ts := uint.nat tsW in
    let hist' := last_extend ts hist ++ [None] in
    (length hist ≤ ts)%nat ->
    is_repl_hist_lb γ key hist' -∗
    is_tuple tuple_l key γ α -∗
    {{{ is_pkg_init tuple ∗ own_phys_hist_half α key hist }}}
      tuple_l @ tuple @ "Tuple'ptr" @ "KillVersion" #tsW
    {{{ RET #(); own_phys_hist_half α key hist' }}}.
  Proof.
    iIntros (ts hist' Hts) "#Hlb #Htpl".
    wp_start as "HphysX".

    (*@ func (tuple *Tuple) KillVersion(ts uint64) {                            @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
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
    wp_auto.
    wp_apply wp_slice_literal. iIntros "%sl Hvers_s". wp_auto.
    wp_apply (wp_slice_append with "[$Hvers $Hvers_cap $Hvers_s]").
    iIntros (versS') "(Hvers & Hvers_cap & _)".
    iAssert (own_slice versS' (DfracOwn 1) (dbpver_to_t <$> (vers ++ [(tsW, None)])))%I
      with "[Hvers]" as "Hvers".
    { iExactEq "Hvers".
      rewrite fmap_app //=. }
    wp_auto.

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@ }                                                                       @*)
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
      { apply list.Forall_app.
        split.
        { apply (list.Forall_impl _ _ _ Hlelast).
          intros x Hx.
          simpl.
          rewrite Hlenhist in Hts.
          clear -Hx Hts. lia.
        }
        by rewrite list.Forall_singleton.
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

  Theorem wp_findVersion (tsW : u64) (versS : slice.t) (vers : list dbpver) :
    let ts := uint.nat tsW in
    Exists (λ v, uint.Z v.1 ≤ ts) vers ->
    {{{ is_pkg_init tuple ∗ own_slice versS (DfracOwn 1) (dbpver_to_t <$> vers) }}}
      tuple @ "findVersion" #tsW (to_val versS)
    {{{ (ver : dbpver) (slow : bool), RET (#(dbpver_to_t ver), #slow);
        own_slice versS (DfracOwn 1) (dbpver_to_t <$> vers) ∗
        ⌜find_version vers ts = Some ver⌝ ∗
        ⌜if slow
         then list.last vers = Some ver ∧ (uint.nat ver.1 < ts)%nat
         else Exists (λ v, (ts ≤ uint.nat v.1)%nat) vers⌝
    }}}.
  Proof.
    iIntros (ts Hexists).
    wp_start as "Hvers".
    wp_auto.
    iPersist "vers ts".
    rewrite Exists_exists in Hexists.
    destruct Hexists as [ver'' [Hin Hle]].
    destruct (nil_or_length_pos vers) as [| Hnonempty].
    { rewrite H in Hin. by destruct (not_elem_of_nil ver''). }
    iDestruct (own_slice_len with "Hvers") as %Hlenvers.

    (*@ func findVersion(ts uint64, vers []tulip.Version) (tulip.Version, bool) { @*)
    (*@     var ver tulip.Version                                               @*)
    (*@     length := uint64(len(vers))                                         @*)
    (*@     var idx uint64 = 0                                                  @*)
    (*@                                                                         @*)
    iRename "ver" into "HverP".
    iRename "idx" into "HidxP".
    iPersist "length".

    (*@     for idx < length {                                                  @*)
    (*@         ver = vers[length - idx - 1]                                    @*)
    (*@         if ver.Timestamp <= ts {                                        @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@         idx++                                                           @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (∃ (ver : dbpver) (idx : u64),
             "HverP"  ∷ (ver_ptr ↦ (dbpver_to_t ver)) ∗
             "HidxP"  ∷ (idx_ptr ↦ idx) ∗
             "Hvers"  ∷ own_slice versS (DfracOwn 1) (dbpver_to_t <$> vers) ∗
             (* "%Hge"   ∷ ⌜(if cont
                          then True
                          else (uint.nat ver.1 ≤ ts)%nat)⌝ ∗ *)
             "%Hlt"   ∷ ⌜(if decide (idx = W64 0)
                          then True
                          else Exists (λ v, (ts < uint.nat v.1)%nat) vers)⌝ ∗
             (* "%Hver"  ∷ ⌜(if cont
                          then True
                          else vers !! (length vers - uint.nat idx - 1)%nat = Some ver)⌝ ∗ *)
             "%Hspec" ∷ ⌜find_version_forward (take (uint.nat idx) (reverse vers)) ts = None ⌝)%I.
    iAssert P with "[-HΦ]" as "HI".
    {
      subst P.
      iExists (W64 0, None).
      iFrame.
      iPureIntro.
      change (uint.nat 0) with 0%nat.
      by rewrite take_0.
    }
    wp_for "HI"; try wp_auto.
    wp_if_destruct.
    { (* Loop body. *)
      wp_auto.
      (*
      { (* Loop condition. *)
        wp_auto.
      iIntros "Hloop HΦ".
      iNamed "Hloop".
      wp_pures.
      wp_load.
      wp_pures.
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
*)
      destruct (list_lookup_lt vers (length vers - S (uint.nat idx))%nat) as [ver' Hver']; first word.
      wp_pure.
      { word. }
      wp_apply (wp_load_slice_elem with "[$Hvers]").
      { iFrame.
        iPureIntro.
        rewrite list_lookup_fmap.
        set x := versS.(slice.len_f).
        assert (H : Z.ge (uint.Z (word.sub x idx)) 1).
        { subst x. word. }
        replace (uint.Z (word.sub _ (W64 1))) with (uint.Z versS.(slice.len_f) - uint.Z idx - 1); last first.
        { subst x. word. }
        replace (Z.to_nat _) with ((length vers) - (S (uint.nat idx)))%nat; last first.
        { rewrite length_fmap in Hlenvers. rewrite Hlenvers. word. }
        rewrite Hver'.
        done.
      }
      iIntros "Hvers".
      wp_auto.
    case_bool_decide as Heq; wp_auto.
    { wp_for_post.
      case_bool_decide as Hidx; try wp_auto; last first.
      { (* Case: Slow-path *)
        iApply "HΦ".
        iFrame "Hvers".
        iPureIntro.

        rewrite -reverse_lookup in Hver'; last first.
        { rewrite length_fmap in Hlenvers; rewrite Hlenvers. word. }
        apply take_drop_middle in Hver'.
        rewrite /find_version.
        split.
        { apply (find_version_forward_match _ _ _ _ _ Hver'); [done | word]. }
        rewrite -> decide_False in Hlt by word.
        apply (list.Exists_impl _ _ _ Hlt).
        intros; word.
      }
      { (* Case: Fast-path hitting the last version. *)
        iApply "HΦ".
        iFrame "Hvers".
        iPureIntro.
        subst.
        change (uint.nat (W64 0)) with 0%nat in *.
        rewrite /find_version.
        split.
        { rewrite <- reverse_lookup in Hver' by word.
          apply take_drop_middle in Hver'.
          eapply find_version_forward_match in Hver'; eauto; word.
        }
        case_bool_decide as Hidx; subst.
        - rewrite list.Exists_exists.
          exists ver'. subst ts.
          by apply elem_of_list_lookup_2 in Hver'.
        - rewrite last_lookup -Hver'.
          split.
          { f_equal; lia. }
          word.
      }
    }
    wp_for_post.
    iFrame "∗%".
    iPureIntro.
    pose proof Hver' as Hlookup.
    rewrite -reverse_lookup in Hver'; last first.
    { rewrite length_fmap in Hlenvers; rewrite Hlenvers. word. }
    apply take_drop_middle in Hver'.
    rewrite -> decide_False by word.
    replace (uint.nat (word.add idx (W64 1))) with (S (uint.nat idx)) by word.
    rewrite (take_S_r _ _ ver'); last first.
    {
      rewrite reverse_lookup //.
      rewrite length_fmap in Hlenvers.
      word.
    }
    admit.
  }
  wp_auto.
  (* TODO: seems repetitive with above *)
  admit.
  (*
      set vers_take := take _ _.
      set vers' := vers_take ++ _.
      split; first done.
      split.
      { clear Hlt.
        case_decide; first done.
        rewrite Exists_exists.
        exists ver'.
        split.
        { apply elem_of_list_lookup_2 in Hver'.
          by rewrite elem_of_reverse in Hver'.
        }
        clear -Heqb0. word.
      }
      split; first done.
      apply (find_version_forward_not_match vers' _ vers_take ver'); [auto | auto | word].


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
        { apply elem_of_list_lookup_2 in Hver'.
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
        by apply elem_of_list_lookup_2 in Hver.
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
   *)
  Admitted.

  Theorem wp_Tuple__ReadVersion_xphys (tuple_l : loc) (tsW : u64) key γ α :
    let ts := uint.nat tsW in
    ts ≠ O ->
    is_tuple tuple_l key γ α -∗
    {{{ is_pkg_init tuple }}}
      tuple_l @ tuple @ "Tuple'ptr" @ "ReadVersion" #tsW
    {{{ (ver : dbpver) (slow : bool), RET (#(dbpver_to_t ver), #slow);
        if slow then True else is_repl_hist_at γ key (pred ts) ver.2
    }}}.
  Proof.
    iIntros (ts Htsnz) "#Htpl".
    wp_start as "_".
    wp_auto.
    iPersist "tuple ts".

    (*@ func (tuple *Tuple) ReadVersion(ts uint64) (tulip.Version, bool) {      @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Htpl]".

    (*@     ver, slow := findVersion(ts - 1, tuple.vers)                        @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_auto.
    wp_apply (wp_findVersion with "[$Hvers]").
    { rewrite list.Exists_exists.
      exists (W64 0, None). simpl.
      split; last word.
      by apply elem_of_list_lookup_2 in Hfirst.
    }
    iIntros (ver slow) "[Hvers %Hfind]".
    destruct Hfind as [Hfind Hlast].
    replace (uint.nat _) with (pred ts) in Hfind, Hlast; last first.
    { word. }
    wp_pures.

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@                                                                         @*)
    wp_auto.
    iPersist "ver slow".
    wp_apply (wp_Mutex__Unlock with "[-HΦ]").
    { by iFrame "Hlock Hlocked ∗ # %". }
    try wp_auto.
    iApply "HΦ".

    (*@     return ver, slow                                                    @*)
    (*@ }                                                                       @*)
    destruct slow; first done.
    iFrame "Hrepl".
    iPureIntro.
    specialize (Habs (pred ts)).
    rewrite /lookup_with_versions Hfind in Habs.
    apply Habs.
    rewrite list.Exists_exists in Hlast.
    destruct Hlast as (v & Hv & Hle).
    rewrite list.Forall_forall in Hlelast.
    specialize (Hlelast _ Hv).
    clear -Hle Hlelast Hlenhist. lia.
  Qed.

  Theorem wp_Tuple__ReadVersion (tuple_l : loc) (tsW : u64) key hist γ α :
    let ts := uint.nat tsW in
    ts ≠ O ->
    is_tuple tuple_l key γ α -∗
    {{{ is_pkg_init tuple ∗ own_phys_hist_half α key hist }}}
      tuple_l @ tuple @ "Tuple'ptr" @ "ReadVersion" #tsW
    {{{ (ver : dbpver) (slow : bool), RET (#(dbpver_to_t ver), #slow);
        own_phys_hist_half α key hist ∗
        if slow
        then is_repl_hist_lb γ key hist ∗
             ⌜list.last hist = Some ver.2⌝ ∗
             ⌜uint.nat ver.1 = pred (length hist)⌝ ∗
             ⌜(length hist < ts)%nat⌝
        else is_repl_hist_at γ key (pred ts) ver.2
    }}}.
  Proof.
    iIntros (ts Htsnz) "#Htpl".
    wp_start as "HphysX".

    (*@ func (tuple *Tuple) ReadVersion(ts uint64) (tulip.Version, bool) {      @*)
    (*@     tuple.mu.Lock()                                                     @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    wp_auto.
    iPersist "tuple ts".
    wp_apply (wp_Mutex__Lock with "[$Hlock]").
    iIntros "[Hlocked Htpl]".

    (*@     ver, slow := findVersion(ts - 1, tuple.vers)                        @*)
    (*@                                                                         @*)
    iNamed "Htpl".
    iDestruct (phys_hist_agree with "HphysX Hphys") as %->.
    wp_auto.
    wp_apply (wp_findVersion with "[$Hvers]").
    { rewrite list.Exists_exists.
      exists (W64 0, None). simpl.
      split; last word.
      by apply elem_of_list_lookup_2 in Hfirst.
    }
    iIntros (ver slow) "[Hvers %Hfind]".
    destruct Hfind as [Hfind Hlast].
    replace (uint.nat _) with (pred ts) in Hfind, Hlast; last first.
    { word. }

    (*@     tuple.mu.Unlock()                                                   @*)
    (*@                                                                         @*)
    wp_auto.
    iPersist "ver slow".
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
    {{{ is_pkg_init tuple ∗ own_phys_hist_half α key [None] }}}
      tuple @ "MkTuple" #()
    {{{ (tuple_l : loc), RET #tuple_l; is_tuple tuple_l key γ α }}}.
  Proof.
    iIntros "#Hrepl".
    wp_start as "Hphys".
    wp_auto.
    wp_alloc tuple_temp as "tuple_temp".
    wp_auto.
    wp_alloc mutex_temp as "mutex_temp".
    wp_auto.

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
    wp_apply (wp_slice_make3 (V:=tulip.Version.t)).
    { word. }
    iIntros (versions_l) "(Hversions & HversionsC & %)".
    wp_auto.
    rewrite replicate_S replicate_0.
    iDestruct (own_slice_len with "Hversions") as %Hlen. simpl in Hlen.
    wp_pure.
    { word. }
    wp_apply (wp_store_slice_elem with "[$Hversions]").
    { iPureIntro. simpl. word. }
    change (uint.nat (W64 0)) with 0%nat.
    cbn [insert list_insert].
    iIntros "Hversions".
    rewrite -wp_fupd.
    wp_auto.
    iApply struct_fields_split in "tuple_temp". iNamed "tuple_temp".
    simpl.

    set verinit : dbpver := (W64 0, None).
    iPersist "Hmu".
    iMod (init_Mutex (own_tuple tuple_temp key γ α) with "[$mutex_temp] [-HΦ]") as "#Hlock".
    { iFrame "∗ #".
      iExists ([(W64 0, None)]), verinit.
      iModIntro.
      iSplit; [ iExact "Hversions" | ].
      iPureIntro.
      split.
      { intros t Ht. simpl in Ht. assert (t = O) as -> by lia.
        simpl.
        rewrite -(app_nil_l [verinit]).
        by rewrite (lookup_with_versions_snoc_r _ _ _ O).
      }
      by rewrite Forall_singleton.
    }
    iModIntro.
    iApply "HΦ".
    iFrame "#".
  Qed.

End program.
