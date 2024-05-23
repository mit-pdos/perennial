From Perennial.program_proof.mvcc Require Import tuple_prelude tuple_repr.

Section proof.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(*******************************************************************)
(* func findVersion(tid uint64, vers []Version) Version            *)
(*******************************************************************)
Local Theorem wp_findVersion (tid : u64) (versS : Slice.t)
                              (vers : list (u64 * bool * string)) :
  {{{ ⌜∃ (ver : pver), (ver ∈ vers) ∧ (uint.Z ver.1.1 < uint.Z tid)⌝ ∗
      slice.own_slice versS (structTy Version) (DfracOwn 1) (ver_to_val <$> vers)
  }}}
    findVersion #tid (to_val versS)
  {{{ (ver : pver), RET (ver_to_val ver);
      ⌜spec_find_ver vers tid = Some ver⌝ ∗
      slice.own_slice versS (structTy Version) (DfracOwn 1) (ver_to_val <$> vers)
  }}}.
Proof.
  iIntros (Φ) "[%Hlt HversS] HΦ".
  destruct Hlt as [ver'' [Hin Hlt]].
  destruct (nil_or_length_pos vers) as [| Hnonempty].
  { rewrite H in Hin. by destruct (not_elem_of_nil ver''). }
  iDestruct (slice.own_slice_small_acc with "HversS") as "[HversS HversC]".
  iDestruct (own_slice_small_sz with "HversS") as "%HversLen".
  rewrite fmap_length in HversLen.
  wp_call.
  
  (***********************************************************)
  (* var ver Version                                         *)
  (* length := uint64(len(vers))                             *)
  (* var idx uint64 = 0                                      *)
  (***********************************************************)
  wp_apply (wp_ref_of_zero); first auto.
  iIntros (verR) "HverR".
  wp_pures.
  wp_apply (wp_slice_len).
  wp_pures.
  wp_apply (wp_ref_to); first auto.
  iIntros (idxR) "HidxR".
  wp_pures.

  (***********************************************************)
  (* for idx < length {                                      *)
  (*     ver = vers[length - idx - 1]                        *)
  (*     if tid > ver.begin {                                *)
  (*         break                                           *)
  (*     }                                                   *)
  (*     idx++                                               *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (∃ (ver : u64 * bool * string) (idx : u64),
             "HverR" ∷ (verR ↦[struct.t Version] ver_to_val ver) ∗
             "HidxR" ∷ (idxR ↦[uint64T] #idx) ∗
             "HversS" ∷ own_slice_small versS (struct.t Version) (DfracOwn 1) (ver_to_val <$> vers) ∗
             "%Hspec" ∷ if b
                        then ⌜spec_find_ver_reverse (take (uint.nat idx) (reverse vers)) tid = None⌝
                        else ⌜spec_find_ver_reverse (reverse vers) tid = Some ver⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [-HΦ HversC]").
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
        pose proof (reverse_length vers) as HversRevLen.
        rewrite take_ge; first done.
        rewrite HversRevLen HversLen.
        word.
      }
      destruct (spec_find_ver_lt_Some _ _ _ Hin Hlt).
      unfold spec_find_ver in H.
      by rewrite H in Hspec.
    }
    wp_load.
    wp_pures.
    
    (* apply Znot_le_gt in Heqb. *)
    destruct (list_lookup_lt _ vers (length vers - S (uint.nat idx))%nat) as [ver' Hver']; first word.
    wp_apply (wp_SliceGet with "[HversS]").
    { iFrame.
      iPureIntro.
      set x := versS.(Slice.sz).
      (**
       * Notes on rewriting between [word.sub] and [Z.sub].
       * 1. In general, to rewrite from [uint.Z (word.sub x y)] to [uint.Z x - uint.Z y],
       * we need to have [uint.Z x ≥ uint.Z y] in the context.
       * 2. For nested [word.sub], e.g., [uint.Z (word.sub (word.sub x y) z)], we can
       * first prove that [uint.Z (word.sub x y) ≥ uint.Z z], and then replace
       * [uint.Z (word.sub (word.sub x y) z)] with [uint.Z x - uint.Z y - uint.Z z].
       *)
      assert (H : Z.ge (uint.Z (word.sub x idx)) 1).
      { subst x. word. }
      replace (uint.Z (word.sub _ (W64 1))) with (uint.Z versS.(Slice.sz) - uint.Z idx - 1); last first.
      { subst x. word. }
      replace (Z.to_nat _) with ((length vers) - (S (uint.nat idx)))%nat; last first.
      { rewrite HversLen. word. }
      rewrite list_lookup_fmap.
      rewrite Hver'.
      by apply fmap_Some_2.
    }
    iIntros "[HversS %Hvalty]".
    wp_store.
    wp_load.
    wp_pures.
    wp_if_destruct.
    { iModIntro.
      iApply "HΦ".
      unfold P.
      do 2 iExists _.
      iFrame "∗ %".
      iPureIntro.
      rewrite -reverse_lookup in Hver'; last first.
      { rewrite HversLen. word. }
      apply take_drop_middle in Hver'.
      apply (spec_find_ver_reverse_match _ _ _ _ _ Hver'); [done | word].
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
    { rewrite HversLen. word. }
    rewrite (take_S_r _ _ ver'); last done.
    set vers_take := take _ _.
    set vers' := vers_take ++ _.
    apply Znot_lt_ge in Heqb0.
    apply (spec_find_ver_reverse_not_match vers' _ vers_take ver'); [auto | auto | word].
  }
  { (* Loop entry. *)
    unfold P.
    iExists (W64 0, false, "").
    iExists _.
    iFrame.
    iPureIntro.
    change (uint.nat 0) with 0%nat.
    rewrite take_0.
    split; auto.
  }
  iIntros "Hloop".
  iNamed "Hloop".
  wp_pures.
  
  (***********************************************************)
  (* return ver                                              *)
  (***********************************************************)
  wp_load.
  iApply "HΦ".
  iDestruct ("HversC" with "HversS") as "HversS".
  by iFrame.
Qed.

Definition ptuple_auth_owned
           γ (key : u64) (owned : bool) (vchain : list dbval)
  : iProp Σ :=
  ptuple_auth γ (if owned then (1 / 4) else (1 / 2))%Qp key vchain.

(*****************************************************************)
(* func (tuple *Tuple) ReadWait(tid uint64)                      *)
(*****************************************************************)
Theorem wp_tuple__ReadWait tuple (tid : u64) (key : u64) γ :
  is_tuple tuple key γ -∗
  {{{ True }}}
    Tuple__ReadWait #tuple #tid
  {{{ (owned : bool) (vchain : list dbval), RET #();
      is_tuple_locked tuple key γ ∗
      own_tuple_read tuple key owned vchain γ ∗
      ptuple_auth_owned γ key owned vchain ∗
      ⌜owned = false ∨ (uint.nat tid < length vchain)%nat⌝
  }}}.
Proof.
  iIntros "#Htuple" (Φ) "!> _ HΦ".
  iNamed "Htuple".
  wp_call.

  (***********************************************************)
  (* tuple.latch.Lock()                                      *)
  (***********************************************************)
  wp_loadField.
  wp_apply (acquire_spec with "Hlock").
  iIntros "[Hlocked HtupleOwn]".
  iNamed "HtupleOwn".
  wp_pures.

  (***********************************************************)
  (* for tid > tuple.tidlast && tuple.owned {                *)
  (*     tuple.rcond.Wait()                                  *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool),
             (∃ (owned : bool) (tidlast tidgc : u64) (vers : list pver) (vchain : list dbval),
                 "Hphys" ∷ own_tuple_phys tuple owned tidlast vers ∗
                 "Habst" ∷ own_tuple_repr key tidlast tidgc vers vchain γ ∗
                 "Hlocked" ∷ locked #latch ∗
                 "Hptuple" ∷ ptuple_auth γ (if owned then (1 / 4) else (1 / 2))%Qp key vchain ∗
                 "%Hexit" ∷ if b then ⌜True⌝ else ⌜owned = false ∨ (uint.Z tid) ≤ (uint.Z tidlast)⌝)%I.
  wp_apply (wp_forBreak_cond P with "[] [-HΦ]").
  { (* Loop body preserves the invariant. *)
    clear Φ.
    clear owned tidlast tidgc vers vchain.
    iIntros (Φ) "!> Hloop HΦ".
    iNamed "Hloop".
    iNamed "Hphys".
    wp_pures.
    (* Evaluate the first condition. *)
    wp_loadField.
    wp_pures.
    wp_bind (If #(bool_decide _) _ _).
    wp_if_destruct; last first.
    { (* Exit the loop due to the first condition. *)
      wp_if_false.
      iApply "HΦ".
      do 5 iExists _.
      iFrame "Hlocked Habst".
      iFrame "Hptuple".
      iSplitR ""; first eauto 10 with iFrame.
      iPureIntro. right. word.
    }
    (* Evaluate the second condition. *)
    wp_loadField.
    wp_if_destruct; last first.
    { (* Exit the loop due to the second condition. *)
      iApply "HΦ".
      do 5 iExists _.
      iFrame "Hlocked Habst".
      iSplitR "Hptuple"; first eauto 10 with iFrame.
      iFrame "Hptuple".
      iPureIntro. by left.
    }
    wp_pures.
    (* Evaluate the loop body. *)
    wp_loadField.
    wp_apply (wp_condWait with "[-HΦ]").
    { eauto 15 with iFrame. }
    iIntros "[Hlocked HtupleOwn]".
    iNamed "HtupleOwn".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    unfold P.
    eauto 15 with iFrame.
  }
  { (* The invariant holds at the start. *)
    unfold P.
    eauto 10 with iFrame.
  }
  clear owned tidlast tidgc vers vchain.
  iIntros "Hloop".
  iNamed "Hloop".
  iNamed "Hphys".
  iNamed "Habst".
  iNamed "Hwellformed".
  wp_pures.

  iModIntro.
  iApply "HΦ".
  iFrame "Hptuple".
  iSplitL "Hlocked"; first by eauto 10 with iFrame.
  iSplit; first by eauto 20 with iFrame.
  iPureIntro.
  destruct Hexit; [by left | word].
Qed.

(**
 * Notes (A) about the preconditions:
 * 1. [mvcc_inv_gc] and [active_tid] are used to deduce that [tidgc ≤ tid] (see
 * B-2).
 * 2. [own_tuple_read] consists of physical states and their relation to logical
 * state.
 * 3. [ptuple_auth_owned] consists of extended logical state.
 * 4. The last one comes from waiting on the CV.
 *
 * Notes (B) about the postcondition [ptuple_ptsto]:
 * 1. [ptuple_ptsto] in the postcondition can be obtained by applying the
 * invariant (i.e., [HtupleAbs]) between the logical and physical version chains
 * to reading a physical verison.
 * 2. However, when GC is involved, the invariant holds only for those physical
 * versions created after a certain tid (i.e., [tidlbN] in [own_tuple]). Thus,
 * we need a proof of [tidlbN ≤ (uint.nat tid)] in order to apply the invariant,
 * which can be deduced from [active_tid γ sid tid] and [min_tid_lb γ tidlbN].
 *)
(*****************************************************************)
(* func (tuple *Tuple) ReadVersion(tid uint64) (string, bool)    *)
(*****************************************************************)
Theorem wp_tuple__ReadVersion
        tuple (tid : u64) (key : u64) (sid : u64) (owned : bool)
        (vchain : list dbval) γ :
  {{{ active_tid γ tid sid ∗
      is_tuple_locked tuple key γ ∗
      own_tuple_read tuple key owned vchain γ ∗
      ptuple_auth_owned γ key owned (extend (S (uint.nat tid)) vchain) ∧
      ⌜owned = false ∨ (uint.nat tid < length vchain)%nat⌝
  }}}
    Tuple__ReadVersion #tuple #tid
  {{{ (val : string) (found : bool), RET (#(LitString val), #found);
      active_tid γ tid sid ∗ ptuple_ptsto γ key (to_dbval found val) (uint.nat tid)
  }}}.
Proof.
  iIntros (Φ) "(Hactive & Htuple & HtupleOwn & Hptuple & %Hwait) HΦ".
  wp_call.

  (***********************************************************)
  (* ver := findVersion(tid, tuple.vers)                     *)
  (***********************************************************)
  iNamed "HtupleOwn".
  iNamed "Hphys".
  iNamed "Hrepr".
  iNamed "Hwellformed".
  iNamed "Htuple".
  wp_loadField.
  iApply fupd_wp.
  iInv "Hinvgc" as ">HinvgcO" "HinvgcC".
  iDestruct (active_ge_min with "HinvgcO Hactive Hgclb") as "%HtidGe".
  iAssert (⌜uint.Z tid > 0⌝)%I with "[Hactive]" as "%HtidGZ".
  { iDestruct "Hactive" as "[_ %H]". iPureIntro. word. }
  iMod ("HinvgcC" with "HinvgcO") as "_".
  iModIntro.
  wp_apply (wp_findVersion with "[$HversS]").
  { iPureIntro.
    setoid_rewrite Exists_exists in HexistsLt.
    apply HexistsLt; word.
  }
  iIntros (ver) "[%Hspec HversS]".
  wp_pures.

  (***********************************************************)
  (* if tuple.tidlast < tid {                                *)
  (*     tuple.tidlast = tid                                 *)
  (* }                                                       *)
  (***********************************************************)
  wp_loadField.
  wp_pures.
  wp_apply (wp_If_join_evar with "[Htidlast]").
  { iIntros (b') "%Eb'".
    case_bool_decide.
    { (* Case [tuple.tidlast < tid]. *)
      wp_if_true.
      wp_storeField.
      iSplit; first done.
      (* Update "Htidrd" to use `b'` for merging states. See comments of wp_If_join_evar in control.v. *)
      replace #tid with #(if b' then tid else tidlast) by by rewrite Eb'.
      iNamedAccu.
    }
    { (* Case [tuple.tidlast ≥ tid]. *)
      wp_if_false.
      iModIntro.
      rewrite Eb'.
      by iFrame.
    }
  }
  iIntros "H".
  iNamed "H".
  wp_pures.

  set vchain' := extend _ _.
  iDestruct (vchain_witness with "Hptuple") as "#Hlb".
  unfold ptuple_auth_owned.
  set q := if owned then _ else _.
  repeat rewrite ite_apply.
  set tidlast' := if bool_decide _ then tid else tidlast.
  set P : iProp Σ :=
    ("%Hlen" ∷ ⌜Z.of_nat (length vchain') = (uint.Z tidlast' + 1)%Z⌝ ∗
     "%Hwellformed" ∷ tuple_wellformed vers tidlast' tidgc ∗
     "%HtupleAbs" ∷ (∀ tid, ⌜uint.Z tidgc ≤ uint.Z tid ≤ uint.Z tidlast' ->
                            vchain' !! (uint.nat tid) = Some (spec_lookup vers tid)⌝))%I.
  iAssert P with "[]" as "HP".
  { unfold P.
    subst q.
    destruct owned eqn:E.
    - (* Case 1. [owned = true]. *)
      subst vchain'.
      iPureIntro.
      destruct Hwait as [Howned | Hlen].
      { (* Obtain contradiction from [Howned] and [E]. *) done. }
      replace tidlast' with tidlast; last first.
      { subst tidlast'.
        case_bool_decide; last done.
        (* Obtain contradiction from [Hlen], [H0], and [HvchainLen]. *)
        word.
      }
      replace (extend _ _) with vchain; last first.
      { symmetry. apply extend_length_same. lia. }
      done.
    - (* Case 2. [owned = false]. *)
      subst tidlast'.
      case_bool_decide.
      + (* Case 1a. [tidlast < tid]. Extending the version chain. *)
        (* TODO: negate [del] and use [to_dbval]. *)
        assert (Hfind : spec_find_ver vers tid = spec_find_ver vers tidlast).
        { apply (spec_find_ver_extensible _ tidlast); [word | done | done]. }
        set v' := if ver.1.2 then Nil else Value ver.2.
        assert (Hv' : last vchain = Some v').
        { rewrite Hlast.
          unfold spec_lookup.
          by rewrite -Hfind Hspec.
        }
        (* Obtain a witness that the value at index [tid] is [v']. *)
        iPureIntro.
        split.
        { (* Prove [HvchainLen]. *)
          rewrite extend_length; last by eauto.
          word.
        }
        split.
        { (* Prove [Hwellformed]. *)
          split; last done.
          apply (Forall_impl _ _ _ HtidlastGt).
          word.
        }
        { (* Prove [HtupleAbs]. *)
          intros tidx Hbound.
          subst vchain'.
          rewrite (extend_last_Some _ _ _ Hv').
          destruct (decide (uint.Z tidx ≤ uint.Z tidlast)).
          { (* [x ≤ tidlast]. *)
            rewrite lookup_app_l; last word.
            apply HtupleAbs.
            word.
          }
          { (* [tidlast < x]. *)
            rename n into HxLower.
            apply Znot_le_gt in HxLower.
            rewrite lookup_app_r; last word.
            rewrite lookup_replicate_2; last word.
            f_equal.
            subst v'.
            unfold spec_lookup.
            rewrite (spec_find_ver_extensible _ tidlast tidx tid); [ | word | word | done].
            by rewrite Hspec.
          }
        }
      + (* Case 1b. [tid ≤ tidlast]. *)
        apply Znot_lt_ge, Z.ge_le in H.
        subst vchain'.
        replace (extend _ _) with vchain; last first.
        { symmetry. apply extend_length_same. lia. }
        iPureIntro.
        do 2 (split; first auto).
        by apply HtupleAbs.
  }
  clear HtupleAbs.
  iNamed "HP".
  clear P.

  iAssert (⌜vchain' !! uint.nat tid = Some (spec_lookup vers tid)⌝)%I as "%Hlookup".
  { subst tidlast'.
    iPureIntro.
    case_bool_decide.
    - apply HtupleAbs. word.
    - apply Znot_lt_ge, Z.ge_le in H. apply HtupleAbs. word.
  }

  assert (Hlast' : last vchain' = Some (spec_lookup vers tidlast')).
  { subst vchain' tidlast'.
    case_bool_decide; last by rewrite extend_last.
    rewrite last_lookup.
    rewrite extend_length; last by eauto.
    replace (_ -  _ + _)%nat with (S (uint.nat tid))%nat; last lia.
    by simpl.
  }
  clear Hlast.

  (***********************************************************)
  (* tuple.latch.Unlock()                                    *)
  (***********************************************************)
  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hactive]").
  { iFrame "Hlock Hlocked". eauto 25 with iFrame. }
  wp_pures.
  iModIntro.
  iApply "HΦ".
  iFrame. iExists _.
  iFrame "Hlb". iPureIntro.
  rewrite Hlookup.
  unfold spec_lookup.
  rewrite Hspec.
  destruct (negb ver.1.2) eqn:E.
  - rewrite negb_true_iff in E. by rewrite E.
  - rewrite negb_false_iff in E. by rewrite E.
Qed.

End proof.
