From Perennial.program_proof.rsm.pure Require Import serialize.
From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program.util Require Import
  decode_string decode_strings.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Opaque u64_le.

(* Copy pasted from grove_ffi_typed.v *)
Ltac inv_undefined :=
  match goal with
  | [ H: relation.denote (match ?e with | _ => _ end) _ _ _ |- _ ] =>
    destruct e; try (apply suchThat_false in H; contradiction)
  end.
Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
  [ apply heap_base_atomic; cbn [relation.denote base_trans]; intros * H;
    repeat inv_undefined;
    try solve [ apply atomically_is_val in H; auto ]
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].
Local Ltac solve_atomic2 :=
  solve_atomic;
  (* TODO(Joe): Cleanup *)
  repeat match goal with
    | [ H: relation.denote _ ?s1 ?s2 ?v |- _ ] => inversion_clear H
    | _ => progress monad_inv
    | _ => case_match
    end; eauto.

Section resume.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Lemma paxos_recoverable_from_wal
    (nidme : u64) (termc terml lsnc : nat) (logn : list byte_string) (wal : list pxcmd)
    nids γ :
    nidme ∈ nids ->
    own_current_term_half γ nidme termc -∗
    own_ledger_term_half γ nidme terml -∗
    own_committed_lsn_half γ nidme lsnc -∗
    own_node_ledger_half γ nidme logn -∗
    own_node_wal_half γ nidme wal -∗
    paxos_inv γ nids -∗
    ⌜execute_paxos_cmds wal = PaxosState termc terml lsnc logn⌝.
  Proof.
    iIntros (Hnidme) "HtermcX HtermlX HlsncX HlognX HwalX Hinv".
    iNamed "Hinv".
    rewrite -Hdomtermlm elem_of_dom in Hnidme.
    destruct Hnidme as [terml0 Hlookup].
    iDestruct (big_sepM_lookup with "Hnodes") as "Hnode".
    { apply Hlookup. }
    iNamed "Hnode".
    iDestruct (current_term_agree with "HtermcX Htermc") as %->.
    iDestruct (ledger_term_agree with "HtermlX Hterml") as %->.
    iDestruct (committed_lsn_agree with "HlsncX Hlsnc") as %->.
    iDestruct (node_ledger_agree with "HlognX Hlogn") as %->.
    by iDestruct (node_wal_agree with "HwalX Hwalnode") as %->.
  Qed.

  Theorem wp_resume
    (fname : byte_string) (nidme termc terml lsnc : u64) (log : list byte_string)
    nids γ :
    let dst := PaxosDurable termc terml log lsnc in
    nidme ∈ nids ->
    is_node_wal_fname γ nidme fname -∗
    know_paxos_inv γ nids -∗
    know_paxos_file_inv γ nids -∗
    {{{ own_crash_ex pxcrashNS (own_paxos_durable γ nidme) dst
    }}}
      resume #(LitString fname)
    {{{ (logP : Slice.t), RET (#termc, #terml, #lsnc, to_val logP);
        own_crash_ex pxcrashNS (own_paxos_durable γ nidme) dst ∗
        own_slice logP stringT (DfracOwn 1) log
    }}}.
  Proof.
    iIntros (dst Hnidme) "#Hfname #Hinv #Hinvfile".
    iIntros (Φ) "!> Hdurable HΦ".
    wp_rec.

    (*@ func resume(fname string) (uint64, uint64, uint64, []string) {          @*)
    (*@     var termc uint64                                                    @*)
    (*@     var terml uint64                                                    @*)
    (*@     var lsnc  uint64                                                    @*)
    (*@     var log = make([]string, 0)                                         @*)
    (*@                                                                         @*)
    wp_apply wp_ref_of_zero; first done.
    iIntros (termcP) "HtermcP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (termlP) "HtermlP".
    wp_apply wp_ref_of_zero; first done.
    iIntros (lsncP) "HlsncP".
    wp_apply wp_NewSlice.
    iIntros (logP) "HlogP".
    rewrite uint_nat_W64_0 /=.
    wp_apply wp_ref_to; first done.
    iIntros (logPP) "HlogPP".

    (*@     var data = grove_ffi.FileRead(fname)                                @*)
    (*@                                                                         @*)
    wp_pures.
    wp_rec. wp_pures.
    wp_bind (ExternalOp _ _).
    iApply (wp_ncatomic _ _ ∅).
    { solve_atomic2. }
    iMod (own_crash_ex_open with "Hdurable") as "[> Hdurable HdurableC]".
    { solve_ndisj. }
    iNamed "Hdurable".
    (* Open the file invariant to obtain (1) the file points-to, (2) encoding
    relation between the file content and the WAL log. *)
    iInv "Hinvfile" as "> HinvfileO" "HinvfileC".
    iDestruct (big_sepS_elem_of_acc with "HinvfileO") as "[Hinvnode HinvnodeC]".
    { apply Hnidme. }
    iNamed "Hinvnode".
    iDestruct (node_wal_fname_agree with "Hfname Hwalfname") as %->.
    (* Open the core invariant to obtain (1) the durable resources (e.g.,
    [own_current_term_half]), (2) the recovery relation between the WAL log and
    the durable resources. *)
    iInv "Hinv" as "> HinvO" "HinvC".
    iDestruct (paxos_recoverable_from_wal with
                "Htermc Hterml Hlsnc Hlogn Hwalfile HinvO") as %Hwal.
    { apply Hnidme. }
    (* Read the WAL file. *)
    iApply ncfupd_mask_intro; first solve_ndisj.
    iIntros "Hmask".
    wp_apply (wp_FileReadOp with "Hfile").
    iIntros (err p len) "[Hfile HdataP]".
    (* Close the core invariant. *)
    iMod "Hmask" as "_".
    iMod ("HinvC" with "HinvO") as "_".
    iDestruct ("HinvnodeC" with "[Hwalfile Hfile]") as "HinvfileO".
    { iFrame "∗ # %". }
    iMod ("HinvfileC" with "HinvfileO") as "_".
    iMod ("HdurableC" $! dst with "[$Htermc $Hterml $Hlogn $Hlsnc]") as "Hdurable".
    iModIntro.
    destruct err; wp_pures.
    { wp_apply wp_Exit. iIntros "[]". }
    iDestruct "HdataP" as "[%Hlen HdataP]".
    set dataP := Slice.mk p len len.
    iDestruct (pointsto_vals_own_slice_small_byte dataP with "HdataP") as "Hdata".
    { done. }
    { simpl. word. }
    wp_apply wp_ref_to.
    { apply (slice_val_ty dataP). }
    iIntros (dataPP) "HdataPP".
    wp_pures.

    (*@     for 0 < uint64(len(data)) {                                         @*)
    (*@         kind, data = marshal.ReadInt(data)                              @*)
    (*@                                                                         @*)
    set P := (λ cont : bool,
                ∃ (q : Slice.t) (applied remaining : list w8) (wala walr : list pxcmd)
                  (termca termla lsnca : u64) (logaP : Slice.t) (loga : list byte_string),
                  let pxst := PaxosState (uint.nat termca) (uint.nat termla) (uint.nat lsnca) loga in
                  "HdataPP" ∷ dataPP ↦[slice.T byteT] q ∗
                  "Hdata"   ∷ own_slice_small q byteT (DfracOwn 1) remaining ∗
                  "HtermcP" ∷ termcP ↦[uint64T] #termca ∗
                  "HtermlP" ∷ termlP ↦[uint64T] #termla ∗
                  "HlsncP"  ∷ lsncP ↦[uint64T] #lsnca ∗
                  "HlogPP"  ∷ logPP ↦[slice.T stringT] (to_val logaP) ∗
                  "HlogP"   ∷ own_slice logaP stringT (DfracOwn 1) loga ∗
                  "%Hwalar" ∷ ⌜wal = wala ++ walr⌝ ∗
                  (* TODO: is [Hwala] unnecessary? *)
                  "%Hwala"  ∷ ⌜encode_paxos_cmds wala = applied⌝ ∗
                  "%Hwalr"  ∷ ⌜encode_paxos_cmds walr = remaining⌝ ∗
                  "%Hexec"  ∷ ⌜execute_paxos_cmds wala = pxst⌝ ∗
                  "%Hcont"  ∷ ⌜if cont then True else length remaining = O⌝)%I.
    wp_apply (wp_forBreak_cond P with
               "[] [HdataPP Hdata $HtermcP $HtermlP $HlsncP $HlogPP $HlogP]");
      last first; first 1 last.
    { iExists dataP.
      iFrame.
      iPureIntro. simpl.
      by exists [], [], wal.
    }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      wp_apply wp_slice_len.
      wp_pures.
      iDestruct (own_slice_small_sz with "Hdata") as %Hlenr.
      case_bool_decide as Hbound; wp_pures; last first.
      { iApply "HΦ".
        iFrame "∗ %".
        iPureIntro.
        clear -Hbound Hlenr. word.
      }
      assert (Hrem : length remaining ≠ O).
      { clear -Hbound Hlenr. word. }
      destruct walr as [| cmd walr'] eqn:Hwalreq.
      { apply length_not_nil_inv in Hrem.
        by rewrite /encode_paxos_cmds serialize_nil in Hwalr.
      }
      wp_load.
      assert (Hvdcmd : valid_wal_entry cmd).
      { rewrite Forall_forall in Hvdwal.
        apply Hvdwal.
        rewrite Hwalar.
        set_solver.
      }
      rewrite -Hwalr.
      rewrite /encode_paxos_cmds serialize_cons.
      destruct cmd eqn:Hcmd; rewrite {1}/encode_paxos_cmd /encode_paxos_extend -app_assoc.
      { (* Case: Extend. *)

        (*@         if kind == CMD_EXTEND {                                         @*)
        (*@             ents, bs1 := util.DecodeStrings(bs)                         @*)
        (*@             data = bs1                                                  @*)
        (*@             // Apply extend.                                            @*)
        (*@             log = append(log, ents...)                                  @*)
        (*@                                                                         @*)
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (q') "Hdata".
        wp_apply (wp_DecodeStrings with "Hdata").
        iIntros (s bs1) "[Hents Hdata]".
        wp_store.
        wp_load.
        iDestruct (own_slice_to_small with "Hents") as "Hents".
        wp_apply (wp_SliceAppendSlice with "[$HlogP $Hents]"); first done.
        iIntros (logaP') "[HlogP Hents]".
        wp_store.
        iApply "HΦ".
        iFrame "HlogPP ∗".
        iPureIntro. simpl.
        exists (applied ++ encode_paxos_cmd cmd), (wala ++ [cmd]), walr'.
        split.
        { by rewrite Hwalar -app_assoc Hcmd. }
        split.
        { by rewrite encode_paxos_cmds_snoc Hwala. }
        split; first done.
        split.
        { by rewrite execute_paxos_cmds_snoc Hexec Hcmd /=. }
        done.
      }
      { (* Case: Append. *)

        (*@         } else if kind == CMD_APPEND {                                  @*)
        (*@             ent, bs1 := util.DecodeString(bs)                           @*)
        (*@             data = bs1                                                  @*)
        (*@             // Apply append.                                            @*)
        (*@             log = append(log, ent)                                      @*)
        (*@                                                                         @*)
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (q') "Hdata".
        wp_apply (wp_DecodeString with "Hdata").
        iIntros (bs1) "Hdata".
        wp_store.
        wp_load.
        wp_apply (wp_SliceAppend with "[$HlogP]").
        iIntros (logaP') "HlogP".
        wp_store.
        iApply "HΦ".
        iFrame "HlogPP ∗".
        iPureIntro. simpl.
        exists (applied ++ encode_paxos_cmd cmd), (wala ++ [cmd]), walr'.
        split.
        { by rewrite Hwalar -app_assoc Hcmd. }
        split.
        { by rewrite encode_paxos_cmds_snoc Hwala. }
        split; first done.
        split.
        { by rewrite execute_paxos_cmds_snoc Hexec Hcmd /=. }
        done.
      }
      { (* Case: Prepare. *)

        (*@         } else if kind == CMD_PREPARE {                                 @*)
        (*@             term, bs1 := marshal.ReadInt(bs)                            @*)
        (*@             data = bs1                                                  @*)
        (*@             // Apply prepare.                                           @*)
        (*@             termc = term                                                @*)
        (*@                                                                         @*)
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (q') "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs1) "Hdata".
        do 2 wp_store.
        iApply "HΦ".
        iFrame "HlogPP ∗".
        iPureIntro. simpl.
        exists (applied ++ encode_paxos_cmd cmd), (wala ++ [cmd]), walr'.
        split.
        { by rewrite Hwalar -app_assoc Hcmd. }
        split.
        { by rewrite encode_paxos_cmds_snoc Hwala. }
        split; first done.
        split.
        { (* Prove [term] fit into u64. *)
          simpl in Hvdcmd.
          rewrite execute_paxos_cmds_snoc Hexec Hcmd /=.
          f_equal.
          clear -Hvdcmd. word.
        }
        done.
      }
      { (* Case: Advance. *)

        (*@         } else if kind == CMD_ADVANCE {                                 @*)
        (*@             term, bs1 := marshal.ReadInt(bs)                            @*)
        (*@             lsn, bs2 := marshal.ReadInt(bs1)                            @*)
        (*@             ents, bs3 := util.DecodeStrings(bs2)                        @*)
        (*@             data = bs3                                                  @*)
        (*@             // Apply advance.                                           @*)
        (*@             terml = term                                                @*)
        (*@             // Prove safety of this triming operation using well-formedness of @*)
        (*@             // the write-ahead log. See [execute_paxos_advance] in recovery.v. @*)
        (*@             log = log[: lsn]                                            @*)
        (*@             log = append(log, ents...)                                  @*)
        (*@                                                                         @*)
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (q') "Hdata".
        iEval list_simplifier in "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs1) "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs2) "Hdata".
        wp_apply (wp_DecodeStrings with "Hdata").
        iIntros (s bs3) "[Hents Hdata]".
        do 2 wp_store.
        wp_load.
        assert (Hsafetrim : (lsn ≤ length loga)%nat).
        { unshelve epose proof (execute_paxos_cmds_prefix_not_stuck (wala ++ [cmd]) wal _ _) as Hns.
          { rewrite Hwalar Hcmd.
            apply prefix_app, prefix_cons, prefix_nil.
          }
          { by rewrite Hwal. }
          rewrite execute_paxos_cmds_snoc Hexec Hcmd in Hns.
          rewrite /execute_paxos_cmds /execute_paxos_cmd in Hns.
          by apply execute_paxos_advance_safely_trimmed in Hns.
        }
        wp_apply (wp_SliceTake_full with "HlogP").
        { clear -Hsafetrim. word. }
        iIntros "HlogP".
        wp_store.
        wp_load.
        iDestruct (own_slice_to_small with "Hents") as "Hents".
        wp_apply (wp_SliceAppendSlice with "[$HlogP $Hents]"); first done.
        iIntros (logaP') "[HlogP Hents]".
        wp_store.
        iApply "HΦ".
        iFrame "HlogPP ∗".
        iPureIntro. simpl.
        exists (applied ++ encode_paxos_cmd cmd), (wala ++ [cmd]), walr'.
        split.
        { by rewrite Hwalar -app_assoc Hcmd. }
        split.
        { by rewrite encode_paxos_cmds_snoc Hwala. }
        split; first done.
        split.
        { (* Prove [term] and [lsn] fit into u64. *)
          simpl in Hvdcmd.
          rewrite execute_paxos_cmds_snoc Hexec Hcmd /=.
          case_decide; last word.
          replace (uint.nat (W64 lsn)) with lsn; last first.
          { clear -Hvdcmd. word. }
          f_equal.
          clear -Hvdcmd. word.
        }
        done.
      }
      { (* Case: Accept. *)

        (*@         } else if kind == CMD_ACCEPT {                                  @*)
        (*@             lsn, bs1 := marshal.ReadInt(bs)                             @*)
        (*@             ents, bs2 := util.DecodeStrings(bs1)                        @*)
        (*@             data = bs2                                                  @*)
        (*@             // Apply accept.                                            @*)
        (*@             // Prove safety of this triming operation using well-formedness of @*)
        (*@             // the write-ahead log. See [execute_paxos_accept] in recovery.v. @*)
        (*@             log = log[: lsn]                                            @*)
        (*@             log = append(log, ents...)                                  @*)
        (*@                                                                         @*)
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (q') "Hdata".
        iEval list_simplifier in "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs1) "Hdata".
        wp_apply (wp_DecodeStrings with "Hdata").
        iIntros (s bs3) "[Hents Hdata]".
        wp_store.
        wp_load.
        assert (Hsafetrim : (lsn ≤ length loga)%nat).
        { unshelve epose proof (execute_paxos_cmds_prefix_not_stuck (wala ++ [cmd]) wal _ _) as Hns.
          { rewrite Hwalar Hcmd.
            apply prefix_app, prefix_cons, prefix_nil.
          }
          { by rewrite Hwal. }
          rewrite execute_paxos_cmds_snoc Hexec Hcmd in Hns.
          rewrite /execute_paxos_cmds /execute_paxos_cmd in Hns.
          by apply execute_paxos_accept_safely_trimmed in Hns.
        }
        wp_apply (wp_SliceTake_full with "HlogP").
        { clear -Hsafetrim. word. }
        iIntros "HlogP".
        wp_store.
        wp_load.
        iDestruct (own_slice_to_small with "Hents") as "Hents".
        wp_apply (wp_SliceAppendSlice with "[$HlogP $Hents]"); first done.
        iIntros (logaP') "[HlogP Hents]".
        wp_store.
        iApply "HΦ".
        iFrame "HlogPP ∗".
        iPureIntro. simpl.
        exists (applied ++ encode_paxos_cmd cmd), (wala ++ [cmd]), walr'.
        split.
        { by rewrite Hwalar -app_assoc Hcmd. }
        split.
        { by rewrite encode_paxos_cmds_snoc Hwala. }
        split; first done.
        split.
        { (* Prove [lsn] fit into u64. *)
          simpl in Hvdcmd.
          rewrite execute_paxos_cmds_snoc Hexec Hcmd /=.
          case_decide; last word.
          replace (uint.nat (W64 lsn)) with lsn; last first.
          { clear -Hvdcmd. word. }
          done.
        }
        done.
      }
      { (* Case: Expand. *)

        (*@         } else if kind == CMD_EXPAND {                                  @*)
        (*@             lsn, bs1 := marshal.ReadInt(bs)                             @*)
        (*@             data = bs1                                                  @*)
        (*@             // Apply expand.                                            @*)
        (*@             lsnc = lsn                                                  @*)
        (*@         }                                                               @*)
        (*@                                                                         @*)
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (q') "Hdata".
        wp_apply (wp_ReadInt with "Hdata").
        iIntros (bs1) "Hdata".
        do 2 wp_store.
        iApply "HΦ".
        iFrame "HlogPP ∗".
        iPureIntro. simpl.
        exists (applied ++ encode_paxos_cmd cmd), (wala ++ [cmd]), walr'.
        split.
        { by rewrite Hwalar -app_assoc Hcmd. }
        split.
        { by rewrite encode_paxos_cmds_snoc Hwala. }
        split; first done.
        split.
        { (* Prove [lsn] fit into u64. *)
          simpl in Hvdcmd.
          rewrite execute_paxos_cmds_snoc Hexec Hcmd /=.
          f_equal.
          clear -Hvdcmd. word.
        }
        done.
      }
    }

    (*@     return termc, terml, lsnc, log                                      @*)
    (*@ }                                                                       @*)
    iNamed 1.
    do 4 wp_load.
    wp_pures.
    assert (walr = []) as ->.
    { apply encode_paxos_cmds_nil_inv, nil_length_inv.
      by rewrite Hwalr.
    }
    rewrite app_nil_r in Hwalar. subst wala.
    rewrite Hwal in Hexec.
    inv Hexec.
    rewrite -(uint_nat_u64_inj _ _ H0).
    rewrite -(uint_nat_u64_inj _ _ H1).
    rewrite -(uint_nat_u64_inj _ _ H2).
    iApply ("HΦ" $! logaP).
    by iFrame.
  Qed.

End resume.
