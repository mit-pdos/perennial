From Perennial.program_proof.session Require Export session_prelude.
From Perennial.program_proof.session Require Export coq_session.

Section heap.
  Context `{hG: !heapGS Σ}.

  Lemma wp_deleteAtIndexOperation (s: Slice.t) (index: w64) (l: list Operation.t) (n: nat) :
    {{{
        ⌜0 <= uint.nat index < length l⌝ ∗   
        operation_slice s l n
    }}}
      deleteAtIndexOperation s #index
    {{{
        (ns: Slice.t), RET slice_val (ns);
        operation_slice ns (coq_deleteAtIndexOperation l (uint.nat index)) n
    }}}.
  Proof. (*
    iIntros (Φ) "(%H & H) H2".
    unfold deleteAtIndexOperation.
    wp_pures.
    unfold operation_slice. unfold operation_slice'.
    assert (uint.nat index < length l)%nat by word.
    apply list_lookup_lt in H0 as [x _].
    iDestruct "H" as "(%ops & H & H1)".
    iDestruct (big_sepL2_length with "H1") as "%len".
    iDestruct (own_slice_sz with "H") as %Hsz.
    wp_apply wp_NewSlice_0. iIntros (s') "H3".
    wp_apply wp_ref_to; auto.
    iIntros (l1) "H4".
    wp_pures. wp_bind (SliceAppendSlice _ _ _).
    iDestruct (own_slice_wf with "H") as %Hcap.
    wp_apply (wp_SliceTake); try word.
    wp_load.
    iDestruct "H" as "[H H5]".
    iDestruct (slice_small_split with "H") as "[H H6]". { assert (uint.Z index <= length ops) by word. eassumption. }
    wp_apply (wp_SliceAppendSlice with "[H H3]"); auto. { iFrame. }
    iIntros (s'') "[H H7]".
    wp_store.
    wp_apply (wp_SliceSkip); try word.
    wp_load.
    wp_apply (wp_SliceAppendSlice with "[H H6]"); auto.
    - iFrame. iDestruct (slice_small_split with "H6") as "[H6 H7]".
      + assert (uint.Z 1 <= length (drop (uint.nat index) ops)).
         { rewrite length_drop. word. } eassumption.
      + assert ((W64 1) = (w64_word_instance.(word.sub) (w64_word_instance.(word.add) index (W64 1)) (index))) by word. rewrite H0. destruct (slice_skip_skip (w64_word_instance.(word.add) index (W64 1)) index s (struct.t Operation)); try word. rewrite <- H0. iApply "H7".
    - iIntros (s''') "[H H6]". wp_pures. iApply "H2".
      iExists (([] ++ take (uint.nat index) ops) ++ drop (uint.nat (W64 1)) (drop (uint.nat index) ops)). simpl.
      iSplit. *)
  Admitted.

  Lemma wp_deleteAtIndexMessage (s: Slice.t) (index: w64) (l: list Message.t) (n: nat) :
    {{{
      ⌜0 <= uint.nat index < length l⌝ ∗   
      message_slice s l n
    }}}
      deleteAtIndexMessage s #index
    {{{
        (ns: Slice.t), RET slice_val (ns);
        message_slice ns (coq_deleteAtIndexMessage l (uint.nat index)) n
    }}}.
  Proof.
  Admitted.
  
  Lemma wp_getDataFromOperationLog (s: Slice.t) (l: list Operation.t) (n: nat) :
    {{{
        operation_slice s l n
    }}}
      getDataFromOperationLog s
    {{{
        r , RET #r;
        ⌜r = coq_getDataFromOperationLog l⌝
    }}}.
  Proof.
  Admitted.

  Lemma wp_equalOperations (opv1: Slice.t*u64) (o1: Operation.t) (opv2: Slice.t*u64) (o2: Operation.t) (n: nat) :
    {{{
          is_operation opv1 o1 n ∗
          is_operation opv2 o2 n
    }}}
      equalOperations (operation_val opv1) (operation_val opv2)
    {{{ r , RET #r;
        ⌜r = coq_equalOperations o1 o2⌝
    }}}.
  Proof.
  Admitted.

  Lemma wp_mergeOperations (s1 s2: Slice.t) (l1 l2: list Operation.t) (n: nat) :
    {{{
          operation_slice s1 l1 n ∗
          operation_slice s2 l2 n 
    }}}
      mergeOperations s1 s2 
      {{{
            (ns: Slice.t), RET slice_val (ns);
            ∃ nxs, operation_slice ns nxs n ∗
                   ⌜nxs = coq_mergeOperations l1 l2⌝
      }}}.
  Proof.
  Admitted.

End heap.
