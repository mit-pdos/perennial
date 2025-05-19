From New.proof Require Import proof_prelude.

From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_inv.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_base.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!IntoVal T'} `{!IntoValTyped T' T} `{Hbounded: BoundedTypeSize T}.


Lemma add_one_lemma_1 : forall slice (first : u64) (count : u64) (e : T') ,
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  subslice (uint.nat first) (uint.nat first + uint.nat count)
  (<[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice ++
   <[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice) = subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).
Proof.
  intuition.
  assert (uint.nat first + uint.nat count < length slice ∨ (length slice <= uint.nat first + uint.nat count < length slice + length slice)).
  { word. }
  destruct H3.
  - replace (Z.to_nat(uint.Z (word.add first count) `mod` length slice)) with (uint.nat(uint.nat first + uint.nat count)).
    + rewrite subslice_take_drop.
      rewrite subslice_take_drop.
      rewrite take_app_le.
      2: { rewrite length_insert. word. }
      rewrite take_app_le.
      2: { word. }
      rewrite take_insert.
      { done. }
      word.
    + rewrite Z.mod_small; word.
  - replace (Z.to_nat(uint.Z (word.add first count) `mod` length slice)) with (uint.nat(uint.nat first + uint.nat count - length slice)).
    + epose proof (subslice_split_r (uint.nat first) (length slice) _ (_ ++ _)).
      rewrite H4.
      2: word.
      2: { rewrite length_app. rewrite length_insert. word. }
      epose proof (subslice_split_r (uint.nat first) (length slice) _ (slice ++ slice)).
      rewrite H5.
      2: word.
      2: { rewrite length_app. word. }
      assert (subslice (uint.nat first) (length slice)
      (<[uint.nat
           (uint.nat first + uint.nat count -
            length slice):=e]> slice ++
       <[uint.nat
           (uint.nat first + uint.nat count -
            length slice):=e]> slice) = subslice (uint.nat first) (length slice)
            (slice ++ slice)).
        {
          rewrite <- subslice_before_app_eq.
          2: { rewrite length_insert. word. }
          rewrite <- subslice_before_app_eq.
          2: word.
          rewrite subslice_take_drop.
          rewrite subslice_take_drop.
          epose proof (length_insert slice (uint.nat (uint.nat first + uint.nat count - length slice)) e).
          rewrite firstn_all.
          replace ((take (length slice)
          (<[uint.nat
               (uint.nat first + uint.nat count -
                length slice):=e]> slice))) with (take (length (<[uint.nat
                (uint.nat first + uint.nat count -
                 length slice):=e]> slice))
                (<[uint.nat
                     (uint.nat first + uint.nat count -
                      length slice):=e]> slice)).
          2: { rewrite H6. eauto. }
          rewrite firstn_all.
          rewrite drop_insert_gt. 
          {done. }
          word.
        }
      rewrite H6.
      rewrite app_inv_head_iff.
      rewrite subslice_comm.
      rewrite subslice_comm.
      rewrite drop_app_length.
      epose proof (length_insert slice (uint.nat (uint.nat first + uint.nat count - length slice)) e).
      replace ((drop (length slice)
                (<[uint.nat (uint.nat first + uint.nat count - length slice):=e]> slice ++
                <[uint.nat (uint.nat first + uint.nat count - length slice):=e]> slice))) with (drop (length (<[uint.nat
                (uint.nat first + uint.nat count -
                 length slice):=e]> slice))
                 (<[uint.nat (uint.nat first + uint.nat count - length slice):=e]> slice ++
                 <[uint.nat (uint.nat first + uint.nat count - length slice):=e]> slice)).
      2: { rewrite H7. eauto. }
      rewrite drop_app_length.
      rewrite take_insert.
      { eauto. }
      word.
    + rewrite -(Z_mod_plus_full _ (-1)).
      rewrite Z.mod_small; word.
  Unshelve.
  { 
  exact T'. }
  { exact (uint.nat first + uint.nat count)%nat. }
  { exact (<[uint.nat
  (uint.nat first + uint.nat count - length slice)%Z:=e]>
slice). }
  { exact (<[uint.nat
  (uint.nat first + uint.nat count - length slice)%Z:=e]>
slice). }
  exact (uint.nat first + uint.nat count)%nat.
Qed.

Lemma add_one_lemma_2 : forall slice (first : u64) (count : u64) (e : T'),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  subslice (uint.nat first + uint.nat count) (uint.nat first + Z.to_nat(uint.Z count + 1))
  (<[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice ++
   <[Z.to_nat (uint.Z (word.add first count) `mod` length slice):=e]>
     slice) = [e].
Proof.
  intuition.
  assert (uint.nat first + uint.nat count < length slice ∨ (length slice <= uint.nat first + uint.nat count < length slice + length slice)).
  { word. }
  destruct H3.
  - replace (Z.to_nat(uint.Z (word.add first count) `mod` length slice)) with (uint.nat(uint.nat first + uint.nat count)).
    + rewrite subslice_comm.
      rewrite drop_app_le.
      2: { rewrite length_insert. word. }
      rewrite drop_insert_le.
      2: { word. }
      assert ((uint.nat (uint.nat first + uint.nat count)%Z -
      (uint.nat first + uint.nat count))%nat = uint.nat 0).
      { word. }
      rewrite H4.
      match goal with
        | |- context [take ?n _] => replace n with 1%nat
      end.
      { rewrite insert_take_drop.
        { rewrite take_0.
          rewrite app_nil_l.
          rewrite firstn_cons.
          rewrite take_0.
          done.
        }
        rewrite length_drop.
        word.
      }
      word.
    + rewrite Z.mod_small; word.
  - replace (Z.to_nat(uint.Z (word.add first count) `mod` length slice)) with (uint.nat(uint.nat first + uint.nat count - length slice)).
    + rewrite subslice_comm.
      rewrite drop_app_ge.
      2: { rewrite length_insert. word. }
      rewrite length_insert.
      rewrite drop_insert_le.
      2: { word. }
      assert ((uint.nat (uint.nat first + uint.nat count - length slice)%Z -
      (uint.nat first + uint.nat count - length slice))%nat = uint.nat 0).
      { word. }
      rewrite H4.
      match goal with
        | |- context [take ?n _] => replace n with 1%nat
      end.
      { rewrite insert_take_drop.
        { rewrite take_0.
          rewrite app_nil_l.
          rewrite firstn_cons.
          rewrite take_0.
          done.
        }
        rewrite length_drop.
        word.
      }
      word.
      + rewrite -(Z_mod_plus_full _ (-1)).
        rewrite Z.mod_small; word.
Qed.

Theorem add_one : forall slice (first : u64) (count : u64) (e: T'), 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  valid_elems (<[uint.nat (word.modu ((word.add) first count) (length slice)):= e]> slice) first (word.add count 1) 
  = valid_elems slice first count ++ [e].
Proof.
  intuition.
  unfold valid_elems.
  rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
    ?word.unsigned_modu_nowrap, ?word.unsigned_of_Z; [ | word .. ].
  rewrite -> !wrap_small by word.
  replace (uint.Z (W64 (length _))) with (Z.of_nat (length slice)) by word.
  rewrite (subslice_split_r (uint.nat first) (uint.nat first + uint.nat count) _ (_ ++ _)).
  - rewrite add_one_lemma_1; eauto.
    rewrite app_inv_head_iff.
    apply add_one_lemma_2; eauto.
  - word.
  - rewrite length_app.
    rewrite length_insert.
    word.
Qed.

Lemma remove_one_lemma_1 : forall slice (first : u64) (e : T'),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  slice !! uint.nat first = Some e -> 
  subslice (uint.nat first) (uint.nat first + 1) (slice ++ slice) = [e].
Proof.
  intuition.
  rewrite subslice_comm.
  match goal with
    | |- context [take ?n _] => replace n with 1%nat
  end.
  2: { word. }
  rewrite drop_app_le.
  2: word.
  rewrite <- (take_drop_middle (slice) (uint.nat first) e).
  2: eauto.
  rewrite drop_app_length'.
  2: { rewrite length_take. word. }
  rewrite firstn_cons.
  rewrite take_0.
  done.
Qed.

Lemma remove_one_lemma_2 : forall (slice : list T') (first : u64) (count : u64) (e : T'),
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  subslice (uint.nat first + 1) (uint.nat first + uint.nat count) (slice ++ slice) = 
  subslice (Z.to_nat
  (uint.Z (word.add first 1)
    `mod` length slice))
  (Z.to_nat
    (uint.Z (word.add first 1)
    `mod` length slice) + Z.to_nat (uint.Z count - 1)) (slice ++ slice).
Proof.
  intuition.
  assert (uint.Z first < length slice - 1 ∨ uint.Z first = length slice - 1).
  { word. }
  destruct H2.
  - rewrite Z.mod_small. 2: word.
    f_equal; word.
  - rewrite H2.
    replace (Init.Nat.add (Z.to_nat (Z.sub (Datatypes.length slice) 1)) 1) with ((length slice)).
    2: word.
    replace (word.unsigned (word.add first 1)) with (uint.Z (length slice)).
    2: word.
    replace ((uint.Z (length slice) `mod` length slice)) with 0.
    2: { replace (uint.Z _) with (Z.of_nat (length slice)) by word. rewrite Z_mod_same //. word. }
    rewrite subslice_comm.
    rewrite drop_app_length.
    rewrite subslice_comm.
    rewrite drop_0.
    rewrite take_app_le. 2: word.
    f_equal. word.
Qed.

Theorem remove_one : forall slice (first : u64) (count : u64) (e:T'), 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  slice !! uint.nat first = Some e -> 
  valid_elems slice first count = e :: valid_elems slice (word.modu ((word.add) first 1) (length slice)) (word.sub count 1).
Proof.
  intuition.
  unfold valid_elems.
  rewrite -> ?word.unsigned_add, ?word.unsigned_sub,
    ?word.unsigned_modu_nowrap, ?unsigned_U64; [ | word .. ].
  rewrite -> !wrap_small by word.
  replace (uint.Z (W64 (length slice))) with (Z.of_nat (length slice)) by word.
  rewrite (subslice_split_r (uint.nat first) (uint.nat first + 1) _ (_++_)).
  - rewrite (remove_one_lemma_1 slice first e); eauto.
    rewrite app_inv_head_iff.
    apply remove_one_lemma_2; eauto.
  - word.
  - rewrite length_app. word.
Qed.



(*
TODO: Update to use param record and new goose things
Lemma buff_enqueue_logical (ch: loc) (γ: chan_names) 
        (size: nat) (vs: valid_chan_state) (is_single_party: bool) 
        (send_count recv_count: nat) (count: nat) (first: u64) 
        (xs: list T') (new_xs: list T') (v: T') 
        (Psingle: Z -> T' -> iProp Σ) (Pmulti: T' -> iProp Σ) 
        (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ)
        (i: nat) (q: Qp):
      
        count < size ->  
        (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
        size > 0 ->
        size + 1 < 2^63 ->
        count + 1 < 2^63 ->
        new_xs = <[uint.nat (word.modu (word.add first (W64 count)) (W64 size)):=v]> xs ->
        
        "HBuffChLogical" ∷ isBufferedChanLogical ch γ  size vs is_single_party 
          send_count recv_count count first xs Psingle Pmulti Qsingle Qmulti R ∗
        "HP" ∷ P is_single_party i v Psingle Pmulti ∗
        "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗
        "HSndPerm" ∷ own_send_counter_frag γ i q
        
        ==∗
        
        "HBuffChLogical" ∷ isBufferedChanLogical ch γ size vs is_single_party 
          (S send_count) recv_count (count + 1) first new_xs Psingle Pmulti Qsingle Qmulti R ∗
        "HQ" ∷ Q is_single_party (send_count - size) Qsingle Qmulti ∗
        "HSndCtrAuth" ∷ own_send_counter_auth γ (S send_count) false ∗
        "HSndPerm" ∷ own_send_counter_frag γ (S i) q.

        Proof.
          intros Hcount_lt Hsp  Hsize_pos Hsize_bound Hcount_bound Hnew_xs .
          iIntros "(HBuffChLogical & HP & HSndCtrAuth & HSndPerm)".
          
          iDestruct "HBuffChLogical" as "(%HBuffCount & %Hsize & Hsizeinv & HPs & HQs)".
          
          iDestruct "Hsizeinv" as "(%Hcount_le & %Hfirst_lt & %Hsize_pos_old & %Hsize_bound_old & %Hcount_bound_old)".
          
          destruct is_single_party.
          
          - subst q.
            iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Helem".
            subst i.
            iMod (send_counter_update γ send_count send_count with "[$HSndCtrAuth $HSndPerm]") as "[HSndCtrAuth HSndPerm]".
            
            iDestruct (big_sep_seq_pop send_count (size - count) (λ i, Q true (i - size) Qsingle Qmulti)  with "HQs") as "[HQ HQs]".
            { lia. }
            
            iAssert ([∗ list] i↦x ∈ valid_elems new_xs first (W64 (count + 1)), 
                      P true (recv_count + i) x Psingle Pmulti)%I with "[HPs HP]" as "HPs'".
            {

              subst new_xs.
              replace size with (length xs).
              replace (W64 (count + 1)) with (w64_word_instance .(word.add) (W64 count) (W64 1))
              by word.
              rewrite (add_one xs first count v). all: try word.
              {
                rewrite big_sepL_snoc. iFrame.
                replace ((recv_count + length (valid_elems xs first (W64 count))))
                with (Z.of_nat send_count).
                {
                  iFrame.
                }
                unfold valid_elems.
                rewrite subslice_length.
                {
                 word. 
                }
                rewrite length_app. word.
              }
            }
            
            (* Reconstruct buff_size_inv for the new state *)
            iAssert (⌜count + 1 <= size⌝ ∗ 
                     ⌜word.unsigned first < size⌝ ∗ 
                     ⌜size > 0⌝ ∗ 
                     ⌜size + 1 < 2 ^ 63⌝ ∗
                     ⌜count + 1 + 1 < 2 ^ 63⌝)%I as "Hsizeinv".
            {
              iPureIntro.
              repeat split; try assumption; try lia.
            }
            
            (* Reassemble the logical channel state *)
            iModIntro.
            iSplitL "Hsizeinv HPs' HQs".
            {
              unfold isBufferedChanLogical.
              iFrame.
              iSplitL "".
              { iPureIntro. lia. }
              iSplitL "".
              { iPureIntro. subst new_xs. rewrite length_insert.
              done. 
             }
              
              (* Handle HQs *)
              rewrite Nat2Z.inj_succ. 
              replace (size - (count + 1)) with (size - count - 1) by lia.
              iFrame "HQs". iPureIntro. subst new_xs. rewrite length_insert.
              word.
            }
            
            (* Return the remaining resources *)
            iFrame "HQ HSndCtrAuth HSndPerm".
            
          - (* Multi-party case - similar structure but with different counter checks *)
            iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hlower".
            iMod (send_counter_update γ send_count i with "[$HSndCtrAuth $HSndPerm]") as "[HSndCtrAuth HSndPerm]".
            
            (* Extract Q from big_sep_seq *)
            iDestruct (big_sep_seq_pop send_count (size - count) (λ i, Q false (i - size) Qsingle Qmulti) 
                       with "HQs") as "[HQ HQs]".
            { lia. }
            
            (* Update Ps for the new buffer content - similar to above *)
            iAssert ([∗ list] i↦x ∈ valid_elems new_xs first (W64 (count + 1)), 
                      P false (recv_count + i) x Psingle Pmulti)%I with "[HPs HP]" as "HPs'".
            {
               (* Similar to single-party case *)
              subst new_xs.
              replace size with (length xs).
              replace (W64 (count + 1)) with (w64_word_instance .(word.add) (W64 count) (W64 1))
              by word.
              rewrite (add_one xs first count v). all: try word.
              {
                rewrite big_sepL_snoc. iFrame.
              }
            }
            
            (* Reconstruct buff_size_inv for the new state *)
            iAssert (⌜count + 1 <= size⌝ ∗ 
                     ⌜word.unsigned first < size⌝ ∗ 
                     ⌜size > 0⌝ ∗ 
                     ⌜size + 1 < 2 ^ 63⌝ ∗
                     ⌜count + 1 + 1 < 2 ^ 63⌝)%I as "Hsizeinv".
            {
              iPureIntro.
              repeat split; try assumption; try lia.
            }
            
            (* Reassemble the logical channel state *)
            iModIntro.
            iSplitL "Hsizeinv HPs' HQs".
            {
              unfold isBufferedChanLogical.
              iFrame.
              iSplitL "".
              { iPureIntro. lia. }
              iSplitL "".
              { iPureIntro.  subst new_xs. rewrite length_insert.
              done.  }
              
              (* Handle HQs *)
              rewrite Nat2Z.inj_succ.
              replace (size - (count + 1)) with (size - count - 1) by lia.
              iFrame "HQs". iPureIntro. subst new_xs. rewrite length_insert.
              word.
            }
            
            (* Return the remaining resources *)
            iFrame "HQ HSndCtrAuth HSndPerm".
        Qed.

Lemma buff_dequeue_logical (ch: loc) (γ: chan_names) 
  (size: nat) (vs: valid_chan_state) (is_single_party: bool) 
  (send_count recv_count: nat) (count: nat) (first: u64) (new_first: u64)
  (xs: list T') (v: T') 
  (Psingle: Z -> T' -> iProp Σ) (Pmulti: T' -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ)
  (i: nat) (q: Qp):
  
  count > 0 ->  (* Buffer is not empty *)
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  size > 0 ->
  
  (* Relate old and new first pointers *)
  new_first = word.modu (word.add first 1) (W64 size) ->
  
  (* The value at the front of the buffer *)
  xs !! (uint.nat first) = Some v ->
  
  (* Input resources *)
  "HBuffChLogical" ∷ isBufferedChanLogical ch γ size vs is_single_party 
    send_count recv_count count first xs Psingle Pmulti Qsingle Qmulti R ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗
  "HRecvPerm" ∷ own_recv_counter_frag γ i q
  
  ==∗
  
  (* Output resources *)
  "HBuffChLogical" ∷ isBufferedChanLogical ch γ size vs is_single_party 
    send_count (S recv_count) (count - 1) new_first xs Psingle Pmulti Qsingle Qmulti R ∗
  "HP" ∷ P is_single_party recv_count v Psingle Pmulti ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (S recv_count) false ∗
  "HRecvPerm" ∷ own_recv_counter_frag γ (S i) q.

  Proof.
    intros Hcount_gt Hsp Hsize_pos Hnew_first Hv_at_first.
    iIntros "(HBuffChLogical & HQ & HRecvCtrAuth & HRecvPerm)".
    
    (* Unfold the logical channel state *)
    iDestruct "HBuffChLogical" as "(%HBuffCount & %Hsize & %Hsizeinv & HPs & HQs)".
    
    (* Extract buff_size_inv components *)
    destruct Hsizeinv as (Hcount_le & Hfirst_lt & Hsize_pos_old & Hsize_bound_old & Hcount_bound_old).
    
    (* Update recv counter *)
    destruct is_single_party.
    
    - (* Single-party case *)
      subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvPerm]") as "%Helem".
      subst i.
      iMod (recv_counter_update γ recv_count recv_count with "[$HRecvCtrAuth $HRecvPerm]") as "[HRecvCtrAuth HRecvPerm]".
      
      (* Add the new Q to the sequence *)
      iDestruct (big_sep_seq_snoc send_count (size - count) (λ i, Q true (i - size) Qsingle Qmulti) 
                 with "[HQ HQs]") as "HQs".
      { lia. }
      { iFrame "HQs". 
      replace (Z.of_nat recv_count) with ((send_count + (size - count) - size)) by lia.
      iFrame.
      }
      
      (* Use remove_one to handle the buffer elements *)
      assert (Hremove_one: valid_elems xs first (W64 count) = 
                           v :: valid_elems xs new_first (W64 (count - 1))).
      {
        subst new_first.
      erewrite (remove_one xs first count); eauto;try word. 
      replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1)) by word.
      replace size with (length xs). done.
      }
      
      (* Extract P for the element we're dequeuing *)
      rewrite Hremove_one.
      iDestruct (big_sepL_cons with "HPs") as "[HP HPs']".
      
      (* Reconstruct buff_size_inv for the new state *)
      iAssert (⌜count - 1 <= size⌝ ∗ 
               ⌜word.unsigned new_first < size⌝ ∗ 
               ⌜size > 0⌝ ∗ 
               ⌜size + 1 < 2 ^ 63⌝ ∗
               ⌜count < 2 ^ 63⌝)%I as "%Hsizeinvnew".
      {
        iPureIntro.
        repeat split.
        - lia.
        - subst new_first. word. 
        - assumption.
        - lia.
        - lia.
      }
      
      (* Reassemble the logical channel state *)
      iModIntro.
      iSplitL "HPs' HQs".
      {
        unfold isBufferedChanLogical.
        iFrame.
        iSplitL "".
        { iPureIntro. lia. }
        iSplitL "".
        { iPureIntro. assumption. }
        
        (* Handle HQs *)
        replace (size - (count - 1)) with (size - count + 1) by lia.
        iFrame "HQs".
        iSplitL "".
        { iPureIntro. word. }
        iFrame.
        setoid_rewrite big_sepL_proper.
        {
        iFrame.
        }
        {
          intros. iSimpl.
            iSplitL.
            {
             iIntros "H". done. 
            }
            iIntros "H". done.
        }
        {
        intros. iSimpl.
            iSplitL.
            {
             iIntros "H".  
              rewrite Z.add_comm. 
              replace (Z.of_nat k + Z.of_nat (S recv_count)) with (Z.of_nat recv_count + Z.of_nat (S k)) by lia.
              iFrame.
            }
            {
             iIntros "H".  
              rewrite Z.add_comm. 
              replace (Z.of_nat (S k) + Z.of_nat  recv_count) with (Z.of_nat (S recv_count) + Z.of_nat k) by lia.
              iFrame.
            }
        }
      }
      replace ((recv_count + 0%nat)) with (Z.of_nat recv_count) by lia.
      iFrame.
      
    - (* Multi-party case *)
      (* Similar to single-party but with different counter handling *)
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvPerm]") as "%Hlower".
      iMod (recv_counter_update γ recv_count i with "[$HRecvCtrAuth $HRecvPerm]") as "[HRecvCtrAuth HRecvPerm]".
      
      (* Add the new Q to the sequence *)
      iDestruct (big_sep_seq_snoc send_count (size - count) (λ i, Q false (i - size) Qsingle Qmulti) 
                 with "[HQ HQs]") as "HQs".
      { lia. }
      { iFrame "HQs". 
      replace (Z.of_nat recv_count) with ((send_count + (size - count) - size)) by lia.
      iFrame.
        unfold Q.
        destruct bool_decide eqn: Hbouter.
        {
          rewrite bool_decide_eq_true in Hbouter.
          destruct bool_decide eqn: Hbinner.
          {
            done.
          }
          {
            destruct i;first done.
            done.
          }
        }
        {
          rewrite bool_decide_eq_false in Hbouter.
          destruct bool_decide.
          {
            done.
          }
          iFrame.
        }

      }
      
      (* Use remove_one to handle the buffer elements *)
      assert (Hremove_one: valid_elems xs first (W64 count) = 
                           v :: valid_elems xs new_first (W64 (count - 1))).
      {
        subst new_first.
      erewrite (remove_one xs first count); eauto;try word. 
      replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1)) by word.
      replace size with (length xs). done.
      }
      
      (* Extract P for the element we're dequeuing *)
      rewrite Hremove_one.
      iDestruct (big_sepL_cons with "HPs") as "[HP HPs']".
      
      (* Reconstruct buff_size_inv for the new state *)
      iAssert (⌜count - 1 <= size⌝ ∗ 
               ⌜word.unsigned new_first < size⌝ ∗ 
               ⌜size > 0⌝ ∗ 
               ⌜size + 1 < 2 ^ 63⌝ ∗
               ⌜count < 2 ^ 63⌝)%I as "%Hsizeinv".
      {
        iPureIntro.
        repeat split.
        - lia.
        - subst new_first. word. 
        - assumption.
        - word.
        - lia.
      }
      
      (* Reassemble the logical channel state *)
      iModIntro.
      iSplitL "HPs' HQs".
      {
        unfold isBufferedChanLogical.
        iFrame "".
        iSplitL "".
        { iPureIntro. lia. }
        iSplitL "".
        { iPureIntro. assumption. }
        
        (* Handle HQs *)
        replace (size - (count - 1)) with (size - count + 1) by lia.
        iFrame "HQs".
        iSplitL "".
        { iPureIntro. word. }
        iFrame.
      }
      {
        intros. iSimpl.
        iFrame.
      }
  Qed.

  *)

End proof.

