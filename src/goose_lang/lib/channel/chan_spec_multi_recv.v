From Perennial.goose_lang Require Import prelude. 
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode array.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang.lib Require Import
      persistent_readonly slice slice.typed_slice  struct loop lock control map.typed_map time proph rand string typed_mem.

From Perennial.goose_lang.lib.channel Require Import auth_set.
From Perennial.goose_lang.lib.channel Require Import chan_use_ctr.
From Goose.github_com.goose_lang.goose Require Import channel.
From Perennial.goose_lang Require Import lang typing.


Definition in_closed_chan_state (cs: nat): bool :=
 bool_decide (cs = 5)%nat. 

Inductive chan_state: Type := 
| start
| receiver_ready
| sender_ready
| receiver_done 
| sender_done
| closed
| invalid
.

Section proof.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.
 Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}. 
 Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!ghost_varG Σ bool}.

Implicit Types (v:val). 

Definition nat_to_chan_state (cs: nat) : chan_state :=
 match cs with 
 | 0%nat => start
 | 1%nat => receiver_ready
 | 2%nat => sender_ready
 | 3%nat => receiver_done
 | 4%nat => sender_done
 | 5%nat => closed
 | _ => invalid
 end
.

Definition chan_state_to_nat (cs: chan_state) : option nat:=
 match cs with 
 | start => Some 0%nat
 | receiver_ready => Some 1%nat
 | sender_ready => Some 2%nat
 | receiver_done => Some 3%nat
 | sender_done => Some 4%nat
 | closed => Some 5%nat
 | invalid => None
 end
.

Lemma not_closed (cs: chan_state) (raw_cs: nat):
  raw_cs ≠ 5%nat -> chan_state_to_nat cs = Some raw_cs -> cs ≠ closed.
  Proof.
    intros.
    unfold chan_state_to_nat in H0.
    destruct cs.
    all: try done.
    assert (raw_cs = 0%nat).
    {
      inversion H0. 
      rewrite H2 in H.
      done.
    }
    inversion H0. 
    rewrite H3 in H.
    done.
  Qed.

Definition is_valid_chan_state (cs: chan_state) : bool :=
  match cs with
  | invalid => false
  | _ => true
  end.

Lemma chan_state_eq_dec: ∀ (cs1 cs2: chan_state), {cs1 = cs2} + {cs1 ≠ cs2}.
Proof.
  decide equality.
Qed.

Lemma chan_state_to_nat_inj: ∀ (cs1 cs2: chan_state),
  chan_state_to_nat cs1 = chan_state_to_nat cs2 → cs1 = cs2.
Proof.
  intros cs1 cs2 H.
  destruct cs1, cs2; simpl in H; try discriminate; auto.
Qed.


Lemma nts_zero (cs:nat) :
  cs < 6 -> nat_to_chan_state cs = closed -> cs = 5%nat.
Proof.
  intros Hlts. intros Hnts.
  unfold nat_to_chan_state in Hnts. 
  do 5(destruct cs;first done). lia.
Qed.

Definition big_sep_seq (start: Z) (size: Z) (Φ : Z → iProp Σ) : iProp Σ :=
⌜ 0 ≤ size ⌝ ∗ 
[∗ list] _↦(i:Z) ∈ (seqZ start size), Φ i
.
Lemma big_sep_seq_singleton  (Φ : Z → iProp Σ) :
  ∀ (start: Z),
  big_sep_seq start 1 Φ  ⊣⊢  (Φ (start)%Z ).
  Proof.
    intros Hsize. unfold big_sep_seq.
    simpl. replace (0%nat + Hsize)%Z with Hsize by lia.
    {
      iSplitL "".
      { iIntros "(%Hsize2 & H &  emp)". done. }
      { iIntros "H". iFrame. iPureIntro. done. }
    }
  Qed.

Lemma big_sep_seq_nil :
  ∀ start Φ,
  big_sep_seq start 0 Φ ⊣⊢ emp.
  Proof.
     intros start. intros. unfold big_sep_seq.
     simpl. iFrame. done.
  Qed.
  
Lemma big_sep_seq_snoc (start: Z) (size: Z)   (Φ : Z → iProp Σ) :
  (0 ≤ size)%Z ->
  Φ (start + size)%Z ∗ big_sep_seq start size Φ  -∗ big_sep_seq start (size + 1)%Z Φ.
  Proof.
    intros H. iIntros "(Hpred & %Hsize & Hsep)".
    unfold big_sep_seq. 
    rewrite seqZ_app.
    {
      rewrite big_sepL_snoc.
      iFrame. iPureIntro. lia.
    }
    {
     lia. 
    }
    {
      done. 
    }
  Qed.

  Lemma big_sep_seq_cons (start: Z) (size: Z)   (Φ : Z → iProp Σ) :
  (0 ≤ size)%Z ->
  big_sep_seq start (size + 1)%Z Φ -∗ Φ (start + size)%Z ∗ big_sep_seq start size Φ.
  Proof.
    intros H. iIntros "(%Hsize & Hpred)".
    unfold big_sep_seq. 
    rewrite seqZ_app.
    {

      rewrite big_sepL_app.
      rewrite big_sepL_singleton.

       simpl.
       replace (0%nat + (start + size))%Z with (start + size)%Z by lia.
       iDestruct "Hpred" as "[Hlist Hpred]". iFrame.
       iPureIntro. lia.

    }
    {
     lia. 
    }
    {
      done. 
    }
  Qed.

  Lemma big_sep_seq_pop (start: Z) (size: Z)   (Φ : Z → iProp Σ) :
  1 ≤ size ->
  big_sep_seq start size%Z Φ -∗ Φ (start)%Z ∗ big_sep_seq (start + 1) (size - 1) Φ.
  Proof.
    intros H. iIntros "(%Hsize & Hpred)".
    unfold big_sep_seq. 
    rewrite seqZ_cons.
    {

      rewrite big_sepL_cons.
      iDestruct "Hpred" as "[Hs Hl]". iFrame. iPureIntro. lia.
    }
    {
      lia.
    }
   
  Qed.


Definition P (is_single_party: bool) (i:Z)
 (v: val) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)): iProp Σ :=
 if is_single_party then Psingle i v  else Pmulti v.

Definition Q (is_single_party: bool) (z: Z) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ): iProp Σ := 
if bool_decide(Z.lt z 0%Z) then True%I else (if is_single_party then Qsingle(z) else Qmulti).

  Definition valid_elems (slice : list val) (first : u64) (count : u64) : list val :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).

Definition buff_size_inv (count : Z) (first : u64) (size : Z): iProp Σ :=
  (⌜count <= size⌝ ∗ ⌜ word.unsigned first < size⌝ ∗ ⌜size > 0⌝ ∗ ⌜size + 1 < 2 ^ 63⌝
  ∗ ⌜ count + 1 < 2 ^ 63 ⌝ )%I.

Lemma add_one_lemma_1 : forall slice (first : u64) (count : u64) (e : val) ,
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
      (* Check take_insert. *)
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
    + (* NOTE: would be cool if [word] could handle this style of reasoning. *)
      rewrite -(Z_mod_plus_full _ (-1)).
      rewrite Z.mod_small; word.
  Unshelve.
  { 
  exact val. }
  { exact (uint.nat first + uint.nat count)%nat. }
  { exact (<[uint.nat
  (uint.nat first + uint.nat count - length slice)%Z:=e]>
slice). }
  { exact (<[uint.nat
  (uint.nat first + uint.nat count - length slice)%Z:=e]>
slice). }
  exact (uint.nat first + uint.nat count)%nat.
Qed.

Lemma add_one_lemma_2 : forall slice (first : u64) (count : u64) (e : val),
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
    + (* NOTE: would be cool if [word] could handle this style of reasoning. *)
      rewrite Z.mod_small; word.
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
    + (* NOTE: would be cool if [word] could handle this style of reasoning. *)
      rewrite -(Z_mod_plus_full _ (-1)).
      rewrite Z.mod_small; word.
Qed.

Theorem add_one : forall slice (first : u64) (count : u64) e, 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  uint.Z count < length slice ->
  valid_elems (<[uint.nat (word.modu ((word.add) first count) (length slice)):= e]> slice) first (word.add count 1) 
  = valid_elems slice first count ++ [e].
Proof.
  intuition.
  unfold valid_elems.
  (* NOTE: needs to carefully do what the old [word_cleanup] would do, so that
  the statements of [add_one_lemma_1] and [add_one_lemma_2] apply. *)
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

Lemma remove_one_lemma_1 : forall slice (first : u64) (e : val),
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

Lemma remove_one_lemma_2 : forall (slice : list val) (first : u64) (count : u64) (e : val),
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

Theorem remove_one : forall slice (first : u64) (count : u64) e, 
  uint.Z (length slice) ≠ 0 ->
  length slice + 1 < 2 ^ 63 ->
  uint.Z first < length slice ->
  0 < uint.Z count <= length slice ->
  slice !! uint.nat first = Some e -> 
  valid_elems slice first count = e :: valid_elems slice (word.modu ((word.add) first 1) (length slice)) (word.sub count 1).
Proof.
  intuition.
  unfold valid_elems.
  (* NOTE: needs to carefully do what the old [word_cleanup] would do, so that
  the statements of [add_one_lemma_1] and [add_one_lemma_2] apply. *)
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

  (* TODO: Note to self, make a helper lemma for pushing and popping *)
  Definition isBufferedChan (ch: loc) (γ: chan_names) (chan_type: ty) (size: Z) (cs: chan_state) 
   (is_single_party: bool) (send_count: Z) (recv_count: Z) (count: Z) 
  (buff: Slice.t) (first:u64) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat-> iProp Σ): iProp Σ := 
    ∃ (xs: list val), 

    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
    "%HBuffCount" ∷ ⌜(count = (send_count - recv_count))⌝ ∗
    "HBuffSlice" ∷ slice.own_slice_small buff chan_type (DfracOwn 1) xs ∗ 
    "%Hsizeinv" ∷  buff_size_inv count first (length xs) ∗ 
    "%HLxsSize" ∷ ⌜size = length xs⌝ ∗ 
    "HPs" ∷ ([∗ list] i↦x ∈ valid_elems xs first count, P is_single_party (recv_count + i) x Psingle Pmulti) ∗ 
    "HQs" ∷ big_sep_seq send_count (size - count) (λ  i,(  (Q is_single_party (i - size) Qsingle Qmulti)))
  .





Definition recv_ctr_frozen
  (cs : chan_state)
  (send_count rec_count : nat) : bool :=
  match cs with
  | closed => Nat.eqb send_count rec_count
  | _      => false
  end.

  Definition send_ctr_frozen (cs: chan_state): bool :=
  match cs with 
    | closed => true
    |  _ => false
  end
    .
Definition isUnbufferedChan (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val) (cs: chan_state) (raw_cs: nat) (is_single_party: bool) (send_count: Z) (recv_count: Z) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ )(R:nat ->  iProp Σ): iProp Σ := 
    "%Hrawcs"  ∷ ⌜ chan_state_to_nat cs = Some raw_cs  ⌝ ∗ 
     match cs with 
      | start => ("%Hcount_eq" ∷ (⌜send_count = recv_count⌝) ∗
       "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) 1%Qp true)  
      | receiver_ready => 
        ("%Hcount_eq" ∷ ⌜send_count = recv_count⌝  ∗
        "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false  ∗ 
        "HQ" ∷ Q is_single_party recv_count Qsingle Qmulti)
      | sender_ready => 
        "%Hcount_eq" ∷  ⌜send_count = recv_count⌝ ∗ 
        "%Hval_ty" ∷  ⌜val_ty v chan_type⌝ ∗ 
        "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp true  ∗ 
        "HP" ∷  P is_single_party send_count v Psingle Pmulti 
      | receiver_done => 
        "%Hcountsendinc" ∷  ⌜recv_count = (send_count + 1)%Z⌝ ∗ 
        "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp true  ∗ 
        "HQ" ∷ Q is_single_party send_count Qsingle Qmulti 
      | sender_done => 
        "%Hcountsendinc" ∷ ⌜send_count = (recv_count + 1)%Z⌝ ∗
        "HP" ∷   P is_single_party recv_count v Psingle Pmulti ∗
        "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false  ∗ 
        "%Hval_ty" ∷  ⌜val_ty v chan_type⌝ 
      | closed => "%Hcount_eq" ∷ ⌜send_count = recv_count⌝  
      | invalid => False
     end
  .

  (* TODO: Note to self, keep making these for every single state transition *)
  Lemma receiver_complete (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val)  (is_single_party: bool) (send_count: Z) (recv_count: nat) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ )(R Ri:nat ->  iProp Σ)
  (i:nat ) (q: Qp):
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷  isUnbufferedChan ch γ chan_type v sender_ready 2%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  ==∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_done 3%nat  is_single_party send_count (S recv_count) Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1)%nat false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (i + 1)%nat Ri  
  .
  intros Hsp.
  iIntros "Hoff". iNamed "Hoff". iNamed "HRecvPerm". iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  unfold isUnbufferedChan. iNamed "HCh".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
    iDestruct ((recv_counter_update γ recv_count i) with "[$HRecvCtrAuth $HRecvCtrFrag]") as ">[HRecvCtrAuth HRecvCtrFrag]".
    iModIntro. iFrame. replace (recv_count + 1)%nat with (S recv_count) by lia.
    replace (i + 1)%nat with (S i) by lia.
    destruct is_single_party.
      {
        subst recv_count. subst send_count. subst q.
        iFrame. iPureIntro. unfold chan_state_to_nat. 
        split; first done. lia.
      }
      {
        iFrame. subst send_count. 
        unfold Q.
        destruct bool_decide eqn: Hbouter.
        {
          rewrite bool_decide_eq_true in Hbouter.
          destruct bool_decide eqn: Hbinner.
          {
            iPureIntro. lia.
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
            iPureIntro. unfold chan_state_to_nat. 
            split;first done.
            lia.
          }
          iFrame. iPureIntro. 
          split;first done. lia.
        }
      }
Qed.

  Lemma receiver_complete_second (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val)  (is_single_party: bool) (send_count: Z) (recv_count: nat) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ )(R Ri:nat ->  iProp Σ)
  (i:nat ) (q: Qp):
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷  isUnbufferedChan ch γ chan_type v sender_done 4%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗  
  "Hsttok'" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false  
  ==∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v start 0%nat  is_single_party send_count (S recv_count) Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1)%nat false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (i + 1)%nat Ri  ∗ 
  "HP" ∷ P is_single_party recv_count v Psingle Pmulti
  .
  Proof.
    intros Hsp.
  iIntros "Hoff". iNamed "Hoff". iNamed "HRecvPerm". iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  unfold isUnbufferedChan. iNamed "HCh".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
    iDestruct ((recv_counter_update γ recv_count i) with "[$HRecvCtrAuth $HRecvCtrFrag]") as ">[HRcvCtrAuth HRecvCtrFrag]".
    iMod ((ghost_var_update true) with "[$Hsttok $Hsttok']") as "Hsttok".
    iModIntro. iFrame. 
    replace (S recv_count) with (recv_count + 1)%nat by lia.
    replace (S i) with (i + 1)%nat by lia.

    iFrame. iPureIntro. split;first done. lia.
  Qed.

  Lemma receiver_rescind (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val)  (is_single_party: bool) (send_count: Z) (recv_count: nat) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ )(R Ri:nat ->  iProp Σ)
  (i:nat ) (q: Qp):
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_ready 1%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗  
  "Hsttok'" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false  
  ==∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v start 0%nat  is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri  
  .
  Proof.
    intros Hsp.
  iIntros "Hoff". iNamed "Hoff". iNamed "HRecvPerm". iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  unfold isUnbufferedChan. iNamed "HCh".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
    iMod ((ghost_var_update true) with "[$Hsttok $Hsttok']") as "Hsttok".
    iModIntro. iFrame.
    destruct is_single_party.
    {
      subst send_count. 
      unfold Q.
      destruct bool_decide eqn: Hbouter.
      {
        rewrite bool_decide_eq_true in Hbouter.
        destruct bool_decide eqn: Hbinner.
        {
          iPureIntro. lia.
        }
        {
          lia.
        }
      }
      {
        rewrite bool_decide_eq_false in Hbouter.
        destruct bool_decide.
        {
          iPureIntro. unfold chan_state_to_nat. 
          done.
        }
        iFrame. subst recv_count. iFrame. iPureIntro. 
        done.
      }
    }
    {
     unfold Q.
     destruct bool_decide eqn: Hbouter.
     {
       rewrite bool_decide_eq_true in Hbouter.
       destruct bool_decide eqn: Hbinner.
       {
         iPureIntro. lia.
       }
       {
         lia.
       }
     }
     {
       rewrite bool_decide_eq_false in Hbouter.
       destruct bool_decide.
       {
         iPureIntro. unfold chan_state_to_nat. 
         done.
       }
       iFrame. iPureIntro. 
       done.
     }
    } 
  Qed.

  

Lemma receiver_offer (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val)  (is_single_party: bool) (send_count: Z) (recv_count: nat) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ )(R Ri:nat ->  iProp Σ)
  (i:nat ) (q: Qp):
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷  isUnbufferedChan ch γ chan_type v start 0%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  ==∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_ready 1%nat  is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗ 
  "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false  
  .
  intros Hsp.
  iIntros "Hoff". iNamed "Hoff". iNamed "HRecvPerm". iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  unfold isUnbufferedChan. iNamed "HCh".
  iMod ((ghost_var_update false) with "Hsttok") as "[Hsttok1 Hsttok2]".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
    iModIntro. iFrame.
    do 1 (iSplitL "";first done).
    destruct is_single_party.
      {
        subst recv_count.
        iFrame.
        done.
      }
      {
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
          done.
        }
      }
Qed.

Lemma wp_Channel__ReceiverCompleteOrOffer_Closed (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t) (cs: chan_state) (raw_cs: nat)   (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
{{{ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 5%nat) 
}}}
     Channel__ReceiverCompleteOrOffer chan_type #ch
{{{  RET #(W64 2); 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 5%nat) 
}}}.
Proof.
  wp_start. wp_loadField. wp_loadField. wp_loadField.
  wp_pures. iModIntro. iApply "HΦ". iFrame.
Qed. 

Lemma wp_Channel__ReceiverCompleteOrOffer_SenderReady (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)    (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v sender_ready 2%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 2%nat) ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrOffer chan_type #ch
{{{  RET #(W64 0); 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_done 3%nat is_single_party send_count (recv_count + 1) Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 3%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1) false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (S i) Ri 
}}}.
Proof.
  intros Hvt Hbuff_zero.
  try (iModIntro (□ _)%I);
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ";
  try wp_rec.
  rewrite -wp_fupd.
  iNamed "Hpre".
  wp_loadField. wp_storeField.
  iDestruct ((receiver_complete)  with "[HCh HQ HRecvCtrAuth HRecvPerm]") as ">Hnew".
  {
    done.
  }
  {
   iFrame. 
  }
  iNamed "Hnew". 
  iModIntro. iApply "HΦ".
  iFrame.
  unfold isUnbufferedChan.
  iNamed "HCh".
  replace (S i) with (i + 1)%nat by lia.
  replace (recv_count + 1) with (Z.of_nat (S recv_count)) by lia.
  iFrame. iPureIntro. done. 
  Unshelve.
  {
    done.
  }
  done.
Qed.


Lemma wp_Channel__ReceiverCompleteOrOffer_InProgress (ch: loc)
(cs: chan_state) (raw_cs: nat) 
(i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)  (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
cs ≠ start ->
cs ≠ sender_ready ->
cs ≠ closed ->
#(W64 raw_cs) ≠ #(W64 0) ->
#(W64 raw_cs) ≠ #(W64 2) ->
#(W64 raw_cs) ≠ #(W64 5) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v cs raw_cs is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrOffer chan_type #ch
{{{  RET #(W64 3); 
"value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
"HCh" ∷  isUnbufferedChan ch γ chan_type v cs raw_cs is_single_party send_count recv_count Psingle 
Pmulti Qsingle Qmulti R ∗ 
"chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
"HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
"HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
"HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}.
Proof.
  intros Hvt Hbuff_zero. intros Hns. intros Hnsd.
  intros Hnc. intros Hrns. intros Hrnsd. intros Hrnc.
  wp_start.
  wp_loadField.
  wp_if_destruct.
  { wp_loadField.
    wp_if_destruct.
    {
      wp_loadField. wp_if_destruct.
      {
        iModIntro. iApply "HΦ".
        iFrame.
      }
    }
  }
Qed.

Lemma wp_Channel__ReceiverCompleteOrOffer_Start (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)    (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v start 0%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 0%nat) ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrOffer chan_type #ch
{{{  RET #(W64 1); 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_ready 1%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 1%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false ∗  
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}.
Proof.
  intros Hvt Hbuff_zero.
  try (iModIntro (□ _)%I);
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ";
  try wp_rec.
  rewrite -wp_fupd.
  iNamed "Hpre".
  wp_loadField. wp_loadField.
  wp_storeField. iDestruct ((receiver_offer)  with "[HCh HQ HRecvCtrAuth HRecvPerm]") as ">Hnew".
  {
    done.
  }
  {
   iFrame. 
  }
  iNamed "Hnew".
  iModIntro. iApply "HΦ".
  iFrame.
  unfold isUnbufferedChan.
  iNamed "HCh".
  iFrame. done.
  Unshelve.
  {
    done.
  }
  all: try done.
Qed.

Lemma wp_Channel__ReceiverCompleteOrOffer (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)    (v: val) (send_count:nat) ( recv_count: nat) (cs: chan_state) (raw_cs: nat)
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
chan_state_to_nat cs = Some raw_cs  ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v cs raw_cs is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen cs send_count recv_count) ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrOffer chan_type #ch
{{{ (ret_code: nat), RET #(W64 ret_code);
match ret_code with 
 | 0%nat => 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_done 3%nat is_single_party send_count (recv_count + 1) Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 3%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1) false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (S i) Ri 
 | 1%nat => 
 "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
 "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_ready 1%nat is_single_party send_count recv_count Psingle 
 Pmulti Qsingle Qmulti R ∗ 
 "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 1%nat) ∗
 "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
 "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false ∗  
 "HRecvPerm" ∷ own_recv_perm γ q i Ri 
 | 2%nat =>
 "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 5%nat) 
 | 3%nat =>
 "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
"HCh" ∷  isUnbufferedChan ch γ chan_type v cs raw_cs is_single_party send_count recv_count Psingle 
Pmulti Qsingle Qmulti R ∗ 
"chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
"HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
"HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
"HRecvPerm" ∷ own_recv_perm γ q i Ri 
 | _ => False
 end
   
}}}.
Proof.
  intros Hsp. intros Hsz. intros Hcs.
  try (iModIntro (□ _)%I);
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ". iNamed "Hpre".
  destruct (chan_state_eq_dec cs closed) as [Hclosed|Hnclosed].
  {
    subst cs.
    simpl in Hcs.
    inversion Hcs.
   wp_apply (wp_Channel__ReceiverCompleteOrOffer_Closed with "[chan_state]").
   all: try done.
   {
    exact closed.
   }
   {
    iIntros "IH". iNamed "IH".
    iSpecialize ("HΦ" $! 2%nat).
    iApply ("HΦ" with "chan_state").
   }
  }
  destruct (chan_state_eq_dec cs start) as [Hstart|Hnstart].
   {
    subst cs. simpl in Hcs. inversion Hcs.

  wp_apply (wp_Channel__ReceiverCompleteOrOffer_Start with "[HCh HQ value HRecvCtrAuth HRecvPerm chan_state]").
  all: try done.
  {
   iFrame. 
  }
    iIntros "IH". iNamed "IH".
    unfold isUnbufferedChan.
    iSpecialize ("HΦ" $! 1%nat).
    iApply "HΦ". iNamed "HCh".
    iDestruct "HCh" as "(H1 & H2 & H3)".
    iFrame. done.
   }
   destruct (chan_state_eq_dec cs sender_ready) as [Hsr|Hnsr].
   {
    subst cs. simpl in Hcs. inversion Hcs.

  wp_apply (wp_Channel__ReceiverCompleteOrOffer_SenderReady with "[HCh HQ value HRecvCtrAuth HRecvPerm chan_state]").
  all: try done.
  {
   iFrame. 
  }
  iIntros "IH". iNamed "IH".
    unfold isUnbufferedChan.
    iSpecialize ("HΦ" $! 0%nat).
    iApply "HΦ". iNamed "HCh".
    iFrame. done.
   }
   wp_apply ((wp_Channel__ReceiverCompleteOrOffer_InProgress ch cs raw_cs) with "[HCh HQ value HRecvCtrAuth HRecvPerm chan_state]").
   all: try done.
   {
    destruct cs.
    all: try
      (simpl in Hcs;
      inversion Hcs;
      done).
   }
   {
    destruct cs.
    all: try
      (simpl in Hcs;
      inversion Hcs;
      done).
   }
   {
    destruct cs.
    all: try
      (simpl in Hcs;
      inversion Hcs;
      done).
   }
   {
    unfold recv_ctr_frozen. replace (match cs with
    | closed => (send_count =? recv_count)%nat
    | _ => false
    end) with false by (destruct cs;auto;done) .

    iFrame.
   }
   {
    iIntros "IH". iNamed "IH".
    unfold isUnbufferedChan.
    iSpecialize ("HΦ" $! 3%nat).
    iApply "HΦ". iNamed "HCh".
    iFrame. done.
    
   }
   Unshelve.
   all: done.
Qed.

Lemma wp_Channel__ReceiverCompleteOrRescindOffer_Complete (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)    (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v sender_done 4%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 4%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false ∗  
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrRescindOffer chan_type #ch
{{{  RET #(W64 1); 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v start 0%nat is_single_party send_count (recv_count + 1) Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 0%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1) false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (S i) Ri 
}}}.
Proof.
  intros Hvt Hbuff_zero.
  try (iModIntro (□ _)%I);
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ";
  try wp_rec.
  rewrite -wp_fupd.
  iNamed "Hpre".
  iNamed "HRecvPerm".
iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
  wp_loadField. wp_pures. wp_auto.
  iDestruct ((receiver_complete_second)  with "[ HCh Hrct Hsttok HRecvCtrAuth HRecvCtrFrag]") as ">Hnew".
  {
    done.
  }
  {
    iNamed "HCh". 
   iFrame. 
   destruct is_single_party.
   {
    iFrame. simpl. iDestruct "HCh" as "(HP & Hsttok & %Hvt2)".
    iFrame. done.
   }
   {
    iDestruct "HCh" as "(HP & Hsttok & %Hvt2)".
    iFrame.
    done.
   }
  }
  iNamed "Hnew". 
  iModIntro. iApply "HΦ".
  iFrame.
  unfold isUnbufferedChan.
  iNamed "HCh".
  replace (S i) with (i + 1)%nat by lia.
  replace (recv_count + 1) with (Z.of_nat (S recv_count)) by lia.
  iFrame. iPureIntro. done. 
  Unshelve.
  {
    done.
  }
  {
    done.
  }
  {
    done.
  }
  done.
Qed.



Lemma wp_Channel__ReceiverCompleteOrRescindOffer_Rescind (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)    (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_ready 1%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 1%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp false ∗  
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrRescindOffer chan_type #ch
{{{  RET #(W64 0); 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷  isUnbufferedChan ch γ chan_type v start 0%nat is_single_party send_count recv_count Psingle 
  Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 0%nat) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}.
intros Hvt Hbuff_zero.
try (iModIntro (□ _)%I);
let x := ident:(Φ) in
iIntros (Φ) "Hpre HΦ";
try wp_rec.
rewrite -wp_fupd.
iNamed "Hpre".
wp_loadField. wp_loadField.
iNamed "HRecvPerm".
iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
wp_storeField. iDestruct ((receiver_rescind)  with "[ Hrct HRecvCtrFrag HCh  Hsttok HRecvCtrAuth ]") as ">Hnew".
{
  done.
}
{
 iFrame.
 destruct is_single_party.
 {
  subst recv_count.
  iNamed "HCh".
  iFrame. done.
 } iNamed "HCh". iFrame. done.  
}
iNamed "Hnew".
iModIntro. iApply "HΦ".
iFrame.
Unshelve.
{
  done.
}
all: try done.
Qed.
(* note to self: maybe make count a w64, or otherwise find a way to make this easier
we can't keep digging into these big prorfs. Notably, if buffered chan doesn't own count
or first we should be able to prove a ==* thing to do the swap of isbufferedchannel 
*)



  Definition isChanInner (ch: loc) (γ: chan_names) (chan_type: ty) 
    (size: nat) (is_single_party: bool) (buff: Slice.t) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R: nat -> iProp Σ)  : iProp Σ := 
    ∃ (raw_cs: nat) (cs: chan_state)  (count: nat) (first: u64) (v: val) (send_count: nat) (recv_count: nat),
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (send_ctr_frozen cs) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen cs send_count recv_count) ∗ 
    "%Hrawcs"  ∷ ⌜ chan_state_to_nat cs = Some raw_cs  ⌝ ∗ 
    "HCloseTokPostClose" ∷ 
    match cs with 
      |closed => (∃ (n:nat) (close_tok_names: gset gname), own_closed_tok_post_close γ n close_tok_names ∗  own_send_counter_frag γ n 1 )
      |_ => True
     end 
      ∗ 
    "HBuffUnbuff" ∷ 
    match size with 
      | 0%nat => isUnbufferedChan ch γ chan_type v cs raw_cs is_single_party send_count recv_count  Psingle Pmulti
      Qsingle Qmulti R 
      | S _ => isBufferedChan ch γ chan_type size cs is_single_party send_count recv_count count buff first Psingle Pmulti Qsingle Qmulti R
              
    end 
  .


Definition isChan (ch: loc) (γ: chan_names) (chan_type: ty) 
  (size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) : iProp Σ := 
    ∃ (mu_l: loc) (buff: Slice.t) ,
    "#mu" ∷ ch ↦[(Channel chan_type) :: "lock"]□ #mu_l
     ∗ 
    "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "%Hbuffsize" ∷ ⌜ (#buff .(Slice.sz) = #(W64 size)) ⌝  ∗ 
    "%Hchantyzero" ∷ ⌜ has_zero chan_type ⌝  ∗ 
    "#Hlock" ∷ is_lock (nroot .@ "Channel") (#mu_l) (isChanInner ch γ chan_type size is_single_party buff Psingle Pmulti Qsingle Qmulti R)
.

Lemma wp_Channel__BufferedTryReceiveLockedEmpty (ch: loc) (γ: chan_names) (chan_type: ty) 
   (is_single_party: bool) (raw_cs:nat )
  (buff: Slice.t)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat-> iProp Σ) (i: nat) (q: Qp):
has_zero chan_type ->
#(W64 raw_cs) ≠ #(W64 5) ->
{{{ 
  
  "HRcvPerm" ∷ own_recv_perm γ q i Ri ∗  
    "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 0)  ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) 

}}}
Channel__BufferedTryReceiveLocked chan_type #ch
 
{{{ 
  RET (#false,(zero_val chan_type),#true); 
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 0)  ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
  "HRcvPerm" ∷ own_recv_perm γ q i Ri  
  
}}}
  .
  Proof.
    intros Hctzero. intros Hrawcs.
    wp_start.
  wp_auto.
  wp_apply wp_ref_of_zero;first done. iIntros (zv) "Hzv".
  wp_auto. wp_if_destruct. wp_load. wp_pures. iApply "HΦ".
  iModIntro. iFrame. 
  Qed.

  Lemma wp_Channel__BufferedTryReceiveLockedClosed (ch: loc) (γ: chan_names) (chan_type: ty) 
  (is_single_party: bool) n (close_tok_names: gset gname) (γr: gname)
 (buff: Slice.t)  (Ri:nat-> iProp Σ) (i: nat) (q: Qp):
has_zero chan_type ->
{{{ 
 
 "HRcvCloseTok" ∷    own_closed_tok_frag γ γr Ri ∗ 
   "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
   "#HSndCtrAuth" ∷ own_send_counter_auth γ n true ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth γ n true ∗ 
   "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 0)  ∗ 
   "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 5) ∗ 
   
   "HCloseTokPostClose"  ∷ own_closed_tok_post_close γ n close_tok_names ∗  
   "HSc"  ∷ own_send_counter_frag γ n 1
}}}
Channel__BufferedTryReceiveLocked chan_type #ch

{{{ 
 RET (#true,(zero_val chan_type),#false); 
   "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 0)  ∗ 
   "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 5) ∗  
 "HRi" ∷  (Ri n) ∗
 "#HScfroz" ∷ own_send_counter_auth γ n true ∗ 
 "#HRcfroz" ∷ own_recv_counter_auth γ n true ∗ 
   "HSc"  ∷ own_send_counter_frag γ n 1 ∗ 
   "HCloseTokPostClose"  ∷ own_closed_tok_post_close γ n (close_tok_names ∖ {[γr]} )  
}}}.
Proof.
    intros Hctzero.
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_rec.
  

  wp_auto.
  wp_apply wp_ref_of_zero;first done. iIntros (zv) "Hzv".
  iNamed "HCloseTokPostClose".
  iDestruct "HCloseTokPostClose" as "[Hauthset Hset]".
  iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSc]") as "%Hag2".
  iDestruct ((own_closed_tok_post_close_pop_raw γ n γr Ri close_tok_names) with "[Hset Hauthset HRcvCloseTok]") as ">Hct".
  {
   iFrame.
  }
  wp_auto. 
  iModIntro. iApply "HΦ".

   intros.
  iDestruct "Hct" as "(Hauth & Hset & HRi)".
  iFrame.
   wp_pures.
   iFrame.
   iFrame "#".
Qed.

Lemma wp_Channel__BufferedTryReceiveLockedSuccess (ch: loc) (γ: chan_names) (chan_type: ty) (size: nat)  (mu_l: loc)
   (is_single_party: bool) raw_cs cs (count: nat) (send_count recv_count: nat) (first: w64)
  (buff: Slice.t)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat-> iProp Σ) (i: nat) (q: Qp):
has_zero chan_type ->
word.unsigned 0 < word.unsigned count ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ 
  
  "HQ" ∷ Q is_single_party i Qsingle Qmulti 
  ∗ 
  "HRcvPerm" ∷ own_recv_perm γ q i Ri ∗  
    "#mu" ∷ ch ↦[(Channel chan_type) :: "lock"]□ #mu_l ∗ 
    "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗ 
  "HCh" ∷   isBufferedChan ch γ chan_type size cs
  is_single_party send_count recv_count count
buff first Psingle Pmulti Qsingle Qmulti R ∗  
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen cs send_count
  (recv_count)) 



}}}
Channel__BufferedTryReceiveLocked chan_type #ch
 
{{{ 
  (new_first: w64) (v: val), RET (#true,v,#true); 
 "HP" ∷  P is_single_party i v Psingle Pmulti ∗ 
 "HRecvPerm" ∷  own_recv_perm γ q (S i) Ri ∗
 "%HVt" ∷  ⌜val_ty v chan_type⌝ ∗  
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 (count - 1)) ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗ 
  "HCh" ∷   isBufferedChan ch γ chan_type size cs
  is_single_party send_count (S recv_count) (count - 1)
buff new_first Psingle Pmulti Qsingle Qmulti R   ∗  
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (S recv_count) (recv_ctr_frozen cs send_count
  (S recv_count)) 
}}}
  .
  intros Hctzero.  intros Hcount. intros Hsp.
  wp_start.
  wp_apply wp_ref_of_zero.
  {
    done.
  }

    iIntros (v_ptr) "Hvptr".
    wp_pures.
    wp_loadField.
    wp_if_destruct.
    wp_auto.
    iNamed "HCh".
    iPoseProof (slice.own_slice_small_sz with "HBuffSlice") as "%".
    wp_auto.
      edestruct (list_lookup_Z_lt xs (uint.Z first)).
      {
        word.
        }
    wp_apply ((slice.wp_SliceGet _ _ _ _ _ xs first x  ) with "[HBuffSlice]").
    { iFrame.
    done.
    }
    iIntros "[Hoss %Hvt]". wp_auto. wp_apply wp_slice_len.
    wp_auto.
    iNamed "HRcvPerm".
    iDestruct "HRcvPerm" as "(HRecvCtrFrag & Hctf)".
          iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iAssert (  own_recv_counter_auth γ recv_count (recv_ctr_frozen cs send_count recv_count) ∗ 
      own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRcvCtrAuth &HRecvCtrFrag & %Hispz)".
        {
          assert (send_count > recv_count) by word.
            assert (((send_count =? recv_count)%nat) = false).
            {
              rewrite Nat.eqb_neq.
              intro H3.
              word.
            }
            unfold recv_ctr_frozen.
            replace (send_count =? recv_count)%nat with false.
          destruct is_single_party.
          {
          subst q.  
          iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag3".
          iFrame.
          destruct cs.
          all: (try (iFrame;done)).
          }
          {
            destruct cs.
          all: (try (iFrame;done)).

          }
        }

        {
          unfold recv_ctr_frozen.
          assert (send_count > recv_count) by word.
            assert (((send_count =? recv_count)%nat) = false).
            {
              rewrite Nat.eqb_neq.
              intro H3.
              word.
            }
      iDestruct ((big_sep_seq_snoc send_count (size - count) (λ  i0,(  (Q is_single_party (i0 - size) Qsingle Qmulti)))) with "[HQ HQs]") as "HQs".
      {
       lia. 
      }
      {
        iFrame. 
        destruct is_single_party.
        {
         unfold Q. 
         rewrite Hispz in Hag2.
         assert (i = recv_count) by lia.
         replace count with (send_count - recv_count)%nat by lia.
         replace (send_count + (size - (send_count - recv_count)%nat) - size) with (Z.of_nat i) by lia. done.
        }
        {
          unfold Q. 
          rewrite HBuffCount.
          replace (send_count + (size - (send_count - recv_count)) - size) with (Z.of_nat recv_count) by lia.
          destruct i.
          {
            simpl. 
            destruct bool_decide.
            all: done.
          }
          {
            simpl. destruct bool_decide; first done.
            iFrame.
          }
        }
      }
      {

        
      
            unfold recv_ctr_frozen.
            replace (send_count =? recv_count)%nat with false.
            replace (match cs with | start | _ => false end) with false by (destruct cs; auto).
      iDestruct ((recv_counter_update γ recv_count i) with "[$HRcvCtrAuth $HRecvCtrFrag]") as ">[HRcvCtrAuth HRecvCtrFrag]".
      iAssert (bupd (own_recv_counter_auth γ (S recv_count)
      (match cs with
      | closed => (send_count =? S recv_count)%nat
      | _ => false
      end)))%I with "[HRcvCtrAuth]" as ">HRcvCtrAuth".
      {
        destruct (send_count =? S recv_count)%nat.
        {
          destruct cs.
          { iModIntro. iFrame. }
          { iModIntro. iFrame. }
          { iModIntro. iFrame. }
          { iModIntro. iFrame. }
          { iModIntro. iFrame. }
          {
       iDestruct ((recv_counter_freeze γ (S recv_count)) with "HRcvCtrAuth") as ">HRcvCtrAuth".  
       {
        done.
       }
       iModIntro. iFrame. }
       {iModIntro. iFrame. }
      }
      {
        replace (match cs with
        | start | _ => false
        end) with false by (destruct cs;auto).
        iModIntro. iFrame.
      }
    }
    {
      erewrite (remove_one xs first count); eauto; try word.
      rewrite big_sepL_cons.
      iDestruct "HPs" as "[HP HPs]".
      iModIntro. iApply "HΦ".
      destruct is_single_party.
      {
        subst recv_count.
        replace (i + 0%nat) with (Z.of_nat i) by lia.
        replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1))
        by word.
        iFrame. simpl. iFrame "%".
        replace ((size - (count - 1))) with (size - count + 1) by word.
        replace (W64 (length xs)) with (buff.(Slice.sz)) by word.
        unfold recv_ctr_frozen.
        iFrame.
       
       
        iSplitL "".
        {
         iPureIntro. lia. 
        }
        iSplitL "".
        {
         word. 
        }
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
              replace (Z.of_nat k + Z.of_nat (S i)) with (Z.of_nat i + Z.of_nat (S k)) by lia.
              iFrame.
            }
            {
             iIntros "H".  
              rewrite Z.add_comm. 
              replace (Z.of_nat (S k) + Z.of_nat  i) with (Z.of_nat (S i) + Z.of_nat k) by lia.
              iFrame.
            }
           }
      }
      {
        replace (recv_count + 0%nat) with (Z.of_nat recv_count) by lia.
        replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1))
        by word.
        iFrame. simpl. iFrame "%".
        replace ((size - (count - 1))) with (size - count + 1) by word.
        replace (W64 (length xs)) with (buff.(Slice.sz)) by word.
        iFrame. iPureIntro. word.
        
      }
    }
  }
        }
Qed.



    (*

       iFrame "#". done.
        iApply 
        wp_pures.

      }

         replace ((w64_word_instance .(word.modu)
         (w64_word_instance .(word.add) (W64 first) (W64 1)) (W64 (length xs))))
         with (W64 first) by word.
        replace ((w64_word_instance .(word.modu)
        (w64_word_instance .(word.add) (W64 first) (W64 1)) (W64 (length xs))))
        with (W64 first).

      wp_storeField.
      wp_storeField.
      wp_load_ty.
      rewrite remove_one.
      wp_storeField.

      wp_store_ty.

    wp_pures.
    iAssert (  own_recv_counter_auth γ recv_count false ∗ 
    own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
      {
        destruct is_single_party.
        {
        subst q.  
        iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
        iFrame. done.
        }
        {
        iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
        iFrame. iPureIntro. done.
        }
      }
    iDestruct ((recv_counter_update γ recv_count i) with "[$HRecvCtrAuth $HRecvCtrFrag]") as ">[HRecvCtrAuth HRecvCtrFrag]".
    iDestruct ((big_sep_seq_snoc send_count (size - count) (λ  i0,(  (Q is_single_party (i0 - size) Qsingle Qmulti)))) with "[HQ HQs]") as "HQs".
    {
     lia. 
    }
    {
     iFrame.
     destruct is_single_party.
     {
      assert (((send_count + (size - count) - size)) = i).
      {
       lia. 
      }
      rewrite H. done.
     } 
     {
      unfold Q.
      destruct bool_decide eqn: Hbouter.
        {
          rewrite bool_decide_eq_true in Hbouter.
          destruct bool_decide eqn: Hbinner.
          {
            iPureIntro. lia.
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
    }
    {
      iModIntro.
      replace (i + 1)%nat with (S i) by lia.
      replace (recv_count + 1)%nat with (S recv_count) by lia.
      replace ((size - (count - 1))) with (size - count + 1) by word.

      edestruct (list_lookup_Z_lt xs (uint.Z first)).
    { word. }
      erewrite (remove_one xs first count); eauto; try word.
      {
        rewrite big_sepL_cons.
        destruct is_single_party. {
        unfold P. subst recv_count.
        replace ((Z.of_nat i) + (Z.of_nat 0)) with (Z.of_nat i) by lia.
        iDestruct "HPs" as "[HP HPs]".
         replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with 
         (W64 (count - 1)) by word.
         unfold valid_elems. 
         iIntros (v). iFrame.

         replace ((w64_word_instance .(word.modu)
         (w64_word_instance .(word.add) (W64 first) (W64 1)) (W64 (length xs))))
         with (W64 first) by word.
        replace ((w64_word_instance .(word.modu)
        (w64_word_instance .(word.add) (W64 first) (W64 1)) (W64 (length xs))))
        with (W64 first).
        {
          admit.
        }
        {
          injection H.
         word. 
        }
        iFrame.
        replace ((w64_word_instance .(word.modu)
        (w64_word_instance .(word.add) (W64 first) (W64 1)) (W64 (length xs)))
        (w64_word_instance .(word.sub) (W64 count) (W64 1)))
        iFrame.
      }
      iDestruct "Helem" as "[Hp Helem]". 
      wp_apply (wp_Mutex__Unlock with "[HlockC H2 Hqueue Hfirst Hcount H3 Helem]").
      { iFrame "∗#". 
        iNext.
        iExists _, (word.sub count1 1).
        iExists _. 
        iFrame "Hfirst Hcount H3". 
        iFrame "Hqueue".
        iSplitR.
        { 
          word.
        }
        iExactEq "Helem". unfold named. rewrite H0. f_equal. f_equal.
        nat_cleanup. unfold W64. rewrite word.of_Z_unsigned. word.
      }

    }
     {

     }
     }
    }


    destruct is_single_party.
    {

    }
  Qed.
*)

  

(*
Lemma wp_Channel__ReceiverCompleteOrOffer (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)   (mu_l: loc)
(cs: chan_state) (raw_cs: nat) (v: val) (send_count:nat) ( recv_count: nat) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff .(Slice.sz) = #(W64 0)) ->
cs ≠ closed ->
{{{ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗
  "HCh" ∷ (isUnbufferedChan ch γ chan_type
  v cs raw_cs is_single_party send_count recv_count Psingle Pmulti Qsingle Qmulti R) ∗ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
     Channel__ReceiverCompleteOrOffer chan_type #ch
{{{  RET #(W64 1); 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 3%nat) ∗  
"HCh" ∷  isUnbufferedChan ch γ chan_type v receiver_done 3%nat  is_single_party send_count (S recv_count) Psingle 
Pmulti Qsingle Qmulti R ∗ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
"HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1)%nat false ∗ 
"HRecvPerm" ∷ own_recv_perm γ q (i + 1)%nat Ri  

}}}.
Proof.
  intros Hvt. intros Hbuff_zero. intros Hstate. intros Hcs.
  wp_start.  iNamed "HCh". 
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "(HRecvCtrFrag & Hctf)".
  iAssert (  own_recv_counter_auth γ recv_count false ∗ 
  own_recv_counter_frag γ i q ∗ (⌜ if is_single_party then  (recv_count = i)  else (i <= recv_count)%nat  ⌝%I) )%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth &HRecvCtrFrag & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
  wp_loadField. wp_if_destruct.
  {
    wp_storeField. 
    iDestruct ((recv_counter_update γ recv_count i) with "[$HRecvCtrAuth $HRecvCtrFrag]") as ">[HRecvCtrAuth HRecvCtrFrag]".
    assert (cs = sender_ready).
    {
      destruct cs.
      all: try(
      simpl in Hcs; inversion Hcs;
      subst raw_cs; word
      ).
      done.
    }
    subst cs.
    iModIntro. iApply "HΦ". iFrame. iNamed "HCh".
    unfold isUnbufferedChan. iFrame. iExists receiver_done.
    iExists 3%nat. iExists 0%nat. iExists (recv_count + 1)%nat.
    iExists (recv_count + 1)%nat.
    iFrame. iFrame "%".
    iFrame. 
    iSplitL "". 
    { iPureIntro. unfold chan_state_to_nat. split. { done. } lia. }


  }

Admitted.
(*
∃ (new_cs: chan_state) (new_raw_cs: nat) (new_i: nat) (new_send_count: nat)
 (new_v: val) ,
 "HCh" ∷ isUnbufferedChan ch γ chan_type
 new_v new_cs new_raw_cs is_single_party new_send_count recv_count Psingle Pmulti Qsingle Qmulti R ∗ 
 match uint.nat exchange_result with 
   | 0%nat => ((Q is_single_party i Qsingle Qmulti ∗ own_send_counter_frag γ new_i q ∗ 
      own_send_counter_auth γ new_send_count false ) ∗ ⌜ new_cs = sender_done ⌝ ∗ ⌜ new_i = S i ⌝ ∗  
   "value" ∷ ch ↦[(Channel chan_type) :: "v"] v  
      ∗ ⌜ new_send_count = S send_count ⌝ 
      ∗ ⌜ new_v = v ⌝ 
      )
   | 1%nat => ( 
   own_send_counter_frag γ new_i q ∗ 
     own_send_counter_auth γ send_count false ∗ ⌜ new_i = i ⌝ ∗ ⌜ new_cs = sender_ready ⌝ ∗ 
   "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp true
      ∗ ⌜ new_v = v ⌝ 
     
     )
   | 2%nat => ( P is_single_party new_i v Psingle Pmulti ∗
     own_send_counter_frag γ new_i q ∗ 
   "value" ∷ ch ↦[(Channel chan_type) :: "v"] v0 ∗ 
       own_send_counter_auth γ send_count false ∗ ⌜ new_i = i ⌝ ∗ ⌜ new_cs = cs ⌝ 
      ∗ ⌜ new_v = v0 ⌝ 
       
       ) 
   | _ => False
   end
*)
*)

Lemma closed_unbuff_eq (ch: loc) (send_count recv_count: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
isUnbufferedChan ch γ chan_type v closed 5%nat is_single_party send_count recv_count
Psingle Pmulti Qsingle Qmulti R -∗ ⌜ send_count = recv_count ⌝ 
.
Proof.
  iIntros "H". iNamed "H". iPureIntro. lia. 
Qed.

Local Opaque load_ty store_ty.

Lemma wp_Channel__UnbufferedTryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
has_zero chan_type ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ 
  "HCh" ∷ isChan ch γ chan_type 0 is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri 
}}}
     Channel__UnbufferedTryReceive chan_type #ch
{{{ (v: val) (ok: bool) (selected: bool), RET (#selected,v,#ok); 
  if selected then 
  (if ok then 
    ((P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝))
    else
    ( own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
      ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
    )
  else 
    ( Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
}}}.
Proof.
 intros Hz. intros Hsp.
 wp_start.
 wp_apply wp_ref_of_zero;first done.
 iIntros (v_ptr) "Hvptr".
 iNamed "HCh".
 wp_auto.
 wp_apply (wp_Mutex__Lock with "Hlock"). 
 iIntros "[locked inv]". wp_pures.
 iNamed "inv".


  wp_apply (wp_Channel__ReceiverCompleteOrOffer with "[Hpre HQ HRcvCtrAuth value chan_state  HBuffUnbuff]").
  all: try done.
  {
    iFrame.
  }
  iIntros (ret_code).
  destruct ret_code.
  {
    iIntros "IH". iNamed "IH".

    wp_apply wp_ref_to;first val_ty. iIntros (ok_ptr) "Hok".
    wp_apply wp_ref_to;first val_ty. iIntros (selected_ptr) "Hsel".
    wp_pures. wp_load. wp_loadField.
    Search "val_ty".
    iDestruct (struct_pointsto_ty with "Hvptr") as %Hv0ty.
    wp_auto.
    assert (val_ty v chan_type).
    {
      admit.
    }
     wp_store.

    wp_auto.
    wp_bind (store_ty _ _).
    iDestruct (struct_pointsto_ty with "Hvptr") as %Hv0ty.
    wp_store.
    unfold store_ty.

    wp_store.
    unfold store_ty.
  wp_apply (wp_store with "[Hvptr").
     wp_apply wp_store.

   iFrame. 
  }
  intros.
   }
   assert (send_count =? recv_count)%nat.
    {
      rewrite Hag2. 
      rewrite Nat.eqb_refl.
      done.
    }
    {

      
      
      admit.
    } 
  }
  iIntros "IH". iNamed "IH".
  wp_auto.
   wp_apply wp_ref_to.
  {
    val_ty.
  } 
  iIntros (b) "Hb".
  wp_auto.
   wp_apply wp_ref_to.
  {
    val_ty.
  } 
  iIntros (sel) "Hsel".
  iFrame.
  wp_auto.
  wp_apply (wp_Mutex__Unlock
        with "[$Hlock HCh 
        HSndCtrAuth HCloseTokPostClose HRecvCtrAuth
         value chan_state count  $locked]").
        {
          unfold isChanInner. iExists 1%nat. iExists receiver_ready.
          iFrame. iPureIntro. done.
        }
        {
         wp_auto. 
        }

  
 }

Lemma wp_Channel__TryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ 
  "HCh" ∷ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri 
}}}
     Channel__TryReceive chan_type #ch
{{{ (v: val) (ok: bool) (selected: bool), RET (#selected,v,#ok); 
  if selected then 
  (if ok then 
    ((P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝))
    else
    ( own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
      ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
    )
  else 
    ( Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
}}}.
Proof.
  intros Hsp.
  wp_start.
  unfold isChan.
  iNamed "Hpre".
  iNamed "HCh".
  wp_auto.
  wp_apply wp_slice_len.
  wp_if_destruct.
  {
    wp_rec.
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock"). 
    iIntros "[locked inv]". wp_pures.
    iNamed "inv".
    destruct (decide(word.unsigned 0 < word.unsigned count )).
    {
      assert (0 < size) by word.
      destruct size as [|size'] eqn:Hsize.
      {
        exfalso. lia.
      }
      wp_apply (wp_Channel__BufferedTryReceiveLockedSuccess with "[HQ count chan_state HRcvCtrAuth HBuffUnbuff Hpre]").
      {
       done. 
      }
      {
        done.
      }
      {
       done. 
      }
      {
       destruct cs;
      try (iFrame; iFrame "#"; done).
      }
      {
      iIntros (new_first v0) "IH". 
      wp_auto. iNamed "IH".
      wp_apply (wp_Mutex__Unlock
        with "[$Hlock HCh HSndCtrAuth HCloseTokPostClose HRecvCtrAuth count value chan_state  $locked]").
        {
          
          iFrame. iExists (count - 1)%nat. iExists new_first.
          replace (Z.of_nat (count - 1)%nat) with (count-1) by word.
          iFrame. done.
        }
        {
         wp_pures.
         iModIntro. iApply "HΦ".
          replace (i + 1)%nat with (S i) by lia.
          iFrame. done.
        }
      }
    }
    {
      destruct (chan_state_eq_dec cs closed) as [Heq|Hneq].
      {
       subst cs.
       assert (size ≠ 0%nat) by word.
       replace (match size with
       | 0%nat =>
       isUnbufferedChan ch γ chan_type v closed raw_cs is_single_party send_count
       recv_count Psingle Pmulti Qsingle Qmulti R
       | S _ =>
       isBufferedChan ch γ chan_type size closed is_single_party send_count recv_count
       count buff first Psingle Pmulti Qsingle Qmulti R
       end) with (isBufferedChan ch γ chan_type size closed is_single_party send_count recv_count
       count buff first Psingle Pmulti Qsingle Qmulti R)%I by (destruct size;first done;done).
       iNamed "HBuffUnbuff".
       iDestruct "Hpre" as "[Hrcf Hctf]".
      iNamed "HCloseTokPostClose".
      iDestruct "HCloseTokPostClose" as "[Hctpc Hscf]".
     iDestruct (send_counter_elem with "[$HSndCtrAuth] [$Hscf]") as "%Hag2".
     assert (count = 0%nat) by word.
     subst count.
     iFrame.
     simpl in Hrawcs.
     injection Hrawcs as Hrcs5.
     subst raw_cs. iFrame.
     assert (send_count = recv_count) by lia.
     subst recv_count. 
     unfold recv_ctr_frozen.
     rewrite Nat.eqb_refl.
      wp_apply (wp_Channel__BufferedTryReceiveLockedClosed with "[HQ count Hctpc Hscf chan_state HRcvCtrAuth Hctf  HSndCtrAuth]").
      all: try done.
      {
       
        iFrame.
        replace n0 with (send_count). iFrame. done.
      }
      {
       iIntros "IH". 
       wp_auto.
        iNamed "IH".
        unfold recv_ctr_frozen.
       wp_apply (wp_Mutex__Unlock
       with "[$Hlock HSc HCloseTokPostClose chan_state count value first HBuffSlice HPs HQs  $locked]").
       {
       iModIntro.
       unfold isChanInner.
       iFrame "#".
         
         iFrame. iExists 5%nat. iExists closed. iExists 0%nat.
         iExists first. iExists send_count. iExists send_count.
        iFrame.
        unfold recv_ctr_frozen.
        rewrite Nat.eqb_refl.
        simpl.
        iFrame "#".
         iSplitL "";first done.
        destruct size.
        {
         done. 
        }
        unfold isBufferedChan. iExists xs.
        iFrame. done.
       }
       {
        wp_auto.
        iModIntro. iApply "HΦ".
        iFrame. iFrame "#". done.
       }
      }
    }
    {
      assert (size ≠ 0%nat) by word.
      replace (match size with
      | 0%nat =>
      isUnbufferedChan ch γ chan_type v cs raw_cs is_single_party send_count
      recv_count Psingle Pmulti Qsingle Qmulti R
      | S _ =>
      isBufferedChan ch γ chan_type size cs is_single_party send_count recv_count
      count buff first Psingle Pmulti Qsingle Qmulti R
      end) with (isBufferedChan ch γ chan_type size closed is_single_party send_count recv_count
      count buff first Psingle Pmulti Qsingle Qmulti R)%I by (destruct size;first done;done).
      iNamed "HBuffUnbuff".
      iDestruct "Hpre" as "[Hrcf Hctf]".
    assert (count = 0%nat) by word.
    subst count.
    assert (send_count = recv_count) by lia.
    subst recv_count. 
    unfold recv_ctr_frozen.
    rewrite Nat.eqb_refl.
      wp_apply ((wp_Channel__BufferedTryReceiveLockedEmpty ch γ chan_type is_single_party raw_cs ) with "[ count chan_state  Hctf Hrcf ]").
      all: try done.
      {
        assert (raw_cs ≠ 5%nat).
        {
          destruct cs.
          all: try 
            (simpl in Hrawcs; inversion Hrawcs;done).
        }
        assert (LitInt (W64 (Z.of_nat raw_cs)) ≠ LitInt (W64 5)).
        {
          destruct cs.
          all: try 
            (simpl in Hrawcs; inversion Hrawcs;done).
        }
        intro Hf.
        apply inv_litv in Hf.
        apply H1.
        apply Hf.
      }
      {
       iFrame. iFrame "#".  
      }
      { 
        iIntros "IH". wp_auto.
        iNamed "IH".
        wp_apply (wp_Mutex__Unlock
        with "[$Hlock chan_state count   HBuffSlice HSndCtrAuth HRcvCtrAuth HCloseTokPostClose HPs HQs value first  $locked]").
        {
        iModIntro.
        iFrame.
        unfold isChanInner.
         iExists 0%nat.
          iExists first.  iExists send_count.
         iFrame.
         unfold recv_ctr_frozen. 
         rewrite Nat.eqb_refl.
         simpl. iFrame. 
          iSplitL "";first done.
          destruct size.
          {
            lia.
          }
          iFrame. iPureIntro. done.
        }
        {
          wp_pures. iModIntro. iApply "HΦ".
          iFrame.
        }
      }
    }
  }
}
{
 wp_rec.
 wp_apply wp_ref_of_zero.
 {
  done.
 }
 iIntros (v_ptr) "Hvptr".
 wp_auto.
 wp_apply (wp_Mutex__Lock with "Hlock"). 
    iIntros "[locked inv]". wp_pures.
    iNamed "inv".
    

}


        exfalso.
        contradictionk.
        combine (H1 Hf).
        word.

        Search "litv".
        {

        }
        apply inv_litv.
        injection H0.
        word.
            done.
           exfalso. apply Hneq.
           done. 
          }
        }
        assert (not_closed cs raw_cs).
        word.
      }
      
    }
        iFrame "first".
        iFrame.
        iSplitL "";first (iPureIntro;lia).
        iSplitL "";first (iPureIntro;lia).
        iSplitL "";first (iPureIntro;lia).
        iSplitR "HQs".
        { subst n1.
         iFrame. 
        }
        }
        unfold Q.
        iExists new_first.
         replace (Z.of_nat (count - 1)%nat) with (count-1) by word.
         iFrame. done.
       }

      }


       iFrame. iFrame "#".
      


       assert (raw_cs = 5%nat) by lia.
       {
        destruct count.
        {
         done. 
        }
        word.
       } 
      }
      
         iSplitL "HP".
         iFrame "HP". 
        }
          iModIntro. 
          iFrame. iExists (S recv_count).
          replace ((W64 (count - 1))) with (W64 (count - 1)%nat) by word.
          iFrame. unfold recv_ctr_frozen. iFrame.
          replace (Z.of_nat (count - 1)%nat) with (count-1) by word.
          iFrame.
          destruct cs.
          all: try (iFrame; iFrame "#"; done).

          iExists  iExists  iFrame.

    }
      word.
       destruct cs.
       {
        iFrame. iFrame "#".
       }
      }



      }

    }


   wp_apply ((wp_Channel__BufferedTryReceiveLocked ch γ chan_type size mu_l is_single_party
   buff Psingle Pmulti Qsingle Qmulti R Ri i q) with "[HBuffUnbuff HCloseTokPostClose HRcvCtrAuth HSndCtrAuth count chan_state value HQ Hpre]").
   {
    word.
   }
   {
    done.
   }
   {
    done.
   }
   {
    iFrame. iFrame "#". iPureIntro. split. { 
    inversion Hbuffsize. done. } done.

    }
    {
     iIntros (v0 ok selected) "IH". destruct selected.
     {
      wp_pures. wp_loadField.
      iNamed "IH".
      destruct ok.
      {
        wp_apply (wp_Mutex__Unlock
        with "[$Hlock IH  $locked]").
        {
          iModIntro. iFrame. iExists first.  
          iFrame.
          admit.
        }
        {
         wp_pures. 
        }
     } 
    } 
  }



Qed.


Lemma wp_Channel__SenderCheckOfferResult (ch: loc) (i: nat) (v: val) (v0: val) (γ: chan_names) (chan_type: ty) (buff: Slice.t)  (mu_l: loc) (is_single_party: bool) (q: Qp) 
 (cs: chan_state) (raw_cs: nat) (send_count:nat) ( recv_count: nat)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
(#buff .(Slice.sz) = #(W64 0)) ->
cs ≠ closed ->
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
  "HCh" ∷ (isUnbufferedChan ch γ chan_type
  v0 cs raw_cs is_single_party send_count recv_count Psingle Pmulti Qsingle Qmulti R) ∗ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
  "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗ 
    ghost_var γ .(unbuffered_state_tracker_name) (1 / 2) true
}}}
     Channel__SenderCheckOfferResult chan_type #ch
{{{  (offer_result: w64) , RET #offer_result; 
 ∃ (new_cs: chan_state) (new_raw_cs: nat) (new_i: nat) (new_send_count: nat)
 (new_recv_count: nat) ,
  "HCh" ∷ isUnbufferedChan ch γ chan_type
  v new_cs new_raw_cs is_single_party new_send_count new_recv_count Psingle Pmulti Qsingle Qmulti R ∗ 
  match uint.nat offer_result with 
    | 1%nat => ((Q is_single_party i Qsingle Qmulti ∗ own_send_counter_frag γ new_i q ∗ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 0) ∗  
       own_send_counter_auth γ new_send_count false ) ∗ ⌜ new_cs = start ⌝ ∗ ⌜ new_i = S i ⌝ 
        ∗ ⌜ new_send_count = (send_count + 1)%nat ⌝ 
        ∗ ⌜ new_recv_count = (recv_count)%nat⌝ 
       )
    | 0%nat => ( P is_single_party new_i v0 Psingle Pmulti ∗
      own_send_counter_frag γ new_i q ∗ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 0) ∗  
        own_send_counter_auth γ new_send_count false ∗ ⌜ new_i = i ⌝ ∗ ⌜ new_cs = start ⌝ 
        ∗ ⌜ new_send_count = send_count⌝ 
        ∗ ⌜ new_recv_count = recv_count%nat⌝ 
        ) 
    | _ => False
        end
}}}.
Proof.
  intros Hvt. intros Hbuff_zero. intros Hstate. intros Hsingleparty.
  wp_start. iNamed "Hpre". iNamed "HCh".
    iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag".
 wp_loadField. wp_if_destruct.
 {
  assert (cs = closed).
  {
    destruct cs.
    

    all: try(
      simpl in Hrawcs; inversion Hrawcs;
      subst raw_cs; word
    ).
    done.
  }
  subst cs. simpl in Hrawcs. inversion Hrawcs.
  subst raw_cs. done. 
  }
  wp_pures. wp_loadField.
  wp_if_destruct. {
    wp_storeField. 

    destruct is_single_party.
    {
      subst q.
      iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
      subst send_count.

    iDestruct ((send_counter_update γ i i) with "[$HSndCtrAuth $HSen]") as ">[HSndCtrAuth Hsen]".
    iApply "HΦ".
    assert (cs = receiver_done).
    {
      destruct cs.
    all: try(
      simpl in Hrawcs; inversion Hrawcs;
      subst raw_cs; word
    ).
    done.
    }
    subst cs.
    iModIntro. iExists start. iExists 0%nat. iExists (S i). iExists (i + 1)%nat.
    iExists (recv_count)%nat.
    replace (uint.nat (W64 1)) with 1%nat by word.
    iFrame. iNamed "HCh". iFrame.
    replace (i + 1)%nat with (S i) by lia.
    iFrame.
    iPureIntro. 
     split.
     { split.
     {
      unfold chan_state_to_nat. done.
     }
      lia.
     }
     done.
    }
    {

    iDestruct ((send_counter_update γ send_count i) with "[$HSndCtrAuth $HSen]") as ">[HSndCtrAuth Hsen]".
    
    iApply "HΦ".
    assert (cs = receiver_done).
    {
      destruct cs.
    all: try(
      simpl in Hrawcs; inversion Hrawcs;
      subst raw_cs; word
    ).
    done.
    }
    subst cs.
    iModIntro. iExists start. iExists 0%nat. iExists (S i). iExists (send_count + 1)%nat.
    iExists (recv_count)%nat.
    replace (uint.nat (W64 1)) with 1%nat by word.
    iFrame. iNamed "HCh". iFrame.
    unfold Q.
    destruct (bool_decide((i < 0 ^ send_count < 0))) eqn:Hb .
    {
      rewrite bool_decide_eq_true in Hb.
      do 2 rewrite -> bool_decide_true by lia.
      iFrame. 
      replace (send_count + 1)%nat with (S send_count) by lia.
      iFrame.
    iPureIntro. 
     split.
     { split.
     {
      unfold chan_state_to_nat. done.
     }
      lia.
     }
     done.
    }
    {
      rewrite bool_decide_eq_false in Hb.
      do 2 rewrite -> bool_decide_false by lia .
      iFrame.  replace (send_count + 1)%nat with (S send_count) by lia.
      iFrame. iPureIntro.
      split.
      { split.
      {
       unfold chan_state_to_nat. done.
      }
       lia.
      }
      done.
    }
    
  }
  }
  {
    iAssert (  own_send_counter_auth γ send_count false ∗ 
  own_send_counter_frag γ i q ∗ (⌜ if is_single_party then  (send_count = i)  else (i <= send_count)%nat  ⌝%I) )%I with "[HSndCtrAuth HSen]" as "(HSndCtrAuth &HSen & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }


    
  wp_loadField. wp_if_destruct.
  {
   wp_storeField. 
   assert (cs = sender_ready).
   {
     destruct cs.
   all: try(
     simpl in Hrawcs; inversion Hrawcs;
     subst raw_cs; word
   ).
   done.
   } subst cs. iNamed "HCh".

   destruct is_single_party.
   {
   iModIntro. iApply "HΦ".
   iExists start. iExists 0%nat. iExists i%nat. iExists send_count.
   iExists recv_count.
    replace (uint.nat (W64 0)) with 0%nat by word.
   iFrame.  iSplitR "HP  ".
   {
    iFrame. iPureIntro. done.
   }
   subst send_count.
   iFrame.
   unfold P.
   iPureIntro. done.
   }
   {  
   iModIntro. iApply "HΦ".
   iExists start. iExists 0%nat. iExists i. iExists send_count.
   iExists recv_count.
    replace (uint.nat (W64 0)) with 0%nat by word.
   iFrame. done.
   }
  }
  {
    destruct cs.
    {
     iNamed "HCh".
    iDestruct (ghost_var_valid_2 with "Hpre Hsttok") as %[H ?].
    done.
    }
    {
     iNamed "HCh".
     iDestruct (ghost_var_agree with "Hsttok Hpre") as "%Hcontra". done. 
    }
    {
     iNamed "HCh". 
     unfold chan_state_to_nat in Hrawcs.
     assert (raw_cs = 2%nat).
     {
      injection Hrawcs. done.
     }
     word.
    }
    {
      iNamed "HCh". 
     unfold chan_state_to_nat in Hrawcs.
     assert (raw_cs = 3%nat).
     {
      injection Hrawcs. done.
     }
     word.
    }
    {
     iNamed "HCh". 
     iDestruct (ghost_var_agree with "Hsttok Hpre") as "%Hcontra". done. 
    }
    {
      done.
    }
    done.
  }
  }
Qed.

(* TODO: add q/is_single_party back, make i geq 0 not gt 0 *)
Lemma wp_Channel__SenderCompleteOrOffer (ch: loc) (i: nat) (v: val) (v0: val) (γ: chan_names) (chan_type: ty) (buff: Slice.t)  (mu_l: loc) (is_single_party: bool) (q: Qp) 
 (cs: chan_state) (raw_cs:nat) (send_count:nat) ( recv_count: nat)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
(#buff .(Slice.sz) = #(W64 0)) ->
cs ≠ closed ->
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
 
  "HCh" ∷ (isUnbufferedChan ch γ chan_type
  v0 cs raw_cs is_single_party send_count recv_count Psingle Pmulti Qsingle Qmulti R) ∗ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v0 ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false 
}}}
     Channel__SenderCompleteOrOffer chan_type #ch v
{{{  (exchange_result: w64) , RET #exchange_result; 
 ∃ (new_cs: chan_state) (new_raw_cs: nat) (new_i: nat) (new_send_count: nat)
 (new_v: val) ,
  "HCh" ∷ isUnbufferedChan ch γ chan_type
  new_v new_cs new_raw_cs is_single_party new_send_count recv_count Psingle Pmulti Qsingle Qmulti R ∗ 
  match uint.nat exchange_result with 
    | 0%nat => ((Q is_single_party i Qsingle Qmulti ∗ own_send_counter_frag γ new_i q ∗ 
       own_send_counter_auth γ new_send_count false ) ∗ ⌜ new_cs = sender_done ⌝ ∗ ⌜ new_i = S i ⌝ ∗  
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗  
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 4)  
       ∗ ⌜ new_send_count = S send_count ⌝ 
       ∗ ⌜ new_v = v ⌝ 
       )
    | 1%nat => ( 
    own_send_counter_frag γ new_i q ∗ 
      own_send_counter_auth γ send_count false ∗ ⌜ new_i = i ⌝ ∗ ⌜ new_cs = sender_ready ⌝ ∗ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 2) ∗  
       ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp true
       ∗ ⌜ new_v = v ⌝ 
      
      )
    | 2%nat => ( P is_single_party new_i v Psingle Pmulti ∗
      own_send_counter_frag γ new_i q ∗ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v0 ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
        own_send_counter_auth γ send_count false ∗ ⌜ new_i = i ⌝ ∗ ⌜ new_cs = cs ⌝ 
       ∗ ⌜ new_v = v0 ⌝ 
        
        ) 
    | _ => False
    end
}}}.
Proof.
  intros Hvt. intros Hbuff_zero. intros Hstate. intros Hsp.
   wp_start. iNamed "HCh".
   iAssert (  own_send_counter_auth γ send_count false ∗ 
  own_send_counter_frag γ i q ∗ (⌜ if is_single_party then  (send_count = i)  else (i <= send_count)%nat  ⌝%I) )%I with "[HSndCtrAuth HSen]" as "(HSndCtrAuth &HSen & %Hispz)".
    {
      destruct is_single_party.
      {
       subst q.  
      iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
      iFrame. done.
      }
      {
      iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
       iFrame. iPureIntro. done.
      }
    }
  wp_loadField. wp_if_destruct.
  {
    assert (cs = closed).
    {
      destruct cs.
      all: try(
        simpl in Hrawcs; inversion Hrawcs;
        subst raw_cs; word
      ).
      done.
    }
    subst cs. simpl in Hrawcs. inversion Hrawcs.
    subst raw_cs. done. 
    }
    wp_pures. wp_loadField.
    wp_if_destruct. {
      wp_storeField. wp_storeField.
      iDestruct ((send_counter_update γ send_count i) with "[$HSndCtrAuth $HSen]") as ">[HSndCtrAuth Hsen]".
      destruct is_single_party. {
        subst send_count.
       iApply "HΦ".
      assert (cs = receiver_ready).
      {
        destruct cs.
      all: try(
        simpl in Hrawcs; inversion Hrawcs;
        subst raw_cs; word
      ).
      done.
      }
      subst cs. iModIntro.   iExists sender_done.
      
      replace (uint.nat (W64 0)) with 0%nat by word.

      iNamed "HCh".
       unfold Q.
       replace recv_count with i%nat by lia.
      simpl. rewrite -> bool_decide_false by lia.
      { iFrame. 
        replace (i + 1)%nat with (S i) by lia.
        iFrame. iExists 4%nat.  iFrame.  iSplitR "".
        {
           iPureIntro.
         split.
         {
          done.
         }
         split.
         {
          unfold chan_state_to_nat. lia.
         }
         {
          val_ty.
         }
        }
        {
          done.
        }
      }
      } 
      {
      iApply "HΦ".
     assert (cs = receiver_ready).
     {
       destruct cs.
     all: try(
       simpl in Hrawcs; inversion Hrawcs;
       subst raw_cs; word
     ).
     done.
     }
     subst cs. iModIntro.   iExists sender_done.
     
     replace (uint.nat (W64 0)) with 0%nat by word.

     iNamed "HCh".
      unfold Q.
     simpl. rewrite -> bool_decide_false by lia.
     {
      unfold isUnbufferedChan. 
     iExists 4%nat. iExists (i + 1)%nat. iExists (S send_count)%nat.
      iExists v.  iFrame. 
       replace (i + 1)%nat with (S i) by lia.
       iFrame.   iFrame.  iSplitR "HQ".
       {
         iFrame. iPureIntro.
        split.
        {
         done.
        }
        split.
        {
         unfold chan_state_to_nat. lia.
        }
        {
         val_ty.
        }
       }
       {
        destruct bool_decide.
        {
         done. 
        }
         iFrame. done.
       }
     }
     } 
    }
    {
      wp_loadField.
      wp_if_destruct.
      {
       repeat wp_storeField.
       assert (cs = start).
      {
        destruct cs.
      all: try(
        simpl in Hrawcs; inversion Hrawcs;
        subst raw_cs; word
      ).
      done.
      }
      subst cs.
        iNamed "HCh".
        iMod ((ghost_var_update true) with "Hsttok") as "[Hsttok1 Hsttok2]".
        destruct is_single_party.
        {
        subst send_count.
       iModIntro. iApply "HΦ". 
      replace (uint.nat (W64 1)) with 1%nat by word.
      iExists sender_ready. iExists 2%nat. iExists i.
      iFrame.
       iPureIntro.  simpl.
      split.
      {
        done. 
      }
      done.
        }
        {
          iModIntro. iApply "HΦ". 
         replace (uint.nat (W64 1)) with 1%nat by word.
         iExists sender_ready. iExists 2%nat. iExists i.
         iFrame.
          iPureIntro.  simpl. exists recv_count%nat.
         split.
         {
           done. 
         }
         done.

        }
      }
      {
          iModIntro. iApply "HΦ". iFrame. iFrame. iPureIntro. 
          exists raw_cs. done.
      }
    }
Qed.

Lemma wp_Channel__BufferedTrySendFail (ch: loc) (i: nat) (v: val) (γ: chan_names) (chan_type: ty) (buff: Slice.t)  (mu_l: loc) (is_single_party: bool) (q: Qp) (first: nat) (size: Z) (count: Z)
 (cs: chan_state) (raw_cs:nat) (send_count:nat) ( recv_count: Z)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
(#buff .(Slice.sz) = #(W64 size)) ->
cs ≠ closed ->
raw_cs ≠ 5%nat ->
size > 0 -> 
uint.Z buff .(Slice.sz) ≤ uint.Z (W64 (send_count - recv_count)) ->
size + 1 < 2 ^ 63 ->
count + 1 < 2 ^ 63 ->
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
 
  "HCh" ∷   isBufferedChan ch γ chan_type size cs
  is_single_party send_count recv_count count
buff first Psingle Pmulti Qsingle Qmulti R ∗ 
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
  "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
    "%Hrawcs"  ∷ ⌜ chan_state_to_nat cs = Some raw_cs  ⌝ ∗ 
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false  
}}}
     Channel__BufferedTrySend chan_type #ch v
{{{   RET #false; 
 "HCh" ∷   isBufferedChan ch γ chan_type size cs
  is_single_party send_count recv_count count
buff first Psingle Pmulti Qsingle Qmulti R ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    "%Hrawcs"  ∷ ⌜ chan_state_to_nat cs = Some raw_cs  ⌝ ∗ 
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false 
}}}.
intros Hvt. intros Hbuff_zero.  intros Hcs. intros Hrawcs.  intros Hgtz. intros Hbuffspace.
intros Hsgen. intros Hrecv. intros Hsp.
   wp_start. iNamed "HCh". wp_loadField.
   wp_pures.
   assert (raw_cs ≠ 5%nat).
   {
    do 5 (destruct raw_cs;first done). 
    destruct raw_cs.
    {
      destruct cs.
      all: try done.
    }
    lia.
    }
    wp_if_destruct.
    {
      do 5 (destruct raw_cs;first done).
      destruct cs.
      all: try done;try lia;try word.
    }
    
   wp_loadField.
   wp_loadField.
   wp_apply wp_slice_len.
    destruct Hsizeinv as (Hcountsize & Hs0 & Hmax).
    iDestruct (slice.own_slice_small_sz with "HBuffSlice") as %Hsz.
 
    replace buff.(Slice.sz) with (W64 (length xs)) by word.
    replace (length xs) with (uint.nat buff .(Slice.sz))  by lia.
      wp_pures.
    wp_if_destruct.
    {
    assert ((uint.Z buff .(Slice.sz)) >  uint.Z (W64 (send_count - recv_count))).
    {
      word.
    }
    word.
    }
    {
     iModIntro. iApply "HΦ". iFrame "#". iFrame. rewrite Hsz.
     iFrame. 
     
     iPureIntro. unfold chan_state_to_nat.
     do 1 (split;first word).
     done.
    } 
Qed.

Lemma wp_Channel__BufferedTrySendSuccess (ch: loc) (i: nat) (v: val) (γ: chan_names) (chan_type: ty) (buff: Slice.t)  (mu_l: loc) (is_single_party: bool) (q: Qp) (first: nat) (size: Z) (count: nat)
 (cs: chan_state) (raw_cs: nat) (send_count:nat) ( recv_count: Z)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
(#buff .(Slice.sz) = #(W64 size)) ->
cs ≠ closed ->
raw_cs ≠ 5%nat ->
size > 0 -> 
uint.Z (W64 (count)) < uint.Z buff .(Slice.sz) ->
size + 1 < 2 ^ 63 ->
count + 1 < 2 ^ 63 ->
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
 
  "HCh" ∷   isBufferedChan ch γ chan_type size cs
  is_single_party send_count recv_count count
buff first Psingle Pmulti Qsingle Qmulti R ∗ 
  "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false  
}}}
     Channel__BufferedTrySend chan_type #ch v
{{{   RET #true; 
 "HCh" ∷   isBufferedChan ch γ chan_type size cs
  is_single_party (S send_count) recv_count (S count)
buff first Psingle Pmulti Qsingle Qmulti R ∗ 
 "HQ"  ∷  Q is_single_party (i - size) Qsingle Qmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ (S i) q ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 raw_cs) ∗  
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 (S count)) ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ (S send_count) false  
}}}.
  intros Hvt. intros Hbuff_zero. intros Hstate. intros Hgtz. intros Hbuffspace. intros Hsz.
  intros Hcount.
  intros Hsp. 
  intros Hsp2.
  wp_start. iNamed "HCh". wp_loadField. 
  wp_if_destruct.
  {
    admit.
  }
  {
    destruct Hsizeinv as (Hcountsize & Hs0 & Hmax).
    iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag".

  iDestruct (slice.own_slice_small_sz with "HBuffSlice") as %Hsize.
 
      replace buff.(Slice.sz) with (W64 (length xs)) by word.
      replace (length xs) with (uint.nat buff .(Slice.sz)) .
      wp_pures.
      wp_loadField.
    assert (size = (length xs)%Z).
    {
        replace size with (Z.of_nat (uint.nat (W64 size))).
        {

         replace (W64 size) with (buff .(Slice.sz)).
         {
          word.
         }
         {
          inversion Hbuff_zero. done.
         }
        }
        { word.
        }
    }
    subst size.
    destruct Hmax as (Hs1 & Hs2 & Hs3).
    
  
   wp_loadField.
   wp_apply wp_slice_len. 
   wp_if_destruct.
  { wp_loadField. wp_loadField. wp_loadField.
    wp_apply wp_slice_len.  wp_apply wp_ref_to;first val_ty.
    iIntros (buf) "Hbuffersize". wp_pures.
    wp_load. wp_loadField.
    iPoseProof (slice.own_slice_small_sz with "HBuffSlice") as "%".

    wp_apply (slice.wp_SliceSet with "[$HBuffSlice]").
                { iPureIntro. split.
                  { apply lookup_lt_is_Some_2. word. }
                  { val_ty. }
                }
    iIntros "Hoss". wp_pures. wp_loadField. wp_storeField.
    destruct is_single_party.
    {
      subst q. 
      iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
       subst send_count.

    iDestruct ((send_counter_update γ i i) with "[$HSndCtrAuth $HSen]") as ">[HSndCtrAuth HSen]".
    iModIntro. iApply "HΦ". iFrame "HSen HSndCtrAuth".
    unfold isBufferedChan.
    iDestruct ((big_sep_seq_pop i ((length xs) - count)  (λ i0 : Z, Q true (i0 - (length xs)) Qsingle Qmulti)) with "[HQs]") as "[HQ HQs]".
    {
     word. 
    }
    {
      
     iFrame. 
    }
    iFrame "HQ". 
    replace ((w64_word_instance .(word.add) (W64 count) (W64 1))) with (W64 (S count)) by word.
    
    iFrame "count".
    iFrame "chan_state".
    iExists (<[uint.nat
    (w64_word_instance .(word.modu)
    (w64_word_instance .(word.add) (W64 first) (W64 (i - recv_count))) buff
    .(Slice.sz)):=v]>
    xs).
    replace ((w64_word_instance .(word.add) (W64 count)
    (W64 1))) with ((W64 (S i - recv_count))) by word.

    

    unfold Q.
    replace ((length xs) - (S i - recv_count))%Z with (((length xs) - count - 1))%Z
    by lia. replace (S i) with (i + 1)%nat by lia.
    replace (Z.of_nat (i+1)%nat) with (i+1) by word.
    iFrame.
    iFrame "%".
    replace (i + 1 - recv_count) with (Z.of_nat (S count)) by word.
    iFrame.
    iSplitL "".
    { iPureIntro. done.
      }



    edestruct (list_lookup_Z_lt xs (uint.nat
    (word.modu
      (word.add first count)
      buff.(Slice.sz)))).
      { word. }
        replace buff.(Slice.sz) with (W64 (length xs)).
        {
          replace (i - recv_count) with (Z.of_nat count) by word.
          replace  ((W64 ((S count)%nat))) with ((w64_word_instance .(word.add) (W64 (count)) (W64 1)))  by word. 
    rewrite (add_one xs first count v).
    {
     iFrame.
      
     rewrite big_sepL_singleton. unfold valid_elems.
     simpl.
     rewrite subslice_length.
     {
      Check (recv_count + (uint.nat (W64 first) + uint.nat (W64 (i - recv_count)) - uint.nat (W64 first) +
      0)%nat).
      Check (i%Z).
      replace (length xs - count - 1) with (length xs - S count) by lia.
      iFrame.
      iEval (replace (Z.of_nat i) with (recv_count + (uint.nat (W64 first) + uint.nat (W64 count) - uint.nat (W64 first) + 0)%nat) by word) in "HP".
      iFrame. iPureIntro. rewrite length_insert. word.
     }
     {
      rewrite length_app. word.
     }
    }
     {
        word.
     }
     {
      word.
     }
     {
      word.
     }
     {
      word.
     }
  }
}
     {
      

    iDestruct ((send_counter_update γ send_count i) with "[$HSndCtrAuth $HSen]") as ">[HSndCtrAuth HSen]".
    iModIntro. iApply "HΦ". iFrame "HSen HSndCtrAuth ".
    unfold isBufferedChan.
    iDestruct ((big_sep_seq_pop send_count ((length xs) - count)  (λ i0 : Z, Q false (i0 - (length xs)) Qsingle Qmulti)) with "[HQs]") as "[HQ HQs]".
    {
     word. 
    }
    {
     iFrame. 
    }
    unfold Q.
    iFrame "chan_state".
    replace ((w64_word_instance .(word.add) (W64 count) (W64 1))) with (W64 (S count)) by word.
    iFrame "count".


    iSplitR "HQ".
    {
    iExists (<[uint.nat
    (w64_word_instance .(word.modu)
    (w64_word_instance .(word.add) (W64 first) (W64 count)) buff
    .(Slice.sz)):=v]>
    xs).

   

    unfold Q.
    replace ((length xs) - (S count))%Z with (((length xs) - (count) - 1))%Z
    by lia. replace (S send_count) with (send_count + 1)%nat by lia.
    replace (big_sep_seq (send_count + 1)%nat ((length xs) - (count) - 1)) 
    with (big_sep_seq (send_count + 1) ((length xs) - (count) - 1)).
    {
      iFrame.
 
    replace (w64_word_instance .(word.add)
    (W64 (count)) (W64 1)) with (W64 (S count)) by word.
    iFrame.
    iFrame "%".
    iSplitL "".
    { iPureIntro. word.
      }
    iSplitL "".
    { rewrite length_insert. iPureIntro. word. }


    edestruct (list_lookup_Z_lt xs (uint.nat
    (word.modu
      (word.add first count)
      buff.(Slice.sz)))).
      { word. }
        replace buff.(Slice.sz) with (W64 (length xs)).
        {
          replace  ((W64 (S count))) with ((w64_word_instance .(word.add) (W64 (count)) (W64 1)))  by word. 
    rewrite (add_one xs first (count) v).
    {
     iFrame.
     simpl. iPureIntro. rewrite length_insert. done.
    }
      
    
     {
        word.
     }
     {
      word.
     }
     {
      word.
     }
     {
      word.
     }
  }
}
     {
         replace ((Z.of_nat send_count + 1)) with ((Z.of_nat (send_count + 1))) by lia.
         done.
     }
    }
    {
      destruct (decide (send_count - length xs < 0)).
      {
      assert (i - length xs < 0) by lia.
      do 2 (rewrite -> bool_decide_true by lia).
      done.
    }
    {
      
      rewrite bool_decide_false.
      {
        destruct (bool_decide(i - length xs < 0)).
        {
          done.
        }
        iFrame.
      }
      {
       lia. 
      }
    }
    }
     }
  }

Qed.
       

Lemma wp_Channel__TrySend (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
size + 1 < 2 ^ 63 ->
{{{ "HCh"  ∷  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
 "HP"  ∷  P is_single_party i v Psingle Pmulti ∗ "HSc" ∷ own_send_counter_frag γ i q
}}}
     Channel__TrySend chan_type #ch v
{{{ (selected: bool), RET #selected; 
  if selected then 
    (Q is_single_party (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q)
  else 
    ( P is_single_party i v Psingle Pmulti ∗ own_send_counter_frag γ i q) 
}}}.
Proof.
  intros Hvt.  intros Hnn. intros Hsp. intros Hsgt64. wp_start.
  iNamed "HCh".
  wp_loadField. wp_pures. wp_apply wp_slice_len.
  wp_apply wp_ref_to;first val_ty. iIntros (sz) "Hsz".
  wp_pures. wp_load. wp_if_destruct.
  {
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock"). 
          iIntros "[locked inv]". wp_pures.
          unfold isChanInner.
          iNamed "inv".
          iAssert (⌜ raw_cs ≠ 5%nat ⌝ ∗ own_send_counter_frag γ i q
          )%I with "[HCloseTokPostClose HSc]" as 
"[H1 H2]".
{
  destruct (decide(raw_cs = 5%nat)).
  {
    assert (cs = closed).
    {
      replace raw_cs with 5%nat in Hrawcs.
      unfold chan_state_to_nat in Hrawcs.
      destruct cs. 
      all: try done.
    }
    destruct cs.
    all: try done.
    iNamed "HCloseTokPostClose".
    iDestruct "HCloseTokPostClose" as "[Hct Hsc]".
      iCombine "Hsc" "HSc" as "H" gives %Hvalid. 
     apply auth_frag_op_valid_1 in Hvalid.
               rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
               rewrite Some_valid in Hvalid.
               rewrite <- (pair_op 1%Qp q n i) in Hvalid.
               rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
               rewrite frac_op in Hqvalid.

               assert (((1 + q)%Qp ≤ 1)%Qp).
               { 
            
               done. }

               apply Qp.not_add_le_l in H0.
               contradiction.
               }
               {
                iFrame.
                done.
               }
}
{


    assert (size > 0).
    {
      destruct size.
      {
       word. 
      }
     lia. 
    }
    set sizeminus := ( size - 1)%nat.
    replace size with  (S sizeminus) by lia.
      iDestruct "H1" as "%H1".
    
    assert (cs ≠ closed ).
    {
     destruct cs.
     all: try done.
     unfold chan_state_to_nat in Hrawcs.
     inversion Hrawcs in H1. lia. 
    }
    destruct (decide(uint.Z buff .(Slice.sz) ≤ uint.Z (W64 (count)))).
    {
      iNamed "HBuffUnbuff".
      
      wp_apply ((wp_Channel__BufferedTrySendFail ch i v γ chan_type buff mu_l is_single_party q first size count cs raw_cs send_count recv_count 
      Psingle Pmulti Qsingle Qmulti R ) with "[ HP H2 HSndCtrAuth
      chan_state count HBuffSlice HPs HQs first]").
      all: try done.
      {
        inversion Hbuffsize.
        done.
      }
      {
        unfold chan_state_to_nat in Hrawcs.
        inversion Hrawcs.
        
        
        word.
      }
      {
        word.
      }
    {
      replace (S sizeminus) with size by lia. 
      replace (S sizeminus) with size  in HLxsSize by lia.
      replace (length xs) with size in Hsizeinv by lia.

      replace (S sizeminus) with size by lia. 
      replace (S sizeminus) with size  in HLxsSize by lia.
       unfold send_ctr_frozen.
      
       iFrame. iFrame "#". 
       destruct cs.
       {
        iFrame; iPureIntro.
        split. { lia. }
        done.
       }
       {
        iFrame; iPureIntro.
        split. { lia. }
        apply Hrawcs.
       }
       {
        iFrame; iPureIntro.
        split. { lia. }
        apply Hrawcs.
       }
       {
        iFrame; iPureIntro.
        split. { lia. }
        apply Hrawcs.
       }
       {
        iFrame; iPureIntro.
        split. { lia. }
        apply Hrawcs.
       }
       {
        exfalso. apply H0.
        done.
       }
       {
       iFrame. done.
       }
    }
    {

        iIntros "H". iNamed "H". wp_loadField.
        wp_apply (wp_Mutex__Unlock
        with "[$Hlock Hsz HRcvCtrAuth HCh value chan_state count  HSndCtrAuth $locked]").
        {
          iModIntro. iFrame. iExists first.  

          iFrame.
      replace (S sizeminus) with size by lia. unfold send_ctr_frozen.
      destruct cs.
      all: try (iFrame;done).
        }

      {
        wp_pures. iModIntro.
       iApply "HΦ". iFrame. 
      }
    }
  }
  {
    iNamed "HBuffUnbuff".

  wp_apply ((wp_Channel__BufferedTrySendSuccess ch i v γ chan_type buff mu_l is_single_party q first size count start send_count recv_count 
  Psingle Pmulti Qsingle Qmulti R ) with "[HP H2 HSndCtrAuth chan_state count HBuffSlice HPs HQs first]").
    all: try done.
    {
      inversion Hbuffsize.
      done.
    }
    {

      word.

    }
   {
      lia.
   }
   {
      replace (S sizeminus) with size by lia.
      iFrame. iFrame "#".
      unfold chan_state_to_nat in Hrawcs.
       iFrame. iPureIntro. word.
    }
    {
      iIntros "H". 
      iNamed "H". wp_loadField.
        wp_apply (wp_Mutex__Unlock
        with "[$Hlock HCh HSndCtrAuth value HCloseTokPostClose HRcvCtrAuth 
        chan_state count  $locked]").
        {
          iModIntro. unfold isChanInner.  iExists 0%nat.
          iExists start. iExists (S count). iExists first.
          iExists v0. iExists (S send_count) . iFrame.
          replace size with (S sizeminus) by lia. iFrame.
          iPureIntro. unfold chan_state_to_nat. 
          replace  (S sizeminus) with size  in HLxsSize by lia. 
          replace (length xs) with size in Hsizeinv by lia.
          replace count with (send_count - recv_count)%nat in Hsizeinv by lia.
          done.
        }

        
        {
         wp_pures. iModIntro. iApply "HΦ". iFrame.
         replace (i + 1)%nat with (S i) by lia.
         iFrame.
        }
    }
  }
    }
    {
      unfold isBufferedChan. iNamed "HBuffUnbuff".
      done.
    }
    {
      unfold isBufferedChan. iNamed "HBuffUnbuff".
      done.
    }
    {
      unfold isBufferedChan. iNamed "HBuffUnbuff".
      done.
    }
    {
      unfold isBufferedChan. iNamed "HBuffUnbuff".
      done.
    }
    {
      unfold isBufferedChan. iNamed "HBuffUnbuff".
      iNamed "HCloseTokPostClose".
      iDestruct "HCloseTokPostClose" as "[Hct Hsc]".
      unfold own_close_perm.
   
      iCombine "Hsc" "HSc" as "H" gives %Hvalid. 
     apply auth_frag_op_valid_1 in Hvalid.
               rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
               rewrite Some_valid in Hvalid.
               rewrite <- (pair_op 1%Qp q n i) in Hvalid.
               rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
               rewrite frac_op in Hqvalid.

               assert (((1 + q)%Qp ≤ 1)%Qp).
               { 
            
               done. }

               apply Qp.not_add_le_l in H0.
               contradiction.
               }
               {
                iNamed "HBuffUnbuff".
                done.
               }
  }
  {
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock"). 
    iIntros "[locked inv]". wp_pures.
    unfold isChanInner.
    iNamed "inv".
      assert (size = 0%nat).
      {
        word.
      }
      subst size.
    destruct  (decide(raw_cs = 5%nat)).
    {
      unfold isUnbufferedChan. iNamed "HBuffUnbuff".
     assert (cs = closed).
     {
      subst raw_cs .
      destruct cs.
      all: try done.
     }
     subst cs.
     iNamed "HCloseTokPostClose".
     iDestruct "HCloseTokPostClose" as "[HCloseTokPostClose Hsc]".
      iCombine "Hsc" "HSc" as "H" gives %Hvalid. 
     apply auth_frag_op_valid_1 in Hvalid.
               rewrite <- (Some_op (1%Qp, n) (q, i)) in Hvalid.
               rewrite Some_valid in Hvalid.
               rewrite <- (pair_op 1%Qp q n i) in Hvalid.
               rewrite pair_valid in Hvalid. destruct Hvalid as [Hqvalid Hivalid].
               rewrite frac_op in Hqvalid.

               assert (((1 + q)%Qp ≤ 1)%Qp).
               {
                done.
               }
               apply Qp.not_add_le_l in H.
               contradiction.
    }
    {
      unfold isUnbufferedChan.
      iNamed "HBuffUnbuff".
      assert (cs ≠ closed).
      {
       destruct cs.
       all: try done.
       unfold chan_state_to_nat in Hrawcs.
       inversion Hrawcs. lia.
      }
      iAssert ((isUnbufferedChan ch γ chan_type v0 cs raw_cs is_single_party send_count recv_count
      Psingle Pmulti Qsingle Qmulti R)%I)  with "[chan_state HBuffUnbuff]" as "HBuffUnbuffs".
      {
       iFrame. iPureIntro. done. 
      }

      Check size.
    wp_apply ((wp_Channel__SenderCompleteOrOffer ch i v v0 γ chan_type buff mu_l is_single_party q 
     cs raw_cs send_count recv_count Psingle Pmulti Qsingle Qmulti R) with "[HSndCtrAuth HBuffUnbuffs HP HSc value]").
    {
      done.
    }
    {
      inversion Heqb. done.
    }
    {
      done.
    }
    {
     done. 
    }
    {
     iFrame.
     destruct cs.
     {

      iFrame.
     }
     {
       unfold send_ctr_frozen.
      iFrame.
     }
     {
       unfold send_ctr_frozen.
      iFrame.

     }
     {
       unfold send_ctr_frozen.
      iFrame.

     }
     {
       unfold send_ctr_frozen.
      iFrame.

     }
     {
      done.
     }
     done.
    }
    {
      iIntros (exchange_result). iIntros "IH". iNamed "IH".
      wp_pures.
      destruct (uint.nat exchange_result).
      {
        wp_loadField.
      (*  wp_apply (wp_Mutex__Unlock
        with "[$Hlock HCh HSndCtrAuth value HCloseTokPostClose HRcvCtrAuth  $locked]").
        {
          iModIntro. unfold isChanInner.  iExists 0%nat.
          iExists start. iExists (S count). iExists first.
          iExists v0. iExists (S send_count) . iFrame.
          replace size with (S sizeminus) by lia. iFrame.
        }
        {
         wp_pures. iModIntro. iApply "HΦ". iFrame.
         replace (i + 1)%nat with (S i) by lia.
         iFrame.
        }

      }


    }
      unfold isUnbufferedChan. unfold send_ctr_frozen.
      iFrame. iNamed "HBuffUnbuffs". iFrame. iPureIntro.
      split.
      { done. }
      
      done. iExists send_or_recv_tok. iFrame.
     } 
    }


  }

      done.
    }
          iExists (S count). iExists first. iExists v. 

          iFrame.
      replace (S sizeminus) with size by lia. iFrame.
        }
      {
        wp_pures. iModIntro.
       iApply "HΦ". iFrame. 
      }
    }



  } *)

Lemma wp_Channel__TrySend (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)  
(is_single_party: bool) (cs: chan_state) (send_count:nat) ( recv_count: Z)  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
  "HCh" ∷ (isUnbufferedChan ch γ chan_type
  v cs is_single_party send_count recv_count Psingle Pmulti Qsingle Qmulti R) ∗ 
  "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false 
}}}
     Channel__TrySend chan_type #ch v
{{{  (selected: bool), RET #selected; 
  "HCh" ∷ isUnbufferedChan ch γ chan_type
  v cs is_single_party send_count recv_count Psingle Pmulti Qsingle Qmulti R ∗ 
  if selected then 
  (Q is_single_party i Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q ∗ 
  "HSen" ∷ own_send_counter_frag γ (i+1) q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ (send_count + 1) false )
    else 
    (
      "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
      "HSen" ∷ own_send_counter_frag γ (i+1) q ∗ 
      "HSndCtrAuth" ∷ own_send_counter_auth γ (send_count + 1) false
    )
}}}.
Proof.
  intros Hvt.  intros Hisp. wp_start.
  wp_loadField. wp_pures. wp_apply wp_slice_len.
  wp_apply wp_ref_to;first val_ty. iIntros (sz) "Hsz".
  wp_pures. wp_load. wp_if_destruct.
  {
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock"). 
          iIntros "[locked inv]". wp_pures.
          iNamed "inv".


  }

Admitted.



Lemma wp_Channel__New (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
0 < size ∧ size + 1 < 2 ^ 63 ->
has_zero chan_type ->
{{{ True }}}
     NewChannelRef chan_type #size
   {{{(ch: loc) (γ: chan_names), RET #ch; 
    isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗ 
    own_recv_perm γ 1%Qp 0 R ∗
    own_closed_tok_auth γ R ∗ 
    own_send_counter_frag γ 0 1%Qp
}}}.
  Proof.
    intros Hs Hz.
  try (iModIntro (□ _)%I);
  let x := ident:(Φ) in
  iIntros (Φ) "Hpre HΦ";
  try wp_rec.
    rewrite -wp_fupd.
   wp_apply (wp_new_free_lock). iIntros (mu) "Hlock".
   wp_pures.
   wp_apply wp_new_slice;first done.
   iIntros (slice_ptr) "Hbuffslice".
   unfold slice.own_slice. 
  wp_apply(wp_allocStruct (Channel chan_type)).
  { val_ty. }
  iIntros (ch). iIntros "Hchan".
   iNamedStruct "Hchan".
   iMod (struct_field_pointsto_persist with "lock") as "#mu".
   iMod (struct_field_pointsto_persist with "buffer") as "#buff".
   iMod (own_chan_ghost_alloc R) as (γ0) "(HSndAuth & HSndFrag & HRcvAuth & HRcvPrm & HCtf)".
   {
     iDestruct "Hbuffslice" as "[Hbss Hcap]".
     destruct size.
     {
    iMod ((slice.own_slice_small_persist ) with "Hbss")
     as "#Hbuffslice". 
  iMod ((alloc_lock (nroot .@ "Channel") _ mu (
    (isChanInner ch γ0 chan_type
    0 is_single_party slice_ptr Psingle Pmulti Qsingle Qmulti R)
  )) with 
  "Hlock [ state $v count first HSndAuth HRcvAuth]" ) as "#Hch".
  {
    iFrame.
    iExists 0%nat. iExists start. iExists 0%nat. iExists 0%nat. iExists 0%nat. iExists 0%nat.
    simpl. unfold recv_ctr_frozen. iFrame. done.
  }
  {
    iModIntro. iApply "HΦ". iFrame "#". replace (uint.nat (W64 0%nat)) with 0%nat by word.
    rewrite replicate_0. unfold slice.own_slice_small. iDestruct "Hbuffslice" as "(#Hsp & %Hlt)".
    destruct Hlt as (Hlt & Hsizecap).
    simpl in Hlt. iSplitL "". { word. }
    iFrame. 
  }
  }
  {
    unfold slice.own_slice_small.
    iDestruct "Hbss" as "[Hbss %Hpurestuff]". 
    iMod ((alloc_lock (nroot .@ "Channel") _ mu (
    (isChanInner ch γ0 chan_type
    (S size) is_single_party slice_ptr Psingle Pmulti Qsingle Qmulti R)
  )) with 
  "Hlock [ state $v count first HSndAuth HRcvAuth Hbss ]" ) as "#Hch".
  {
    iModIntro. iFrame. iFrame "#". iExists 0%nat. iExists start.
    iExists 0%nat. iExists 0%nat. iExists 0%nat. iExists 0%nat. 
    iFrame. simpl. unfold isBufferedChan. simpl. iFrame "#".
    iSplitL "";first done.
    iSplitL "";first done. 


    unfold big_sep_seq.
    iAssert (big_sep_seq 0 0 (λ i,Q is_single_party
    (i - size - 1) Qsingle
    Qmulti)) as "Hnil".
    {
      iApply big_sep_seq_nil. done.
    }



    iDestruct (big_sepL_intro (λ i,(λ i,Q is_single_party
    (i - (S size)) Qsingle
    Qmulti)) (seqZ 0%Z (S size)%Z)) as "H".
    iAssert ([∗ list] x ∈ seqZ 0 (S size), Q is_single_party (x - (S size))
      Qsingle Qmulti)%I with "[H]" as "HQs".
    {
      iApply "H". iIntros (k x). iIntros "%Hseq".
      rewrite -> (lookup_seqZ 0 (S size) k x) in Hseq.
      destruct Hseq as [Hs1 Hs2].  subst x.
       destruct k.
      { unfold Q. assert (0 ≤  size). { lia. }
        rewrite bool_decide_true. { done. } { lia. } }
        unfold Q. rewrite bool_decide_true.
        { done. }
      lia.
      

    } iFrame "#".
    iFrame. iFrame "%".
    unfold buff_size_inv. iFrame "%".
    simpl. unfold valid_elems.
    assert ((uint.nat (W64 0%nat) + uint.nat (W64 0%nat)) = 0).
    { word. }
    replace ((uint.nat (W64 0%nat) + uint.nat (W64 0%nat))) with 0.
    assert ((uint.nat (W64 0%nat)) = 0%nat).
    { done. }
    replace (uint.nat (W64 0%nat)) with 0%nat. 
    simpl. iExists (replicate (uint.nat (W64 (S size)))
    (zero_val chan_type)).
    iFrame "%". unfold slice.own_slice_small.  simpl. iSplitL "Hbss".
    {
      iFrame. iPureIntro. word.
    } iFrame "%".
    rewrite length_replicate. iPureIntro.
    intuition.
    { word. }
    { word. }
    { word. }
    { word. }
    { word. }
  }
  {

        iModIntro. iApply "HΦ". iFrame "#". iFrame.
        destruct Hpurestuff as (H1 & H2). rewrite length_replicate in H1.
         iPureIntro. simpl in H1. 
         assert ((slice_ptr .(Slice.sz)) = (W64 (S size))).
         { word. }
         replace (slice_ptr .(Slice.sz)) with (W64 (S size)).
         done.

      }
  }
   }
  Qed.

  Lemma wp_Channel__Close (ch: loc) (n: nat) (γ: chan_names) (chan_type: ty) 
  (size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
#ch ≠ #null ->
  {{{ 
    isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
    own_close_perm γ R n
  }}}
       Channel__Close chan_type #ch
  {{{ RET #(); True }}}.
  Proof.
  Admitted.

Lemma wp_Channel__Send (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
val_ty v chan_type -> 
#ch ≠ #null ->
size + 1 < 2 ^ 63 ->
(if is_single_party then q = 1%Qp else ((q < 1)%Qp)) ->
{{{ 
  "#HCh" ∷ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q
}}}
     Channel__Send chan_type #ch v
{{{ RET #(); 
  Q is_single_party (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q
}}}.
Admitted.




Lemma wp_Channel__Receive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri:nat -> iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q is_single_party i Qsingle Qmulti ∗ 
  own_recv_perm γ q i Ri 
}}}
     Channel__Receive chan_type #ch
{{{ (v: val) (ok: bool), RET (v,#ok); 
  (P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝)
    ∨  
  ( own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
    ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
}}}.
Admitted.

Lemma wp_Channel__ReceiveDiscardOk (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
#ch ≠ #null ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri:nat -> iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q is_single_party i Qsingle Qmulti ∗ 
  own_recv_perm γ q i Ri 
}}}
     Channel__ReceiveDiscardOk chan_type #ch
{{{ (v: val), RET (v); 
  (P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜val_ty v chan_type⌝)
    ∨  
  (own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝
    ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
}}}.
Admitted.

Lemma wp_Channel__TryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R:nat -> iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri:nat -> iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri 
}}}
     Channel__TryReceive chan_type #ch
{{{ (v: val) (ok: bool) (selected: bool), RET (#selected,v,#ok); 
  if selected then 
    ((P is_single_party i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝)
    ∨  
    ( own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
      ∗ ∃ n, (Ri n) ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
    )
  else 
    ( Q is_single_party i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
}}}.
Admitted.



End proof.




