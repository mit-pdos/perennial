From Perennial.goose_lang Require Import prelude. 
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode array.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.automation Require Import extra_tactics.
From Perennial.goose_lang.lib Require Import
      persistent_readonly slice slice.typed_slice struct loop lock control map.typed_map time proph rand string typed_mem.

From Perennial.goose_lang.lib.channel Require Import auth_set.
From Perennial.goose_lang.lib.channel Require Import chan_use_ctr.
From Goose.github_com.goose_lang.goose Require Import channel.
From Perennial.goose_lang Require Import lang typing.


Section proof.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}. 
Context `{!closePropTrackerG Σ, !inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!ghost_varG Σ (bool * val)}.

Implicit Types (v:val).

(* Define valid states as an inductive type *)
Inductive valid_chan_state := 
  | Valid_start
  | Valid_receiver_ready
  | Valid_sender_ready
  | Valid_receiver_done
  | Valid_sender_done
  | Valid_closed.


(* Define equality comparison for valid_chan_state *)
Definition valid_chan_state_eq (vs1 vs2: valid_chan_state) : bool :=
  match vs1, vs2 with
  | Valid_start, Valid_start => true
  | Valid_receiver_ready, Valid_receiver_ready => true
  | Valid_sender_ready, Valid_sender_ready => true
  | Valid_receiver_done, Valid_receiver_done => true
  | Valid_sender_done, Valid_sender_done => true
  | Valid_closed, Valid_closed => true
  | _, _ => false
  end.

(* Notation for equality *)
Notation "vs1 =?= vs2" := (valid_chan_state_eq vs1 vs2) (at level 70).


(* Define word constants to match Go implementation *)
Definition CS_START_W : w64 := W64 0.
Definition CS_RECEIVER_READY_W : w64 := W64 1.
Definition CS_SENDER_READY_W : w64 := W64 2.
Definition CS_RECEIVER_DONE_W : w64 := W64 3.
Definition CS_SENDER_DONE_W : w64 := W64 4.
Definition CS_CLOSED_W : w64 := W64 5.

(* Conversion function from valid state to word representation *)
Definition valid_to_word (vs: valid_chan_state) : w64 := 
  match vs with
    | Valid_start => CS_START_W
    | Valid_receiver_ready => CS_RECEIVER_READY_W
    | Valid_sender_ready => CS_SENDER_READY_W
    | Valid_receiver_done => CS_RECEIVER_DONE_W
    | Valid_sender_done => CS_SENDER_DONE_W
    | Valid_closed => CS_CLOSED_W
  end.

(* Helper function to check if a word corresponds to a valid channel state *)
Definition is_valid_cs_word (w: w64) : bool :=
  match word.unsigned w with
  | 0 | 1 | 2 | 3 | 4 | 5 => true
  | _ => false
  end.

(* Helper lemma for valid states *)
Lemma valid_states_eq_dec : forall (vs1 vs2 : valid_chan_state),
  {vs1 = vs2} + {vs1 ≠ vs2}.
Proof.
  decide equality.
Qed.

(* Helper functions for state properties *)
Definition send_ctr_frozen (vs: valid_chan_state): bool :=
  match vs with 
    | Valid_closed => true
    | _ => false
  end.

Definition recv_ctr_frozen (vs: valid_chan_state) (send_count recv_count: nat): bool :=
  match vs with
    | Valid_closed => (send_count =? recv_count)
    | _ => false
  end.

Definition full_exchange_token (γ: chan_names): iProp Σ :=
  ghost_var γ.(unbuffered_state_tracker_name) 1%Qp (true, #()).

Definition exchange_token (γ: chan_names) (sender_initiated: bool) (v: val): iProp Σ :=
  ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp (sender_initiated, v).

(* Half token for sender - contains both flag and value *)
Definition sender_exchange_token (γ: chan_names) (v: val): iProp Σ :=
exchange_token γ true v.

(* Half token for receiver - contains only flag *)
Definition receiver_exchange_token (γ: chan_names): iProp Σ :=
∃ dummy_v, 
exchange_token γ false dummy_v.

  Lemma exchange_token_combine γ:
  ∀ sender_initiated sender_initiated' v v',
  exchange_token γ sender_initiated v ∗
  exchange_token γ sender_initiated' v' ==∗
  full_exchange_token γ.
Proof.
  unfold exchange_token, full_exchange_token.
  iIntros (sender_initated). iIntros (sender_initiated').
  iIntros (v v').
  iIntros "[Htok1 Htok2]".
  iCombine "Htok1 Htok2" as "Htok" gives "%Hvalid".
  iApply (ghost_var_update (true, #()) with "Htok").
Qed.

Lemma exchange_token_agree(γ : chan_names) (sender_initiated sender_initiated' : bool) (v v' : val) :
exchange_token γ sender_initiated v  -∗  exchange_token γ sender_initiated' v' -∗ ⌜ v = v' ∧ sender_initiated = sender_initiated' ⌝ .
iIntros "H1". iIntros "H2".
iDestruct (ghost_var_agree with "[$H1] [$H2]") as "%H". iPureIntro. injection H.
intros H1. intros H2. done.
Qed.

Lemma exchange_token_split γ sender_initiated v:
  full_exchange_token γ ==∗
  exchange_token γ sender_initiated v ∗
  exchange_token γ sender_initiated v.
Proof.
  unfold full_exchange_token, exchange_token.
  iIntros "Htok".
  iMod (ghost_var_update (sender_initiated, v) with "Htok") as "Htok".
  iDestruct "Htok" as "[Htok1 Htok2]".
  iModIntro. iFrame.
Qed.


Lemma sender_exchange_token_split γ v:
  full_exchange_token γ ==∗
  sender_exchange_token γ v ∗
  sender_exchange_token γ v.
Proof.
  unfold  sender_exchange_token. apply exchange_token_split.
Qed.

(* Receiver token split lemma *)
Lemma receiver_exchange_token_split γ:
  full_exchange_token γ ==∗
  receiver_exchange_token γ ∗
  receiver_exchange_token γ.
Proof.
  unfold receiver_exchange_token, full_exchange_token.
  iIntros "Htok".
  iMod (ghost_var_update (false, #()) with "Htok") as "[Htok1 Htok2]".
  iFrame. done.
Qed.

(* Combine sender tokens *)
Lemma sender_exchange_token_combine γ v v':
  sender_exchange_token γ v ∗ sender_exchange_token γ v' ==∗
  full_exchange_token γ.
Proof.
  unfold sender_exchange_token.
  iIntros "[Htok1 Htok2]".
  iApply (exchange_token_combine γ true true v v' with "[Htok1 Htok2]").
  iFrame.
Qed.

(* Combine receiver tokens *)
Lemma receiver_exchange_token_combine γ:
  receiver_exchange_token γ ∗ receiver_exchange_token γ ==∗
  full_exchange_token γ.
Proof.
  unfold receiver_exchange_token.
  iIntros "[Htok1 Htok2]".
  iDestruct "Htok1" as (dummy_v1) "Htok1".
  iDestruct "Htok2" as (dummy_v2) "Htok2".
  iApply (exchange_token_combine γ false false dummy_v1 dummy_v2 with "[Htok1 Htok2]").
  iFrame.
Qed.

(* Sender token agreement - useful for verification *)
Lemma sender_exchange_token_agree γ v v':
  sender_exchange_token γ v -∗ sender_exchange_token γ v' -∗ ⌜v = v'⌝.
Proof.
  unfold sender_exchange_token.
  iIntros "Htok1 Htok2".
  iDestruct (exchange_token_agree γ true true v v' with "[$Htok1] [$Htok2]") as "(%Hv & _)".
  iPureIntro. exact Hv.
Qed.

Definition P (is_single_party: bool) (i:Z)
 (v: val) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)): iProp Σ :=
 if is_single_party then Psingle i v else Pmulti v.

Definition Q (is_single_party: bool) (z: Z) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ): iProp Σ := 
if bool_decide(Z.lt z 0%Z) then True%I else (if is_single_party then Qsingle(z) else Qmulti).

(* Core representation of channel state - pure facts *)
Definition chan_state_facts (vs: valid_chan_state) (send_count recv_count: nat) (v: val) (chan_type: ty): iProp Σ :=
  match vs with
    | Valid_start => ⌜send_count = recv_count⌝
    | Valid_receiver_ready => ⌜send_count = recv_count⌝
    | Valid_sender_ready => (⌜send_count = recv_count⌝ ∗ ⌜val_ty v chan_type⌝)
    | Valid_receiver_done => ⌜recv_count = S send_count⌝ 
    | Valid_sender_done => (⌜send_count = S recv_count⌝ ∗ ⌜val_ty v chan_type⌝)
    | Valid_closed => ⌜send_count = recv_count⌝
  end.

  Definition chan_state_resources (vs: valid_chan_state) (γ: chan_names) (is_single_party: bool)
  (send_count recv_count: nat) (v: val)
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ)
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ): iProp Σ :=
match vs with
| Valid_start => 
full_exchange_token γ (* Full token with default value *)
| Valid_receiver_ready => 
receiver_exchange_token γ ∗ (* Receiver initiated *)
Q is_single_party recv_count Qsingle Qmulti
| Valid_sender_ready => 
sender_exchange_token γ v ∗ (* Sender initiated *)
P is_single_party send_count v Psingle Pmulti
| Valid_receiver_done => 
sender_exchange_token γ v ∗ (* Receiver will complete *)
Q is_single_party send_count Qsingle Qmulti
| Valid_sender_done => 
receiver_exchange_token γ ∗  (* Sender will complete *)
P is_single_party recv_count v Psingle Pmulti  
| Valid_closed => emp
end.


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


  Definition buff_size_inv (count : Z) (first : u64) (size : Z): iProp Σ :=
  (⌜count <= size⌝ ∗ ⌜word.unsigned first < size⌝ ∗ ⌜size > 0⌝ ∗ ⌜size + 1 < 2 ^ 63⌝
  ∗ ⌜count + 1 < 2 ^ 63⌝)%I.

Definition valid_elems (slice : list val) (first : u64) (count : u64) : list val :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).


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


  Definition isBufferedChanLogical (ch: loc) (γ: chan_names) (chan_type: ty) (size: nat) (vs: valid_chan_state) 
  (is_single_party: bool) (send_count recv_count: nat) (count: Z) 
  (first: u64) (xs: list val) (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ): iProp Σ := 
   ⌜count = (send_count - recv_count)⌝ ∗
   ⌜size = length xs⌝ ∗
   buff_size_inv count first (length xs) ∗
   ([∗ list] i↦x ∈ valid_elems xs first count, P is_single_party (recv_count + i) x Psingle Pmulti) ∗ 
   big_sep_seq send_count (size - count) (λ i, Q is_single_party (i - size) Qsingle Qmulti).

Definition isBufferedChan (ch: loc) (γ: chan_names) (chan_type: ty) (size: nat) (vs: valid_chan_state) 
  (is_single_party: bool) (send_count recv_count: nat) (count: Z) 
  (buff: Slice.t) (first: u64) (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ): iProp Σ := 
   ∃ (xs: list val), 
   slice.own_slice_small buff chan_type (DfracOwn 1) xs ∗
   isBufferedChanLogical ch γ chan_type size vs is_single_party 
     send_count recv_count count first xs Psingle Pmulti Qsingle Qmulti R.


(* Unbuffered channel invariant *)
Definition isUnbufferedChan (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val) (vs: valid_chan_state) (is_single_party: bool) (send_count recv_count: nat) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ): iProp Σ := 
    chan_state_facts vs send_count recv_count v chan_type ∗
    chan_state_resources vs γ is_single_party send_count recv_count v Psingle Pmulti Qsingle Qmulti.

(* Inner channel invariant with a unified structure *)
Definition isChanInner (ch: loc) (γ: chan_names) (chan_type: ty) 
    (size: nat) (is_single_party: bool) (buff: Slice.t) 
    (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
    (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ): iProp Σ := 
  ∃ (vs: valid_chan_state) (count: nat) (first: u64) (v: val) (send_count recv_count: nat),
    (* Physical state - directly using word representation *)
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    (if size =? 0 then emp else "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first) ∗
    
    (* Counter resources *)
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (send_ctr_frozen vs) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen vs send_count recv_count) ∗ 
    
    (* Close resources *)
    "HCloseTokPostClose" ∷ 
      (match vs with
        | Valid_closed => 
           ∃ (n: nat) (close_tok_names: gset gname), 
             own_closed_tok_post_close γ n close_tok_names ∗ own_send_counter_frag γ n 1
        | _ => True
       end) ∗

    (* Buffer vs unbuffered channels *)
    "HChanState" ∷ 
      (if size =? 0 then
        isUnbufferedChan ch γ chan_type v vs is_single_party send_count recv_count 
        Psingle Pmulti Qsingle Qmulti R
      else
        isBufferedChan ch γ chan_type size vs is_single_party send_count recv_count count
        buff first Psingle Pmulti Qsingle Qmulti R).

Lemma buff_enqueue_logical (ch: loc) (γ: chan_names) (chan_type: ty) 
        (size: nat) (vs: valid_chan_state) (is_single_party: bool) 
        (send_count recv_count: nat) (count: nat) (first: u64) 
        (xs: list val) (new_xs: list val) (v: val) 
        (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
        (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ)
        (i: nat) (q: Qp):
        
        val_ty v chan_type ->
        count < size ->  (* Buffer is not full *)
        (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
        size > 0 ->
        size + 1 < 2^63 ->
        count + 1 < 2^63 ->
        
        (* Explicitly specify what new_xs is *)
        new_xs = <[uint.nat (word.modu (word.add first (W64 count)) (W64 size)):=v]> xs ->
        
        
        (* Input resources *)
        "HBuffChLogical" ∷ isBufferedChanLogical ch γ chan_type size vs is_single_party 
          send_count recv_count count first xs Psingle Pmulti Qsingle Qmulti R ∗
        "HP" ∷ P is_single_party i v Psingle Pmulti ∗
        "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗
        "HSndPerm" ∷ own_send_counter_frag γ i q
        
        ==∗
        
        (* Output resources *)
        "HBuffChLogical" ∷ isBufferedChanLogical ch γ chan_type size vs is_single_party 
          (S send_count) recv_count (count + 1) first new_xs Psingle Pmulti Qsingle Qmulti R ∗
        "HQ" ∷ Q is_single_party (send_count - size) Qsingle Qmulti ∗
        "HSndCtrAuth" ∷ own_send_counter_auth γ (S send_count) false ∗
        "HSndPerm" ∷ own_send_counter_frag γ (S i) q.

        Proof.
          intros Hvt Hcount_lt Hsp  Hsize_pos Hsize_bound Hcount_bound Hnew_xs .
          iIntros "(HBuffChLogical & HP & HSndCtrAuth & HSndPerm)".
          
          (* Unfold the logical channel state *)
          iDestruct "HBuffChLogical" as "(%HBuffCount & %Hsize & Hsizeinv & HPs & HQs)".
          
          (* Extract buff_size_inv components *)
          iDestruct "Hsizeinv" as "(%Hcount_le & %Hfirst_lt & %Hsize_pos_old & %Hsize_bound_old & %Hcount_bound_old)".
          
          (* Update the send counter *)
          destruct is_single_party.
          
          - (* Single-party case *)
            subst q.
            iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Helem".
            subst i.
            iMod (send_counter_update γ send_count send_count with "[$HSndCtrAuth $HSndPerm]") as "[HSndCtrAuth HSndPerm]".
            
            (* Extract Q from big_sep_seq *)
            iDestruct (big_sep_seq_pop send_count (size - count) (λ i, Q true (i - size) Qsingle Qmulti) 
                       with "HQs") as "[HQ HQs]".
            { lia. }
            
            (* Update Ps for the new buffer content *)
            (* This is the tricky part - we need to relate old and new valid_elems *)
            
            (* First, build the separation logic predicate for the updated buffer content *)
            iAssert ([∗ list] i↦x ∈ valid_elems new_xs first (W64 (count + 1)), 
                      P true (recv_count + i) x Psingle Pmulti)%I with "[HPs HP]" as "HPs'".
            {

              subst new_xs.
              replace size with (length xs).
              replace (W64 (count + 1)) with (w64_word_instance .(word.add) (W64 count) (W64 1))
              by word.
              rewrite (add_one xs first count v).
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
              rewrite (add_one xs first count v).
              {
                rewrite big_sepL_snoc. iFrame.
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

        Lemma buff_dequeue_logical (ch: loc) (γ: chan_names) (chan_type: ty) 
  (size: nat) (vs: valid_chan_state) (is_single_party: bool) 
  (send_count recv_count: nat) (count: nat) (first: u64) (new_first: u64)
  (xs: list val) (v: val) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
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
  "HBuffChLogical" ∷ isBufferedChanLogical ch γ chan_type size vs is_single_party 
    send_count recv_count count first xs Psingle Pmulti Qsingle Qmulti R ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗
  "HRecvPerm" ∷ own_recv_counter_frag γ i q
  
  ==∗
  
  (* Output resources *)
  "HBuffChLogical" ∷ isBufferedChanLogical ch γ chan_type size vs is_single_party 
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

  Lemma wp_Channel__BufferedTrySend (ch: loc) (v: val) (γ: chan_names) (chan_type: ty) 
  (buff: Slice.t) (is_single_party: bool) (q: Qp) (first: u64) 
  (size: nat) (count: nat) (vs: valid_chan_state) 
  (send_count recv_count: nat) (Psingle: Z -> val -> iProp Σ) 
  (Pmulti: val -> iProp Σ) (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) 
  (R: nat -> iProp Σ) (i: nat):

val_ty v chan_type ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
vs ≠ Valid_closed ->
(#buff.(Slice.sz) = #(W64 size)) ->
size > 0 ->
size + 1 < 2^63 ->
count + 1 < 2^63 ->

{{{ 
  "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗  
  "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
  "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
  "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
  "HSen" ∷ own_send_counter_frag γ i q ∗ 
  "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗
  "HCh" ∷ isBufferedChan ch γ chan_type size vs
            is_single_party send_count recv_count count
            buff first Psingle Pmulti Qsingle Qmulti R
}}}
Channel__BufferedTrySend chan_type #ch v
{{{ (success: bool), RET #success;
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
  
  if success then
    (* Successful send - buffer had space *)
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 (S count)) ∗ 
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
    "HSen" ∷ own_send_counter_frag γ (S i) q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ (S send_count) false ∗
    "HQ" ∷ Q is_single_party (i - size) Qsingle Qmulti ∗ 
    "HCh" ∷ isBufferedChan ch γ chan_type size vs
              is_single_party (S send_count) recv_count (S count)
              buff first Psingle Pmulti Qsingle Qmulti R
  else
    (* Failed send - buffer was full *)
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
    "HP" ∷ P is_single_party i v Psingle Pmulti ∗ 
    "HSen" ∷ own_send_counter_frag γ i q ∗ 
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗
    "HCh" ∷ isBufferedChan ch γ chan_type size vs
              is_single_party send_count recv_count count
              buff first Psingle Pmulti Qsingle Qmulti R
}}}.
Proof.
  intros Hvt Hsp  Hnot_closed Hbuff_sz Hsize_pos Hsize_bound Hcount_bound.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  
  (* Check if channel is closed *)
  wp_loadField.
  wp_pures.

  wp_if_destruct.
  {
    destruct vs. all: try done.
  }
  
  
  (* Check if buffer has space *)
  wp_loadField.
  wp_loadField.
  wp_pures.
  
  (* Extract buffer channel resources *)
  iDestruct "HCh" as (xs) "(HBuffSlice & %Hsize & %Hsizeinv & %HBuffcount & HPs & HQs)".
  destruct HBuffcount as (Hcount_le & Hfirst_lt & Hsize_pos_old & Hsize_bound_old & Hcount_bound_old).
  
  (* Get slice size *)
  iDestruct (slice.own_slice_small_sz with "HBuffSlice") as %Hslice_size.
  replace buff.(Slice.sz) with (W64 (length xs)) by word.
  
  (* Check if count < buffer size *)
  wp_apply wp_slice_len.
  wp_if_destruct.

  - (* Case: Buffer has space - can send *)
    rewrite <- Hsizeinv in Hcount_le.
    
      (* Calculate last index and set the value *)
      wp_loadField.
      wp_loadField.
      wp_loadField. wp_apply wp_slice_len.
      wp_apply wp_ref_to; first val_ty.
      iIntros (last_ptr) "Hlast_ptr".
      wp_pures.
      wp_load.
      
      (* Set the value in the slice *)
      wp_loadField.
      
      (* Locate target index in slice *)
      set (idx := uint.nat (word.modu (word.add first (word.unsigned count)) (word.unsigned size))).
      
      (* Use SliceSet to store the value *)
      wp_apply (slice.wp_SliceSet with "[$HBuffSlice]").
      { iPureIntro. split.
        - apply lookup_lt_is_Some_2. word.
        - exact Hvt.
      }
      iIntros "HBuffSlice".
      
      (* Update channel count field *)
      wp_pures.
      wp_loadField.
      wp_storeField.
      
      (* Return success *)
      wp_pures.

      (* Build assertion for counter elements *)
      iAssert (own_send_counter_auth γ send_count false ∗ 
      own_send_counter_frag γ i q ∗ 
      ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I 
      with "[HSndCtrAuth HSen]" as "(HSndCtrAuth & HSen & %Hispz)".
      {
      destruct is_single_party.
      - subst q.
      iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
      iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSen]") as "%Hag2".
      iFrame. iPureIntro. lia.
      }

      
      (* Set the new buffer state *)
      set (new_xs := <[idx:=v]> xs).
      iMod (buff_enqueue_logical ch γ chan_type size vs is_single_party
      send_count recv_count count first xs new_xs v
      Psingle Pmulti Qsingle Qmulti R i q
      with "[ HPs HQs HP HSndCtrAuth HSen]") as 
      "IH". all: (try done;try word).
      {
        subst idx.
        subst new_xs.
        replace (W64 (uint.Z (W64 count))) with (W64 count) by word.
        replace ((W64 (uint.Z (W64 size)))) with (W64 size) by word.
        exact.
      }
      { 
       iFrame. iPureIntro. word.
      }
      iModIntro. iApply "HΦ".
      iFrame. iNamed "IH". iFrame.
            (* First, replace count + 1 with S count *)
      replace (count + 1)%nat with (S count)%nat by lia.

      (* Replace word.add (W64 count) (W64 1) with W64 (S count) *)
      replace (w64_word_instance.(word.add) (W64 count) (W64 1)) with (W64 (S count)) by word.

     

      (* Now we can frame everything except HQ *)
      iFrame.
      replace (count + 1) with (Z.of_nat (S count)) by lia.
      subst new_xs. subst idx.
      replace ((W64 (uint.Z (W64 size)))) with (W64 size) by word.
      replace ((W64 (uint.Z (W64 count)))) with (W64 count) by word.
      replace (length xs) with size in Hslice_size.
      replace (buff .(Slice.sz)) with (W64 size).
      iFrame. 
      unfold Q.
      destruct is_single_party.
      {
       subst q. subst send_count. iFrame.
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
            rewrite bool_decide_eq_false in Hbinner.
            lia.
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
 - iModIntro. iApply "HΦ". iFrame. done.
Qed. 

Lemma wp_Channel__BufferedTryReceiveLocked (ch: loc) (γ: chan_names) (chan_type: ty) 
  (size: nat) (mu_l: loc) (is_single_party: bool)  (vs: valid_chan_state)
  (count: nat) (send_count recv_count: nat) (first: u64) (buff: Slice.t)
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ)
  (i: nat) (q: Qp):

has_zero chan_type ->
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ 
  (* Common preconditions for all cases *)
  "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
  "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
  "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
  "HRcvPerm" ∷ own_recv_perm γ q i Ri ∗
  "HCh" ∷ isBufferedChan ch γ chan_type size vs is_single_party
              send_count recv_count count buff first Psingle Pmulti Qsingle Qmulti R ∗  

  (* Conditional resources based on channel state *)
 
    (* Non-closed channel with data or empty *)
    if (uint.Z (W64 0) <? uint.Z (W64 count)) then
      (* Channel has data *)
      "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗
      "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen vs send_count recv_count)
    else
      match vs with 
      | Valid_closed => 
          (* Closed channel case *)
        ∃ (close_tok_names: gset gname) ,
        "#HSndCtrAuth" ∷ own_send_counter_auth γ send_count true ∗ 
        "HRcvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen vs send_count recv_count) ∗
        "HCloseTokPostClose" ∷ own_closed_tok_post_close γ send_count close_tok_names ∗  
        "HSc" ∷ own_send_counter_frag γ send_count 1 ∗
        "%Hct" ∷ ⌜count = 0%nat⌝ 
      | _ => emp
  end
}}}
Channel__BufferedTryReceiveLocked chan_type #ch
{{{ (success: bool) (v: val) (has_value: bool), RET (#success, v, #has_value);
  (* Common postconditions *)
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #( valid_to_word vs) ∗
  
  (* Case-specific postconditions *)
  match success, has_value with
  | true, true =>
    (* Successful receive with value *)
    ∃ (new_first: u64),
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 (count - 1)) ∗
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #new_first ∗ 
    "HP" ∷ P is_single_party i v Psingle Pmulti ∗
    "HRecvPerm" ∷ own_recv_perm γ q (S i) Ri ∗
    "%HVt" ∷ ⌜val_ty v chan_type⌝ ∗
    "HCh" ∷ isBufferedChan ch γ chan_type size vs is_single_party
            send_count (S recv_count) (count - 1) buff new_first 
            Psingle Pmulti Qsingle Qmulti R ∗
    "HRecvCtrAuth" ∷ own_recv_counter_auth γ (S recv_count) 
                    (recv_ctr_frozen vs send_count (S recv_count))
  | true, false =>
    (* Successful but channel is closed *)
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 0) ∗
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
    "HRi" ∷ Ri recv_count ∗
    "#HScfroz" ∷ own_send_counter_auth γ send_count true ∗
    "#HRcfroz" ∷ own_recv_counter_auth γ recv_count true ∗
    "HSc" ∷ own_send_counter_frag γ recv_count 1 ∗
    ∃ (close_tok_names: gset gname) (γr: gname),
    "HCloseTokPostCloseNew" ∷ own_closed_tok_post_close γ recv_count (close_tok_names ∖ {[γr]}) ∗
    ⌜ vs = Valid_closed ⌝ ∗ 
    ⌜v = zero_val chan_type⌝
  | false, true =>
    (* No value available, empty channel *)
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 0) ∗
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #first ∗ 
    "HRcvPerm" ∷ own_recv_perm γ q i Ri ∗  
  "HCh" ∷ isBufferedChan ch γ chan_type size vs is_single_party
              send_count recv_count count buff first Psingle Pmulti Qsingle Qmulti R ∗  
    ⌜v = zero_val chan_type⌝ ∗ 
    ⌜ W64 count = W64 0 ⌝ ∗ 
    ⌜vs =?= Valid_closed = false⌝
  | _, _ =>
    (* Impossible case *)
    False
  end
}}}.
Proof.
  intros Hzero Hsp .
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  wp_apply wp_ref_of_zero; first done.
  iIntros (v_ptr) "Hv_ptr".
  wp_pures.
  
  (* Load channel count *)
  wp_auto.
  wp_pures.
  
  (* Branch based on count *)
  wp_if_destruct.
  
  - (* Case: channel has data - count > 0 *)
    simpl. (* All non-closed states with data follow similar pattern *)
      (* Extract resources for channels with data *)
      assert (uint.Z (W64 0) <? uint.Z (W64 count) = true) as Hcond.
      {
        rewrite Z.ltb_lt. exact Heqb.
      }
      rewrite Hcond.
      iNamed "Hpre".
      assert (0 < count) by word.
      (* Access the buffered channel resources *)
      iDestruct "HCh" as (xs) "(HBuffSlice & %Hsize & %Hsizeinv & %HBuffCount & HPs & HQs)".
    iPoseProof (slice.own_slice_small_sz with "HBuffSlice") as "%".
      destruct HBuffCount as (Hcount_le & Hfirst_lt & Hsize_pos & Hsize_bound & Hcount_bound).
      wp_auto.
      edestruct (list_lookup_Z_lt xs (uint.Z first)) as [x Hlookup].
        { word. }
      wp_apply ((slice.wp_SliceGet _ _ buff chan_type (DfracOwn 1) xs first x  ) with "[$HBuffSlice]").
      {
        iPureIntro. done.
      }
      iIntros "[HBuffSlice %Hvty]".
      wp_store. wp_loadField. 



      wp_auto.
      assert (send_count ≠ recv_count)%Z by lia.

      
      (* Calculate new_first *)
      set (new_first := word.modu (word.add first 1) (W64 size)).
      iNamed "HRcvPerm".
      iDestruct "HRcvPerm" as "[HRecvCtrFrag Hctf]".
      (* Apply buff_dequeue_logical lemma to update the logical buffer state *)
      iMod (buff_dequeue_logical ch γ chan_type size _ is_single_party
      send_count recv_count count first new_first xs x
      Psingle Pmulti Qsingle Qmulti R i q
      with "[HQ  HPs HQs HRecvCtrAuth HRecvCtrFrag]") as 
      "IH".
      (* Prove lemma preconditions *)
        ++ word. (* count > 0 *)
        ++ exact Hsp. (* ownership constraint *)
        ++ lia. (* size > 0 *)
        ++ reflexivity. (* new_first definition *)
        ++ exact Hlookup. (* x is at first index *)
        ++ iFrame. unfold recv_ctr_frozen.  
        assert ((send_count =? recv_count) = false) as Heq_false.
        { 
          rewrite Z.eqb_neq. lia. 
        }
        rewrite Heq_false.
        destruct vs; auto.
        ++ wp_apply wp_slice_len. wp_auto. 
        
     
      iNamed "IH".
    
      (* First, establish the condition as a pure fact *)
      set (should_freeze := ((count =? 1) && (vs =?= Valid_closed))).
      (* Now create a conditional assertion for the possibly-frozen counter *)
      iAssert (bupd(own_recv_counter_auth γ (S recv_count) should_freeze))%I
        with "[HRecvCtrAuth]" as ">HRecvCtrAuth".
      {
        destruct should_freeze.
        - (* Case: need to freeze *)
          iMod (recv_counter_freeze γ (S recv_count) with "HRecvCtrAuth") as "HRecvCtrAuth".
          { done. }
          iModIntro. iExact "HRecvCtrAuth".
        - (* Case: no freezing needed *)
          iModIntro. iExact "HRecvCtrAuth".
      }

      iModIntro. iApply "HΦ". 
      
      (* Update the counters *)
      destruct is_single_party.
      {
        (* Single-party case *)
        subst q.
        iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvPerm]") as "%Helem".
        unfold isBufferedChanLogical.
        iDestruct "HBuffChLogical" as "(%Hct & %Hsz & %Hnewsizeinv & HPs & HQs)".
        iFrame.
        replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1)) by word. subst new_first.
        replace size with (length xs) by lia.
        replace (length xs) with (uint.nat buff .(Slice.sz)) by lia.
        replace ((W64 (Z.of_nat (uint.nat buff .(Slice.sz))))) with (buff .(Slice.sz)) by word.
        replace recv_count with i by lia.
        iFrame. unfold recv_ctr_frozen.
        destruct should_freeze eqn:Hb.
        {
          assert (count = 1%nat) as Hcount_one.
          {
            (* From should_freeze = true, we know (count =? 1) && (cs =?= Valid_closed) = true *)
            (* For a conjunction to be true, both parts must be true *)
            apply andb_prop in Hb as [Hcount_eq _].
            lia.
          }
          subst count.
          assert (i = recv_count) as Hi_eq.
          { injection Helem as Hi_eq. exact Hi_eq. }

          assert (send_count = S recv_count) as Hsend_eq.
          {
            simpl in Hct. (* Simplifies 1%nat - 1 to 0 *)
            (* Now Hct is: 0 = send_count - S recv_count *)
            lia.
          }

          assert (send_count = S i) as Hsend_eq_Si.
          {
            lia.
          }

          assert (send_count =? S i = true) as Hresult.
          {
            subst recv_count. 
            rewrite Z.eqb_eq. lia.
          }
          rewrite Hresult.
          assert (vs = Valid_closed) as Hcs_closed.
          {
            apply andb_prop in Hb as [_ Hcs_eq].
            unfold valid_chan_state_eq in Hcs_eq.
            destruct vs; try discriminate.
            reflexivity.
          }
          subst vs. iFrame. iPureIntro. split;first val_ty. split; first lia. word. 
        }
        {
          iSplitL ""; first done.
          iSplitL ""; first word.
          assert (count ≠ 1%nat ∨ vs ≠ Valid_closed) as Hcount_or_cs.
          {
            (* For a conjunction to be false, at least one part must be false *)
            
            apply not_true_iff_false in Hb.

            rewrite andb_true_iff in Hb.
            
            apply Classical_Prop.not_and_or in Hb.
            destruct Hb as [Hcount_not_eq | Hcs_not_eq].
            - left. lia.
            - right. destruct vs;auto.
          }
          destruct vs. all: try iFrame.
          destruct Hcount_or_cs.
          {
            assert (send_count ≠ S i) as Hsend_neq_Si.
            {
              (* First, establish i = recv_count from Helem *)
              injection Helem as Hi_eq.
              lia.
            }
           assert ((send_count =? (S i)) = false).
           {
            rewrite Z.eqb_neq. lia.
           }
           rewrite H3.
           iFrame.
          }
          {
           done. 
          }
      }
    }
      {
        (* Single-party case *)
        iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvPerm]") as "%Helem".
        unfold isBufferedChanLogical.
        iDestruct "HBuffChLogical" as "(%Hct & %Hsz & %Hnewsizeinv & HPs & HQs)".
        iFrame.
        replace ((w64_word_instance .(word.sub) (W64 count) (W64 1))) with (W64 (count - 1)) by word. subst new_first.
        replace size with (length xs) by lia.
        replace (length xs) with (uint.nat buff .(Slice.sz)) by lia.
        replace ((W64 (Z.of_nat (uint.nat buff .(Slice.sz))))) with (buff .(Slice.sz)) by word.
        iFrame.
        destruct should_freeze eqn:Hb.
        {
          assert (count = 1%nat) as Hcount_one.
          {
            (* From should_freeze = true, we know (count =? 1) && (cs =?= Valid_closed) = true *)
            (* For a conjunction to be true, both parts must be true *)
            apply andb_prop in Hb as [Hcount_eq _].
            lia.
          }
          subst count.

          assert (send_count = S recv_count) as Hsend_eq.
          {
            simpl in Hct. (* Simplifies 1%nat - 1 to 0 *)
            (* Now Hct is: 0 = send_count - S recv_count *)
            lia.
          }

          unfold recv_ctr_frozen.
          assert (vs = Valid_closed) as Hcs_closed.
          {
            apply andb_prop in Hb as [_ Hcs_eq].
            unfold valid_chan_state_eq in Hcs_eq.
            destruct vs; try discriminate.
            reflexivity.
          }
          subst vs. iFrame. assert ((send_count =? S recv_count) = true).
          { inversion Hsend_eq. lia. }
          simpl. iSplitL "";first done. iSplitL "";first (iPureIntro;word). rewrite H2. iFrame.
        }
        {
          iSplitL ""; first done.
          iSplitL ""; first word.
          assert (count ≠ 1%nat ∨ vs ≠ Valid_closed) as Hcount_or_cs.
          {
            (* For a conjunction to be false, at least one part must be false *)
            
            apply not_true_iff_false in Hb.

            rewrite andb_true_iff in Hb.
            
            apply Classical_Prop.not_and_or in Hb.
            destruct Hb as [Hcount_not_eq | Hcs_not_eq].
            - left. lia.
            - right. destruct vs;auto.
          }
          destruct vs. all: try iFrame.
          destruct Hcount_or_cs.
          {
            assert (send_count ≠ S recv_count) as Hsend_neq_Si.
            {
              (* First, establish i = recv_count from Helem *)
              lia.
            }
           assert ((send_count =? (S recv_count)) = false).
           {
            rewrite Z.eqb_neq. lia.
           }
           unfold recv_ctr_frozen.
           rewrite H3.
           iFrame.
          }
          {
           done. 
          }
      }
    }
    
  - (* Case: channel is empty - count = 0 *)
    wp_loadField.
    
    destruct (vs =?= Valid_closed) eqn: Hc.
    
    + (* Empty non-closed channel cases - similar for all non-closed states *)
      (* Empty case - return false *)
      assert (uint.Z (W64 0) <? uint.Z (W64 count) = false) as Hcond.
      {
        lia.
      }
      rewrite Hcond.
      iNamed "Hpre".
      assert (vs = Valid_closed) as Hcs_eq.
      {
        unfold valid_chan_state_eq in Hc.
        destruct vs; try discriminate.
        (* Only the Valid_closed case remains *)
        reflexivity.
      }
      subst vs. iNamed "Hpre".
      wp_pures. 
      replace ((W64 5%nat)) with ((W64 5)) by word.
      wp_pures. wp_load.
      iSpecialize ("HΦ" $! true (zero_val chan_type) false).
      (* Return failure due to empty channel *)
      iNamed "HCloseTokPostClose".
      iDestruct "HCloseTokPostClose" as "[Hauthset Hset]".
      iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSc]") as "%Hag2".
      iNamed "HRcvPerm". iDestruct "HRcvPerm" as "[HRct HRcvCloseTok]".
      iDestruct ((own_closed_tok_post_close_pop_raw γ send_count γi Ri close_tok_names) with "[Hset Hauthset HRcvCloseTok]") as ">Hct".
      {
       iFrame.
      }
      wp_pures.
      iModIntro.
      iApply "HΦ".
      unfold recv_ctr_frozen.
      iFrame.
      subst count. iFrame "#".
      iFrame "count". iFrame. unfold isBufferedChan.
      iDestruct "HCh" as (xs) "(HBuffSlice & %Hsize & %Hsizeinv & %HBuffCount & HPs & HQs)".
      assert (send_count = recv_count) by lia.
      replace recv_count with send_count. iFrame "#".
       iDestruct "Hct" as "(Hset & Hauthset & Hri)".
      iFrame. rewrite Z.eqb_refl. iFrame. 
      iFrame. done.
    
    +  
    assert (uint.Z (W64 0) <? uint.Z (W64 count) = false) as Hcond.
    {
      lia.
    }
    rewrite Hcond.
      wp_if_destruct.
      {
        unfold valid_to_word in Heqb0. 
        destruct vs. all: try done.
      }
      wp_load. wp_pures. iModIntro.
      iApply "HΦ".
       assert ((W64 count) = (W64 0)).
      {
        word.
      }
      rewrite H.
      iFrame. done.
      Unshelve.
      done.
Qed.
      
      
(* Top-level channel invariant *)
Definition isChan (ch: loc) (γ: chan_names) (chan_type: ty) 
  (size: nat) (is_single_party: bool) (Psingle: Z -> val -> iProp Σ) 
  (Pmulti: val -> iProp Σ) (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) 
  (R: nat -> iProp Σ): iProp Σ := 
  ∃ (mu_l: loc) (buff: Slice.t),
    "#mu" ∷ ch ↦[(Channel chan_type) :: "lock"]□ #mu_l ∗ 
    "#buff" ∷ ch ↦[(Channel chan_type) :: "buffer"]□ (slice_val buff) ∗
    "%Hbuffsize" ∷ ⌜#buff.(Slice.sz) = #(W64 size)⌝ ∗
    "%Hchantyzero" ∷ ⌜has_zero chan_type⌝ ∗
    "#Hlock" ∷ is_lock (nroot.@"Channel") (#mu_l) 
      (isChanInner ch γ chan_type size is_single_party buff Psingle Pmulti Qsingle Qmulti R).

(* Helper lemmas for working with channel states *)

(* Lemma for checking if a channel is closed *)
Lemma is_closed_state (vs: valid_chan_state) :
  vs = Valid_closed <-> valid_to_word vs = CS_CLOSED_W.
Proof.
  split; intros H.
  - subst vs. reflexivity.
  - destruct vs; try (inversion H; fail).
    reflexivity.
Qed.

(* Example helper lemma for closed channels *)
Lemma closed_unbuff_eq (ch: loc) (send_count recv_count: nat) (v: val) 
  (γ: chan_names) (chan_type: ty) (is_single_party: bool) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R: nat -> iProp Σ):
  isUnbufferedChan ch γ chan_type v Valid_closed is_single_party send_count recv_count
  Psingle Pmulti Qsingle Qmulti R -∗ ⌜send_count = recv_count⌝.
Proof.
  iIntros "[%Heq _]". iPureIntro. exact Heq.
Qed.

(* Lemma for receiver_offer: Valid_start → Valid_receiver_ready *)
Lemma receiver_offer (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val) (is_single_party: bool) (send_count: nat) (recv_count: nat) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ)
  (i: nat) (q: Qp):
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  ==∗ 
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_receiver_ready is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗ 
  "Hsttok" ∷ ghost_var γ.(unbuffered_state_tracker_name) (1/2)%Qp (false,v).
Proof.
  intros Hsp.
  iIntros "IH". iNamed "IH". iNamed "HRecvPerm". 
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[HChanFacts HChanRes]".
  
  (* Extract state token from channel resources *)
  destruct is_single_party.
  { (* Single-party case *)
    iDestruct "HChanRes" as "Hsttok".
    (* Split the token *)
    iDestruct ((exchange_token_split γ false v) with "[$Hsttok]") as ">[Hsttok1 Hsttok2]".
    
    (* Build assertion for counter elements *)
    iAssert (own_recv_counter_auth γ recv_count false ∗ 
             own_recv_counter_frag γ i q ∗ 
             ⌜recv_count = i⌝)%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
    {
      subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. done.
    }
    
    (* Update state field *)
    iModIntro.
    
    (* Reassemble resources *)
    iFrame "HRecvCtrAuth".
    iSplitL "HChanFacts HQ Hsttok1".
    {
      (* Rebuild channel invariant *)
      iSplitL "HChanFacts".
      { (* Facts - unchanged for this transition *) iExact "HChanFacts". }
      { (* Resources for receiver_ready state *)
        subst recv_count.
        iFrame.
      }
    }
    (* Frame remaining resources *)
    iFrame "HRecvCtrFrag Hrct Hsttok2".
  }
  { (* Multi-party case - similar structure *)
    iDestruct "HChanRes" as "Hsttok".
    (* Split the token *)
    iDestruct ((exchange_token_split γ false v) with "[$Hsttok]") as ">[Hsttok1 Hsttok2]".
    
    (* Build assertion for counter elements *)
    iAssert (own_recv_counter_auth γ recv_count false ∗ 
             own_recv_counter_frag γ i q ∗ 
             ⌜i <= recv_count⌝%I)%I with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
    {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
    }
    
    (* Update state field *)
    iModIntro.
    
    (* Reassemble resources *)
    iFrame "HRecvCtrAuth".
    iSplitL "HChanFacts HQ Hsttok1".
    {
      (* Rebuild channel invariant *)
      iSplitL "HChanFacts".
      { (* Facts - unchanged for this transition *) iExact "HChanFacts". }
      { (* Resources for receiver_ready state *)
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
    }

    (* Frame remaining resources *)
    iFrame "HRecvCtrFrag Hrct Hsttok2".
  }
Qed.

(* Lemma for receiver_complete: Valid_sender_ready → Valid_receiver_done *)
Lemma receiver_complete (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val) (is_single_party: bool) (send_count: nat) (recv_count: nat) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ)
  (i: nat) (q: Qp):
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_sender_ready is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  ==∗ 
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_receiver_done is_single_party send_count (S recv_count) 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (S recv_count) false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (S i) Ri.
Proof.
  intros Hsp. iIntros "Hpre".
  iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[%HChanFacts HChanRes]".
  
  (* Extract state resources *)
  iDestruct "HChanRes" as "(Hsttok & HP)".
  
  (* Build assertion for counter elements *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I 
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Update counter *)
  iDestruct (recv_counter_update γ recv_count i with "[$HRecvCtrAuth $HRecvCtrFrag]") 
    as ">[HRecvCtrAuth HRecvCtrFrag]".
  
  (* Update state field *)
  iModIntro.
  
  (* Reassemble resources *)
  iFrame "HRecvCtrAuth".
  iSplitL "Hsttok HQ".
  {
    (* Rebuild channel invariant *)
    iSplitL "".
    {
      (* Update channel facts for new state *)
      destruct is_single_party.
      - subst q. subst recv_count.
        (* Create facts for receiver_done state *)
        iPureIntro. lia.
        (* Other facts that might be needed... *)
      - (* Similar for multi-party case *)
        iPureIntro.
        lia.
        (* Other facts that might be needed... *)
    }
    {
      (* Resources for receiver_done state *)
      iFrame.
      destruct is_single_party.
      {
       replace send_count with i by lia.
       iFrame.
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
        }
    }
  }
}
  (* Frame remaining resources *)
  iFrame "HRecvCtrFrag Hrct".
Qed.

(* Lemma for receiver_rescind: Valid_receiver_ready → Valid_start *)
Lemma receiver_rescind (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val) (is_single_party: bool) (send_count: nat) (recv_count: nat) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ)
  (i: nat) (q: Qp):
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_receiver_ready is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗  
  "Hsttok'" ∷ exchange_token γ false v  
  ==∗ 
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri.
Proof.
  intros Hsp.
  iIntros "Hpre". iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[HChanFacts HChanRes]".
  
  (* Extract state resources *)
  iDestruct "HChanRes" as "(Hsttok & HQ)".
  
  (* Combine the tokens *)
  unfold receiver_exchange_token. iNamed "Hsttok".
  iDestruct ((exchange_token_combine γ) with "[$Hsttok $Hsttok']") as ">Hsttok".
  
  (* Build assertion for counter elements *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I 
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Update state field *)
  iModIntro.
  
  destruct is_single_party.
  {
    subst recv_count. iFrame.
  }
  {
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
            lia.
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
Qed.

(* Lemma for receiver_complete_second: Valid_sender_done → Valid_start *)
Lemma receiver_complete_second (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v: val) (is_single_party: bool) (send_count: nat) (recv_count: nat) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ)
  (i: nat) (q: Qp):
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_sender_done is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗  
  "Hsttok'" ∷ exchange_token γ false v 
  ==∗ 
  "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party send_count (S recv_count) 
    Psingle Pmulti Qsingle Qmulti R ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ (S recv_count) false ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q (S i) Ri ∗ 
  "HP" ∷ P is_single_party recv_count v Psingle Pmulti.
Proof.
  intros Hsp.
  iIntros "Hpre". iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[%HChanFacts HChanRes]".
  
  (* Extract state resources *)
  iDestruct "HChanRes" as "(Hsttok & HP)".
  
  (* Combine the tokens *)

  unfold receiver_exchange_token. iNamed "Hsttok". 
  iDestruct ((exchange_token_combine γ) with "[$Hsttok $Hsttok']") as ">Hsttok".
  
  (* Build assertion for counter elements *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I 
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Update counter *)
  iDestruct (recv_counter_update γ recv_count i with "[$HRecvCtrAuth $HRecvCtrFrag]") 
    as ">[HRecvCtrAuth HRecvCtrFrag]".
  
  (* Update state field *)
  
  (* Reassemble resources *)
  iFrame. iPureIntro. lia.
Qed.

(* Define receiver transitions as a simple enum type *)
Inductive receiver_transition : Type :=
  | receiver_offer_trans : receiver_transition
  | receiver_rescind_trans : receiver_transition
  | receiver_complete_trans : receiver_transition
  | receiver_complete_second_trans : receiver_transition.

(* Define a relation that checks if a transition is valid between two states *)
Definition is_valid_transition (tr: receiver_transition) (vs_old vs_new: valid_chan_state) : Prop :=
  match tr, vs_old, vs_new with
  | receiver_offer_trans, Valid_start, Valid_receiver_ready => True
  | receiver_rescind_trans, Valid_receiver_ready, Valid_start => True
  | receiver_complete_trans, Valid_sender_ready, Valid_receiver_done => True
  | receiver_complete_second_trans, Valid_sender_done, Valid_start => True
  | _, _, _ => False
  end.

(* Define how receiving count changes in each transition *)
Definition receiver_recv_count_change (tr: receiver_transition) : nat :=
  match tr with
  | receiver_complete_trans => 1
  | receiver_complete_second_trans => 1
  | _ => 0
  end.

(* Define whether Q resource is needed for the transition *)
Definition receiver_needs_Q (tr: receiver_transition) : bool :=
  match tr with
  | receiver_offer_trans => true
  | receiver_complete_trans => true
  | _ => false
  end.

(* Define whether additional token is needed for the transition *)
Definition receiver_needs_token (tr: receiver_transition) : bool :=
  match tr with
  | receiver_rescind_trans => true
  | receiver_complete_second_trans => true
  | _ => false
  end.

(* Define whether P resource is produced by the transition *)
Definition receiver_produces_P (tr: receiver_transition) : bool :=
  match tr with
  | receiver_complete_second_trans => true
  | _ => false
  end.

(* Define whether token is produced by the transition *)
Definition receiver_produces_token (tr: receiver_transition) : bool :=
  match tr with
  | receiver_offer_trans => true
  | _ => false
  end.

  (* General receiver transition lemma *)
Lemma receiver_transition_general (ch: loc) (γ: chan_names) (chan_type: ty) 
(v: val) (vs_old vs_new: valid_chan_state) (tr: receiver_transition) 
(is_single_party: bool) (send_count: nat) (recv_count: nat) 
(Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
(Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ) 
(i: nat) (q: Qp):
(* Precondition: transition is valid between states *)
is_valid_transition tr vs_old vs_new ->
(* Ownership constraint *)
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(* Resources *)
"HCh" ∷ isUnbufferedChan ch γ chan_type v vs_old is_single_party send_count recv_count 
   Psingle Pmulti Qsingle Qmulti R ∗
(if receiver_needs_Q tr then "HQ" ∷ Q is_single_party i Qsingle Qmulti else emp) ∗
(if receiver_needs_token tr then "Hsttok'" ∷ receiver_exchange_token γ else emp) ∗
"HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
"HRecvPerm" ∷ own_recv_perm γ q i Ri
==∗ 
(* Result resources *)
"HCh" ∷ isUnbufferedChan ch γ chan_type v vs_new is_single_party send_count
   (recv_count + receiver_recv_count_change tr) Psingle Pmulti Qsingle Qmulti R ∗
(if receiver_produces_P tr then "HP" ∷ P is_single_party recv_count v Psingle Pmulti else emp) ∗
(if negb (receiver_produces_P tr) && negb (receiver_needs_Q tr) 
 then "HQ" ∷ Q is_single_party i Qsingle Qmulti else emp) ∗
(if receiver_produces_token tr 
 then "Hsttok" ∷ exchange_token γ false v else emp) ∗
"HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + receiver_recv_count_change tr) false ∗ 
"HRecvPerm" ∷ own_recv_perm γ q (i + receiver_recv_count_change tr) Ri.
Proof.
intros Hvalid Hsp.
iIntros "Hpre".

(* First, destruct by transition type to handle each case specifically *)
destruct tr; simpl in *; unfold is_valid_transition in Hvalid;
destruct vs_old, vs_new; try (exfalso; exact Hvalid).

- (* Case: receiver_offer_trans - Valid_start → Valid_receiver_ready *)
  simpl in *.
  iNamed "Hpre". iDestruct "Hpre" as "[Hemp Hpre]".
  iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[HChanFacts HChanRes]".
  
  (* Handle token splitting *)
  iDestruct "HChanRes" as "Hsttok".
  
  iDestruct ((exchange_token_split γ false v) with "[$Hsttok]") as ">[Hsttok1 Hsttok2]".
  
  (* Handle counter verification *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Finalize *)
  iModIntro.
  replace (recv_count + 0)%nat with recv_count by lia.
  replace (i + 0)%nat with i by lia.
  iFrame "HRecvCtrAuth".
  
  (* Rebuild channel invariant *)
  iSplitL "HChanFacts HQ Hsttok1".
  {
    iSplitL "HChanFacts".
    { iExact "HChanFacts". }
    { 
      destruct is_single_party.
      - subst recv_count. iFrame.
      - iFrame.
        unfold Q.
        destruct bool_decide eqn:Hbouter.
        {
          rewrite bool_decide_eq_true in Hbouter.
          destruct bool_decide; try lia.  
        } 
        rewrite bool_decide_eq_false in Hbouter.
        destruct bool_decide; try done.
    }
  }
  
  (* Frame remaining resources *)
  iFrame "HRecvCtrFrag Hrct Hsttok2".

- (* Case: receiver_rescind_trans - Valid_receiver_ready → Valid_start *)
  simpl in *.
  iNamed "Hpre". iDestruct "Hpre" as "[Hemp Hpre]".
  iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[HChanFacts HChanRes]".
  
  (* Extract state resources *)
  iDestruct "HChanRes" as "(Hsttok & HQ')".
  
  (* Combine the tokens *)
  iDestruct ((receiver_exchange_token_combine γ) with "[$Hsttok $Hsttok']") as ">Hsttok".
  
  (* Handle counter verification *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Finalize *)
  iModIntro.
  
  (* Rebuild channel invariant *)
  iSplitL "HChanFacts Hsttok".
  {
    iSplitL "HChanFacts".
    { replace (recv_count + 0)%nat with recv_count by lia. iExact "HChanFacts". }
    { iFrame "Hsttok". }
  }
  
  (* Frame remaining resources and handle Q *)
  destruct is_single_party.
  + subst recv_count. iFrame. replace (i + 0)%nat with i by lia. iFrame.
  + replace (recv_count + 0)%nat with recv_count by lia. 
    (* Handle Q for multi-party case *)
    unfold Q.
    destruct bool_decide eqn:Hbouter; try done.
    {
    rewrite bool_decide_eq_true in Hbouter.
    destruct bool_decide; try lia.
    }
    rewrite bool_decide_eq_false in Hbouter.
    destruct bool_decide; try lia.
    {
     iFrame. replace (i + 0)%nat with i by lia. iFrame. 
    }
    iFrame. replace (i + 0)%nat with i by lia. done. 

- (* Case: receiver_complete_trans - Valid_sender_ready → Valid_receiver_done *)
  simpl in *.
  iNamed "Hpre". iDestruct "Hpre" as "[Hemp Hpre]".
  iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[%HChanFacts HChanRes]".
  
  (* Extract state resources *)
  iDestruct "HChanRes" as "(Hsttok & HP)".
  
  (* Handle counter verification and update *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Update counter *)
  iDestruct (recv_counter_update γ recv_count i with "[$HRecvCtrAuth $HRecvCtrFrag]") 
    as ">[HRecvCtrAuth HRecvCtrFrag]".
  
  (* Finalize *)
  iModIntro.
  replace (S recv_count) with (recv_count + 1)%nat by lia.
replace (S i) with (i + 1)%nat by lia.
  iFrame "HRecvCtrAuth".
  
  (* Rebuild channel invariant *)
  iSplitL "Hsttok HQ".
  {
    iSplitL "".
    {
      (* Update facts for new state *)
      destruct is_single_party.
      - subst q. subst recv_count. iPureIntro. lia.
      - iPureIntro. lia.
    }
    {
      (* Resources for receiver_done state *)
      iFrame.
      destruct is_single_party.
      - replace send_count with i by lia. done.
      - unfold Q.
        destruct bool_decide eqn:Hbouter.
        {
          rewrite bool_decide_eq_true in Hbouter.
          destruct bool_decide; try done.
          lia.
        }
        rewrite bool_decide_eq_false in Hbouter.
        destruct bool_decide; try done.
    }
  }
  
  (* Frame remaining resources *)
  iFrame "HRecvCtrFrag Hrct".

- (* Case: receiver_complete_second_trans - Valid_sender_done → Valid_start *)
  simpl in *.
  iNamed "Hpre". iDestruct "Hpre" as "[Hemp Hpre]".
  iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Split unbuffered channel into facts and resources *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[%HChanFacts HChanRes]".
  
  (* Extract state resources *)
  iDestruct "HChanRes" as "(Hsttok & HP')".
  
  (* Combine the tokens *)
  iDestruct ((receiver_exchange_token_combine γ) with "[$Hsttok $Hsttok']") as ">Hsttok".
  
  (* Handle counter verification and update *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    - subst q.
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. done.
    - iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
  }
  
  (* Update counter *)
  iDestruct (recv_counter_update γ recv_count i with "[$HRecvCtrAuth $HRecvCtrFrag]") 
    as ">[HRecvCtrAuth HRecvCtrFrag]".
  
  (* Finalize *)
  iModIntro.
  
  (* Rebuild resources *)
  iSplitL "Hsttok".
  {
    iSplitL "".
    { iPureIntro. lia. }
    { iFrame "Hsttok". }
  }
  iFrame.
  replace (S recv_count) with (recv_count + 1)%nat by lia.
replace (S i) with (i + 1)%nat by lia.
  iFrame.
Qed.

(* Define word constants for receiver results to match Go implementation *)
Definition RECEIVER_COMPLETED_WITH_SENDER_W : w64 := W64 0.
Definition RECEIVER_MADE_OFFER_W : w64 := W64 1.
Definition RECEIVER_OBSERVED_CLOSED_W : w64 := W64 2.
Definition RECEIVER_CANNOT_PROCEED_W : w64 := W64 3.

(* Define result type for better type safety and readability *)
Inductive receiver_result := 
  | ReceiverCompletedWithSender
  | ReceiverMadeOffer
  | ReceiverObservedClosed
  | ReceiverCannotProceed.

(* Conversion function from result type to word representation *)
Definition result_to_word (res: receiver_result) : w64 := 
  match res with
    | ReceiverCompletedWithSender => RECEIVER_COMPLETED_WITH_SENDER_W
    | ReceiverMadeOffer => RECEIVER_MADE_OFFER_W
    | ReceiverObservedClosed => RECEIVER_OBSERVED_CLOSED_W
    | ReceiverCannotProceed => RECEIVER_CANNOT_PROCEED_W
  end.

(* Define word constants for offer results to match Go implementation *)
Definition OFFER_RESCINDED_W : w64 := W64 0.
Definition COMPLETED_EXCHANGE_W : w64 := W64 1.
Definition CLOSE_INTERRUPTED_OFFER_W : w64 := W64 2.

(* Define result type for better type safety and readability *)
Inductive rescind_result := 
  | OfferRescinded
  | CompletedExchange
  | CloseInterruptedOffer.

(* Conversion function from result type to word representation *)
Definition rescind_to_word (res: rescind_result) : w64 := 
  match res with
    | OfferRescinded => OFFER_RESCINDED_W
    | CompletedExchange => COMPLETED_EXCHANGE_W
    | CloseInterruptedOffer => CLOSE_INTERRUPTED_OFFER_W
  end.

  Lemma wp_Channel__ReceiverCompleteOrRescindOffer (ch: loc) (i: nat) (q: Qp) (γ: chan_names) 
  (chan_type: ty) (buff: Slice.t) (v: val) (send_count: nat) (recv_count: nat) 
  (vs: valid_chan_state) (size: nat) (is_single_party: bool) 
  (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) 
  (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ):
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff.(Slice.sz) = #(W64 0)) ->
(vs = Valid_receiver_ready \/ vs = Valid_sender_done \/ vs = Valid_closed) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷ isUnbufferedChan ch γ chan_type v vs is_single_party send_count recv_count Psingle 
    Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen vs send_count recv_count) ∗
  (if (vs =?= Valid_receiver_ready) || (vs =?= Valid_sender_done)
   then "Hsttok" ∷ exchange_token γ false v
   else emp) ∗
  "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗ 
  "HCloseTokPostClose" ∷ 
  if (vs =?= Valid_closed)
  then (∃ (n:nat) (close_tok_names: gset gname),
  "Hnameset" ∷  own_closed_tok_post_close γ n close_tok_names ∗ 
 "Hsc" ∷ own_send_counter_frag γ recv_count 1 ∗ 
  "#HSndCtrAuth" ∷ own_send_counter_auth γ n true 
  ) else emp
   
}}}
Channel__ReceiverCompleteOrRescindOffer chan_type #ch
{{{ (res: rescind_result), RET #(rescind_to_word res);
  match vs, res with
  | Valid_receiver_ready, OfferRescinded =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party send_count recv_count Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_start) ∗
      "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
      "HRecvPerm" ∷ own_recv_perm γ q i Ri ∗
      "HQ" ∷ Q is_single_party i Qsingle Qmulti
      
  | Valid_sender_done, CompletedExchange =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party send_count (recv_count + 1) Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_start) ∗
      "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1) false ∗ 
      "HRecvPerm" ∷ own_recv_perm γ q (i + 1) Ri ∗
      "HP" ∷ P is_single_party recv_count v Psingle Pmulti
      
  | Valid_closed, CloseInterruptedOffer =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_closed) ∗
      (* Resources for closed channel case *)
      own_recv_counter_frag γ i q ∗
      (∃ n: nat, Ri n ∗ own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
      
  | _, _ =>
      False
  end
}}}.
Proof.
intros Hvt Hbuff_zero Hvs.
iIntros (Φ) "Hpre HΦ".
iNamed "Hpre".

wp_rec. wp_pures.

(* Load current state *)
wp_apply (wp_loadField with "chan_state").
iIntros "chan_state".
wp_pures.

(* Cases based on current state *)
destruct vs.

- destruct Hvs as [Hvs | [Hvs | Hvs]];done.
- wp_auto. 
  (* Valid_receiver_ready case: Can rescind offer *)
  
  (* Apply transition *)
  simpl. 
  iNamed "Hpre".
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Set up counter verification *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    {
      subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
    }
    {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
    }
  }
  
  (* Apply transition using the general lemma *)
  iMod (receiver_transition_general ch γ chan_type v Valid_receiver_ready Valid_start
         receiver_rescind_trans is_single_party send_count recv_count
         Psingle Pmulti Qsingle Qmulti R Ri i q
         with "[HCh HRecvCtrAuth HRecvCtrFrag Hrct Hsttok]") as 
         "(HCh & HQ & HRecvCtrAuth & HRecvPerm)".
  { apply I. }
  { exact Hvt. }
  { simpl. iFrame.
    unfold isUnbufferedChan.
    unfold chan_state_resources.
    iDestruct "HCh" as "(%Hcsf & Hgv & HQ)".
    iFrame. done.
  }
  
  (* Return result *)
  iModIntro. simpl. 
  iSpecialize ("HΦ" $! OfferRescinded).
  iApply "HΦ". 
  replace (i + 0)%nat with i by lia.
  replace (recv_count + 0)%nat with recv_count by lia.
  iDestruct "HRecvPerm" as "(Hemp & Hrcauth & Hrcp)".
  iFrame. 
  
- (* Valid_sender_ready case: Invalid state *)
  destruct Hvs as [Hvs | [Hvs | Hvs]];done.
  
- destruct Hvs as [Hvs | [Hvs | Hvs]];done.
  
- (* Valid_sender_done case: Can complete exchange *)
  wp_auto.
  
  (* Complete exchange: sender_done → start *)
  simpl. iNamed "Hpre". 
  
  (* Apply transition *)
  iNamed "HRecvPerm".
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Set up counter verification *)
  iAssert (own_recv_counter_auth γ recv_count false ∗ 
           own_recv_counter_frag γ i q ∗ 
           ⌜if is_single_party then recv_count = i else i <= recv_count⌝%I)%I
    with "[HRecvCtrAuth HRecvCtrFrag]" as "(HRecvCtrAuth & HRecvCtrFrag & %Hispz)".
  {
    destruct is_single_party.
    {
      subst q.  
      iDestruct (recv_counter_elem with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. done.
    }
    {
      iDestruct (recv_counter_lower with "[$HRecvCtrAuth] [$HRecvCtrFrag]") as "%Hag2".
      iFrame. iPureIntro. lia.
    }
  }
  
  (* Apply transition using the general lemma *)
  iMod (receiver_transition_general ch γ chan_type v Valid_sender_done Valid_start
  receiver_complete_second_trans is_single_party send_count recv_count
  Psingle Pmulti Qsingle Qmulti R Ri i q 
  with "[HCh HRecvCtrAuth HRecvCtrFrag Hrct Hsttok]") as 
  "(HCh & HP & _ & _ & HRecvCtrAuth & HRecvPerm)".
  { apply I. }
  { exact Hvt. }
  { 
    iNamed "HCh".
    iFrame. 
    destruct is_single_party.
    {
      iFrame. simpl. iDestruct "HCh" as "(%Hvt2 & Hsttok & HP)".
      iFrame. done.
    }
    {
      iDestruct "HCh" as "(%Hvt2 & Hsttok & HP)".
      iFrame. done.
    }
  }
  
  (* Return result *)
  iModIntro. 
  iSpecialize ("HΦ" $! CompletedExchange).
  iApply "HΦ".
  iFrame.
  
- (* Valid_closed case: Channel is closed *)
  simpl. iDestruct "Hpre" as "[_ HRecvPerm]".
  iNamed "HRecvPerm". iNamed "HRecvPerm".
  
  (* Handle closed channel case *)
  iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
  
  (* Return result *)
  iSpecialize ("HΦ" $! CloseInterruptedOffer).
  
  (* Extract from invariant *)
  unfold isUnbufferedChan.
  iDestruct "HCh" as "[%HChanFacts HChanStateResources]".
  iFrame. iNamed "HCloseTokPostClose". 
  unfold own_closed_tok_post_close.
  iDestruct "Hnameset" as "[Hauthset Hset]".
  iDestruct (send_counter_elem with "[$HSndCtrAuth] [$Hsc]") as "%Hag2".
  iDestruct ((own_closed_tok_post_close_pop_raw γ n γi Ri close_tok_names) with "[Hset Hauthset Hrct]") as ">(Hset & Hauthset & Hri)".
  {
   iFrame.
  }
  wp_pures.
  iDestruct (send_counter_elem with "[$HSndCtrAuth] [$Hsc]") as "%Hag3".

  iApply "HΦ".
  iFrame "value chan_state HRecvCtrFrag".

  iModIntro. 
  iExists recv_count. iFrame "#". replace recv_count with n. iFrame. iFrame "#".
  replace ((send_count =? n)) with true by lia. iFrame.
Qed.
Lemma wp_Channel__ReceiverCompleteOrOffer (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) (buff: Slice.t)
  (v: val) (send_count: nat) (recv_count: nat) (vs: valid_chan_state)
  (size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) 
  (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ):
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
(#buff.(Slice.sz) = #(W64 0)) ->
{{{ 
  "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
  "HCh" ∷ isUnbufferedChan ch γ chan_type v vs is_single_party send_count recv_count Psingle 
    Pmulti Qsingle Qmulti R ∗ 
  "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
  "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
  "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count (recv_ctr_frozen vs send_count recv_count) ∗ 
  "HRecvPerm" ∷ own_recv_perm γ q i Ri 
}}}
Channel__ReceiverCompleteOrOffer chan_type #ch
{{{ (res: receiver_result), RET #(result_to_word res);
  match res with 
  | ReceiverCompletedWithSender =>
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_receiver_done is_single_party send_count (recv_count + 1) Psingle 
      Pmulti Qsingle Qmulti R ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_receiver_done) ∗
    "HRecvCtrAuth" ∷ own_recv_counter_auth γ (recv_count + 1) false ∗ 
    "HRecvPerm" ∷ own_recv_perm γ q (i + 1) Ri 
  | ReceiverMadeOffer =>
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_receiver_ready is_single_party send_count recv_count Psingle 
      Pmulti Qsingle Qmulti R ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_receiver_ready) ∗
    "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
    "Hsttok" ∷ receiver_exchange_token γ ∗  
    "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  | ReceiverObservedClosed =>
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_closed)
  | ReceiverCannotProceed =>
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "HCh" ∷ isUnbufferedChan ch γ chan_type v vs is_single_party send_count recv_count Psingle 
      Pmulti Qsingle Qmulti R ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
    "HQ" ∷ Q is_single_party i Qsingle Qmulti ∗ 
    "HRecvCtrAuth" ∷ own_recv_counter_auth γ recv_count false ∗ 
    "HRecvPerm" ∷ own_recv_perm γ q i Ri 
  end
}}}.
Proof.
  intros Hsp Hbuffsz.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  
  (* Cases based on current state *)
  destruct vs.
  
  - (* Valid_start case: Can make an offer *)
    wp_auto.
    
    (* Apply transition *)
    iNamed "HRecvPerm".
    iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
    
    (* Apply transition using the general lemma *)
    iMod (receiver_transition_general ch γ chan_type v Valid_start Valid_receiver_ready 
           receiver_offer_trans is_single_party send_count recv_count
           Psingle Pmulti Qsingle Qmulti R Ri i q
           with "[HCh HQ HRecvCtrAuth HRecvCtrFrag Hrct]") as 
           "(HCh & _ & _ & Hsttok & HRecStuff)".
    { apply I. }
    { exact Hsp. }
    { iFrame. }
    iNamed "HRecStuff".
    iNamed "HCh".
    
    iModIntro.
  iSpecialize ("HΦ" $! ReceiverMadeOffer).
    iApply "HΦ". 
    replace (recv_count + 0)%nat with recv_count by lia.
    replace (i + 0)%nat with i by lia.
    iFrame. iDestruct "HCh" as "[%Hfacts Hresources]".
    simpl.
    iDestruct "Hresources" as "[Htok HQ]".
    iFrame.
    iFrame. simpl in Hfacts.
    replace (i + 0)%nat with i by lia.
    replace (recv_count + 0)%nat with recv_count by lia.
    iFrame. unfold receiver_exchange_token. iPureIntro. lia.

    
  - (* Valid_receiver_ready case: Cannot proceed *)
    wp_auto. 
    iSpecialize ("HΦ" $! ReceiverCannotProceed).
    iApply "HΦ". 
    iFrame.
    iModIntro. done.
    
  - (* Valid_sender_ready case: Can complete receive *)
    wp_auto.
    
    (* Apply transition *)
    iNamed "HRecvPerm".
    iDestruct "HRecvPerm" as "[HRecvCtrFrag Hrct]".
    
    (* Apply transition using the general lemma *)
    iMod (receiver_transition_general ch γ chan_type v Valid_sender_ready Valid_receiver_done 
           receiver_complete_trans is_single_party send_count recv_count
           Psingle Pmulti Qsingle Qmulti R Ri i q
           with "[HCh HQ HRecvCtrAuth HRecvCtrFrag Hrct]") as 
           "(HCh & _ & _ & _ & HRecvCtrAuth & HRecvPerm)".
    { apply I. }
    { exact Hsp. }
    { iFrame. }
    
    iModIntro.
    iSpecialize ("HΦ" $! ReceiverCompletedWithSender).

    iApply "HΦ". 
    iFrame.
    
  - (* Valid_receiver_done case: Cannot proceed *)
    wp_auto. 
    iSpecialize ("HΦ" $! ReceiverCannotProceed).
    iApply "HΦ". 
    iFrame.
    iModIntro. done.
    
  - (* Valid_sender_done case: Cannot proceed *)
    wp_auto. 
    iSpecialize ("HΦ" $! ReceiverCannotProceed).
    iApply "HΦ". 
    iFrame.
    iModIntro. done.
    
  - (* Valid_closed case: Channel is closed *)
    wp_auto.
    iSpecialize ("HΦ" $! ReceiverObservedClosed).
    iApply "HΦ". 
    iFrame "chan_state".
    iModIntro. done.
Qed.
(* Define word constants for sender results to match Go implementation *)
Definition SENDER_COMPLETED_WITH_RECEIVER_W : w64 := W64 0.
Definition SENDER_MADE_OFFER_W : w64 := W64 1.
Definition SENDER_CANNOT_PROCEED_W : w64 := W64 2.

(* Define result type for better type safety and readability *)
Inductive sender_result := 
  | SenderCompletedWithReceiver
  | SenderMadeOffer
  | SenderCannotProceed.

(* Conversion function from result type to word representation *)
Definition sender_result_to_word (res: sender_result) : w64 := 
  match res with
    | SenderCompletedWithReceiver => SENDER_COMPLETED_WITH_RECEIVER_W
    | SenderMadeOffer => SENDER_MADE_OFFER_W
    | SenderCannotProceed => SENDER_CANNOT_PROCEED_W
  end.

(* Define sender transitions as a simple enum type *)
Inductive sender_transition : Type :=
  | sender_offer_trans
  | sender_complete_trans
  | sender_rescind_trans
  | sender_complete_second_trans.

(* Define a relation that checks if a transition is valid between two states *)
Definition is_valid_send_transition (tr: sender_transition) (vs_old vs_new: valid_chan_state) : Prop :=
  match tr, vs_old, vs_new with
  | sender_offer_trans, Valid_start, Valid_sender_ready => True
  | sender_complete_trans, Valid_receiver_ready, Valid_sender_done => True
  | sender_rescind_trans, Valid_sender_ready, Valid_start => True
  | sender_complete_second_trans, Valid_receiver_done, Valid_start => True
  | _, _, _ => False
  end.

(* Define how sending count changes in each transition *)
Definition sender_send_count_change (tr: sender_transition) : nat :=
  match tr with
  | sender_complete_trans => 1
  | sender_complete_second_trans => 1
  | _ => 0
  end.

(* Define whether additional token is needed for the transition *)
Definition sender_needs_token (tr: sender_transition) : bool :=
  match tr with
  | sender_rescind_trans => true
  | sender_complete_second_trans => true
  | _ => false
  end.

(* Define whether token is produced by the transition *)
Definition sender_produces_token (tr: sender_transition) : bool :=
  match tr with
  | sender_offer_trans => true
  | _ => false
  end.

(* Define whether P resource is needed for the transition *)
Definition sender_needs_P (tr: sender_transition) : bool :=
  match tr with
  | sender_offer_trans => true
  | sender_complete_trans => true
  | _ => false
  end.

(* Define whether Q resource is produced by the transition *)
Definition sender_produces_Q (tr: sender_transition) : bool :=
  match tr with
  | sender_complete_trans => true
  | sender_complete_second_trans => true
  | _ => false
  end.

(* General sender transition lemma *)
Lemma sender_transition_general (ch: loc) (γ: chan_names) (chan_type: ty) 
  (v vold: val) (vs_old vs_new: valid_chan_state) (tr: sender_transition) 
  (is_single_party: bool) (send_count recv_count: nat) 
  (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ) 
  (i: nat) (q: Qp):
  is_valid_send_transition tr vs_old vs_new ->
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  val_ty v chan_type ->
  (* Resources *)
  "HCh" ∷ isUnbufferedChan ch γ chan_type vold vs_old is_single_party send_count recv_count 
     Psingle Pmulti Qsingle Qmulti R ∗
  (if sender_needs_token tr then "Hsttok'" ∷ exchange_token γ true v else emp ∗ "%Heqv'" ∷  ⌜vold = v ⌝) ∗
  (if sender_needs_P tr then "HP" ∷ P is_single_party send_count v Psingle Pmulti else emp) ∗
  "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (send_ctr_frozen vs_old) ∗ 
  "HSndPerm" ∷ own_send_counter_frag γ i q  
  ==∗ 
  (* Result resources *)
  "HCh" ∷ isUnbufferedChan ch γ chan_type vold vs_new is_single_party 
     (send_count + sender_send_count_change tr) recv_count
     Psingle Pmulti Qsingle Qmulti R ∗
  (if negb (sender_produces_Q tr) && negb (sender_needs_P tr) 
  then "HP" ∷ P is_single_party send_count v Psingle Pmulti else emp ∗
    
  if sender_produces_token tr 
   then "Hsttok" ∷ exchange_token γ  true v else emp) ∗ "%Heqv"  ∷ ⌜vold = v ⌝  ∗
  (if sender_produces_Q tr 
   then "HQ" ∷ Q is_single_party i Qsingle Qmulti else emp) ∗
  "HSndCtrAuth" ∷ own_send_counter_auth γ (send_count + sender_send_count_change tr) 
                                         (send_ctr_frozen vs_new) ∗ 
  "HSndPerm" ∷ own_send_counter_frag γ (i + sender_send_count_change tr) q.
Proof.
  intros Hvalid Hsp Hvt.
  iIntros "( HCh & Htok & HP & HSndCtrAuth & HSndPerm)".
  
  (* First, destruct by transition type to handle each case specifically *)
  destruct tr; simpl in *; unfold is_valid_send_transition in Hvalid;
  destruct vs_old, vs_new; try (exfalso; exact Hvalid).
  
  - (* Case: sender_offer_trans - Valid_start → Valid_sender_ready *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "Hsttok".
    
    (* Handle token splitting *)
  iDestruct ((exchange_token_split γ true v) with "[$Hsttok]") as ">[Hsttok1 Hsttok2]".
  iNamed "HSndPerm".
    
    (* Handle counter verification *)
    iAssert (own_send_counter_auth γ send_count false ∗ 
             own_send_counter_frag γ i q ∗ 
             ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct is_single_party.
      - subst q.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    replace (send_count + 0)%nat with (send_count)%nat by lia.
    replace (i + 0)%nat with i by lia.
    
    (* Finalize *)
    iModIntro.
    unfold chan_state_resources.

    
    (* Rebuild resources *)
    iFrame. simpl. iDestruct "Htok" as "[Hemp %Heqv]". subst v. iFrame. done.
    
  - (* Case: sender_complete_trans - Valid_receiver_ready → Valid_sender_done *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "(Hsttok & HQ)".
    
    (* Handle counter verification and update *)
    iAssert (own_send_counter_auth γ send_count false ∗ 
             own_send_counter_frag γ i q ∗ 
             ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct is_single_party.
      - subst q.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Update counter *)
    iDestruct (send_counter_update γ send_count i with "[$HSndCtrAuth $HSndPerm]") 
      as ">[HSndCtrAuth HSndPerm]".
    
    (* Finalize *)
    iModIntro.
    iDestruct "Htok" as "[Hemp %Heqv]". 
    (* Rebuild resources *)
    iFrame.
    replace (send_count + 1)%nat with (S send_count)%nat by lia.
    replace (i + 1)%nat with (S i) by lia.
    iFrame. iNamed "HP". replace recv_count with send_count. iFrame.
    destruct is_single_party.
    {
     subst i. iFrame.
     iFrame. subst v. iFrame. done.
    }
    {
      subst v.
      iFrame.
      unfold Q.
      destruct (bool_decide (i < 0)%Z) eqn:?; simpl; [done|].
      iFrame.
       destruct bool_decide.
       {
        word.
       }
       destruct bool_decide eqn:?;simpl.
       {
        apply bool_decide_eq_true in Heqb0.
        lia.
       }
       { 
       iFrame. iPureIntro. done.
       } 
    }
    
  - (* Case: sender_rescind_trans - Valid_sender_ready → Valid_start *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "(Hsttok & HP')".
  iDestruct ((exchange_token_agree) with "[$Hsttok] [$Htok]") as "%Heq".
    
    (* Combine the tokens *)
  iDestruct ((exchange_token_combine) with "[$Hsttok $Htok]") as ">Hsttok".
    
    (* Handle counter verification *)
    iAssert (own_send_counter_auth γ send_count false ∗ 
             own_send_counter_frag γ i q ∗ 
             ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct is_single_party.
      - subst q.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Finalize *)
    iModIntro.
    
    (* Rebuild resources *)
    replace (send_count + 0)%nat with (send_count)%nat by lia.
    replace (i + 0)%nat with i by lia.
    iFrame.
    unfold chan_state_resources. iFrame.
    destruct Heq as [Heq _].
    rewrite Heq.
    iFrame.
    iPureIntro. destruct HChanFacts as [H1 H2]. done.
    
    
  - (* Case: sender_complete_second_trans - Valid_receiver_done → Valid_start *)
    simpl in *.
    
    (* Split unbuffered channel into facts and resources *)
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%HChanFacts HChanRes]".
    
    (* Extract state resources *)
    iDestruct "HChanRes" as "(Hsttok & HQ)".
    
    (* Combine the tokens *)
  iDestruct ((exchange_token_agree) with "[$Hsttok] [$Htok]") as "%Heq".
  iDestruct ((exchange_token_combine γ) with "[$Hsttok $Htok]") as ">Hsttok".
    
    (* Handle counter verification *)
    iAssert (own_send_counter_auth γ send_count false ∗ 
             own_send_counter_frag γ i q ∗ 
             ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct is_single_party.
      - subst q.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }

    iDestruct (send_counter_update γ send_count i with "[$HSndCtrAuth $HSndPerm]") 
      as ">[HSndCtrAuth HSndPerm]".
    
    (* Finalize *)
    iModIntro.
    
    (* Rebuild resources *)
    iFrame .
    
    (* Rebuild channel invariant *)
    iSplitL "".
    {
      iPureIntro. replace (send_count + 1)%nat with (S send_count) by lia.
      done.
    }
    destruct is_single_party.
    {
      subst i. iFrame.
      replace (send_count + 1)%nat with (S send_count) by lia.
    iFrame. destruct Heq as [Heq _]. done.
    }
    {
      unfold Q.
      replace (i + 1)%nat with (S i) by lia.
      replace (send_count + 1)%nat with (S send_count) by lia.
      destruct (bool_decide (i < 0)%Z) eqn:?; simpl.
      {
       iFrame.  
       iPureIntro. destruct Heq as [Heq _]. done.
      }
      iFrame.
       destruct bool_decide.
       {
        word.
       }
       destruct bool_decide eqn:?;simpl.
       {
        apply bool_decide_eq_true in Heqb0.
        lia.
       }
       destruct Heq as [Heq _].
       iFrame.
       done.
    }
Qed.

Lemma sender_token_state_agree γ ch v vs send_count recv_count v0 chan_type
  is_single_party Psingle Pmulti Qsingle Qmulti R :
  vs ≠ Valid_closed ->
  sender_exchange_token γ v -∗
  isUnbufferedChan ch γ chan_type v0 vs is_single_party send_count recv_count 
    Psingle Pmulti Qsingle Qmulti R -∗
  ⌜(vs = Valid_sender_ready ∨ vs = Valid_receiver_done) ∧ v = v0⌝.
Proof.
  intros Hvs.
  iIntros "Htok HChan".
  unfold isUnbufferedChan, chan_state_resources.
  iDestruct "HChan" as "[HChanFacts HChanRes]". unfold chan_state_facts.
  
  destruct vs.
  
  - (* Valid_start *)
    iDestruct "HChanRes" as "Hfull".
    unfold sender_exchange_token, exchange_token, full_exchange_token.
    iDestruct (ghost_var_valid_2 with "[$Htok] [$Hfull]") as "%Hvalid".
    (* Contradiction: can't have 1/2 + 1 = 1 *)
    iPureIntro. destruct Hvalid as [H1 H2].
    apply Qp.not_add_le_r in H1.
    contradiction.
    
  - (* Valid_receiver_ready *)
    iDestruct "HChanRes" as "[Hrec HQ]".
    unfold sender_exchange_token, exchange_token, receiver_exchange_token.
    iDestruct "Hrec" as (dummy_v) "Hrec".
    iDestruct (ghost_var_valid_2 with "[$Htok] [$Hrec]") as "%Hvalid".
    (* Contradiction: (true, v) ≠ (false, dummy_v) *)
    iPureIntro.
    destruct Hvalid as [_ Heq].
    inversion Heq. 
    
  - (* Valid_sender_ready *)
    iDestruct "HChanRes" as "[Hsnd HP]".
    unfold sender_exchange_token.
    iDestruct (ghost_var_agree with "[$Htok] [$Hsnd]") as "%Heq".
    (* Success: v = v0 *)
    iPureIntro. 
    split; [left; reflexivity | injection Heq; intros; subst; reflexivity].
    
  - (* Valid_receiver_done *)
    iDestruct "HChanRes" as "[Hsnd HQ]".
    unfold sender_exchange_token.
    iDestruct (ghost_var_agree with "[$Htok] [$Hsnd]") as "%Heq".
    (* Success: v = v0 *)
    iPureIntro.
    split; [right; reflexivity | injection Heq; intros; subst; reflexivity].
    
  - (* Valid_sender_done *)
    iDestruct "HChanRes" as "[Hrec HP]".
    unfold sender_exchange_token, exchange_token, receiver_exchange_token.
    iDestruct "Hrec" as (dummy_v) "Hrec".
    iDestruct (ghost_var_valid_2 with "[$Htok] [$Hrec]") as "%Hvalid".
    (* Contradiction: (true, v) ≠ (false, dummy_v) *)
    iPureIntro.
    destruct Hvalid as [_ Heq].
    inversion Heq. 
    
  - done. (* Valid_closed *)
    
Qed.

Lemma wp_Channel__SenderCheckOfferResult (ch: loc) (v: val) (γ: chan_names) (chan_type: ty) (buff: Slice.t)
  (send_count: nat) (recv_count: nat) (vs: valid_chan_state)
  (size: nat) (is_single_party: bool) (Psingle: (Z -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) 
  (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ)
  (i: nat) (q: Qp):
  (#buff.(Slice.sz) = #(W64 0)) ->
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  vs ≠ Valid_closed ->
  (vs = Valid_receiver_done \/ vs = Valid_sender_ready) ->
  {{{ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "HCh" ∷ isUnbufferedChan ch γ chan_type v vs is_single_party send_count recv_count Psingle 
      Pmulti Qsingle Qmulti R ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (send_ctr_frozen vs) ∗ 
    "Hsttok" ∷ exchange_token γ true v ∗
    "HSndPerm" ∷ own_send_counter_frag γ i q
  }}}
  Channel__SenderCheckOfferResult chan_type #ch
  {{{ (res: rescind_result), RET #(rescind_to_word res);
    match vs, res with
    | Valid_receiver_done, CompletedExchange =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party (S send_count) recv_count Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_start) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth γ (S send_count) false ∗ 
      "HSndPerm" ∷ own_send_counter_frag γ (i + 1) q ∗
      "HQ" ∷ Q is_single_party i Qsingle Qmulti
      
    | Valid_sender_ready, OfferRescinded =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_start is_single_party send_count recv_count Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_start) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗ 
      "HP" ∷  P is_single_party send_count v Psingle Pmulti ∗ 
      "HSndPerm" ∷ own_send_counter_frag γ i q
      
    | _, _ =>
      False
    end
  }}}.
Proof.
  intros Hbuffsz Hsp Hnot_closed Hvs.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  
  (* Check if channel is closed *)
  wp_apply (wp_loadField with "chan_state").
  iIntros "chan_state".
  wp_pures.
    iDestruct (struct_field_pointsto_ty with "[$value]") as "%H".
    {
     simpl. done. 
    }
  
  (* Cases based on vs ≠ Valid_closed *)
  destruct vs.
  
  - (* Valid_start case: Not a valid state *)
    destruct Hvs as [Hvs | Hvs]; discriminate.
    
  - (* Valid_receiver_ready case: Not a valid state *)
    destruct Hvs as [Hvs | Hvs]; discriminate.
    
  - (* Valid_sender_ready case: Can rescind offer *)
    destruct Hvs as [Hvs | Hvs]; try discriminate.
    wp_auto.
    unfold isUnbufferedChan.
    iDestruct "HCh" as "[%Hfacts Hres]".
    unfold chan_state_resources.
    iDestruct "Hres" as "[Hgv HP]".
    
    (* Apply sender_transition_general *)
    iMod (sender_transition_general ch γ chan_type v v Valid_sender_ready Valid_start 
           sender_rescind_trans is_single_party send_count recv_count
           Psingle Pmulti Qsingle Qmulti R Ri i q with 
          "[HSndCtrAuth HSndPerm Hgv Hsttok HP]") as 
          "IH".
    { (* Prove valid transition *)
      unfold is_valid_send_transition.
      destruct Valid_sender_ready, Valid_start; try done.
    }
    { (* Ownership constraint *)
      exact Hsp.
    }
    { (* Value type check *)
      val_ty.
    }
    {
      simpl.
      iFrame. done.
    }
    
    
    (* Finalize *)
    iModIntro.
    iSpecialize ("HΦ" $! OfferRescinded).
    
    iApply "HΦ". iNamed "IH". simpl. iNamed "IH". 
    iFrame. simpl. iNamed "HCh". iDestruct "IH" as "[H1 H2]".
    replace (send_count + 0)%nat with send_count by lia.
    replace (i + 0)%nat with i by lia.
    iFrame.
    
  - (* Valid_receiver_done case: Can complete exchange *)
    destruct Hvs as [Hvs | Hvs]; try discriminate.
    wp_auto.
    
    (* Apply sender_transition_general *)
    iMod (sender_transition_general ch γ chan_type v v  Valid_receiver_done Valid_start 
           sender_complete_second_trans is_single_party send_count recv_count
           Psingle Pmulti Qsingle Qmulti R Ri i q with 
          "[HCh HSndCtrAuth HSndPerm Hsttok]") as 
          "(HCh & HQ & HSndCtrAuth & HSndPerm)".
    { (* Prove valid transition *)
      unfold is_valid_send_transition.
      destruct Valid_receiver_done, Valid_start; try done.
    }
    { (* Ownership constraint *)
      exact Hsp.
    }
    { (* Value type check *)
      val_ty.
    }
    { 
      iFrame.
      (* Need to supply HP if needed *)
      destruct (sender_needs_P sender_complete_second_trans).
      + simpl. unfold isUnbufferedChan. simpl. unfold chan_state_resources.
      iDestruct "HCh" as "(%Hp & Hgv & HP)". iFrame. done.
      + simpl. unfold isUnbufferedChan. simpl. unfold chan_state_resources.
      iDestruct "HCh" as "(%Hp & Hgv & HP)". iFrame. done.
    }
    
    (* Finalize *)
    iModIntro.
    iSpecialize ("HΦ" $! CompletedExchange).
    iApply "HΦ". 
    iNamed "HCh".
    iFrame. simpl. iNamed "HCh". iDestruct "HSndPerm" as "(HnQ & H1 & H2)".
    replace (send_count + 0)%nat with send_count by lia.
    replace (send_count + 1)%nat with (S send_count) by lia.
    replace (i + 0)%nat with i by lia.
    iFrame. 
    
  - (* Valid_sender_done case: Not a valid state *)
    destruct Hvs as [Hvs | Hvs]; discriminate.
    
  - (* Valid_closed case *)
    exfalso.
    apply Hnot_closed. reflexivity.
Qed.

Lemma wp_Channel__SenderCompleteOrOffer (ch: loc) (v vold: val) (γ: chan_names) (chan_type: ty) 
  (buff: Slice.t) (vs: valid_chan_state) (send_count recv_count: nat) (size: nat) 
  (is_single_party: bool) (Psingle: Z -> val -> iProp Σ) (Pmulti: val -> iProp Σ) 
  (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) (R Ri: nat -> iProp Σ) (i: nat) (q: Qp):
  val_ty v chan_type ->
  val_ty vold chan_type ->
  (#buff.(Slice.sz) = #(W64 0)) ->
  vs ≠ Valid_closed ->
  (if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
  {{{ 
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] vold ∗ 
    "HCh" ∷ isUnbufferedChan ch γ chan_type vold vs is_single_party send_count recv_count Psingle 
      Pmulti Qsingle Qmulti R ∗ 
    "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
    "HP" ∷ P is_single_party i v Psingle Pmulti ∗
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (send_ctr_frozen vs) ∗ 
    "HSndPerm" ∷ own_send_counter_frag γ i q
  }}}
  Channel__SenderCompleteOrOffer chan_type #ch v
  {{{ (res: sender_result), RET #(sender_result_to_word res);
    match res, vs with
    | SenderCompletedWithReceiver, Valid_receiver_ready =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_sender_done is_single_party (send_count + 1) recv_count Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_sender_done) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth γ (send_count + 1) false ∗ 
      "HSndPerm" ∷ own_send_counter_frag γ (i + 1) q ∗
      "HQ" ∷ Q is_single_party i Qsingle Qmulti
      
    | SenderMadeOffer, Valid_start =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type v Valid_sender_ready is_single_party send_count recv_count Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word Valid_sender_ready) ∗
      "HSndCtrAuth" ∷ own_send_counter_auth γ send_count false ∗ 
      "HSndPerm" ∷ own_send_counter_frag γ i q ∗
      "Hsttok" ∷ exchange_token γ true v
      
    | SenderCannotProceed, _ =>
      "value" ∷ ch ↦[(Channel chan_type) :: "v"] vold ∗ 
      "HCh" ∷ isUnbufferedChan ch γ chan_type vold vs is_single_party send_count recv_count Psingle 
        Pmulti Qsingle Qmulti R ∗ 
      "chan_state" ∷ ch ↦[(Channel chan_type) :: "state"] #(valid_to_word vs) ∗
      "HP" ∷ P is_single_party i v Psingle Pmulti ∗
      "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (send_ctr_frozen vs) ∗ 
      "HSndPerm" ∷ own_send_counter_frag γ i q
      
    | _, _ => False
    end
  }}}.
Proof.
  intros Hval_ty Hval_tynew Hbuffsz Hnot_closed Hsp.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  
  wp_rec. wp_pures.
  
  (* Check if channel is closed *)
  wp_apply (wp_loadField with "chan_state").
  iIntros "chan_state".
  wp_pures.
  
  (* Cases based on vs ≠ Valid_closed *)
  destruct vs.
  
  - (* Valid_start case: Can make an offer *)
    wp_auto.
    (* Handle counter verification and update *)
    iAssert (own_send_counter_auth γ send_count false ∗ 
             own_send_counter_frag γ i q ∗ 
             ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct is_single_party.
      - subst q.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Apply transition using the general lemma *)
    iMod (sender_transition_general ch γ chan_type v v  Valid_start Valid_sender_ready 
           sender_offer_trans is_single_party send_count recv_count
           Psingle Pmulti Qsingle Qmulti R Ri i q with 
          "[HCh HSndCtrAuth HSndPerm HP]") as 
          "(HCh & Hsttok & _ & _ &  HSndCtrAuth & HSndPerm)".
    { (* Prove valid transition *)
      unfold is_valid_send_transition.
      destruct Valid_start, Valid_sender_ready; try done.
    }
    { (* Ownership constraint *)
      exact Hsp.
    }
    { (* Value type check *)
      exact Hval_ty.
    }
    { 
      simpl.
      unfold isUnbufferedChan. unfold chan_state_resources.
      iFrame.
      unfold P.
      destruct is_single_party.
      {
        subst. iFrame.
        done.
        }
        (* Supply HP for this transition *)
        iFrame.
        done.
    }
    
    (* Finalize *)
    iModIntro.
    iSpecialize ("HΦ" $! SenderMadeOffer).
    iApply "HΦ". simpl.
    replace (send_count + 0)%nat with send_count by lia.
    replace (i + 0)%nat with i by lia.
    iFrame.
    iDestruct "Hsttok" as "[_ Hsttok]". iFrame. 
    
  - (* Valid_receiver_ready case: Can complete exchange *)
    wp_auto.
    iAssert (own_send_counter_auth γ send_count false ∗ 
             own_send_counter_frag γ i q ∗ 
             ⌜if is_single_party then send_count = i else i <= send_count⌝%I)%I
      with "[HSndCtrAuth HSndPerm]" as "(HSndCtrAuth & HSndPerm & %Hispz)".
    {
      destruct is_single_party.
      - subst q.
        iDestruct (send_counter_elem with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. done.
      - iDestruct (send_counter_lower with "[$HSndCtrAuth] [$HSndPerm]") as "%Hag2".
        iFrame. iPureIntro. lia.
    }
    
    (* Apply transition using the general lemma *)
    unfold isUnbufferedChan. unfold chan_state_resources.
    iMod (sender_transition_general ch γ chan_type v v Valid_receiver_ready Valid_sender_done 
           sender_complete_trans is_single_party send_count recv_count
           Psingle Pmulti Qsingle Qmulti R Ri i q with 
          "[HCh HSndCtrAuth HSndPerm HP]") as 
          "(HCh & _ & HQ & HSndCtrAuth & HSndPerm)".
    { (* Prove valid transition *)
      unfold is_valid_send_transition.
      destruct Valid_receiver_ready, Valid_sender_done; try done.
    }
    { (* Ownership constraint *)
      exact Hsp.
    }
    { (* Value type check *)
    done.
    }
    { 
      iFrame.
      simpl.
      unfold P.
      destruct is_single_party.
      {
        subst. iFrame. done.

      }
      (* Supply HP for this transition *)
      iFrame.
     done. 
    }
    
    (* Finalize *)
    iModIntro.
    iSpecialize ("HΦ" $! SenderCompletedWithReceiver).
    iApply "HΦ". 
    iFrame. done.
    
  - (* Valid_sender_ready case: Cannot proceed *)
    wp_auto.
    iSpecialize ("HΦ" $! SenderCannotProceed).
    iApply "HΦ". 
    iFrame. iModIntro. done.
    
  - (* Valid_receiver_done case: Cannot proceed *)
    wp_auto.
    iSpecialize ("HΦ" $! SenderCannotProceed).

    iApply "HΦ". 
    iFrame. iModIntro. done.
    
  - (* Valid_sender_done case: Cannot proceed *)
    wp_auto.
    iSpecialize ("HΦ" $! SenderCannotProceed).
    iApply "HΦ". 
    iFrame. iModIntro. done.
    
  - (* Valid_closed case *)
    exfalso.
    apply Hnot_closed. reflexivity.
Qed.


End proof.