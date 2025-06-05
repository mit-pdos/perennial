From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_base.
From New.generatedproof.github_com.goose_lang.goose.model
  Require Import channel.
Require Import New.proof.sync.

Section proof.
 Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context  `{!chanGhostStateG Σ}.

Record chan  (V: Type )  := {
  (* Type and type classes for the value type of a channel *)
  ch_t : go_type;
  ch_IntoVal : IntoVal V;
  ch_IntoValTyped : IntoValTyped V ch_t;
  ch_BoundedTypeSize : BoundedTypeSize ch_t;
  (* ptr to channel *)
  ch_loc: loc;
  (* mutex that guards channel internals *)
  ch_mu: loc;
  (* slice that acts as buffered channel's internal circular buffer *)
  ch_buff: slice.t;
  (* ghost names for channel ghost state *)
  ch_γ: chan_names;
  (* 0 for unbuffered, size of buffer for buffered *)
  ch_size: Z;
  (* 
    Whether this channel will only be used by 1 sender and 1 receiver. If so, we 
    can access the sequence number in predicates using the _single versions below
  *)
  ch_is_single_party: bool;
  (* Predicates sent from sender to receiver, where we can access the sequence 
    number if we agree not to have multiple parties, which loses ordering.

    If you aren't planning on using this predicate, just have it return True or emp. If 
    you are planning on restricting the number of operations over the channel to n, 
    have it return False after n operations
  *)
  ch_Psingle: Z -> V -> iProp Σ;
  ch_Pmulti: V -> iProp Σ;
  (* Predicates sent from receiver to sender, where we can access the sequence 
    number if we agree not to have multiple parties, which loses ordering. 
    ch_Qsingle handles buffered channels by allowing a sender to gain the i-buffer_size 
    predicate, providing synchronization by guaranteeing a receiver has blocked or 
    consumed a value. 

    If you aren't planning on using this predicate, just have it return True or emp. If 
    you are planning on restricting the number of operations over the channel to n, 
    have it return False after n operations
  *)
  ch_Qsingle: Z -> iProp Σ;
  ch_Qmulti: iProp Σ;
  (* 
    The central predicate for closing. The nat here is the number of sends/receives at 
    the time of close. If we won't close, use (n) => False 
    This can be split amongst multiple receivers using the lemmas in chan_ghost_state.
   *)
  ch_R: nat -> iProp Σ;
}.

Arguments ch_loc: default implicits.
Arguments ch_mu: default implicits.
Arguments ch_buff: default implicits.
Arguments ch_γ: default implicits.
Arguments ch_size: default implicits.
Arguments ch_is_single_party: default implicits.
Arguments ch_Psingle: default implicits.
Arguments ch_Qsingle: default implicits.
Arguments ch_Qmulti: default implicits.
Arguments ch_Pmulti: default implicits.
Arguments ch_R: default implicits.

(* Args for a simple use of send for synchronization i.e. using Send to join a goroutine. 
 Enforces that a channel isn't closed using a always-False R predicate. 
 *)
Definition make_unbuffered_params_simple_single_sync
V {H: IntoVal V} {t} {H': IntoValTyped V t} {B: BoundedTypeSize t}
(ch: loc)
(mu: loc)
(buff: slice.t)
(γ: chan_names)
(Psingle: Z -> V -> iProp Σ)
: chan V :=
{|
  ch_loc := ch;
  ch_mu := mu;
  ch_buff := buff;
  ch_γ := γ;
  ch_size := 0;
  ch_is_single_party := true;
  ch_Psingle := Psingle;  
  ch_Pmulti := λ _, True%I;    
  ch_Qsingle := λ _, True%I;   
  ch_Qmulti := True%I;         
  ch_R := λ _,False%I; (*No closing*)
|}
.

Definition P (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (is_single_party: bool) (i: Z) (v: V) 
              (Psingle: Z -> V -> iProp Σ) (Pmulti: V -> iProp Σ) : iProp Σ := 
  if is_single_party then Psingle i v else Pmulti v.

Definition Q (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (is_single_party: bool) (z: Z) 
              (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) : iProp Σ := 
  if bool_decide(Z.lt z 0%Z) then True%I else (if is_single_party then Qsingle(z) else Qmulti).

Definition buff_size_inv (count : Z) (first : u64) (size : Z): iProp Σ :=
(⌜count <= size⌝ ∗ ⌜word.unsigned first < size⌝ ∗ ⌜size > 0⌝ ∗ ⌜size + 1 < 2 ^ 63⌝
∗ ⌜count + 1 < 2 ^ 63⌝)%I.

Definition valid_elems (V: Type) (slice : list V) (first : u64) (count : u64) : list V :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).

Definition isBufferedChanLogical (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t}
 (params: chan V  ) 
  (vs: valid_chan_state) (send_count recv_count: nat) (count: Z) 
  (first: u64) (xs: list V) : iProp Σ := 
  "%HCountMinus" ∷ ⌜count = (send_count - recv_count)⌝ ∗
  "%HSizeLen" ∷ ⌜(ch_size params) = length xs⌝ ∗
  "%HBuffSizeInv" ∷ buff_size_inv count first (length xs) ∗
  "HPs" ∷ ([∗ list] i↦x ∈ valid_elems V xs first count, 
            P V (ch_is_single_party params)  (recv_count + i) x (ch_Psingle params) (ch_Pmulti   params)) ∗ 
  "HQs" ∷ big_sep_seq send_count ((ch_size params)- count) 
           (λ i, Q V (ch_is_single_party params) (i - (ch_size params)) (ch_Qsingle  params) (ch_Qmulti params)).

Definition isBufferedChan (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V ) 
  (vs: valid_chan_state) (send_count recv_count: nat) (count: Z) 
  (first: u64) : iProp Σ := 
  ∃ (xs: list V), 
    "HBuffSlice" ∷ own_slice 
                     (ch_buff params) (DfracOwn 1) xs ∗
    isBufferedChanLogical V params vs send_count recv_count count first xs.

Definition chan_state_facts (vs: valid_chan_state) (send_count recv_count: nat) : iProp Σ :=
match vs with
  | Valid_start => ⌜send_count = recv_count⌝
  | Valid_receiver_ready => ⌜send_count = recv_count⌝
  | Valid_sender_ready => (⌜send_count = recv_count⌝ )
  | Valid_receiver_done => ⌜recv_count = S send_count⌝ 
  | Valid_sender_done => (⌜send_count = S recv_count⌝ )
  | Valid_closed => ⌜send_count = recv_count⌝
end.

Definition chan_state_resources (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V)
  (vs: valid_chan_state) (send_count recv_count: nat) (v: V) : iProp Σ :=
  match vs with
  | Valid_start => 
      "Hextok" ∷ full_exchange_token (ch_γ params)
  | Valid_receiver_ready => 
      "Hextok" ∷ receiver_exchange_token params.(ch_γ) ∗
      "HQ" ∷ Q V params.(ch_is_single_party) recv_count params.(ch_Qsingle) params.(ch_Qmulti)
  | Valid_sender_ready => 
      "Hextok" ∷ sender_exchange_token params.(ch_γ) v ∗
      "HP" ∷ P V (ch_is_single_party params) send_count v params.(ch_Psingle) (ch_Pmulti params)
  | Valid_receiver_done => 
      "Hextok" ∷ sender_exchange_token params.(ch_γ) v ∗
      "HQ" ∷ Q V params.(ch_is_single_party) send_count params.(ch_Qsingle) params.(ch_Qmulti)
  | Valid_sender_done => 
      "Hextok" ∷ receiver_exchange_token params.(ch_γ) ∗
      "HP" ∷ P V params.(ch_is_single_party) recv_count v params.(ch_Psingle) (ch_Pmulti params)
  | Valid_closed => emp
  end.


Definition isUnbufferedChan (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V)
(v: V) (vs: valid_chan_state) (send_count recv_count: nat) : iProp Σ := 
"%HUnBuffFacts" ∷ chan_state_facts vs send_count recv_count ∗
chan_state_resources V params vs send_count recv_count v.

Definition isChanInner (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V): iProp Σ := 
  ∃ (vs: valid_chan_state) (count: nat) (first: u64) (v: V) (send_count recv_count: nat),
    (* Physical state *)
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
    "first" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "first"] first ∗
    "count" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "count"] (W64 count) ∗ 
    "state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word vs) ∗ 
    
    (* Counter resources *)
    "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count (send_ctr_frozen vs) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth params.(ch_γ) recv_count (recv_ctr_frozen vs send_count recv_count) ∗ 
    
    (* Close resources *)
    "HCloseTokPostClose" ∷ 
      (match vs with
        | Valid_closed => 
           ∃ (n: nat) (close_tok_names: gset gname), 
             own_closed_tok_post_close params.(ch_γ) n close_tok_names ∗ 
             own_send_counter_frag params.(ch_γ) n 1
        | _ => True
       end) ∗

    (* Buffer vs unbuffered channels *)
    "HChanState" ∷ 
      (if params.(ch_size) =? 0 then
        isUnbufferedChan V params v vs send_count recv_count
      else
        isBufferedChan V params vs send_count recv_count count first).

Definition isChanInnerClosed (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V): iProp Σ := 

  ∃ (count: nat) (first: u64) (v: V) (send_count recv_count: nat),
    (* Physical state *)
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "v"] v ∗ 
    "first" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "first"] first ∗
    "count" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "count"] (W64 count) ∗ 
    "state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "state"] (valid_to_word Valid_closed) ∗ 
    
    (* Counter resources *)
    "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_γ) send_count (send_ctr_frozen Valid_closed) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth params.(ch_γ) recv_count (recv_ctr_frozen Valid_closed send_count recv_count) ∗ 
    
    (* Close resources *)
    "HCloseTokPostClose" ∷ 
      
           ∃ (n: nat) (close_tok_names: gset gname), 
             own_closed_tok_post_close params.(ch_γ) n close_tok_names ∗ 
             own_send_counter_frag params.(ch_γ) n 1
         ∗

    (* Buffer vs unbuffered channels *)
    "HChanState" ∷ 
      (if params.(ch_size) =? 0 then
        isUnbufferedChan V params v Valid_closed send_count recv_count
      else
        isBufferedChan V params Valid_closed send_count recv_count count first).

Definition isChan (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) : iProp Σ := 
    "#mu" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "lock"]□ params.(ch_mu) ∗
    "#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "buffer"]□ params.(ch_buff) ∗
    "%Hbuffsize" ∷ ⌜#params.(ch_buff).(slice.len_f) = #(W64 params.(ch_size))⌝ ∗
    "%Hbuffsize" ∷ ⌜0 ≤  params.(ch_size)⌝ ∗
    "%Hbuffsize" ∷ ⌜params.(ch_size) + 1 < 2 ^ 63⌝ ∗
    "#Hlock" ∷ is_Mutex params.(ch_mu) (isChanInner V params).

Definition send_pre (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) (v: V) : iProp Σ :=
  "%Hsp" ∷ ⌜if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp⌝ ∗
  "HCh" ∷ isChan V params ∗
  "HP" ∷ P V (ch_is_single_party params) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
  "HSc" ∷ own_send_counter_frag params.(ch_γ) i q.

Definition send_pre_inner (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) (v: V) : iProp Σ :=
  "%Hsp" ∷ ⌜if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp⌝ ∗
  "HCh" ∷ isChanInner V params ∗
  "%Hbuffsize" ∷ ⌜params.(ch_buff).(slice.len_f) = (W64 params.(ch_size))⌝ ∗
    "#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "buffer"]□ params.(ch_buff) ∗
  "HP" ∷ P V params.(ch_is_single_party) i v (ch_Psingle params) (ch_Pmulti params) ∗ 
  "HSc" ∷ own_send_counter_frag params.(ch_γ) i q.

Definition send_post (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) : iProp Σ :=
Q V params.(ch_is_single_party) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
own_send_counter_frag params.(ch_γ) (i + 1)%nat q.


Definition send_post_inner (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) : iProp Σ :=
  "HCh" ∷ isChanInner V params ∗
Q V params.(ch_is_single_party) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
own_send_counter_frag params.(ch_γ) (i + 1)%nat q.

Definition recv_pre (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) (Ri: nat -> iProp Σ) : iProp Σ :=
  "%Hsp" ∷  ⌜if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp⌝ ∗
  "HCh" ∷ isChan V params ∗
  "HQ" ∷ Q V params.(ch_is_single_party) i params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
  "HRecvPerm" ∷ own_recv_perm params.(ch_γ) q i Ri.

Definition default_val (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) : V :=
@default_val V t _ H H'.

Definition recv_post (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) (ok: bool) (v: V) (Ri: nat -> iProp Σ) : iProp Σ :=
if ok then
  (P V params.(ch_is_single_party) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
   own_recv_perm params.(ch_γ) q (i + 1) Ri)%I
else
  ("HRecFrag" ∷ own_recv_counter_frag params.(ch_γ) i q ∗ 
   "%Hvdef" ∷ ⌜v = default_val V params⌝ ∗ 
   (∃ n, "HRi" ∷ Ri n ∗ 
         "#Hsca" ∷ own_send_counter_auth params.(ch_γ) n true ∗ 
         "#Hrca" ∷ own_recv_counter_auth params.(ch_γ) n true))%I.

Definition recv_pre_inner (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) (Ri: nat -> iProp Σ) : iProp Σ :=
"%Hsp" ∷ ⌜if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp⌝ ∗
"HCh" ∷ isChanInner V params ∗
"%Hbuffsize" ∷ ⌜params.(ch_buff).(slice.len_f) = W64 params.(ch_size)⌝ ∗
"#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty t) :: "buffer"]□ params.(ch_buff) ∗
"HQ" ∷ Q V params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
"HRecvPerm" ∷ own_recv_perm params.(ch_γ) q i Ri.
       
Definition recv_post_inner (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (q: Qp) (i: nat) (ok: bool) (v: V) (Ri: nat -> iProp Σ) : iProp Σ :=
  "HCh" ∷ isChanInner V params ∗
  if ok then
    (P V params.(ch_is_single_party) (Z.of_nat i) v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
    own_recv_perm params.(ch_γ) q (i + 1) Ri)%I
  else
    ("HRecFrag" ∷ own_recv_counter_frag params.(ch_γ) i q ∗ 
    "%Hvdef" ∷ ⌜v = default_val V params⌝ ∗ 
    (∃ n, "HRi" ∷ Ri n ∗ 
          "#Hsca" ∷ own_send_counter_auth params.(ch_γ ) n true ∗ 
          "#Hrca" ∷ own_recv_counter_auth params.(ch_γ) n true))%I.

Lemma closed_unbuff_eq (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (params: chan V) (send_count recv_count: nat) (v: V):
  isUnbufferedChan V params v Valid_closed send_count recv_count -∗ ⌜send_count = recv_count⌝.
Proof.
  iIntros "[%Heq _]". iPureIntro. exact Heq.
Qed.

Lemma chan_pointsto_non_null (V: Type) {H: IntoVal V} {t} {H': IntoValTyped V t} (lock: loc) (params: chan V):
  params.(ch_loc) ↦s[channel.Channel.ty t :: "lock"]□ lock -∗ ⌜ #params.(ch_loc) ≠ #null ⌝.
Proof.
  iIntros "Hb.a".
  iDestruct (typed_pointsto_not_null with "Hb.a") as %Hnotnull.
  { rewrite go_type_size_unseal. done. }
  iPureIntro. intro H0. subst.
  rewrite struct.field_ref_f_unseal in Hnotnull.
  rewrite to_val_unseal in H0. simpl in H0. inversion H0. replace (params.(ch_loc)) with null in *. 
  simpl in Hnotnull.
  contradiction.
Qed.

End proof.
