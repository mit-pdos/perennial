From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_base.
From New.generatedproof.github_com.goose_lang.goose.model
  Require Import channel.
Require Import New.proof.sync.

Section proof.
 Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
Implicit Types (v:val). 
Context `{!ghost_varG Σ (bool * val)}.

Record chan := {
  ch_T': Type;
  ch_T: go_type;
  ch_IntoVal: IntoVal ch_T';
  ch_IntoValTyped: IntoValTyped ch_T' ch_T;
  ch_Hbounded: BoundedTypeSize ch_T;
  ch_loc: loc;
  ch_names: chan_names;
  ch_size: Z;
  ch_is_single_party: bool;
  ch_q: Qp;
  ch_Psingle: Z -> ch_T' -> iProp Σ;
  ch_Pmulti: ch_T' -> iProp Σ;
  ch_Qsingle: Z -> iProp Σ;
  ch_Qmulti: iProp Σ;
  ch_R: nat -> iProp Σ;
  ch_Ri: nat -> iProp Σ;
}.

(* Args for a simple use of send for synchronization i.e. using Send to join a goroutine. 
 Enforces that a channel isn't closed using a always-False R predicate. 
 *)
Definition make_unbuffered_params_simple_single_sync (t': Type)
(t: go_type)
(iv: IntoVal t')
(ivt: IntoValTyped t' t)
(hb: BoundedTypeSize t)
(ch: loc)
(γ: chan_names)
(Psingle: Z -> t' -> iProp Σ)
: chan :=
{|
  ch_T' := t';
  ch_T := t;
  ch_IntoVal := iv;
  ch_IntoValTyped := ivt;
  ch_Hbounded := hb;
  ch_loc := ch;
  ch_names := γ;
  ch_size := 0;
  ch_is_single_party := true;
  ch_q := 1%Qp;
  ch_Psingle := Psingle;  
  ch_Pmulti := λ _, True%I;    
  ch_Qsingle := λ _, True%I;   
  ch_Qmulti := True%I;         
  ch_R := λ _,False%I; (*No closing*)
  ch_Ri := λ _, False%I; (*No closing*)
|}
.


Definition P {T'} (is_single_party: bool) (i: Z) (v: T') 
              (Psingle: Z -> T' -> iProp Σ) (Pmulti: T' -> iProp Σ) : iProp Σ := 
  if is_single_party then Psingle i v else Pmulti v.

Definition Q (is_single_party: bool) (z: Z) 
              (Qsingle: Z -> iProp Σ) (Qmulti: iProp Σ) : iProp Σ := 
  if bool_decide(Z.lt z 0%Z) then True%I else (if is_single_party then Qsingle(z) else Qmulti).

Definition buff_size_inv (count : Z) (first : u64) (size : Z): iProp Σ :=
(⌜count <= size⌝ ∗ ⌜word.unsigned first < size⌝ ∗ ⌜size > 0⌝ ∗ ⌜size + 1 < 2 ^ 63⌝
∗ ⌜count + 1 < 2 ^ 63⌝)%I.

Definition valid_elems {T'} (slice : list T') (first : u64) (count : u64) : list T' :=
  subslice (uint.nat first) (uint.nat first + uint.nat count) (slice ++ slice).

Definition isBufferedChanLogical (params: chan) 
  (vs: valid_chan_state) (send_count recv_count: nat) (count: Z) 
  (first: u64) (xs: list params.(ch_T')) : iProp Σ := 
  "%HCountMinus" ∷ ⌜count = (send_count - recv_count)⌝ ∗
  "%HSizeLen" ∷ ⌜params.(ch_size) = length xs⌝ ∗
  "%HBuffSizeInv" ∷ buff_size_inv count first (length xs) ∗
  "HPs" ∷ ([∗ list] i↦x ∈ valid_elems xs first count, 
            P params.(ch_is_single_party) (recv_count + i) x params.(ch_Psingle) params.(ch_Pmulti)) ∗ 
  "HQs" ∷ big_sep_seq send_count (params.(ch_size) - count) 
           (λ i, Q params.(ch_is_single_party) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti)).

Definition isBufferedChan (params: chan ) 
  (vs: valid_chan_state) (send_count recv_count: nat) (count: Z) 
  (buff: slice.t) (first: u64) : iProp Σ := 
  let intoVal := params.(ch_IntoVal) in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  ∃ (xs: list params.(ch_T')), 
    "HBuffSlice" ∷ own_slice 
                     buff (DfracOwn 1) xs ∗
    isBufferedChanLogical params vs send_count recv_count count first xs.

Definition chan_state_facts (vs: valid_chan_state) (send_count recv_count: nat) : iProp Σ :=
match vs with
  | Valid_start => ⌜send_count = recv_count⌝
  | Valid_receiver_ready => ⌜send_count = recv_count⌝
  | Valid_sender_ready => (⌜send_count = recv_count⌝ )
  | Valid_receiver_done => ⌜recv_count = S send_count⌝ 
  | Valid_sender_done => (⌜send_count = S recv_count⌝ )
  | Valid_closed => ⌜send_count = recv_count⌝
end.

Definition chan_state_resources (params: chan)
  (vs: valid_chan_state) (send_count recv_count: nat) (v: params.(ch_T')) : iProp Σ :=
  let intoVal := params.(ch_IntoVal) in
  match vs with
  | Valid_start => 
    "Hextok" ∷ full_exchange_token params.(ch_names) (* Full token with default value *)
  | Valid_receiver_ready => 
    "Hextok" ∷ receiver_exchange_token params.(ch_names) ∗ (* Receiver initiated *)
    "HQ" ∷ Q params.(ch_is_single_party) recv_count params.(ch_Qsingle) params.(ch_Qmulti)
  | Valid_sender_ready => 
    "Hextok" ∷ sender_exchange_token params.(ch_names) #v ∗ (* Sender initiated *)
    "HP" ∷ P params.(ch_is_single_party) send_count v params.(ch_Psingle) params.(ch_Pmulti)
  | Valid_receiver_done => 
    "Hextok" ∷ sender_exchange_token params.(ch_names) #v ∗ (* Receiver will complete *)
    "HQ" ∷ Q params.(ch_is_single_party) send_count params.(ch_Qsingle) params.(ch_Qmulti)
  | Valid_sender_done => 
    "Hextok" ∷ receiver_exchange_token params.(ch_names) ∗  (* Sender will complete *)
    "HP" ∷ P params.(ch_is_single_party) recv_count v params.(ch_Psingle) params.(ch_Pmulti)  
  | Valid_closed => emp
  end.

Definition isUnbufferedChan (params: chan)
(v: params.(ch_T')) (vs: valid_chan_state) (send_count recv_count: nat) : iProp Σ := 
"%HUnBuffFacts" ∷ chan_state_facts vs send_count recv_count ∗
chan_state_resources params vs send_count recv_count v.

Definition isChanInner (params: chan) (buff: slice.t) : iProp Σ := 
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  ∃ (vs: valid_chan_state) (count: nat) (first: u64) (v: T') (send_count recv_count: nat),
    (* Physical state *)
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "v"] v ∗ 
    "first" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "first"] first ∗
    "count" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "count"] (W64 count) ∗ 
    "state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "state"] (valid_to_word vs) ∗ 
    
    (* Counter resources *)
    "HSndCtrAuth" ∷ own_send_counter_auth params.(ch_names) send_count (send_ctr_frozen vs) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth params.(ch_names) recv_count (recv_ctr_frozen vs send_count recv_count) ∗ 
    
    (* Close resources *)
    "HCloseTokPostClose" ∷ 
      (match vs with
        | Valid_closed => 
           ∃ (n: nat) (close_tok_names: gset gname), 
             own_closed_tok_post_close params.(ch_names) n close_tok_names ∗ 
             own_send_counter_frag params.(ch_names) n 1
        | _ => True
       end) ∗

    (* Buffer vs unbuffered channels *)
    "HChanState" ∷ 
      (if params.(ch_size) =? 0 then
        isUnbufferedChan params v vs send_count recv_count
      else
        isBufferedChan params vs send_count recv_count count buff first).

Definition isChan (params: chan) : iProp Σ := 
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  ∃ (mu_l: loc) (buff: slice.t),
    "#mu" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "lock"]□ mu_l ∗
    "#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "buffer"]□ buff ∗
    "%Hbuffsize" ∷ ⌜#buff.(slice.len_f) = #(W64 params.(ch_size))⌝ ∗
    "#Hlock" ∷ is_Mutex mu_l (isChanInner params buff).

Definition send_pre (params: chan) (i: nat) (v: params.(ch_T')) : iProp Σ :=
  "%HChNonnull" ∷ ⌜params.(ch_loc) ≠ null⌝ ∗
  "%Hsp" ∷ ⌜if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp⌝ ∗
  "HCh" ∷ isChan params ∗
  "HP" ∷ P params.(ch_is_single_party) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
  "HSc" ∷ own_send_counter_frag params.(ch_names) i params.(ch_q).

Definition send_post (params: chan) (i: nat) : iProp Σ :=
Q params.(ch_is_single_party) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
own_send_counter_frag params.(ch_names) (i + 1)%nat params.(ch_q).

Definition recv_pre (params: chan) (i: nat) : iProp Σ :=
  "%HChnonnull" ∷ ⌜params.(ch_loc) ≠ null⌝ ∗
  "%Hsp" ∷  ⌜if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp⌝ ∗
  "HCh" ∷ isChan params ∗
  "HQ" ∷ Q params.(ch_is_single_party) i params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
  "HRecvPerm" ∷ own_recv_perm params.(ch_names) params.(ch_q) i params.(ch_Ri).

Definition default_val (params: chan) : params.(ch_T') :=
@default_val params.(ch_T') params.(ch_T) _ params.(ch_IntoVal) params.(ch_IntoValTyped).

Definition recv_post (params: chan) (i: nat) (ok: bool) (v: params.(ch_T')) : iProp Σ :=
if ok then
  (P params.(ch_is_single_party) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
   own_recv_perm params.(ch_names) params.(ch_q) (i + 1) params.(ch_Ri))%I
else
  ("HRecFrag" ∷ own_recv_counter_frag params.(ch_names) i params.(ch_q) ∗ 
   "%Hvdef" ∷ ⌜v = default_val params⌝ ∗ 
   (∃ n, "HRi" ∷ params.(ch_Ri) n ∗ 
         "#Hsca" ∷ own_send_counter_auth params.(ch_names) n true ∗ 
         "#Hrca" ∷ own_recv_counter_auth params.(ch_names) n true))%I.

Lemma closed_unbuff_eq (params: chan) (send_count recv_count: nat) (v: params.(ch_T')):
  isUnbufferedChan params v Valid_closed send_count recv_count -∗ ⌜send_count = recv_count⌝.
Proof.
  iIntros "[%Heq _]". iPureIntro. exact Heq.
Qed.

Lemma chan_pointsto_non_null (lock: loc) (params: chan):
  params.(ch_loc) ↦s[channel.Channel.ty params.(ch_T) :: "lock"]□ lock -∗ ⌜ #params.(ch_loc) ≠ #null ⌝.
Proof.
  iIntros "Hb.a".
  iDestruct (typed_pointsto_not_null with "Hb.a") as %Hnotnull.
  { rewrite go_type_size_unseal. done. }
  iPureIntro. intro H. subst.
  rewrite struct.field_ref_f_unseal in Hnotnull.
  rewrite to_val_unseal in H. simpl in H. inversion H. replace (params.(ch_loc)) with null in *. 
  simpl in Hnotnull.
  contradiction.
Qed.

End proof.

