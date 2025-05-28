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



Record chan  (t': Type) := {
  ch_T: go_type;
  #[export]
  ch_IntoVal:: IntoVal t';
  #[export]
  ch_IntoValTyped:: IntoValTyped t' ch_T;
  #[export]
  ch_Hbounded:: BoundedTypeSize ch_T;
  ch_loc: loc;
  ch_mu: loc;
  ch_buff: slice.t;
  ch_γ: chan_names;
  ch_size: Z;
  ch_is_single_party: bool;
  ch_q: Qp;
  ch_Psingle: Z -> t' -> iProp Σ;
  ch_Pmulti: t' -> iProp Σ;
  ch_Qsingle: Z -> iProp Σ;
  ch_Qmulti: iProp Σ;
  ch_R: nat -> iProp Σ;
}.
  Arguments ch_T {t'}.
  Arguments ch_IntoVal {t'}.
Arguments ch_T {t'} .
Arguments ch_IntoVal {t'} .
Arguments ch_IntoValTyped {t'} .
Arguments ch_Hbounded {t'} .
Arguments ch_loc {t'} .
Arguments ch_mu {t'} .
Arguments ch_buff {t'} .
Arguments ch_γ {t'} .
Arguments ch_size {t'} .
Arguments ch_is_single_party {t'} .
Arguments ch_q {t'} .
Arguments ch_Psingle {t'} .
Arguments ch_Pmulti {t'} .
Arguments ch_Qsingle {t'} .
Arguments ch_Qmulti {t'} .



(* Args for a simple use of send for synchronization i.e. using Send to join a goroutine. 
 Enforces that a channel isn't closed using a always-False R predicate. 
 *)
Definition make_unbuffered_params_simple_single_sync
 (t': Type)
(t: go_type)
(iv: IntoVal t')
(ivt: IntoValTyped t' t)
(hb: BoundedTypeSize t)
(ch: loc)
(mu: loc)
(buff: slice.t)
(γ: chan_names)
(Psingle: Z -> t' -> iProp Σ)
: chan t' :=
{|
  ch_T := t;
  ch_IntoVal := iv;
  ch_IntoValTyped := ivt;
  ch_Hbounded := hb;
  ch_loc := ch;
  ch_mu := mu;
  ch_buff := buff;
  ch_γ := γ;
  ch_size := 0;
  ch_is_single_party := true;
  ch_q := 1%Qp;
  ch_Psingle := Psingle;  
  ch_Pmulti := λ _, True%I;    
  ch_Qsingle := λ _, True%I;   
  ch_Qmulti := True%I;         
  ch_R := λ _,False%I; (*No closing*)
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

Definition isBufferedChanLogical  {t': Type} 
 (params: chan t'  ) 
  (vs: valid_chan_state) (send_count recv_count: nat) (count: Z) 
  (first: u64) (xs: list t') : iProp Σ := 
  "%HCountMinus" ∷ ⌜count = (send_count - recv_count)⌝ ∗
  "%HSizeLen" ∷ ⌜ch_size params = length xs⌝ ∗
  "%HBuffSizeInv" ∷ buff_size_inv count first (length xs) ∗
  "HPs" ∷ ([∗ list] i↦x ∈ valid_elems xs first count, 
            P params.(ch_is_single_party)  (recv_count + i) x params.(ch_Psingle) params.(ch_Pmulti)) ∗ 
  "HQs" ∷ big_sep_seq send_count (params.(ch_size)- count) 
           (λ i, Q (ch_is_single_party  params) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti)).

Definition isBufferedChan (t': Type)  (params: chan t' ) 
  (vs: valid_chan_state) (send_count recv_count: nat) (count: Z) 
  (first: u64) : iProp Σ := 
  let intoVal := params.(ch_IntoVal) in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  ∃ (xs: list t'), 
    "HBuffSlice" ∷ own_slice 
                     params.(ch_buff) (DfracOwn 1) xs ∗
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

Definition chan_state_resources (t': Type) (params: chan t')
  (vs: valid_chan_state) (send_count recv_count: nat) (v: t') : iProp Σ :=
    let _ : IntoVal t' := params.(ch_IntoVal) in
  match vs with
  | Valid_start => 
      "Hextok" ∷ full_exchange_token params.(ch_γ)
  | Valid_receiver_ready => 
      "Hextok" ∷ receiver_exchange_token params.(ch_γ) ∗
      "HQ" ∷ Q params.(ch_is_single_party) recv_count params.(ch_Qsingle) params.(ch_Qmulti)
  | Valid_sender_ready => 
      "Hextok" ∷ sender_exchange_token params.(ch_γ) v ∗
      "HP" ∷ P params.(ch_is_single_party) send_count v params.(ch_Psingle) params.(ch_Pmulti)
  | Valid_receiver_done => 
      "Hextok" ∷ sender_exchange_token params.(ch_γ) v ∗
      "HQ" ∷ Q params.(ch_is_single_party) send_count params.(ch_Qsingle) params.(ch_Qmulti)
  | Valid_sender_done => 
      "Hextok" ∷ receiver_exchange_token params.(ch_γ) ∗
      "HP" ∷ P params.(ch_is_single_party) recv_count v params.(ch_Psingle) params.(ch_Pmulti)
  | Valid_closed => emp
  end.


Definition isUnbufferedChan (t': Type) (params: chan t')
(v: t') (vs: valid_chan_state) (send_count recv_count: nat) : iProp Σ := 
"%HUnBuffFacts" ∷ chan_state_facts vs send_count recv_count ∗
chan_state_resources t' params vs send_count recv_count v.

Definition isChanInner (t': Type) (params: chan t'): iProp Σ := 
  ∃ (vs: valid_chan_state) (count: nat) (first: u64) (v: t') (send_count recv_count: nat),
    (* Physical state *)
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty params.(ch_T)) :: "v"] v ∗ 
    "first" ∷ params.(ch_loc) ↦s[(channel.Channel.ty params.(ch_T)) :: "first"] first ∗
    "count" ∷ params.(ch_loc) ↦s[(channel.Channel.ty params.(ch_T)) :: "count"] (W64 count) ∗ 
    "state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty params.(ch_T)) :: "state"] (valid_to_word vs) ∗ 
    
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
        isUnbufferedChan t' params v vs send_count recv_count
      else
        isBufferedChan t' params vs send_count recv_count count first).

Definition isChanInnerClosed (params: chan t'): iProp Σ := 

  ∃ (count: nat) (first: u64) (v: t') (send_count recv_count: nat),
    (* Physical state *)
    "value" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "v"] v ∗ 
    "first" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "first"] first ∗
    "count" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "count"] (W64 count) ∗ 
    "state" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "state"] (valid_to_word Valid_closed) ∗ 
    
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
        isUnbufferedChan params v Valid_closed send_count recv_count
      else
        isBufferedChan params Valid_closed send_count recv_count count first).

Definition isChan (params: chan t') : iProp Σ := 
    "#mu" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "lock"]□ params.(ch_mu) ∗
    "#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty T) :: "buffer"]□ params.(ch_buff) ∗
    "%Hbuffsize" ∷ ⌜#params.(ch_buff).(slice.len_f) = #(W64 params.(ch_size))⌝ ∗
    "%Hbuffsize" ∷ ⌜0 ≤  params.(ch_size)⌝ ∗
    "%Hbuffsize" ∷ ⌜params.(ch_size) + 1 < 2 ^ 63⌝ ∗
    "#Hlock" ∷ is_Mutex params.(ch_mu) (isChanInner params).

Definition send_pre (params: chan t') (i: nat) (v: t') : iProp Σ :=
  "%HChNonnull" ∷ ⌜params.(ch_loc) ≠ null⌝ ∗
  "%Hsp" ∷ ⌜if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp⌝ ∗
  "HCh" ∷ isChan params ∗
  "HP" ∷ P params.(ch_is_single_party) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
  "HSc" ∷ own_send_counter_frag params.(ch_γ) i params.(ch_q).

Definition send_pre_inner (params: chan t') (i: nat) (v: t') : iProp Σ :=
  "%HChNonnull" ∷ ⌜params.(ch_loc) ≠ null⌝ ∗
  "%Hsp" ∷ ⌜if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp⌝ ∗
  "HCh" ∷ isChanInner params ∗
  "%Hbuffsize" ∷ ⌜params.(ch_buff).(slice.len_f) = (W64 params.(ch_size))⌝ ∗
    "#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty params.(ch_T)) :: "buffer"]□ params.(ch_buff) ∗
  "HP" ∷ P params.(ch_is_single_party) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
  "HSc" ∷ own_send_counter_frag params.(ch_γ) i params.(ch_q).

Definition send_post (params: chan t') (i: nat) : iProp Σ :=
Q params.(ch_is_single_party) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
own_send_counter_frag params.(ch_γ) (i + 1)%nat params.(ch_q).


Definition send_post_inner(params: chan t') (i: nat) : iProp Σ :=
  "HCh" ∷ isChanInner params ∗
Q params.(ch_is_single_party) (i - params.(ch_size)) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
own_send_counter_frag params.(ch_γ) (i + 1)%nat params.(ch_q).

Definition recv_pre (params: chan t') (i: nat) (Ri: nat -> iProp Σ) : iProp Σ :=
  "%HChnonnull" ∷ ⌜params.(ch_loc) ≠ null⌝ ∗
  "%Hsp" ∷  ⌜if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp⌝ ∗
  "HCh" ∷ isChan params ∗
  "HQ" ∷ Q params.(ch_is_single_party) i params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
  "HRecvPerm" ∷ own_recv_perm params.(ch_γ) params.(ch_q) i Ri.

Definition default_val (params: chan t') : t' :=
@default_val t' params.(ch_T) _ params.(ch_IntoVal) params.(ch_IntoValTyped).

Definition recv_post (params: chan t') (i: nat) (ok: bool) (v: t') (Ri: nat -> iProp Σ) : iProp Σ :=
if ok then
  (P params.(ch_is_single_party) i v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
   own_recv_perm params.(ch_γ) params.(ch_q) (i + 1) Ri)%I
else
  ("HRecFrag" ∷ own_recv_counter_frag params.(ch_γ) i params.(ch_q) ∗ 
   "%Hvdef" ∷ ⌜v = default_val params⌝ ∗ 
   (∃ n, "HRi" ∷ Ri n ∗ 
         "#Hsca" ∷ own_send_counter_auth params.(ch_γ) n true ∗ 
         "#Hrca" ∷ own_recv_counter_auth params.(ch_γ) n true))%I.

Definition recv_pre_inner (params: chan t') (i: nat) (Ri: nat -> iProp Σ) : iProp Σ :=
"%HChnonnull" ∷ ⌜params.(ch_loc) ≠ null⌝ ∗
"%Hsp" ∷ ⌜if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp⌝ ∗
"HCh" ∷ isChanInner params ∗
"%Hbuffsize" ∷ ⌜params.(ch_buff).(slice.len_f) = W64 params.(ch_size)⌝ ∗
"#buffer" ∷ params.(ch_loc) ↦s[(channel.Channel.ty params.(ch_T)) :: "buffer"]□ params.(ch_buff) ∗
"HQ" ∷ Q params.(ch_is_single_party) (Z.of_nat i) params.(ch_Qsingle) params.(ch_Qmulti) ∗ 
"HRecvPerm" ∷ own_recv_perm params.(ch_γ) params.(ch_q) i Ri.
       
Definition recv_post_inner (params: chan t') (i: nat) (ok: bool) (v: t') (Ri: nat -> iProp Σ) : iProp Σ :=
  "HCh" ∷ isChanInner params ∗
  if ok then
    (P params.(ch_is_single_party) (Z.of_nat i) v params.(ch_Psingle) params.(ch_Pmulti) ∗ 
    own_recv_perm params.(ch_γ) params.(ch_q) (i + 1) Ri)%I
  else
    ("HRecFrag" ∷ own_recv_counter_frag params.(ch_γ) i params.(ch_q) ∗ 
    "%Hvdef" ∷ ⌜v = default_val params⌝ ∗ 
    (∃ n, "HRi" ∷ Ri n ∗ 
          "#Hsca" ∷ own_send_counter_auth params.(ch_γ ) n true ∗ 
          "#Hrca" ∷ own_recv_counter_auth params.(ch_γ) n true))%I.

Lemma closed_unbuff_eq (params: chan t') (send_count recv_count: nat) (v: t'):
  isUnbufferedChan params v Valid_closed send_count recv_count -∗ ⌜send_count = recv_count⌝.
Proof.
  iIntros "[%Heq _]". iPureIntro. exact Heq.
Qed.

Lemma chan_pointsto_non_null (lock: loc) (params: chan t'):
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

