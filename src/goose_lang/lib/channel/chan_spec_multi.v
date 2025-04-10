From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Export auth excl frac numbers.
From iris.base_logic.lib Require Export invariants.

From Perennial.goose_lang Require Import prelude. 
From Perennial.program_proof.rsm Require Import big_sep.
From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode wpc_proofmode array.
From Perennial.goose_lang.lib Require Import typed_mem.
From Perennial.goose_lang Require Export into_val.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Export
      persistent_readonly slice slice.typed_slice struct loop lock control map.typed_map time proph rand string.

From Perennial.goose_lang.lib.channel Require Import auth_set.
From Goose.github_com.goose_lang.goose Require Import channel.

Record chan_names :=
 {
    sender_name: gname;
    receiver_name: gname;
    close_name: gname;
    close_tok_names_name: gname;
 }.

Class closePropTrackerG Σ := ClosePropTrackerG {
    sender_main_saved_propG :: savedPropG Σ;
    close_prop_auth_setG :: auth_setG Σ gname;
  }.

Definition closePropTrackerΣ: gFunctors :=
  #[ savedPropΣ; auth_setΣ gname ].

#[global] Instance subG_closePropTrackerG Σ : subG closePropTrackerΣ Σ → closePropTrackerG Σ.
Proof. solve_inG. Qed.

Definition in_closed_state (state: nat): bool :=
 bool_decide (state = 5). 

Inductive chanState: Type := 
| start
| receiver_ready
| sender_ready
| receiver_done 
| sender_done
| closed
.

Definition nat_to_state (state: nat) : chanState :=
 match state with 
 | 0 => start
 | 1 => receiver_ready
 | 2 => sender_ready
 | 3 => receiver_done
 | 4 => sender_done
 | 5 => closed
 | _ => start
 end
.

Section proof.
 Context `{hG: heapGS Σ, !ffi_semantics _ _, !ext_types _}. 
 Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.

Implicit Types (v:val). 

Definition own_chan_counter_frag (γ : gname)
 (n : nat) (q : Qp) : iProp Σ :=
   own γ (◯ Some (q, n)).

Definition own_chan_counter_auth (γ : gname) 
   (n : nat) (frozen : bool) : iProp Σ :=
     own γ (●{if frozen then DfracDiscarded else (DfracOwn 1)} Some (1%Qp, n)).

Definition own_send_counter_frag (γ: chan_names) (n: nat) (q: Qp) : iProp Σ :=
    own_chan_counter_frag γ.(sender_name) n q.

Definition own_send_counter_auth (γ : chan_names) 
   (n : nat)  (frozen : bool) : iProp Σ :=
   own_chan_counter_auth γ.(sender_name) n frozen.

Definition own_recv_counter_frag (γ: chan_names) (n: nat) (q: Qp) : iProp Σ :=
   own_chan_counter_frag γ.(receiver_name) n q.

Definition own_recv_counter_auth (γ : chan_names) 
  (n : nat) (frozen : bool) : iProp Σ :=
  own_chan_counter_auth γ.(receiver_name) n frozen.

Lemma own_chan_counter_split (γ : gname) (n m : nat) (p q : Qp) :
  own_chan_counter_frag γ (n + m) (p + q) ⊣⊢ own_chan_counter_frag γ n p ∗ own_chan_counter_frag γ m q.
Proof.
 setoid_rewrite <-own_op.
  iSplit.
  { iIntros "H". done. }
  { iIntros "H". done. }
Qed.

Lemma own_send_counter_split (γ : chan_names) (n m : nat) (p q : Qp) :
  own_send_counter_frag γ (n + m) (p + q) ⊣⊢ own_send_counter_frag γ n p ∗ own_send_counter_frag γ m q.
Proof.
  unfold own_send_counter_frag. apply own_chan_counter_split.
Qed.

Lemma own_recv_counter_split (γ : chan_names) (n m : nat) (p q : Qp) :
  own_recv_counter_frag γ (n + m) (p + q) ⊣⊢ own_recv_counter_frag γ n p ∗ own_recv_counter_frag γ m q.
Proof.
  unfold own_recv_counter_frag. apply own_chan_counter_split.
Qed.

Definition own_closed_tok_frag (γ: chan_names) (γi: gname) (R: iProp Σ): iProp Σ :=
    auth_set_frag γ.(close_name) γi ∗ saved_prop_own γi (DfracDiscarded) R.

Definition own_closed_tok_auth (γ: chan_names) (R: iProp Σ): iProp Σ :=
  ∃ (close_tok_names: gset gname),
    auth_set_auth γ.(close_name) close_tok_names ∗ 
    (▷R -∗ ([∗ set] γi ∈ close_tok_names,
                        ∃ Ri, saved_prop_own γi DfracDiscarded Ri ∗  ▷ Ri))                     
    .

Definition own_closed_tok_post_close (γ: chan_names): iProp Σ := 
∃ (close_tok_names: gset gname),
auth_set_auth γ.(close_name) close_tok_names ∗ 
([∗ set] γi ∈ close_tok_names,
                    ∃ Ri, saved_prop_own γi DfracDiscarded Ri ∗  ▷ Ri)                  
.

Definition own_recv_perm (γ: chan_names) (q: Qp) (i: nat) (T: iProp Σ): iProp Σ :=
 ∃ (γi: gname),
  own_recv_counter_frag γ i q ∗ own_closed_tok_frag γ γi T .

Definition own_close_perm (γ: chan_names) (R: iProp Σ) (n: nat): iProp Σ :=
  R ∗ own_send_counter_frag γ n 1 ∗ own_closed_tok_auth γ R.

Definition P (q: Qp) (i: nat)
 (v: val) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)): iProp Σ :=
 if bool_decide(q = 1%Qp) then Psingle i v  else Pmulti v.

Definition Q (q: Qp) (z: Z) (Qsingle: (Z -> iProp Σ)) (Qmulti: iProp Σ): iProp Σ := 
if bool_decide(Z.lt z 0%Z) then True%I else (if bool_decide(q = 1%Qp) then Qsingle(z) else Qmulti).


Lemma own_closed_tok_frag_split (γ : chan_names) (γi: gname) (T U : iProp Σ):
    ∀ R,
    (own_closed_tok_auth γ R ∗  own_closed_tok_frag γ γi (T ∗ U) ==∗ 
    ∃ (γj γk: gname), own_closed_tok_auth γ R ∗ own_closed_tok_frag γ γj T 
    ∗ own_closed_tok_frag γ γk U
    ).
Proof.
Admitted.

Lemma own_recv_perm_split (γ : chan_names) (r s : Qp) (i k: nat) (T U: iProp Σ) : 
∀ R,
own_closed_tok_auth γ R ∗ own_recv_perm γ (r + s) (i + k) (T ∗ U) ==∗   
own_closed_tok_auth γ R ∗ own_recv_perm γ r i T ∗ own_recv_perm γ s k U.
Proof.
Admitted.

Definition isUnbufferedChan (γ: chan_names) (chan_type: ty) 
  (v: val) (state: nat) (is_single_party: bool) (send_count: nat) (recv_count: nat) (q: Qp) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ): iProp Σ := 
    "HStateChanOwns" ∷ 
     match nat_to_state(state) with 
      | start => (⌜send_count = recv_count⌝)
      | receiver_ready => ⌜send_count = recv_count⌝  ∗ Q q recv_count Qsingle Qmulti
      | sender_ready => ⌜send_count = recv_count ∧ val_ty v chan_type⌝ ∗ P q send_count v Psingle Pmulti 
      | receiver_done => ⌜recv_count = (send_count + 1)%nat⌝ ∗ Q q recv_count Qsingle Qmulti 
      | sender_done => ⌜send_count = (recv_count + 1)%nat ∧ val_ty v chan_type⌝ ∗ P q send_count v Psingle Pmulti 
      | closed => ⌜send_count = recv_count⌝  
     end
  .

  Definition isBufferedChan (γ: chan_names) (chan_type: ty) (size: nat) (state: nat) (is_single_party: bool) (send_count: nat) (recv_count: nat) (count: nat) 
  (buff: Slice.t) (q: Qp) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ): iProp Σ := 
    ∃ (xs: list val), 
    "%HBuffCount" ∷ ⌜count = (send_count - recv_count)%nat⌝ ∗
    "HBuffSlice" ∷ slice.own_slice_small buff chan_type (DfracOwn 1) xs ∗ 
    "%Hcap" ∷ ⌜size = length xs⌝ ∗ 
    "HPs" ∷ [∗ list] i↦x ∈ xs, (P q (recv_count + i) (nth (recv_count + i) xs (zero_val chan_type)) Psingle Pmulti) ∗ 
    "HQs" ∷ [∗ list] (i: nat) ∈ (seq 0 (size - send_count + recv_count)), (Q q (recv_count - i + size) Qsingle Qmulti) 
  .


  Definition counters_frozen (state: nat) (send_count: nat) (rec_count: nat): bool :=
  (in_closed_state state) && bool_decide(send_count = rec_count).

  Definition isChanInner (ch: loc) (γ: chan_names) (chan_type: ty) 
    (size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ)  : iProp Σ := 
    ∃ (state: nat) (buff: Slice.t) (count: nat) (first: nat) (v: val) (send_count: nat) (recv_count: nat) (p: dfrac)
     (q: Qp),
    "state" ∷ ch ↦[(Channel chan_type) :: "state"] #(W64 state) ∗
    "value" ∷ ch ↦[(Channel chan_type) :: "v"] v ∗ 
    "count" ∷ ch ↦[(Channel chan_type) :: "count"] #(W64 count) ∗ 
    "first" ∷ ch ↦[(Channel chan_type) :: "first"] #(W64 first) ∗ 
    "#buff" ∷ ch ↦[(Channel chan_type) :: "buff"]□ (slice_val buff) ∗
    "HSndCtrAuth" ∷ own_send_counter_auth γ send_count (counters_frozen state send_count recv_count) ∗ 
    "HRcvCtrAuth" ∷ own_recv_counter_auth γ recv_count (counters_frozen state send_count recv_count) ∗ 
    "HCloseTokPostClose" ∷ if (in_closed_state state) then own_closed_tok_post_close γ
    else True  ∗ 
    "%HCounterOwn" ∷ ⌜if is_single_party then q = 1%Qp else (q < 1)%Qp⌝ ∗ 
    "HBuffUnbuff" ∷ 
    if bool_decide(size = 0) then  
      isUnbufferedChan γ chan_type v state is_single_party send_count recv_count q Psingle Pmulti
      Qsingle Qmulti R 
    else 
      isBufferedChan γ chan_type size state is_single_party send_count recv_count count
      buff q Psingle Pmulti Qsingle Qmulti R
  .


Definition isChan (ch: loc) (γ: chan_names) (chan_type: ty) 
  (size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) : iProp Σ := 
    ∃ (mu_l: loc) ,
    "#mu" ∷ ch ↦[(Channel chan_type) :: "lock"]□ #mu_l
     ∗ 
    "#Hlock" ∷ is_lock (nroot .@ "Channel") (#mu_l) (isChanInner ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R)
.

Lemma wp_Channel__New (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
{{{ True }}}
     NewChannel chan_type #()
   {{{(ch: loc) (γ: chan_names), RET #ch; 
    isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗ 
    own_recv_perm γ 1%Qp 0 R ∗
    own_closed_tok_auth γ R ∗ 
    own_send_counter_frag γ 0 1%Qp
}}}.
Admitted.

Lemma wp_Channel__Send (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
val_ty v chan_type -> 
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  P q i v Psingle Pmulti ∗ own_send_counter_frag γ i q
}}}
     Channel__Send chan_type #ch v
{{{ RET #(); 
  Q q (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q
}}}.
Admitted.

Lemma wp_Channel__TrySend (ch: loc) (i: nat) (v: val) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
val_ty v chan_type -> 
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
{{{ isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  P q i v Psingle Pmulti ∗ own_send_counter_frag γ i q
}}}
     Channel__TrySend chan_type #ch v
{{{ (selected: bool), RET #selected; 
  if selected then 
    (Q q (i - size) Qsingle Qmulti ∗ own_send_counter_frag γ (i + 1)%nat q)
  else 
    ( P q i v Psingle Pmulti ∗ own_send_counter_frag γ i q) 
}}}.
Admitted.

Lemma wp_Channel__Receive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri: iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q q i Qsingle Qmulti ∗ 
  own_recv_perm γ q i Ri 
}}}
     Channel__Receive chan_type #ch
{{{ (v: val) (ok: bool), RET (v,#ok); 
  (P q i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝)
    ∨  
  (Ri ∗ own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
    ∗ ∃ n, own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
}}}.
Admitted.

Lemma wp_Channel__ReceiveDiscardOk (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri: iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q q i Qsingle Qmulti ∗ 
  own_recv_perm γ q i Ri 
}}}
     Channel__ReceiveDiscardOk chan_type #ch
{{{ (v: val), RET (v); 
  (P q i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜val_ty v chan_type⌝)
    ∨  
  (Ri ∗ own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝
    ∗ ∃ n, own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
}}}.
Admitted.

Lemma wp_Channel__TryReceive (ch: loc) (i: nat) (q: Qp) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
(if is_single_party then q = 1%Qp else (q < 1)%Qp) ->
∃ (Ri: iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  Q q i Qsingle Qmulti ∗ own_recv_perm γ q i Ri 
}}}
     Channel__TryReceive chan_type #ch
{{{ (v: val) (ok: bool) (selected: bool), RET (#selected,v,#ok); 
  if selected then 
    ((P q i v Psingle Pmulti ∗ own_recv_perm γ q (i + 1) Ri ∗ ⌜ok⌝ ∗ ⌜val_ty v chan_type⌝)
    ∨  
    (Ri ∗ own_recv_counter_frag γ i q ∗ ⌜v = (zero_val chan_type)⌝ ∗ ⌜ok = false⌝
      ∗ ∃ n, own_send_counter_auth γ n true ∗ own_recv_counter_auth γ n true)
    )
  else 
    ( Q q i Qsingle Qmulti ∗ own_recv_perm γ q i Ri)
}}}.
Admitted.

Lemma wp_Channel__Close (ch: loc) (n: nat) (γ: chan_names) (chan_type: ty) 
(size: nat) (is_single_party: bool) (Psingle: (nat -> val -> iProp Σ)) (Pmulti: (val -> iProp Σ)) (Qsingle: (Z -> iProp Σ)) (Qmulti R: iProp Σ) :
∃ (Ri: iProp Σ),
{{{ 
  isChan ch γ chan_type size is_single_party Psingle Pmulti Qsingle Qmulti R ∗
  own_close_perm γ R n
}}}
     Channel__Close chan_type #ch
{{{ RET #(); True }}}.
Admitted.

End proof.
