From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_ghost_state chan_spec_inv chan_spec_select chan_spec_base chan_spec_send chan_spec_recv.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.  
Context  `{!chanGhostStateG Σ}.
Context `{!goGlobalsGS Σ}.

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

(*---------------------------------------------------------------------------
 User must unfold send_post, see chan_spec_inv for definition and descriptions
 of chan record components
 ---------------------------------------------------------------------------*)
Lemma wp_Channel__Send 
  (V: Type) {K: IntoVal V} {t: go_type}
  {H': IntoValTyped V t} {B: BoundedTypeSize t}
  (params: chan V) (i: nat) (q: Qp) (v: V):
  (if params.(ch_is_single_party) then q = 1%Qp else (q ≤ 1)%Qp) ->
  {{{ is_pkg_init channel ∗ send_pre V params q i v }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Send" #t #v 
  {{{ RET #(); send_post V params q i }}}.
Proof.
  intros Hsp.
  wp_start. wp_auto.
  let x := ident:(Φ) in try clear x.
  iNamed "Hpre". iNamed "HCh".
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  assert (params .(ch_loc) ≠ null).
  {
    intro H1.
    rewrite H1 in HNonNull. done.
  }
  wp_if_destruct; first contradiction.
  wp_auto.
  wp_apply (wp_NewSendCase with "[HP c HSc]"). all: try done.
  {
    rewrite -> bool_decide_true by done.
    iFrame. iFrame "#".
    done.
  }
  iIntros (case_ptr) "Hosc". wp_auto.
  wp_apply (wp_Select1 with "[Hosc]"). all: try done.
  {
   rewrite -> bool_decide_true by (apply n).
   iFrame.
  }
  iIntros (selected_idx) "Hosc". wp_auto.
  destruct selected_idx.
  {
    simpl. unfold own_select_case.
    iApply "HΦ". iFrame.
    destruct bool_decide.
    - iDestruct "Hosc" as "[Ht Hf]". done.
    - unfold own_select_case_logical. iNamed "Hosc". iFrame. iNamed "Hosc". iFrame.
  }
  iApply "HΦ". unfold own_select_case.
  destruct bool_decide eqn:Hb.
  - rewrite bool_decide_eq_true in Hb. done.
  - iNamed "Hosc". iDestruct "Hb" as "%". done.
Qed.

(*---------------------------------------------------------------------------
 User must unfold recv_post, see chan_spec_inv for definition and descriptions
 of chan record components
 ---------------------------------------------------------------------------*)
Lemma wp_Channel__Receive
  (V: Type) {K: IntoVal V} {t: go_type}
  {H': IntoValTyped V t} {B: BoundedTypeSize t}
  (params: chan V) (i: nat) (q: Qp) (Ri: nat -> iProp Σ):
  {{{ is_pkg_init channel ∗ recv_pre V params q i Ri }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Receive" #t #()
  {{{ (v: V) (ok: bool), RET (#v, #ok);
      recv_post V params q i ok v Ri }}}.
Proof.
  wp_start. wp_auto. iNamed "Hpre". iNamed "HCh".
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  assert (params .(ch_loc) ≠ null).
  {
    intro H1.
    rewrite H1 in HNonNull. done.
  }
  wp_if_destruct; first contradiction. wp_auto.
  wp_apply (wp_NewRecvCase with "[HQ c HRecvPerm]").
  { iFrame "#". iFrame. iPureIntro. done. }
  iIntros (case_ptr) "Hosc". wp_auto.
  wp_apply (wp_Select1 with "[Hosc]"). all: try done.
  iIntros (selected_idx) "Hosc". wp_auto.
  iNamed "Hosc".
  destruct selected_idx.
  {
    simpl. unfold own_select_case.
    iNamed "Hosc".
    destruct bool_decide; [done|].
    iFrame. iNamed "Hosc".
    wp_auto. iApply "HΦ". iFrame.
  }
  iDestruct "Hb" as "%". done.
Qed.

(*---------------------------------------------------------------------------
Use if we don't use the ok value in a select case
 ---------------------------------------------------------------------------*)
Lemma wp_Channel__ReceiveDiscardOk
  (V: Type) {K: IntoVal V} {t: go_type}
  {H': IntoValTyped V t} {B: BoundedTypeSize t}
  (params: chan V) (i: nat) (q: Qp) (Ri: nat -> iProp Σ):
  {{{ is_pkg_init channel ∗ recv_pre V params q i Ri }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "ReceiveDiscardOk" #t #()
  {{{ (v: V) (ok: bool), RET #v;
      recv_post V params q i ok v Ri }}}.
Proof.
  wp_start. wp_auto. iNamed "Hpre".
  wp_apply (wp_Channel__Receive with "[HRecvPerm HQ HCh c]").
  { iFrame. done. }
  iIntros (v ok) "Hrcvpost". wp_auto. iApply "HΦ". done.
Qed.

(*--------------------------------------------------------------------------
  This is the new specification that allows for choosing any of the available parameters. 
  It is likely to be rare that all of these will be necessary but other specifications 
  depend on this one. 
 ---------------------------------------------------------------------------*)
Lemma wp_NewChannelRef_base
  (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t}
  (size: Z)
  (is_single_party: bool)
  (Psingle: Z -> V -> iProp Σ)
  (Pmulti: V -> iProp Σ)
  (Qsingle: Z -> iProp Σ)
  (Qmulti: iProp Σ)
  (R: nat -> iProp Σ):
  0 ≤ size ->
  size + 1 < 2 ^ 63 ->
  {{{ is_pkg_init channel }}}
    channel @ "NewChannelRef" #t #(W64 size)
  {{{ (ch_ref_ptr ch_mu_loc: loc) (ch_buff_slice: slice.t) (ch_γ_names: chan_names) (params: chan V),
      RET #ch_ref_ptr;
        "Hparams" ∷ ⌜params = {| ch_t := t;
                                  ch_IntoVal := K;
                                  ch_IntoValTyped := H';
                                  ch_BoundedTypeSize := B;
                                  ch_loc := ch_ref_ptr;
                                  ch_mu := ch_mu_loc;
                                  ch_buff := ch_buff_slice;
                                  ch_γ := ch_γ_names;
                                  ch_size := size;
                                  ch_is_single_party := is_single_party;
                                  ch_Psingle := Psingle;
                                  ch_Pmulti := Pmulti;
                                  ch_Qsingle := Qsingle;
                                  ch_Qmulti := Qmulti;
                                  ch_R := R |}⌝ ∗
        "HCh" ∷ isChan V params ∗
        own_closed_tok_auth params.(ch_γ) R ∗
        "HSc" ∷ own_send_counter_frag params.(ch_γ) 0%nat 1 ∗
        "HRecvPerm" ∷ own_recv_perm params.(ch_γ) 1 0 R
  }}}.
Proof.
  intros Hsz0 Hszlim.
  wp_start. wp_auto.
  rewrite -wp_fupd.
  wp_apply ( @wp_slice_make2 _ _ _ _ _ _ V).
  iIntros (slice) "Hslice".
  wp_auto.
  wp_alloc mu as "Hmu".
  wp_auto.
  rewrite /named.
  wp_alloc loc as "HCh".
  iDestruct (struct_fields_split with "HCh") as "HCh".
  iNamed "HCh". simpl.
  iDestruct own_chan_ghost_alloc as ">Hghost".
  iNamed "Hghost".
  iDestruct "Hghost" as "(Hscauth & Hscf & Hrcauth & Hrperm & Hoct &Het)".

  (* Setup mutex and slice ownerships *)
  iPersist "Hlock" as "#mu".
  iPersist "Hbuffer" as "#buff".
  iDestruct "Hslice" as "[Hsl1 Hsl2]".
  iDestruct (own_slice_len with "Hsl1") as "%Hlen".

  assert (size = uint.nat slice.(slice.len_f)).
  { rewrite length_replicate in Hlen. rewrite <- Hlen. word. }

  iMod (init_Mutex (isChanInner V {|
    ch_t := t;
    ch_IntoVal := K;
    ch_IntoValTyped := H';
    ch_BoundedTypeSize := B;
    ch_loc := loc;
    ch_mu := mu;
    ch_buff := slice;
    ch_γ := γ;
    ch_size := size;
    ch_is_single_party := is_single_party;
    ch_Psingle := Psingle;
    ch_Pmulti := Pmulti;
    ch_Qsingle := Qsingle;
    ch_Qmulti := Qmulti;
    ch_R := R
  |}) _ mu with "[$] [-HΦ Hscf Hrperm Hoct]") as "#Hlock".
  {
    iModIntro. unfold isChan. iFrame. iExists Valid_start.
    iFrame "#". 
    destruct (size =? 0) eqn:Hb.
    - rewrite Hb. iFrame. iExists 0%nat. iFrame. done.
    - rewrite Hb. iFrame. iExists 0%nat. unfold isBufferedChanLogical. iFrame "Hcount".
      do 1 (iSplitL ""; first done). simpl. iFrame.
      rewrite length_replicate in Hlen. rewrite length_replicate.
      iFrame "%". iSplitL "";first word.
      iAssert (big_sep_seq 0 0 (λ i,Q V is_single_party
    (i - size - 1) Qsingle
    Qmulti)) as "Hnil".
    {
      iApply big_sep_seq_nil. done.
    }

    iDestruct (big_sepL_intro (λ i,(λ i,Q V  is_single_party
    (i - size) Qsingle
    Qmulti)) (seqZ 0 (size)%Z)) as "H".
    iAssert ([∗ list] x ∈ seqZ 0%nat (size), Q V is_single_party (x - size )
      Qsingle Qmulti)%I with "[H]" as "HQs".
    {
      iApply "H". iIntros (k x). iIntros "%Hseq".
      rewrite -> (lookup_seqZ 0 (size) k x) in Hseq.
      destruct Hseq as [Hs1 Hs2].  subst x.
       destruct k.
      { unfold Q. assert (0 ≤  size). { lia. }
        rewrite bool_decide_true. { done. } { lia. } }
        unfold Q. rewrite bool_decide_true.
        { done. }
      lia.
    }
    unfold big_sep_seq. 
    iFrame.
    replace (size - 0%nat) with size by lia.
    iFrame "HQs".
    simpl. 
   unfold valid_elems.
    
   iSplitL "". { iPureIntro. do 2 (split;first (try word;try done)).
    {
      inversion Hlen.
      rewrite H. 
      word.
    }
   }
    replace (uint.nat (W64 0)) with 0%nat by word.
    replace (uint.nat (W64 (Z.of_nat 0))) with 0%nat by word. simpl.
    done.
   }
  {
    wp_auto. iApply "HΦ". iFrame.
    iSplitL ""; first done.
    iFrame "#". simpl. iFrame. iPureIntro. rewrite H.
    split.
    { rewrite length_replicate in Hlen. rewrite <- H. inversion Hlen.
      replace (slice.(slice.len_f)) with (W64 size) by word. done. }
    word.
  }
Qed.

(*
  Used for a simple sync use case where an unbuffered channel is used as a notfication or 
  join handle. 
*)
Lemma wp_NewChannelRef_simple_unbuffered_sync
(V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t} 
(Psingle: Z -> V -> iProp Σ):
  {{{ is_pkg_init channel }}}
    channel @ "NewChannelRef" #t #(W64 0)
  {{{ (ch_ref_ptr: loc) (ch_mu_loc: loc) (ch_buff_slice: slice.t) (ch_γ_names: chan_names)  (params: chan V), RET #ch_ref_ptr;
          "%Hparams" ∷ ⌜params = {|
      ch_t := t;
      ch_IntoVal := K;
      ch_IntoValTyped := H';
      ch_BoundedTypeSize := B;
      ch_loc := ch_ref_ptr;
      ch_mu := ch_mu_loc;
      ch_buff := ch_buff_slice;
      ch_γ := ch_γ_names;
      ch_size := 0;
      ch_is_single_party := true;
      ch_Psingle := Psingle;  
      ch_Pmulti := λ _, True%I;    
      ch_Qsingle := λ _, True%I;   
      ch_Qmulti := True%I;         
      ch_R := λ _,False%I; (*No closing*)
    |}⌝ ∗
          "HCh" ∷ isChan V params ∗ 
          "HSc" ∷ own_send_counter_frag ch_γ_names 0%nat 1 ∗ 
          "HRecvPerm" ∷ own_recv_perm ch_γ_names 1 0 (λ _,False%I)
  }}}.
Proof.
  wp_start_folded as "Hs".
  wp_apply (((wp_NewChannelRef_base V 0 true Psingle (λ _, True%I) (λ _, True%I) (True%I) 
  (λ _, False%I)) )). all: try done.
  iIntros (ch_ref_ptr ch_mu_loc ch_buff_slice ch_γ_names params) "IH".
  iNamed "IH". iDestruct "IH" as "(Hoct & HSc & HRecvPerm)".
  iSpecialize ("HΦ" $! ch_ref_ptr ch_mu_loc ch_buff_slice ch_γ_names params). iApply "HΦ".
  iDestruct "Hparams" as "%Hparams".
  iFrame. subst. iFrame. iPureIntro. set_solver.
Qed.
  
Lemma wp_Channel__Len (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t}  (params: chan V) :
  {{{ is_pkg_init channel ∗  isChan V params }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Len" #t #()
  {{{ (n: nat), RET #(W64 n); ⌜ (0 ≤ n)%nat ⌝ }}}.
Proof.
  wp_start. wp_auto. iNamed "Hpre".  wp_if_destruct.
  {
   iSpecialize ("HΦ" $! 0%nat).
   iApply "HΦ". done. 
  }
  wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked HisChanInner]". wp_pures.
  iNamed "HisChanInner".
  wp_auto.
  wp_apply (wp_Mutex__Unlock with "[-chan_len HΦ]").
  - iFrame. iFrame "#". iModIntro. iFrame.
  - iApply "HΦ". iPureIntro. lia.
Qed.

Lemma wp_Channel__Cap (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t}  (params: chan V) :
  {{{ is_pkg_init channel ∗ isChan V params }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Cap" #t #()
  {{{ RET #(W64 params.(ch_size)); True%I }}}.
Proof.
  wp_start. wp_auto. iNamed "Hpre".
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  wp_if_destruct.
  {
    rewrite e in HNonNull. done.
  }
  {
    wp_auto.
    replace (params.(ch_buff).(slice.len_f)) with (W64 params.(ch_size)).
    {
       iApply "HΦ". done.
    }
    {
       apply (inj _) in Hbuffsize.
       done.
    }
  }
Qed.

Lemma wp_Channel__Close (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t}  (params: chan V)  (n: nat) :
  {{{ is_pkg_init channel ∗ "HCh" ∷ isChan V params ∗ "HCp" ∷ own_close_perm params.(ch_γ) params.(ch_R) n }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Close" #t #()
  {{{ RET #(); True }}}.
Proof.
   wp_start. wp_auto.
   iNamed "Hpre". iNamed "HCh".
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  assert (params .(ch_loc) ≠ null).
  {
    intro H1.
    rewrite H1 in HNonNull. done.
  }
  wp_if_destruct.
  {
    rewrite e in HNonNull. done.
  }
  wp_auto.
  iAssert (∃ (done_b: bool),
  "done" ∷  done_ptr ↦ done_b ∗ 
  if done_b then True else 
 ("HCh" ∷  isChan V params ∗ 
"HCp" ∷  own_close_perm params .(ch_γ) params .(ch_R) n ∗ 
"c" ∷  c_ptr ↦ params .(ch_loc) )%I )%I
 with "[done HCp c]" as "HI".
 {
  iExists false.
  iFrame. iFrame "#". iPureIntro. done.
 }
  wp_for. 
  iNamed "HI".
   wp_auto.
   destruct done_b.
   {
    destruct decide.
    {
      inversion e.
      inversion H1.
      assert (false = true) as Hcontra.
      { apply (to_val_inj _ _ e). }
      congruence. 
      
    }
    destruct decide.
    {
     wp_auto. iApply "HΦ". done. 
    }
    done.
   }
   
   destruct decide.
   {
    wp_auto.
    iNamed "HI".
   

    simpl.
   wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked HisChanInner]". wp_auto.
  wp_apply ((wp_Channel__TryClose) with "[$HisChanInner $HCp]").
  iIntros (selected) "IH". wp_auto.
  iNamed "IH". 
  destruct selected.
  {
  wp_apply (wp_Mutex__Unlock with "[$Hlocked IH $Hlock]").
  {
   iModIntro. 
   {
    iNamed "IH". unfold isChanInner. iFrame "value first count state".
    iFrame "HSndCtrAuth HRcvCtrAuth".
    iNamed "HCloseTokPostClose".
    iDestruct "HCloseTokPostClose" as "(Hoc & Hscf & Hcs)".
    iFrame.
   } 
  }
  {
    wp_for_post. iFrame.
  }
  }
  iDestruct "IH" as "[Hcp IH]".
  wp_apply (wp_Mutex__Unlock with "[$Hlocked  IH  $Hlock]").
  {
   iModIntro. 
   {
    iNamed "IH". unfold isChanInner.  iFrame "value first count state".
    iFrame "HSndCtrAuth HRcvCtrAuth".
    iNamed "HCloseTokPostClose".
    destruct vs. all: try (iFrame;done).
   }
  } 
   {
    wp_for_post. iFrame "HΦ". iFrame. iFrame "#".
    iSplitL "";first (iPureIntro;done).
    iFrame.
   }
  }
  {
    done.
  }
Qed.

Lemma wp_Select2
(V1: Type) {K1: IntoVal V1} {t1: go_type} {H'1: IntoValTyped V1 t1} {B1: BoundedTypeSize t1}  (params1: chan V1)
(V2: Type) {K2: IntoVal V2} {t2: go_type} {H'2: IntoValTyped V2 t2} {B2: BoundedTypeSize t2}  (params2: chan V2)
(dir1 dir2: select_dir)
(case1_ptr case2_ptr: loc)
(i1 i2: nat) 
(v1: V1) (v2: V2)
(q1 q2: Qp)
(Ri1 Ri2: nat-> iProp Σ)
(blocking: bool):
{{{ is_pkg_init channel ∗
    own_select_case V1 params1 dir1 case1_ptr false i1 q1 #v1 Ri1 ∗
    own_select_case V2 params2 dir2 case2_ptr false i2 q2 #v2 Ri2
}}}
  channel @ "Select2" #t1 #t2 #case1_ptr #case2_ptr #blocking
{{{ (selected_idx: Z), RET #(W64 selected_idx);
    ⌜selected_idx ≤ 2⌝ ∗
    match selected_idx with 
    | 0 =>
      own_select_case V1 params1 dir1 case1_ptr true i1 q1 #v1 Ri1 ∗
      own_select_case V2 params2 dir2 case2_ptr false i2 q2 #v2 Ri2
    | 1 =>
      own_select_case V1 params1 dir1 case1_ptr false i1 q1 #v1 Ri1 ∗
      own_select_case V2 params2 dir2 case2_ptr true i2 q2 #v2 Ri2
    | _ => 
      ⌜blocking = false⌝ ∗
      own_select_case V1 params1 dir1 case1_ptr false i1 q1 #v1 Ri1 ∗
      own_select_case V2 params2 dir2 case2_ptr false i2 q2 #v2 Ri2
      end
}}}.
wp_start. wp_auto. 
iNamed "Hpre". 
 wp_apply wp_alloc.
iIntros (case_2) "Hc2p".
wp_auto.
wp_apply wp_alloc.
iIntros (case_1) "Hc1p".
wp_auto.
wp_apply wp_RandomUint64.
iIntros (x) "Hx". wp_auto.
set ran := w64_word_instance .(word.modu) x (W64 2).
set ind := uint.nat ran.
assert (ind = uint.nat ran) by lia.
assert (ind = 0%nat ∨ ind = 1%nat).
{
  destruct ind.
  {
   left. done. 
  }
  destruct ind.
  {
   right. done. 
  }
  subst ran.
  word.
}
destruct ind eqn: Hin.
{
 assert (ran = (W64 0)) by word.
wp_apply   (wp_TrySelectCase2 with "[Hpre]"). all: try done.
{
 left. done. 
}
iIntros (selected) "Hcases". 
destruct selected.
{
  wp_auto. replace ran with (W64 0). simpl. iApply "HΦ".
  iFrame. done.
}
{
 wp_auto. wp_for.
    destruct decide.
    {
    iDestruct "Hcases" as "[H1 H2]".
wp_apply   (wp_TrySelect with "[H1]"). all: try done.
{
iIntros (selected). rewrite H1.
iIntros "Hcases".  
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
 wp_auto. 
wp_apply   (wp_TrySelect with "[H2]"). all: try done.
iIntros (selected).
iIntros "Hcase2".
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
  wp_auto.
  destruct blocking.
  {
    wp_auto. wp_for_post. iFrame. 
  }
  {
   wp_auto. wp_for_post. iFrame. 
   iApply "HΦ". iFrame. done.
  }
}
}
}
    }
{
    iDestruct "Hcases" as "[H1 H2]".
wp_apply   (wp_TrySelect with "[H1]"). all: try done.
}
}
}
{
  wp_apply   (wp_TrySelectCase2 with "[Hpre]"). all: try done.
{
  word.
}
iIntros (selected) "Hcases". 
destruct selected.
{
  wp_auto. 
   destruct n.
  {
  assert (ind = 1%nat) by lia.
  assert (ran = (W64 1)) by word.
  replace ran with (W64 1).
  iApply "HΦ". iFrame. done.
  }
  {
    replace ran with (W64 (S (S n))) by word.
   iApply "HΦ". lia. 
  }
}
{
 wp_auto. wp_for.
  destruct decide.
    {
    iDestruct "Hcases" as "[H1 H2]".
wp_apply   (wp_TrySelect with "[H1]"). all: try done.
{
iIntros (selected). rewrite e.
iIntros "Hcases". 
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
 wp_auto. 
wp_apply   (wp_TrySelect with "[H2]"). all: try done.
iIntros (selected).
iIntros "Hcase2".
destruct selected.
{
 wp_auto. wp_for_post. iApply "HΦ". iFrame. done. 
}
{
 wp_auto. 
  destruct blocking.
  {
    wp_auto. wp_for_post. iFrame. 
  }
  {
   wp_auto. wp_for_post. iFrame. 
   iApply "HΦ". iFrame. done.
  }

}

} 
}
    }
    {
      iDestruct "Hcases" as "[H1 H2]".
wp_apply   (wp_TrySelect with "[H1]"). all: try done.
{
iIntros (selected). 
iIntros "Hcases". 
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
 wp_auto. 
wp_apply   (wp_TrySelect with "[H2]"). all: try done.
iIntros (selected).
iIntros "Hcase2".
destruct selected.
{
 wp_auto. wp_for_post. iApply "HΦ". iFrame. done. 
}
{
 wp_auto. 
  destruct blocking.
  {
    wp_auto. wp_for_post. iFrame. 
  }
  {
   wp_auto. wp_for_post. iFrame. 
   iApply "HΦ". iFrame. done.
  }

}

} 
}
      
    }
}
}
Qed.

End proof.
