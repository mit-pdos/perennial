From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_inv chan_spec_select chan_spec_base chan_spec_send.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.


Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
   Context `{!goGlobalsGS Σ}.
Context `{!ghost_varG Σ (bool * val)}.
#[global] Program Instance : IsPkgInit channel := ltac2:(build_pkg_init ()).

Lemma wp_Channel__Send  (params: chan) (i: nat) (v: params.(ch_T')):
(* Could let bindings be implicit args? *)
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  params.(ch_loc) ≠ null ->
  (if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp) ->
  {{{ is_pkg_init channel ∗ send_pre params i v }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Send" #T #v 
  {{{ RET #();
      send_post params i
  }}}.
Proof. 
  intros HT' HT Hiv_inst Hivt_inst Hb_inst Hnn Hsp. wp_start. wp_auto.   
  let x := ident:(Φ) in
  try clear x.
 iNamed "Hpre". wp_if_destruct;first contradiction. wp_auto.
  wp_apply (wp_NewSendCase with "[HCh HP c HSc]"). 
  {
    iFrame. iPureIntro. done.
  }
  iIntros (case_ptr) "Hosc". wp_auto. wp_apply (wp_Select1 with "[Hosc]").
  {
    done.
  }
  {
    iFrame.
  }
  iIntros (selected_idx) "Hosc".
  wp_auto. 
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. 
    iApply "HΦ". iFrame.
    destruct bool_decide.
    {
      iDestruct "Hosc" as "[Ht Hf]".
      done.
    } unfold own_select_case_logical.
    iNamed "Hosc".
    iFrame.
    iNamed "Hosc". iFrame.
  }
  iApply "HΦ".
  unfold own_select_case.
  destruct bool_decide eqn: Hb.
  {
    rewrite bool_decide_eq_true in Hb.
    done.
  }
  iNamed "Hosc".
  iDestruct "Hb" as "%". done.
Qed.

Lemma wp_Channel__Receive (params: chan) (i: nat):
  (if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp) ->
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  {{{ is_pkg_init channel ∗ recv_pre params i }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Receive" #T #()
  {{{ (v: params.(ch_T')) (ok: bool), RET (#v, #ok);
      recv_post params i ok v
  }}}.
Proof.
  intros Hsp HT' HT Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto. iNamed "Hpre". wp_if_destruct;first contradiction. wp_auto. wp_apply (wp_NewRecvCase with "[HCh HQ c HRecvPerm]"). 
  {
    iFrame. iPureIntro. done.
  }
  iIntros (case_ptr) "Hosc". wp_auto. wp_apply (wp_Select1 with "[Hosc]"). all: try done.
  iIntros (selected_idx) "Hosc".
  wp_auto.
  iNamed "Hosc".
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. 
   iNamed "Hosc". 
   destruct bool_decide.
   {
    done.
   }
   iFrame.
   iNamed "Hosc".
 
   wp_auto. iApply "HΦ". iFrame.
  }
  iDestruct "Hb" as "%". done.
Qed.

Lemma wp_Channel__ReceiveDiscardOk (params: chan) (i: nat):
  (if params.(ch_is_single_party) then params.(ch_q) = 1%Qp else (params.(ch_q) < 1)%Qp) ->
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  {{{ is_pkg_init channel ∗ recv_pre params i }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "ReceiveDiscardOk" #T #()
  {{{ (v: params.(ch_T')) (ok: bool), RET #v;
      recv_post params i ok v
  }}}.
Proof.
  intros Hsp HT' HT Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto. iNamed "Hpre".
  wp_apply (wp_Channel__Receive with "[HRecvPerm HQ HCh c]").
  {
    done.
  }
  {
   iFrame. iPureIntro. done. 
  }
  iIntros (v ok) "Hrcvpost". wp_auto. iApply "HΦ". done.
Qed.

Lemma wp_NewChannelRef
 (t': Type)
  (t: go_type)
(iv: IntoVal t')
(ivt: IntoValTyped t' t)
(hb: BoundedTypeSize t)
(Psingle: Z -> t' -> iProp Σ)
(size: Z)

:
 0 ≤ size ->
  {{{ is_pkg_init channel }}}
    channel @ "NewChannelRef" #t #(W64 0)
  {{{ (ch_ref_ptr: loc), RET #ch_ref_ptr;
  ∃ (params:chan),
          "%Hsize" ∷ ⌜params.(ch_size) = 0 ⌝ ∗ 
          "%Hchptr" ∷ ⌜params.(ch_loc) = ch_ref_ptr⌝ ∗
          "%Hchq" ∷ ⌜params.(ch_q) = 1%Qp⌝  ∗
          "HCh" ∷ isChan params ∗ 
          "HSc" ∷ own_send_counter_frag params.(ch_names) 0%nat params.(ch_q) ∗ 
          "HRecvPerm" ∷ own_recv_perm params.(ch_names) params.(ch_q) 0 params.(ch_Ri)
  }}}.
Proof.
  intros Hsz.
   wp_start. wp_auto.
  rewrite -wp_fupd.
  wp_apply wp_slice_make2.
  iIntros (slice) "Hslice".
  wp_auto.
  wp_alloc mu as "Hl".
  wp_auto.
  rewrite /named.
  wp_alloc loc as "HCh".

  iDestruct (struct_fields_split with "HCh") as "HCh".
  iNamed "HCh". simpl.
  iDestruct own_chan_ghost_alloc as ">H".
  iNamed "H".
  iDestruct "H" as "(Hscauth & Hscf & Hrcauth & Hrperm & Hoct &Het)".
  pose my_params := make_unbuffered_params_simple_single_sync t' t iv ivt hb loc mu slice γ Psingle
  .
  iPersist "Hlock" as "#mu".
  iPersist "Hbuffer" as "#buff".
    

  iDestruct "Hslice" as "[Hsl1 Hsl2]".
  iDestruct (own_slice_len with "Hsl1") as "%Hlen".

  iMod (init_Mutex (isChanInner my_params) _ mu
         with "[$] [-HΦ Hscf Hrperm]") as "#Hlock".
         {
iModIntro.
  unfold isChan. iFrame.
  iFrame "#". 
  unfold isChan. iFrame.
  iFrame "#".
  unfold make_unbuffered_params_simple_single_sync in my_params.
  simpl in my_params.
    replace my_params.(ch_buff) with slice in Hlen by done.
  replace (my_params.(ch_size)) with 0 by set_solver.
  simpl. rewrite length_replicate in Hlen.
   replace (W64 0) with (slice .(slice.len_f)) by word.
   iExists Valid_start. iFrame. iExists 0%nat.
   replace (slice.(slice.len_f)) with (W64 0) by word.
   iFrame. unfold isUnbufferedChan.
   unfold chan_state_resources.
   unfold chan_state_facts. simpl. 
   iFrame.
   done.
  }

  wp_auto_lc 2.
  iModIntro.
  iApply "HΦ".
  replace mu with (my_params.(ch_mu)) by set_solver.
  replace slice with (my_params.(ch_buff)) by set_solver.
  iFrame "#".
  replace (my_params.(ch_size)) with 0 by set_solver.
  simpl. 
  rewrite length_replicate in Hlen.
    replace my_params.(ch_buff) with slice in Hlen by done.
   replace (W64 0) with (slice .(slice.len_f)) by word.
  iSplitL "".
  {
   done. 
  }
  iFrame.
  iPureIntro. 
   done.
Qed.

(* Len *)
Lemma wp_Channel__Len_params (params: chan):
  {{{ is_pkg_init channel ∗  isChan params }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Len" #params.(ch_T) #()
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

(* Cap *)
Lemma wp_Channel__Cap_params (params: chan):
  params.(ch_loc) ≠ null ->
  {{{ is_pkg_init channel ∗ isChan params }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Cap" #params.(ch_T) #()
  {{{ RET #(W64 params.(ch_size)); True%I }}}.
Proof.
  intros Hnn.
  wp_start. wp_auto. iNamed "Hpre".  wp_if_destruct.
  {
    done.
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


(* Close *)
Lemma wp_Channel__Close (params: chan) (n: nat) :
  #params.(ch_loc) ≠ #null ->
  {{{ is_pkg_init channel ∗ "HCh" ∷ isChan params ∗ "HCp" ∷ own_close_perm params.(ch_names) params.(ch_R) n }}}
    params.(ch_loc) @ channel @ "Channel'ptr" @ "Close" #params.(ch_T) #()
  {{{ RET #(); True }}}.
Proof.
  intros Hnotnull. wp_start. wp_auto.
  wp_if_destruct. 
  {
   replace params.(ch_loc) with null in Hnotnull. exfalso. apply Hnotnull.
   done. 
  }
  wp_auto.
  iNamed "Hpre".
  iAssert (∃ (done_b: bool),
  "done" ∷  done_ptr ↦ done_b ∗ 
  if done_b then True else 
 ("HCh" ∷  isChan params ∗ 
"HCp" ∷  own_close_perm params .(ch_names) params .(ch_R) n ∗ 
"c" ∷  c_ptr ↦ params .(ch_loc) )%I )%I
 with "[done HCh HCp c]" as "HI".
 {
  iExists false.
  iFrame.
 }
  wp_for. 
  iNamed "HI".
   wp_auto.
   destruct done_b.
   {
    destruct decide.
    {
      inversion e.
      inversion H0.
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
      
   iNamed "HCh".
    
   wp_auto.
  wp_apply (wp_Mutex__Lock with "[$Hlock]").
  iIntros "[Hlocked HisChanInner]". wp_auto.
  wp_apply ((wp_Channel__TryClose) with "[$HisChanInner $HCp]").
  {
   done. 
  } 
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
(params1 params2: chan) 
(dir1 dir2: select_dir)
(case1_ptr case2_ptr: loc)
(i1 i2: nat) 
(v1: params1.(ch_T')) (v2: params2.(ch_T'))
(blocking: bool):
let T1 := params1.(ch_T) in
let T2 := params2.(ch_T) in
let IntoVal_inst1 := params1.(ch_IntoVal) in
let IntoValTyped_inst1 := params1.(ch_IntoValTyped) in
let IntoVal_inst2 := params2.(ch_IntoVal) in
let IntoValTyped_inst2 := params2.(ch_IntoValTyped) in
{{{ is_pkg_init channel ∗
    own_select_case dir1 params1 case1_ptr false i1 #v1 ∗
    own_select_case dir2 params2 case2_ptr false i2 #v2
}}}
  channel @ "Select2" #T1 #T2 #case1_ptr #case2_ptr #blocking
{{{ (selected_idx: Z), RET #(W64 selected_idx);
    ⌜selected_idx ≤ 2⌝ ∗
    match selected_idx with 
    | 0 =>
      own_select_case dir1 params1 case1_ptr true i1 #v1 ∗
      own_select_case dir2 params2 case2_ptr false i2 #v2
    | 1 =>
      own_select_case dir1 params1 case1_ptr false i1 #v1 ∗
      own_select_case dir2 params2 case2_ptr true i2 #v2
    | _ => 
      ⌜blocking = false⌝ ∗
      own_select_case dir1 params1 case1_ptr false i1 #v1 ∗
      own_select_case dir2 params2 case2_ptr false i2 #v2
      end
}}}.
intros Ht1 Ht2 Hiv1 Hivt1 Hiv2 Hivt2.
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
wp_auto. 
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
iIntros "Hcases". wp_auto. 
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
 wp_auto. 
wp_apply   (wp_TrySelect with "[H2]"). all: try done.
iIntros (selected).
iIntros "Hcase2".
 wp_auto. 
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
wp_auto. 
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
iIntros "Hcases". wp_auto. 
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
 wp_auto. 
wp_apply   (wp_TrySelect with "[H2]"). all: try done.
iIntros (selected).
iIntros "Hcase2".
wp_auto. 
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
iIntros "Hcases". wp_auto. 
destruct selected.
{
  wp_auto. wp_for_post. iApply "HΦ". iFrame. done.
}
{
 wp_auto. 
wp_apply   (wp_TrySelect with "[H2]"). all: try done.
iIntros (selected).
iIntros "Hcase2".
wp_auto. 
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