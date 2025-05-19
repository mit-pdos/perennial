From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_inv chan_spec_select chan_spec_base.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.


Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
   Context `{!goGlobalsGS Σ}.
Context `{!ghost_varG Σ (bool * val)}.
#[global] Program Instance : IsPkgInit channel := ltac2:(build_pkg_init ()).

Lemma wp_Channel__Send (params: chan) (i: nat) (v: params.(ch_T')):
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
Admitted.

Lemma wp_NewSendCase
  (params: chan) (i: nat) (v: params.(ch_T')):
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  {{{ is_pkg_init channel ∗ send_pre params i v }}}
    channel @ "NewSendCase" #T #params.(ch_loc) #v
  {{{ (case_ptr: loc), RET #case_ptr;
      own_select_case SelectSend params case_ptr false i (to_val v)
  }}}.
Proof.
  intros HT' HT Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto.   iNamed "Hpre".
  wp_apply wp_alloc. iIntros (ptr) "Hptr". 
  iApply struct_fields_split in "Hptr"; iNamed "Hptr". wp_auto. iApply "HΦ".
  iNamed "HCh".
  unfold own_select_case. simpl.
  destruct bool_decide.
  {
   done.
  }
  iFrame.  
  iFrame.  simpl. iFrame "#". iPureIntro. done.
Qed.

Lemma wp_NewRecvCase
  (params: chan) (i: nat):
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  {{{ is_pkg_init channel ∗ recv_pre params i }}}
    channel @ "NewRecvCase" #T #params.(ch_loc)
  {{{ (case_ptr: loc), RET #case_ptr;
      own_select_case SelectRecv params case_ptr false i (to_val (default_val T'))
  }}}.
Proof.
  intros HT' HT Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto. iNamed "Hpre".
  wp_apply wp_alloc. iIntros (ptr) "Hptr".
  iApply struct_fields_split in "Hptr"; iNamed "Hptr". wp_auto. iApply "HΦ".
  iNamed "HCh".
  unfold own_select_case. simpl.
  destruct bool_decide.
  {
    done.
  }
  iFrame.
  simpl. iFrame "#". iPureIntro. done.
Qed.

Lemma wp_Select1
    (params1: chan)
    (dir1: select_dir)
    (case1 : loc)
    (i1: nat) (v1: val)
    (blocking : bool) :
    {{{ is_pkg_init channel ∗ own_select_case dir1 params1 case1 false i1 v1 }}}
      channel @ "Select1" #params1.(ch_T) #case1 #blocking
    {{{ (selected_idx : nat), RET #(W64 selected_idx);
        own_selected_case_params1 dir1 params1 blocking selected_idx case1 v1 i1 }}}.
  Proof. 
    wp_start. wp_auto.
Admitted.

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
  iIntros (case_ptr) "Hosc". wp_auto. wp_apply (wp_Select1 with "[Hosc]").
  {
   iFrame. 
  }
  iIntros (selected_idx) "Hosc".
  wp_auto. unfold own_selected_case_params1. iNamed "Hosc".
  unfold own_selected_case_multi.
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. unfold nil_select_case. simpl.
   iNamed "Hosc". 
   destruct bool_decide.
   {
    done.
   }
   iFrame.
 
   iNamed "Hselcase".
   wp_auto. iApply "HΦ". iFrame.
  }
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. unfold nil_select_case. simpl.
   iNamed "Hosc". iFrame. done.
  }
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. unfold nil_select_case. simpl.
   iNamed "Hosc". iFrame. done.
  }
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. unfold nil_select_case. simpl.
   iNamed "Hosc". iFrame. done.
  }
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. unfold nil_select_case. simpl.
   iNamed "Hosc". iFrame. done.
  }
  destruct selected_idx.
  {
   simpl. 
   unfold own_select_case. unfold nil_select_case. simpl.
   iNamed "Hosc". iFrame. iDestruct "Hosc" as "[%Hosc %Hcontra]". done.  
  }
  simpl. destruct bool_decide eqn: Hc.
  {
    rewrite bool_decide_eq_true in Hc. lia.
  }
   iNamed "Hosc". iFrame. iDestruct "Hosc" as "[%Hosc %Hcontra]". done.  
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
  (params: chan):
  let T' := params.(ch_T') in
  let T := params.(ch_T) in
  let IntoVal_inst := params.(ch_IntoVal) in
  let IntoValTyped_inst := params.(ch_IntoValTyped) in
  let Hbounded := params.(ch_Hbounded) in
  {{{ is_pkg_init channel }}}
    channel @ "NewChannelRef" #T #(W64 params.(ch_size))
  {{{ (ch_ref_ptr: loc), RET #ch_ref_ptr;
      ∃ 
         (γ: chan_names),
          "%Hchptr" ∷ ⌜params.(ch_loc) = ch_ref_ptr⌝ ∗
          "%Hchq" ∷ ⌜params.(ch_q) = 1%Qp⌝  ∗
          "HCh" ∷ isChan params ∗ 
          "HSc" ∷ own_send_counter_frag params.(ch_names) 0%nat params.(ch_q) ∗ 
          "HRecvPerm" ∷ own_recv_perm params.(ch_names) params.(ch_q) 0 params.(ch_Ri)
  }}}.
Proof.
  intros HT' HT Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto.
Admitted.

Lemma wp_Select2
    (dir1 dir2: select_dir)
    (params1 params2: chan )
    (case1 case2 : loc)
    (blocking : bool) 
  (v1 v2: val) 
  (i1 i2: nat) : 

    {{{ is_pkg_init channel ∗ own_select_case dir1 params1 case1 false i1 v1 ∗ own_select_case dir2 params2 case2 false i2 v2 }}}
      channel @ "Select2" #params1.(ch_T) #params2.(ch_T) #case1 #case2 #blocking
    {{{ (i : nat), RET #(W64 i);
        own_selected_case_params2 dir1 dir2 params1 params2 blocking i case1 case2 v1 v2 i1 i2 }}}.
    Proof.
      wp_start. wp_auto.
Admitted.

Lemma wp_Select3
  (dir1 dir2 dir3: select_dir)
  (params1 params2 params3: chan)
  (case1 case2 case3: loc)
  (blocking: bool)
  (v1 v2 v3: val)
  (i1 i2 i3: nat) :
  {{{ is_pkg_init channel ∗
      own_select_case dir1 params1 case1 false i1 v1 ∗
      own_select_case dir2 params2 case2 false i2 v2 ∗
      own_select_case dir3 params3 case3 false i3 v3 }}}
    channel @ "Select3" #params1.(ch_T) #params2.(ch_T) #params3.(ch_T)
                         #case1 #case2 #case3 #blocking
  {{{ (i : nat), RET #(W64 i);
      own_selected_case_params3 dir1 dir2 dir3 params1 params2 params3 blocking i
                                case1 case2 case3 v1 v2 v3 i1 i2 i3 }}}.
Proof.
  wp_start. wp_auto.
Admitted.

Lemma wp_Select4
  (dir1 dir2 dir3 dir4: select_dir)
  (params1 params2 params3 params4: chan)
  (case1 case2 case3 case4: loc)
  (blocking: bool)
  (v1 v2 v3 v4: val)
  (i1 i2 i3 i4: nat) :
  {{{ is_pkg_init channel ∗
      own_select_case dir1 params1 case1 false i1 v1 ∗
      own_select_case dir2 params2 case2 false i2 v2 ∗
      own_select_case dir3 params3 case3 false i3 v3 ∗
      own_select_case dir4 params4 case4 false i4 v4 }}}
    channel @ "Select4" #params1.(ch_T) #params2.(ch_T) #params3.(ch_T) #params4.(ch_T)
                         #case1 #case2 #case3 #case4 #blocking
  {{{ (i : nat), RET #(W64 i);
      own_selected_case_params4 dir1 dir2 dir3 dir4
        params1 params2 params3 params4 blocking i
        case1 case2 case3 case4 v1 v2 v3 v4 i1 i2 i3 i4 }}}.
Proof.
  wp_start. wp_auto.
Admitted.

Lemma wp_Select5
  (dir1 dir2 dir3 dir4 dir5: select_dir)
  (params1 params2 params3 params4 params5: chan)
  (case1 case2 case3 case4 case5: loc)
  (blocking: bool)
  (v1 v2 v3 v4 v5: val)
  (i1 i2 i3 i4 i5: nat) :
  {{{ is_pkg_init channel ∗
      own_select_case dir1 params1 case1 false i1 v1 ∗
      own_select_case dir2 params2 case2 false i2 v2 ∗
      own_select_case dir3 params3 case3 false i3 v3 ∗
      own_select_case dir4 params4 case4 false i4 v4 ∗
      own_select_case dir5 params5 case5 false i5 v5 }}}
    channel @ "Select5"
             #params1.(ch_T) #params2.(ch_T) #params3.(ch_T) #params4.(ch_T) #params5.(ch_T)
             #case1 #case2 #case3 #case4 #case5 #blocking
  {{{ (i : nat), RET #(W64 i);
      own_selected_case_params5 dir1 dir2 dir3 dir4 dir5
        params1 params2 params3 params4 params5
        blocking i
        case1 case2 case3 case4 case5
        v1 v2 v3 v4 v5
        i1 i2 i3 i4 i5 }}}.
Proof.
  wp_start. wp_auto.
Admitted.

End proof.
