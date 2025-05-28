From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_ghost_state chan_spec_inv chan_spec_base chan_spec_send chan_spec_recv.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.
Require Export New.code.sync.
Require Export New.generatedproof.sync.
From New.proof.sync_proof Require Import base mutex sema.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!ghost_varG Σ (bool * val)}.
   Context `{!goGlobalsGS Σ}.
#[global] Program Instance : IsPkgInit channel := ltac2:(build_pkg_init ()).

(* Parameterized select case logical function *)
Definition own_select_case_logical
  (params: chan) (dir: select_dir)
  (v: params.(ch_T')) (selected: bool) (i: nat) (ok: bool) : iProp Σ :=
match selected with
| false =>
    match dir with
    | SelectSend => send_pre params i v
    | SelectRecv => recv_pre params i
    end
| true =>
    match dir with
    | SelectSend => send_post params i
    | SelectRecv => recv_post params i ok v
    end
end.

Definition own_select_case
  (dir: select_dir) (params: chan) (case_ptr: loc) (selected: bool) (i: nat) (v': val) : iProp Σ :=
  if bool_decide (params.(ch_loc) = null) then
    (* For nil case, precondition is True, postcondition is False *)
    (if selected then False%I else 
      "%Hintty" ∷ ⌜params.(ch_T) = int64T⌝ ∗  (* This connects v' to a properly typed v *)
      "chan_ptr" ∷ case_ptr ↦s[(channel.SelectCase.ty params.(ch_T)) :: "channel"] null
    
    %I)%I
  else
    (let T' := params.(ch_T') in
    let T := params.(ch_T) in
    let IntoVal_inst := params.(ch_IntoVal) in
    let IntoValTyped_inst := params.(ch_IntoValTyped) in
    let Hbounded := params.(ch_Hbounded) in
    ∃  (v: T') (ok: bool),
      (*"%Hvalconv" ∷ ⌜v' = to_val v⌝ ∗  (* This connects v' to a properly typed v *) *)
      "chan_ptr" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "channel"] params.(ch_loc) ∗
      "dir" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "dir"] (select_dir_to_word dir) ∗
      "Value" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "Value"] v ∗
      "Ok" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "Ok"] ok ∗ 
      "Hlogicalselect" ∷ own_select_case_logical params dir v selected i ok)%I.


Lemma wp_TrySelect (params: chan) (dir: select_dir) (case_ptr: loc) 
      (i: nat) (v: params.(ch_T')):
      let IntoVal_inst := params.(ch_IntoVal) in
      let IntoValTyped_inst := params.(ch_IntoValTyped) in
      {{{ is_pkg_init channel ∗ own_select_case dir params case_ptr false i #v }}}
        channel @ "TrySelect" #params.(ch_T) #case_ptr
      {{{ (selected: bool), RET #selected;
          own_select_case dir params case_ptr selected i #v
      }}}.
    Proof.
      intros Hiv_inst Hivt_inst.
      wp_start. wp_auto.
      unfold own_select_case.
      destruct bool_decide eqn:Hb.
      {
        iNamed "Hpre".  replace params.(ch_T) with int64T.
        wp_auto. 
        iApply "HΦ". iFrame. done.
      }
      {
        iNamed "Hpre".
        wp_auto. rewrite Hb. wp_auto. wp_if_destruct.
        {
         wp_auto.
         Search wp_Channel__TrySend.
         unfold own_select_case_logical.
          assert (dir = SelectSend).
         {
          destruct dir;first done;done.
         }
         subst dir.
         iNamed "Hlogicalselect".
         iNamed "HCh".
         wp_apply (wp_Channel__TrySend params i v0 with "[HSc  HP  ]"). all: try done;try lia; try word.
         {
          iFrame "#". iFrame. iPureIntro. done.
         }
         {
          iIntros (selected) "Hsel".
          
          wp_auto. iApply "HΦ".
          destruct selected.
          {
           iFrame. 
          }
          {
           iFrame.  
          }
         }
        }
        {
         wp_auto. wp_if_destruct.
         {
          wp_auto.
          assert (dir = SelectRecv).
         {
          destruct dir;first done;done.
         }
          iNamed "Hlogicalselect".
          unfold own_select_case_logical. subst dir.
          iNamed "Hlogicalselect".
          wp_apply (wp_Channel__TryReceive params i with "[HCh HQ HRecvPerm]").
          all: try done.
          {
           iFrame. done. 
          }
          iIntros (v1).
          iIntros (ok1).
          iIntros (selected).
          destruct selected.
          {
            iIntros "Hrecvpost".
           wp_auto. iApply "HΦ". iFrame.  
          }
          {
            iIntros "HRecvpre".
           wp_auto. iApply "HΦ". iFrame.  
          }
         }
         {
          iApply "HΦ". iFrame.
         }
        }
      }
    Qed.

    Lemma wp_Select1
    (params1: chan)
    (dir1: select_dir)
    (case1 : loc)
    (i1: nat) (v1: params1.(ch_T'))
    (blocking : bool) :
    let IntoVal_inst1 := params1.(ch_IntoVal) in
    let IntoValTyped_inst1 := params1.(ch_IntoValTyped) in
    params1.(ch_loc) ≠ null ->
    {{{ is_pkg_init channel ∗ own_select_case dir1 params1 case1 false i1 #v1 }}}
      channel @ "Select1" #params1.(ch_T) #case1 #blocking
    {{{ (selected : bool), RET #selected;
       "Hb" ∷ ⌜if blocking then selected else true⌝%I ∗ 
       if selected then 
       own_select_case dir1 params1 case1 true i1 #v1 
        else 
        own_select_case dir1 params1 case1 false i1 #v1 
        }}}.
  Proof. 
    intros Hiv Hivt Hnn.
    wp_start. wp_auto.
    wp_for. unfold own_select_case. iNamed "Hpre".
    destruct bool_decide eqn: Hb.
    {
      apply bool_decide_eq_true in Hb.
     done. 
    }
    iNamed "Hpre".
     wp_apply (wp_TrySelect with "[chan_ptr dir Value Ok Hlogicalselect]").
     {
      unfold own_select_case.
      destruct bool_decide.
      {
       done. 
      }
        iFrame.
     }
     iIntros (selected) "Hsel".
     wp_auto.
     destruct selected.
     {
      wp_auto.
      wp_for_post. iApply "HΦ". unfold own_select_case.
      destruct bool_decide.
      {
        done.
      }
      iFrame. iPureIntro. destruct blocking. all: done.
     }
     wp_auto. destruct blocking.
     {
      wp_auto. wp_for_post. iFrame. unfold own_select_case.
      destruct bool_decide.
      {
        done.
      }
      iFrame.
     }
     wp_auto. wp_for_post. iApply "HΦ". unfold own_select_case.
     destruct bool_decide; first done.
     iFrame.
     Unshelve.
     {
      iPureIntro. done.
     }
     done.
  Qed.

    Lemma wp_TrySelectCase2 
    (params1 params2: chan) 
    (dir1 dir2: select_dir)
    (case1_ptr case2_ptr: loc)
    (i1 i2: nat) 
    (v1: params1.(ch_T')) (v2: params2.(ch_T'))
    (index: u64):
    let IntoVal_inst1 := params1.(ch_IntoVal) in
    let IntoValTyped_inst1 := params1.(ch_IntoValTyped) in
    let IntoVal_inst2 := params2.(ch_IntoVal) in
    let IntoValTyped_inst2 := params2.(ch_IntoValTyped) in
    (index = W64 0 ∨ index = W64 1) ->
    {{{ is_pkg_init channel ∗
       "Hc1pre" ∷ own_select_case dir1 params1 case1_ptr false i1 #v1 ∗
       "Hc2pre" ∷ own_select_case dir2 params2 case2_ptr false i2 #v2
    }}}
      channel @ "TrySelectCase2" #params1.(ch_T) #params2.(ch_T) #index #case1_ptr #case2_ptr
    {{{ (selected: bool), RET #selected;
        if decide (index = W64 0) then
          own_select_case dir1 params1 case1_ptr selected i1 #v1 ∗
          own_select_case dir2 params2 case2_ptr false i2 #v2
        else (* index = W64 1 *)
          own_select_case dir1 params1 case1_ptr false i1 #v1 ∗
          own_select_case dir2 params2 case2_ptr selected i2 #v2
    }}}.
  Proof.
    intros Hiv1 Hivt1 Hiv2 Hivt2 Hindex.
    wp_start. wp_apply wp_alloc.
    iNamed "Hpre". 
    iIntros (case_2) "Hc2p".
     wp_auto.
     wp_apply wp_alloc.
    iIntros (case_1) "Hc1p".
    wp_auto. 
    wp_if_destruct.
    {
     wp_auto.

     wp_apply (wp_TrySelect params1 dir1 case1_ptr i1 v1 with "[Hc1pre Hc1p]").
     {
      iFrame.
     }
     iIntros (selected) "Hsc".
     wp_auto. iApply "HΦ". iFrame.
    }
    {
    wp_auto.
     wp_if_destruct.
     {
      wp_auto. 
     wp_apply (wp_TrySelect params2 dir2 case2_ptr i2 v2 with "[Hc2pre Hc2p]").
     {
      iFrame.
     }
     iIntros (selected) "Hsc".
     wp_auto. iApply "HΦ". iFrame.
     }
     word.
    }
  Qed.

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
      own_select_case SelectSend params case_ptr false i #v
  }}}.
Proof.
  intros HT' HT Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto. iNamed "Hpre".
  wp_apply wp_alloc. iIntros (ptr) "Hptr".
  iApply struct_fields_split in "Hptr"; iNamed "Hptr". wp_auto. iApply "HΦ".
  iNamed "HCh".
  unfold own_select_case. simpl.
  destruct bool_decide eqn: Hb.
  {
    apply bool_decide_eq_true in Hb.
    done.
  }
  iFrame.
  simpl. iFrame "#". iFrame. iPureIntro. done. 
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
      own_select_case SelectRecv params case_ptr false i (#(default_val params.(ch_T')))
  }}}.
Proof.
  intros H1 H2 Hiv_inst Hivt_inst Hb_inst. wp_start. wp_auto. iNamed "Hpre".
  wp_apply wp_alloc. iIntros (ptr) "Hptr".
  iApply struct_fields_split in "Hptr"; iNamed "Hptr". wp_auto. iApply "HΦ".
  iNamed "HCh".
  unfold own_select_case. simpl.
  destruct bool_decide eqn: Hb.
  {
    apply bool_decide_eq_true in Hb.
    done.
  }
  iFrame.
  simpl. iFrame "#". iPureIntro. done.
Qed.

End proof.
