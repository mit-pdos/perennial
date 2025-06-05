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
Context `{!goGlobalsGS Σ}.
Context  `{!chanGhostStateG Σ}.

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

(* Parameterized select case logical function *)
Definition own_select_case_logical
  (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) (dir: select_dir)
  (v: V) (selected: bool) (q: Qp) (i: nat) (ok: bool) (Ri: nat -> iProp Σ): iProp Σ :=
match selected with
| false =>
    match dir with
    | SelectSend => send_pre  V params q i v
    | SelectRecv => recv_pre V params q i Ri
    end
| true =>
    match dir with
    | SelectSend => send_post V params q i
    | SelectRecv => recv_post V params q i ok v Ri
    end
end.

Definition own_select_case
  (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) (dir: select_dir)  (case_ptr: loc) (selected: bool) (i: nat) (q: Qp) (v': val) (Ri: nat->iProp Σ) : iProp Σ :=
  if bool_decide (params.(ch_loc) = null) then
    (* For nil case, precondition is True, postcondition is False *)
    (if selected then False%I else 
      (*"%Hintty" ∷ ⌜t = int64T⌝ ∗  (* This connects v' to a properly typed v *) *)
      "chan_ptr" ∷ case_ptr ↦s[(channel.SelectCase.ty t) :: "channel"] null
    
    %I)%I
  else
    (
    ∃  (v: V) (ok: bool),
      "chan_ptr" ∷ case_ptr ↦s[(channel.SelectCase.ty t) :: "channel"] params.(ch_loc) ∗
      "dir" ∷ case_ptr ↦s[(channel.SelectCase.ty t) :: "dir"] (select_dir_to_word dir) ∗
      "Value" ∷ case_ptr ↦s[(channel.SelectCase.ty t) :: "Value"] v ∗
      "Ok" ∷ case_ptr ↦s[(channel.SelectCase.ty t) :: "Ok"] ok ∗ 
      "Hlogicalselect" ∷ own_select_case_logical V params dir v selected q i ok Ri)%I.


Lemma wp_TrySelect (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V)  (dir: select_dir) (case_ptr: loc) 
      (i: nat) (q: Qp) (v: V) (Ri: nat -> iProp Σ):
      {{{ is_pkg_init channel ∗ own_select_case V params dir case_ptr false i q #v Ri }}}
        channel @ "TrySelect" #t #case_ptr
      {{{ (selected: bool), RET #selected;
          own_select_case V params dir case_ptr selected i q #v Ri
      }}}.
    Proof.
      wp_start. wp_auto.
      unfold own_select_case.
      destruct bool_decide eqn:Hb.
      {
        iNamed "Hpre".  
        wp_auto. 
        iApply "HΦ". iFrame. 
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
         wp_apply (wp_Channel__TrySend V params i q v0 with "[HSc  HP  ]"). all: try done;try lia; try word.
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
          wp_apply (wp_Channel__TryReceive V params i with "[HCh HQ HRecvPerm]").
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
    (V: Type) {K: IntoVal V} {t} {H': IntoValTyped V t}  (params: chan V) 
    (dir1: select_dir)
    (case1 : loc)
    (i1: nat) (q1: Qp) (v1: V) 
    (blocking : bool) (Ri: nat -> iProp Σ) :
    params.(ch_loc) ≠ null ->
    {{{ is_pkg_init channel ∗ own_select_case V params dir1 case1 false i1 q1 #v1 Ri }}}
      channel @ "Select1" #t #case1 #blocking
    {{{ (selected : bool), RET #selected;
       "Hb" ∷ ⌜if blocking then selected else true⌝%I ∗ 
       if selected then 
       own_select_case V params dir1 case1 true i1 q1 #v1 Ri
        else 
        own_select_case V params dir1 case1 false i1 q1 #v1 Ri
        }}}.
  Proof. 
    intros Hnn.
    wp_start. wp_auto.
    wp_for. unfold own_select_case. iNamed "Hpre".
    destruct bool_decide eqn: Hb.
    {
      apply bool_decide_eq_true in Hb.
     done. 
    }
    iNamed "Hpre".
     wp_apply ((wp_TrySelect V params) with "[chan_ptr dir Value Ok Hlogicalselect]").
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
    (V1: Type) {K1: IntoVal V1} {t1} {H'1: IntoValTyped V1 t1}  (params1: chan V1) 
    (V2: Type) {K2: IntoVal V2} {t2} {H'2: IntoValTyped V2 t2}  (params2: chan V2) 
   
    (dir1 dir2: select_dir)
    (case1_ptr case2_ptr: loc)
    (i1 i2: nat) 
    (v1: V1) (v2: V2)
    (Ri1 Ri2: nat->iProp Σ)
    (q1 q2: Qp)
    (index: u64)
    :
 
    (index = W64 0 ∨ index = W64 1) ->
    {{{ is_pkg_init channel ∗
       "Hc1pre" ∷ own_select_case V1 params1 dir1  case1_ptr false i1 q1 #v1 Ri1 ∗
       "Hc2pre" ∷ own_select_case V2 params2 dir2  case2_ptr false i2 q2 #v2 Ri2
    }}}
      channel @ "TrySelectCase2" #t1 #t2 #index #case1_ptr #case2_ptr
    {{{ (selected: bool), RET #selected;
        if decide (index = W64 0) then
          own_select_case V1 params1 dir1 case1_ptr selected i1 q1 #v1 Ri1 ∗
          own_select_case V2 params2 dir2 case2_ptr false i2 q2 #v2 Ri2
        else (* index = W64 1 *)
          own_select_case V1 params1 dir1 case1_ptr false i1 q1 #v1 Ri1 ∗
          own_select_case V2 params2 dir2 case2_ptr selected i2 q2 #v2 Ri2
    }}}.
  Proof.
    intros Hindex.
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

     wp_apply (wp_TrySelect V1 params1 dir1 case1_ptr i1 q1 v1 with "[Hc1pre Hc1p]").
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
     wp_apply (wp_TrySelect V2 params2 dir2 case2_ptr i2 q2 v2 with "[Hc2pre Hc2p]").
     {
      iFrame.
     }
     iIntros (selected) "Hsc".
     wp_auto. iApply "HΦ". iFrame.
     }
     word.
    }
  Qed.

Definition null_Ri: Z->iProp Σ := 
 ( λ _, False%I)
 .

  Lemma wp_NewSendCase
  (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t}  (params: chan V) 
   (i: nat) (q: Qp) (v: V) (l: loc):

  (l = 
  (ch_loc params)) ->
  {{{ is_pkg_init channel ∗ 
  if bool_decide(params.(ch_loc) ≠ null) then send_pre V params q i v else True%I
   }}}
    channel @ "NewSendCase" #t #l #v
  {{{ (case_ptr: loc), RET #case_ptr;
    if bool_decide(params.(ch_loc) ≠ null) then  own_select_case V params SelectSend case_ptr false i q #v null_Ri else True%I
  }}}.
Proof.
  intros Hl.
  wp_start. wp_auto. iNamed "Hpre".
  wp_apply wp_alloc. iIntros (ptr) "Hptr".
  iApply (struct_fields_split ) in "Hptr". iNamed "Hptr". wp_auto.
  
  iApply "HΦ".
  iNamed "Hpre".
  simpl.
  unfold send_pre. simpl. 
  unfold own_select_case. subst l.
  destruct (bool_decide(params .(ch_loc) = null)) eqn: Houter.
  {
    apply bool_decide_eq_true in Houter.
    rewrite Houter.
    simpl. iFrame. 
  }
  {
    apply bool_decide_eq_false in Houter.
    destruct bool_decide.
    {
      iNamed "Hpre". iFrame. done.
    }
    {
     done. 
    }
  }
Qed.

Lemma wp_NewRecvCase
  (V: Type) {K: IntoVal V} {t: go_type} {H': IntoValTyped V t} {B: BoundedTypeSize t}  (params: chan V)  (i: nat) (q: Qp) (Ri: nat -> iProp Σ):
  
  {{{ is_pkg_init channel ∗ recv_pre V params q i Ri }}}
    channel @ "NewRecvCase" #t #params.(ch_loc)
  {{{ (case_ptr: loc), RET #case_ptr;
      own_select_case V params SelectRecv case_ptr false i q (#(default_val V)) Ri
  }}}.
Proof.
   wp_start. wp_auto. iNamed "Hpre".
  wp_apply wp_alloc. iIntros (ptr) "Hptr".
  iApply struct_fields_split in "Hptr"; iNamed "Hptr". wp_auto. iApply "HΦ".
  iNamed "HCh".
  unfold own_select_case. simpl.
  iDestruct (chan_pointsto_non_null V (params.(ch_mu)) params with "mu") as %HNonNull.
  assert (params .(ch_loc) ≠ null).
  {
    intro H1.
    rewrite H1 in HNonNull. done.
  }
  destruct bool_decide eqn: Hb.
  {
    apply bool_decide_eq_true in Hb.
    done.
  }
  iFrame.
  simpl. iFrame "#". iPureIntro. done.
Qed.

End proof.
