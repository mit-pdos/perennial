From New.proof Require Import proof_prelude.
From Perennial.algebra Require Import auth_map.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_inv chan_ghost_state chan_spec_api chan_spec_base.
From Perennial.base_logic Require Import lib.ghost_map.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From New.code.github_com.goose_lang.goose.testdata.examples Require Import channel.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

From Perennial.Helpers Require Import bytes.
From Coq Require Import Program.Equality.
Set Default Proof Using "Type*".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context  `{!chanGhostStateG Σ}.
Context `{!ghost_varG Σ (w64)}.
Context `{!goGlobalsGS Σ}.
Context `{ ghost_mapG Σ Z w64 }.
#[global] Program Instance : IsPkgInit chan_spec_raw_examples := ltac2:(build_pkg_init ()).

(* 
  Transfers pointer ownership from main to forked goroutine.
  Maintains word requirements and exact pointer name. 
*)
Definition ghost_pt_pred (γ: gname) (val1_ptr val2_ptr val3_ptr: loc) (i: Z) (l: loc)  : iProp Σ :=  (∃ (w: w64), (l ↦ w) ∗ (i ↪[γ] w) ∗ ⌜i < 3 ⌝ ∗ ⌜ word.unsigned w + 1 < 2 ^ 63 ⌝ 
∗ 
   match i with 
        | 0 => ⌜l = val1_ptr ⌝ 
        | 1 => ⌜l = val2_ptr ⌝ 
        | 2 => ⌜l = val3_ptr ⌝ 
        | _ => False
        end

).

Lemma wp_DoubleValues :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    chan_spec_raw_examples @ "DoubleValues" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.

  (* Allocate empty slice *)
  wp_apply wp_fupd.
  iDestruct own_slice_nil as "Hempty".
  wp_apply wp_slice_literal.
  iMod (ghost_map_alloc (∅ : gmap Z w64)) as (γ) "[Hauth _]".
  iIntros (sl) "Hsl".
  iModIntro. wp_auto.

  (* Append val1_ptr to slice *)
  wp_apply ((wp_slice_append slice.nil [] sl [val1_ptr]) with "[$Hsl $Hempty]").
  {
    iApply own_slice_cap_none.
    done.
  }
  iIntros (s') "(Hs' & Hosc & Hsl')".
  wp_auto.

  (* Insert ghost map entries *)
  wp_apply wp_fupd.
  set (five := W64 5).
  set (ten := W64 10).
  set (fifteen := W64 15).
  set (twenty := W64 20).
  set (thirty := W64 30).

  iMod (ghost_map_insert 0 five with "[$Hauth]") as "[Hauth Hptstofive]";first done.
  iMod (ghost_map_insert 1 ten with "[$Hauth]") as "[Hauth' Hptstoten]".
  {
    rewrite -> lookup_insert_ne. all: done.
  }
  iMod (ghost_map_insert 2 fifteen with "[$Hauth']") as "[Hauth'' Hptstofifteen]".
  {
    rewrite -> lookup_insert_ne.
    {
     rewrite -> lookup_insert_ne. all: done.
    } done.
  }

  (* Additional slices *)
  wp_apply wp_slice_literal.
  iIntros (sl0) "Hsl0".
  iModIntro. wp_auto.

  wp_apply (wp_slice_append with "[$Hs' $Hosc $Hsl0]").
  iIntros (s0') "(Hs0' & Hosc & Hsl0')".
  wp_auto.

  wp_apply wp_slice_literal.
  iIntros (sl1) "Hsl1".
  wp_auto.

  wp_apply (wp_slice_append with "[$Hs0' $Hosc $Hsl1]").
  iIntros (s1') "(Hs1' & Hosc & Hsl1')".
  wp_auto.

  (* Slice length *)
  iDestruct (own_slice_len with "Hs1'") as %Hlen.
  simpl in Hlen.

  (* Create channel refs *)
  wp_apply (wp_NewChannelRef_base loc
              0 (* unbuffered *)
              true (* single party *)
              (* Gain ptrs from main goroutine *)
              (ghost_pt_pred γ val1_ptr val2_ptr val3_ptr)
              (λ _, True)%I
              (λ _, True)%I
              True%I
              (* 3 uses only *)
              (λ n, ⌜n = 3%nat⌝)%I).
  all: try done.
  iIntros (vals_ch mu vals_buf_slice γ1 vals_params)
    "(%Hvalsparams & #HvalsCh & Hctvals & HScvals & HRecvPermVals)".
  wp_auto.

  wp_apply (wp_NewChannelRef_base w64
              0 (* unbuffered *)
              true (* single party *)
              (* Can't send *)
              (λ i (v: w64), False%I)%I
              (* Unused, we are single party *)
              (λ _, False%I)%I
              (* Not false, necessary for receiving on closed *)
              (λ _, True)%I
              (* Unused, we are single party *)
              False%I
              (* Send all of the ptrs back to main *)
              (λ n, ∃ a b c,
                "%Hww" ∷ ⌜0 < a + 1 < 2^63 ∧ 0 < b + 1 < 2^63 ∧ 0 < c + 1 < 2^63⌝ ∗
                0 ↪[γ] (W64 a) ∗ val1_ptr ↦ (W64 (2 * a)) ∗
                1 ↪[γ] (W64 b) ∗ val2_ptr ↦ (W64 (2 * b)) ∗
                2 ↪[γ] (W64 c) ∗ val3_ptr ↦ (W64 (2 * c)))%I).
  all: try done.
  iIntros (sync_ch mu2 ch_buf_slice2 γ2 sync_params)
    "(%Hsyncparams & #HsyncCh & Hctsync & HScsync & HRecvPermSync)".
  iPersist "ch" as "#valsCh".
  wp_auto.
  iPersist "done" as "#doneCh".

  (* Forked thread *)
  wp_apply (wp_fork with "[HRecvPermVals HScsync Hctsync]").
{
  iAssert (
    ∃ (i : nat) (a b c : Z),
      "Hcase" ∷ ⌜ i ∈ [0%nat;1%nat;2%nat;3%nat] ⌝ ∗
      "Hbounds" ∷ ⌜ 0 < a + 1 < 2^63 ∧ 0 < b + 1 < 2^63 ∧ 0 < c + 1 < 2^63 ⌝ ∗
      "Hrecvperm" ∷ own_recv_perm vals_params.(ch_γ loc) 1 i (λ n, ⌜n = 3%nat⌝) ∗
      "Hresources" ∷ (
        match i with
        | 0%nat => True
        | 1%nat => 0 ↪[γ] (W64 a) ∗ val1_ptr ↦ (W64 (2 * a))
        | 2%nat => 0 ↪[γ] (W64 a) ∗ val1_ptr ↦ (W64 (2 * a))
             ∗ 1 ↪[γ] (W64 b) ∗ val2_ptr ↦ (W64 (2 * b))
        | 3%nat => 0 ↪[γ] (W64 a) ∗ val1_ptr ↦ (W64 (2 * a))
             ∗ 1 ↪[γ] (W64 b) ∗ val2_ptr ↦ (W64 (2 * b))
             ∗ 2 ↪[γ] (W64 c) ∗ val3_ptr ↦ (W64 (2 * c))
        | _ => False
        end
      )
  )%I with "[HRecvPermVals]" as "Hinv".
  {
    iExists 0%nat, 0, 0, 0.
    iFrame.
    iPureIntro.
    split; [set_solver | split; repeat split; lia].
  }

  wp_auto.
  wp_for "Hinv".
  iDestruct "Hcase" as %Hi_case.
  iDestruct "Hbounds" as %Hbounds.
  destruct i as [| [| [| ]]].
  {
    replace vals_ch with (vals_params.(ch_loc loc)) by (subst;done).
    wp_apply ((wp_Channel__Receive loc vals_params 0%nat 1%Qp (λ n, ⌜n = 3%nat⌝)%I) with "[Hrecvperm]").
    {
      iFrame "#%". iFrame. unfold Q. subst. simpl. done.
    }
    iIntros (v ok) "Hrecv".
    destruct ok.
      - iDestruct "Hrecv" as "[Hval Hrest]".
        unfold P. subst. simpl. unfold ghost_pt_pred.
        iNamed "Hval". simpl.
        iDestruct "Hval" as "(Hvw & Hwmap & %Hlt & %Hw & %Hv)".
        subst v. wp_auto.
        wp_for_post.
        iFrame.
        iExists (word.unsigned w), b, c.
        replace (W64 (uint.Z w)) with w by word.
        replace (w64_word_instance .(word.mul) w (W64 2)) with (W64 (2 * (uint.Z w))) by word.
        iFrame.
        iPureIntro.
        split; [set_solver | word].
      - wp_auto. unfold recv_post.
        iNamed "Hrecv". iNamed "Hrecv".  
        iDestruct "HRi" as "%Hri". subst n.
        iDestruct (recv_counter_elem vals_params.(ch_γ loc)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
        done.
  }
  {
    replace vals_ch with (vals_params.(ch_loc loc)) by (subst;done).
    wp_apply ((wp_Channel__Receive loc vals_params 1%nat 1%Qp (λ n, ⌜n = 3%nat⌝)%I) with "[Hrecvperm]").
    {
      iFrame "#%". iFrame. unfold Q. subst. simpl. done.
    }
    iIntros (v ok) "Hrecv".
    destruct ok.
    - iDestruct "Hrecv" as "[Hval Hrest]".
      unfold P. subst. simpl. unfold ghost_pt_pred.
      iNamed "Hval". simpl.
      iDestruct "Hval" as "(Hvw & Hwmap & %Hlt & %Hw & %Hv)".
      subst v. wp_auto.
      wp_for_post.
      iFrame.
      iExists a, (word.unsigned w), c.
      replace (W64 (uint.Z w)) with w by word.
      replace (w64_word_instance .(word.mul) w (W64 2)) with (W64 (2 * (uint.Z w))) by word.
      iFrame.
      iPureIntro.
      split; [set_solver | word].
    - wp_auto. unfold recv_post.
      iNamed "Hrecv". iNamed "Hrecv".  
      iDestruct "HRi" as "%Hri". subst n.
      iDestruct (recv_counter_elem vals_params.(ch_γ loc)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
      done.
  }
  {
    replace vals_ch with (vals_params.(ch_loc loc)) by (subst;done).
    wp_apply ((wp_Channel__Receive loc vals_params 2%nat 1%Qp (λ n, ⌜n = 3%nat⌝)%I) with "[Hrecvperm]").
    {
      iFrame "#%". iFrame. unfold Q. subst. simpl. done.
    }
    iIntros (v ok) "Hrecv".
    destruct ok.
    - iDestruct "Hrecv" as "[Hval Hrest]".
      unfold P. subst. simpl. unfold ghost_pt_pred.
      iNamed "Hval". simpl.
      iDestruct "Hval" as "(Hvw & Hwmap & %Hlt & %Hw & %Hv)".
      subst v. wp_auto.
      wp_for_post.
      iFrame.
      iExists a, b, (word.unsigned w).
      replace (W64 (uint.Z w)) with w by word.
      replace (w64_word_instance .(word.mul) w (W64 2)) with (W64 (2 * (uint.Z w))) by word.
      iFrame.
      iPureIntro.
      split; [set_solver | word].
    - wp_auto. unfold recv_post.
      iNamed "Hrecv". iNamed "Hrecv".  
      iDestruct "HRi" as "%Hri". subst n.
      iDestruct (recv_counter_elem vals_params.(ch_γ loc)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
      done.
  }
  {
  (* Prove that n = 0 using the invariant *)
  assert (n = 0%nat) as -> by set_solver.

  (* Replace pointer consistency *)
  replace vals_ch with (vals_params.(ch_loc loc)) by (subst; done).

  (* Apply receive on channel index 3 *)
  wp_apply ((wp_Channel__Receive loc vals_params 3%nat 1%Qp (λ n, ⌜n = 3%nat⌝)%I) with "[$Hrecvperm]").
  {
    unfold Q. subst. simpl.
    iFrame "%#". iFrame.
    iPureIntro.
    done.
  }
  iIntros (v1 ok1) "Hrecv".
  unfold recv_post.

  destruct ok1.
  - (* Received successfully, process the value *)
    unfold P.
    replace (vals_params.(ch_is_single_party loc)) with true by (subst; done).
    wp_auto.

    (* Destruct the heap points-to and ghost resources *)
    iDestruct "Hrecv" as "[Hval Hghost]".
    subst. simpl.
    iNamed "Hval". simpl. 
    iDestruct "Hval" as "[Hv1 [Hw %Hf]]".
    destruct Hf as [Hf1 Hf2].
    done.  (* Possibly you want to continue with your intended proof here *)

  - (* Receive failed; close the sync channel *)
    wp_auto.
    wp_for_post.
    iNamed "Hrecv".
    iNamed "Hrecv".
    iDestruct "HRi" as "%Hri".
    replace sync_ch with (sync_params.(ch_loc w64)) by (subst; done).

    (* Close the sync channel *)
    wp_apply ((wp_Channel__Close w64 sync_params 0) with "[Hresources HScsync Hctsync]").
    {
      subst. simpl.
      unfold own_close_perm.
      iFrame "#".
      iFrame "%".
      iFrame "HScsync".
      iFrame.
    }
    done.
    } 
}
  iNamed "HRecvPermSync".
  wp_pure. { word. }


  (* === Load and Send first element === *)
  wp_apply ((wp_load_slice_elem s1' (W64 0) [val1_ptr; val2_ptr; val3_ptr] (DfracOwn 1) val1_ptr) with "[$Hs1']").
  { iPureIntro. simpl. reflexivity. }
  iIntros "Hs1'".
  wp_auto.
  replace vals_ch with (vals_params.(ch_loc loc)) by (subst; done).
  wp_apply ((wp_Channel__Send loc vals_params 0%nat 1%Qp val1_ptr) with "[$HScvals val1 Hptstofive]"). all: try (subst;done).
  {
    subst. simpl.
    iFrame "#%".
    unfold P. iFrame.
    unfold ghost_pt_pred.
    simpl.
    iFrame. done.
  }
  iIntros "Hsend0".
  iDestruct "Hsend0" as "[_ Hscf]".
  wp_auto.

  wp_pure. { simpl in Hlen. word. }

  (* === Load and Send second element === *)
  wp_apply ((wp_load_slice_elem s1' (W64 1) [val1_ptr; val2_ptr; val3_ptr] (DfracOwn 1) val2_ptr) with "[$Hs1']").
  { iPureIntro. simpl. reflexivity. }
  iIntros "Hs1'".
  wp_auto.

  wp_apply ((wp_Channel__Send loc vals_params 1%nat 1%Qp val2_ptr) with "[$Hscf val2 Hptstoten]").
  all: try (subst;done).
  {
    subst. simpl.
    iFrame "#%".
    unfold P. iFrame.
    iSplitL ""; first done.
    unfold ghost_pt_pred.
    simpl. done.
  }
  iIntros "Hsend1".
  iDestruct "Hsend1" as "[_ Hscf]".
  wp_auto.

  wp_pure. { word. }

  (* === Load and Send third element === *)
  wp_apply ((wp_load_slice_elem s1' (W64 2) [val1_ptr; val2_ptr; val3_ptr] (DfracOwn 1) val3_ptr) with "[$Hs1']").
  { iPureIntro. simpl. reflexivity. }
  iIntros "Hs1'".
  wp_auto.

  wp_apply ((wp_Channel__Send loc vals_params 2%nat 1%Qp val3_ptr) with "[$Hscf val3 Hptstofifteen]"). all: try (subst;done).
  {
    subst. simpl.
    unfold P. iFrame.
    iSplitL ""; first done.
    unfold ghost_pt_pred.
    simpl.
    iFrame "#". done.
  }
  iIntros "Hsend2".
  iDestruct "Hsend2" as "[_ Hscf]".
  wp_auto.

  (* === Close vals channel === *)
  wp_apply ((wp_Channel__Close loc vals_params 3) with "[$Hscf Hctvals]").
  {
    subst. simpl.
    iFrame.
    iFrame "#". done.
  }

  (* === Receive from sync channel === *)
  replace sync_ch with (sync_params.(ch_loc w64)) by (subst; done).
  wp_apply ((wp_Channel__Receive w64 sync_params 0%nat 1%Qp) with "[$HRecvPerm]").
  {
    subst. simpl. iFrame "%#". done.
  }
  iIntros (v ok) "Hrecv".
  wp_auto.

  destruct ok.
  - iDestruct "Hrecv" as "[Hf _]".
    subst. simpl. done.
  - iNamed "Hrecv". iNamed "Hrecv". iNamed "HRi".
    iDestruct "HRi" as "(H1 & H2 & H3 & H4 & H5 & H6)".

    (* Ghost map lookup *)
    iDestruct (ghost_map_lookup with "[$Hauth''] [$H1]") as %Hlookup1.
    iDestruct (ghost_map_lookup with "[$Hauth''] [$H3]") as %Hlookup2.
    iDestruct (ghost_map_lookup with "[$Hauth''] [$H5]") as %Hlookup3.
    destruct Hww as (Ha & Hb & Hc).
    assert (W64 a = five) as Heqa.
    { 
      rewrite -> lookup_insert_ne in Hlookup1 by done. 
      symmetry.
      inversion Hlookup1 as [Heq].
      subst. 
      apply word.unsigned_inj.
      rewrite -> lookup_insert_ne in Heq by done.
      rewrite -> lookup_insert_eq in Heq by done.
      unfold five in *. inversion Heq as [Heq'].
      done.
    }
    assert (W64 b = ten) as Heqb.
    { 
      unfold ten.
      rewrite -> lookup_insert_ne in Hlookup2 by done. 
      rewrite -> lookup_insert_eq in Hlookup2 by done. 
      symmetry. 
      inversion Hlookup2 as [Heq].
      subst.  
      apply word.unsigned_inj. done.
    }
    assert (W64 c = fifteen).
    {
      rewrite lookup_insert_eq in Hlookup3.
      symmetry.
      inversion Hlookup3 as [Heq].
      subst. apply word.unsigned_inj. exact Heq.
    }

    (* Final conclusion *)
    unfold five in *. unfold ten in *. unfold fifteen in *.
    replace a with 5 by word.
    replace b with 10 by word.
    replace c with 15 by word.
    wp_auto.
    iApply "HΦ". done.
Qed.

Lemma wp_CoordinatedChannelClose (γ: chan_names):
  {{{ is_pkg_init chan_spec_raw_examples }}}
    chan_spec_raw_examples @ "CoordinatedChannelClose" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start; wp_auto.
  wp_apply wp_fupd.

  (* Allocate two ghost variables for distinguishing send cases *)
  iMod (ghost_var_alloc (W64 42)) as (γs1) "HSend42".
  iMod (ghost_var_alloc (W64 84)) as (γs2) "HSend84".

  (* Allocate buffered channel for sending 42 or 84 *)
  wp_apply (wp_NewChannelRef_base w64
    2 (* buffered size *)
    false (* single party *)
    (λ i (v: w64), emp)%I
    (λ (v:w64),
      (ghost_var γs1 1%Qp (W64 42) ∗ ⌜v = W64 42⌝) ∨
      (ghost_var γs2 1%Qp (W64 84) ∗ ⌜v = W64 84⌝)
    )%I
    (λ i, True)%I
    True%I
    (λ n, ⌜n = 2%nat⌝)%I).
  all: try done.
  iIntros (buf_ch mu1 ch_buf_slice1 γ1 buff_params) "Hbuffchan".
  iNamed "Hbuffchan". iDestruct "HCh" as "#HCh".
  iDestruct "Hbuffchan" as "[Hclosedtok Hrest]". iNamed "Hrest".
  iModIntro.
  wp_auto.

  (* Allocate unbuffered sync channel for controlling coordination *)
  wp_apply (wp_NewChannelRef_base w64
    0 (* unbuffered *)
    true (* single party *)
    (λ i _, if decide (i = 0) then own_send_counter_frag (buff_params.(ch_γ w64)) 1 (1/2)%Qp else False)%I
    (λ (v: w64), True)%I
    (λ i, True)%I
    True%I
    (λ n, False)%I).
  all: try done.
  iIntros (sync_ch mu2 ch_buf_slice2 γ2 sync_params) "(%Hsyncparams & #Hsyncchan & Hctsync & HScsync & HRecvPermSync)".
  wp_auto.
  iNamed "HCh".
  iDestruct "Hsyncchan" as "(#musync  & #buffsync & %Hbuffsizesync & %Hbuffltsync & %Hmaxsync & #Hlocksync)".

  (* Ensure channels are valid (non-null) *)
  iDestruct (chan_pointsto_non_null w64 (buff_params.(ch_mu w64)) buff_params with "mu") as %HBufNonNull.
  assert (buff_params.(ch_loc w64) ≠ null) as HBufNotNull by (intro; congruence).
  iDestruct (chan_pointsto_non_null w64 (sync_params.(ch_mu w64)) sync_params with "musync") as %HSyncNonNull.
  assert (sync_params.(ch_loc w64) ≠ null) as HSyncNotNull by (intro; congruence).
  iPersist "syncCh" as "#syncCh".
  iPersist "bufCh" as "#bufCh".
  iDestruct "HSc" as "[HMainBuffSend HForkBuffSend]".
  iDestruct "Hparams" as "%".

  (* Fork worker thread to send 42 and 0 *)
  wp_apply (wp_fork with "[HScsync HForkBuffSend HSend42]").
  {

    replace sync_ch with (sync_params.(ch_loc w64)) by (subst;done).
    replace buf_ch with buff_params.(ch_loc w64) by (subst;done).
    (* Send 42 on buffered channel *)
    wp_auto.
    wp_apply ((wp_Channel__Send w64 buff_params 0%nat (1/2)%Qp (W64 42)) with "[HForkBuffSend HSend42 bufCh]"). all: try (subst;done).
    { 
      iFrame "#%". unfold P. iFrame. subst. simpl. iSplitL "";first done. 
      iLeft. iFrame. done.
    }
    iIntros "HSendDone".
    wp_auto.

    (* Send 0 on sync channel to join forked sender so we can safely close *)
    wp_apply ((wp_Channel__Send w64 sync_params 0%nat 1%Qp (W64 0)) with "[HScsync syncCh HSendDone]").
    all: try (subst;done).
    { iFrame "#". subst. simpl. unfold send_post. simpl. iDestruct "HSendDone" as "[_ Hsc]".
      iFrame.
      destruct decide.
      {
       iFrame. iPureIntro. done. 
      } 
      {
        done.
      } 
      }
    iIntros "_".
    wp_auto. done.
  }

  replace sync_ch with (sync_params.(ch_loc w64)) by (subst;done).
  replace buf_ch with buff_params.(ch_loc w64) by (subst;done).
  (* Send 84 on buffered channel *)
  wp_apply ((wp_Channel__Send w64 buff_params 0%nat (1/2)%Qp (W64 84)) with "[bufCh HMainBuffSend HSend84]"). all: try (subst;done).
  { iFrame "#". unfold P. subst. simpl. iFrame "%". iFrame. iSplitL "";first done.
    iRight. iFrame. done. 
  }
  iIntros "HSendDone84".
  wp_auto.

  (* Receive discard from sync channel *)
  wp_apply ((wp_Channel__ReceiveDiscardOk w64 sync_params 0%nat 1%Qp (λ n, False)%I) with "[HRecvPermSync]").
  {
    subst. simpl. iFrame "%".
    iFrame. iFrame "#". iPureIntro; done.
  }
  iIntros (v ok) "HRecvSync".
  wp_auto.
  iDestruct "HSendDone84" as "[_ Hscf]".

  destruct ok.
  - (* Proceed to close the buffered channel *)
    unfold recv_post.
    iDestruct "HRecvSync" as "[HMainBufSend HRcp]".
    wp_apply ((wp_Channel__Close w64 buff_params 2) with "[HMainBufSend Hscf Hclosedtok]").
    all: try (subst;done).
    { subst. simpl. iFrame. iFrame "#". iFrame "%". unfold send_post. 
      (* Put the send permissions back together *)
      destruct decide.
      {
      iCombine "HMainBufSend Hscf" as "Hcperm".
      iFrame. iPureIntro. done. 
      } 
      {
        done.
      } 
    }

    (* Receive both values from buffered channel *)
    wp_apply ((wp_Channel__Receive w64 buff_params 0%nat 1%Qp (λ n, ⌜n = 2%nat⌝)%I) with "[HRecvPerm]").
    { subst. simpl. iFrame. iFrame "#". iFrame "%". iPureIntro; done. }
    iIntros (v0 ok0) "HRecv1".
    wp_auto.

    destruct ok0.
    + iDestruct "HRecv1" as "[HP Hrecvperm]". unfold P.
      wp_apply ((wp_Channel__Receive w64 buff_params 1%nat 1%Qp (λ n, ⌜n = 2%nat⌝)%I) with "[Hrecvperm]").
        { 
          subst. simpl. iFrame. iFrame "#". iFrame "%". simpl. iPureIntro; done. 
        }
        iIntros (v1 ok1) "HRecv2".
        wp_auto.

        destruct ok1.
      *

       unfold recv_post.
      iDestruct "HRecv2" as "[HP2 HRecvPerm2]". unfold P. subst. simpl.
      (* Handle possible orderings of buffered results *)
       iDestruct "HP" as "[[Hg42 %H42]|[Hg84 %H84]]". 
       {
        iDestruct "HP2" as "[[Hg42' %H42']|[Hg84' %H84']]".  
        {
          subst v1. simpl. subst v0.   
          iCombine "Hg42 Hg42'" as "Hinvalid" gives "(%Hinvalid & %Hv)".
          done.  
        }
        {
         subst v1. simpl. subst v0. wp_auto. iApply "HΦ". done. 
        }
       }
       {
        iDestruct "HP2" as "[[Hg42' %H42']|[Hg84' %H84']]".  
        {
         subst v1. simpl. subst v0. wp_auto. iApply "HΦ". done. 
        }
        {
          subst v1. simpl. subst v0.   
          iCombine "Hg84 Hg84'" as "Hinvalid" gives "(%Hinvalid & %Hv)".
          done.  
        }
       }
      * wp_auto. iNamed "HRecv2". iNamed "HRecv2". unfold own_recv_perm.
        iNamed "HRcp". iDestruct "HRi" as "%". 
        iDestruct "HRcp" as "[HRcp Hoct]".
        subst n.
        (* We must receive 2 elements which we contracted through Ri, can't be closed here *)
        iDestruct (recv_counter_elem buff_params.(ch_γ w64)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
        done.
    + iNamed "HRecv1". iNamed "HRecv1". iDestruct "HRi" as "%". subst n.
      iDestruct (recv_counter_elem buff_params.(ch_γ w64)  with "[$Hrca] [$HRecFrag]") as "%Hag2".
      done.
  - (* We agreed not to close the sync channel in sync_params R *)
    iNamed "HRecvSync". iNamed "HRecvSync". done. 
Qed.

Definition hello_world_pred
(z: Z) (v: byte_string): iProp Σ :=
 (⌜ v = "hello world"%go ⌝%I) 
.

Lemma wp_SendMessage:
  {{{ is_pkg_init chan_spec_raw_examples }}}
    chan_spec_raw_examples @ "SendMessage" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start; wp_auto.

  (* Allocate an unbuffered sync channel with hello_world_pred *)
  wp_apply (wp_NewChannelRef_simple_unbuffered_sync
              byte_string
              hello_world_pred).
  iIntros (msg_ch_ptr mu ch_buf_slice ch_γ_names params) "HChan".
  iNamed "HChan". iNamed "HCh".
  wp_auto.

  (* Validate channel pointer is non-null *)
  iDestruct (chan_pointsto_non_null byte_string (params.(ch_mu byte_string)) params with "mu") as %HMsgNonNull.
  assert (params.(ch_loc byte_string) ≠ null) as HMsgNotNull by (intro; congruence).
  iPersist "messageChan" as "#messageChan".

  (* Fork off sender thread *)
  wp_apply (wp_fork with "[HSc]").
  {
    replace msg_ch_ptr with (params.(ch_loc byte_string)) by (subst;done).
    wp_auto.
    (* Send "hello world" on the message channel *)
    wp_apply ((wp_Channel__Send byte_string params 0%nat 1%Qp "hello world"%go) with "[messageChan HSc]").
    all: try (subst;done).
    { iFrame "#". iFrame "%". iFrame. unfold P. subst. simpl. iFrame. iPureIntro; done. }
    iIntros "_". wp_auto. done.
  }

  replace msg_ch_ptr with (params.(ch_loc byte_string)) by (subst;done).
  (* Main thread discards the received message *)
  wp_apply ((wp_Channel__ReceiveDiscardOk byte_string params 0%nat) with "[HRecvPerm]").
  {
    iFrame "#".
    unfold Q. subst. simpl. iFrame. iPureIntro; done.
  }
  iIntros (v ok) "HRecvPost".
  wp_auto.

  destruct ok.
  - (* Received successfully *)
    unfold recv_post, hello_world_pred.
    iDestruct "HRecvPost" as "[HP HRecvPerm]".
    unfold P. subst. simpl. iDestruct "HP" as "%HP".
    subst v.
    destruct bool_decide eqn:HDecide.
    + wp_auto. iApply "HΦ". done.
    + done.
  - (* We agreed not to close *)
    iNamed "HRecvPost". iNamed "HRecvPost". done.
Qed.

End proof.
