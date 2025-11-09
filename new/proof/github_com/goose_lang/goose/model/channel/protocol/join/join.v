Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel.protocol Require Export base.
From New.golang.theory Require Import chan.
From Perennial.algebra Require Import auth_set.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Import saved_prop.
From Perennial.algebra Require Import ghost_var.

Module join.

Record join_names :=
  {
    chan_name: chan_names;
    join_prop_name: gname;
    worker_names_name: gname;
    join_counter_name: gname;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!chan_protocolG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

Definition join (γ: join_names) (count:nat) (Q: iProp Σ): iProp Σ :=
  ghost_var γ.(join_counter_name) (DfracOwn (1/2)) count ∗
  ∃ Q', saved_prop_own γ.(join_prop_name) (DfracOwn (1/2)) Q' ∗ (Q' -∗ Q).

Definition worker (γ: join_names) (P: iProp Σ): iProp Σ :=
  ∃ γS, auth_set_frag γ.(worker_names_name) γS ∗
        saved_prop_own γS DfracDiscarded P.

Definition own_join (γ : join_names) (ch : loc) (cap: nat) : iProp Σ :=
  ∃ (workerQ: iProp Σ) (sendNames: gset gname) s count,
    "Hch" ∷ own_channel ch cap s γ.(chan_name) ∗
    "joinQ" ∷ saved_prop_own γ.(join_prop_name) (DfracOwn (1/2)) workerQ ∗
    "%HnumWaiting" ∷ ⌜size sendNames = count⌝ ∗
    "Hjoincount" ∷ ghost_var γ.(join_counter_name) (DfracOwn (1/2)) count ∗
    "HsendNames_auth" ∷ auth_set_auth γ.(worker_names_name) sendNames ∗
    "HworkerQ_wand" ∷ ((([∗ set] γS ∈ sendNames,
                          ∃ P, saved_prop_own γS DfracDiscarded P ∗ ▷ P) -∗
                        ▷ workerQ) ∨ (ghost_var γ.(join_counter_name) (DfracOwn (1/2)) count)) ∗
    match s with
    | chan_rep.Buffered msgs =>
        [∗ list] _ ∈ msgs, ∃ P, worker γ P ∗ P
    | chan_rep.SndPending v =>
        ∃ P, worker γ P ∗ P
    | chan_rep.SndCommit v =>
        ∃ P, worker γ P ∗ P
    | chan_rep.Idle | chan_rep.RcvPending | chan_rep.RcvCommit => True
    | _ => False
    end.

Definition is_join (γ : join_names) (ch : loc) (cap : nat) : iProp Σ :=
  is_channel ch cap γ.(chan_name) ∗
  inv nroot ("Hbar" ∷ own_join γ ch cap)%I.

#[global] Instance is_join_persistent ch γ cap : Persistent (is_join γ ch cap) := _.

#[global] Instance worker_proper : Proper ((=) ==> (≡) ==> (≡)) worker.
Proof.
  intros γ _ <- Q1 Q2 Heq.
  rewrite /worker.
  setoid_rewrite Heq; done.
Qed.

Lemma join_mono γ Q Q' n :
  (Q -∗ Q') -∗ (join γ n Q -∗ join γ n Q').
Proof.
  iIntros "Hwand Hrecv".
  unfold join.
  iDestruct "Hrecv" as "[HJoin Hrecv]".
  iDestruct "Hrecv" as (Q'') "[Hsaved Hwand2]".
  iFrame "Hsaved HJoin".
  iIntros "H". iApply "Hwand". iApply "Hwand2". iFrame.
Qed.

Lemma own_join_alloc_unbuff (ch : loc) (γch : chan_names):
  is_channel ch 0 γch -∗
  own_channel ch 0 chan_rep.Idle γch ={⊤}=∗
  ∃ γ,  is_join γ ch 0 ∗ join γ 0 emp.
Proof.
  iIntros "Hchan_info Hchan_own".
  iMod (saved_prop_alloc emp (DfracOwn 1)) as (γjoin_prop) "Hjoin_prop".
  { done. }
  iMod (auth_set_init (A:=gname)) as (γworker_names) "Hworker_names".
  iMod (ghost_var_alloc 0) as (γjoin_counter) "Hjoin_counter".
  set (γ := {|
    chan_name := γch;
    join_prop_name := γjoin_prop;
    worker_names_name := γworker_names;
    join_counter_name := γjoin_counter;
  |}).
  iDestruct "Hjoin_counter" as "[Hjc1 Hjc2]".
  iDestruct "Hjoin_prop" as "[Hjp1 Hjp2]".
   iMod (inv_alloc nroot _ (own_join γ ch 0) with "[$Hjc1 $Hjp1 $Hworker_names $Hchan_own]") as "#Hinv".
  { iNext. unfold own_join.  iFrame. simpl.
    iFrame "#%".
    iSplitL "". {
     iPureIntro. done. }
    iSplitL "".
    {
    iLeft.
    rewrite big_sepS_empty.
    done.
  }
  done.
    }
iModIntro.
iExists γ.
  iFrame.
  iSplitL "". { done. }
  done.
Qed.

Lemma own_join_alloc_buff (ch : loc) (γch : chan_names) (cap:nat) :
  is_channel ch cap γch -∗
  own_channel ch cap (chan_rep.Buffered []) γch ={⊤}=∗
  ∃ γ, is_join γ ch cap ∗  join γ 0 emp.
Proof.
   iIntros "Hchan_info Hchan_own".
  iMod (saved_prop_alloc emp (DfracOwn 1)) as (γjoin_prop) "Hjoin_prop".
  { done. }
  iMod (auth_set_init (A:=gname)) as (γworker_names) "Hworker_names".
  iMod (ghost_var_alloc 0) as (γjoin_counter) "Hjoin_counter".
  set (γ := {|
    chan_name := γch;
    join_prop_name := γjoin_prop;
    worker_names_name := γworker_names;
    join_counter_name := γjoin_counter;
  |}).
  iDestruct "Hjoin_counter" as "[Hjc1 Hjc2]".
  iDestruct "Hjoin_prop" as "[Hjp1 Hjp2]".
   iMod (inv_alloc nroot _ (own_join γ ch cap) with "[$Hjc1 $Hjp1 $Hworker_names $Hchan_own]") as "#Hinv".
  { iNext. unfold own_join.  iFrame. simpl.
    iFrame "#%".
    iSplitL "". {
     iPureIntro. done. }
    iSplitL "".
    {
    iLeft.
    rewrite big_sepS_empty.
    done.
  }
  done.
    }
iModIntro.
iExists γ.
  iFrame.
  iSplitL "". { done. }
  done.
  Qed.


Lemma join_alloc_worker γ ch cap Q P count :
  £ 1 -∗
  is_join γ ch cap -∗
  join γ count Q ={⊤}=∗
  join γ (S count) (Q ∗ P) ∗ worker γ P.
Proof.
  iIntros "Hlc (#Hisjoin & Hjoininv) Hjoin".
  iInv "Hjoininv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iNamed "Hbar".
  unfold join.
  iDestruct "Hjoin" as "[Hcount Hrest]".
  iNamed "Hrest".
  iDestruct "Hrest" as "[Hsp HQimp]".
  iDestruct (saved_prop_agree with "joinQ Hsp") as "#HQeq".
  iMod (saved_prop_update_halves (Q ∗ P) with "joinQ Hsp") as "[joinQ worker_prop]".
  iDestruct (ghost_var_agree with "Hjoincount Hcount") as %Hcount_eq.
  assert (count = count0) as -> by done.
  iMod (ghost_var_update_halves (S count0) with "Hjoincount Hcount") as "[Hjoincount Hjoincount2]".
  iMod (saved_prop_alloc_cofinite sendNames P DfracDiscarded) as (γS) "[%Hfresh #HworkerS]".
  { done. }
  iMod (auth_set_alloc γS with "HsendNames_auth") as "[HsendNames_auth HγS_frag]".
  { set_solver. }
  iDestruct "HworkerQ_wand" as "[HworkerQ_wand|H2]".
  {
    iMod ("Hinv_close" with "[Hch Hbar HworkerQ_wand HQimp joinQ Hjoincount HsendNames_auth]").
    {
      iModIntro. iFrame. iFrame "#".
      iSplitL "".
      {
        iPureIntro.
        rewrite size_union.
        { rewrite size_singleton. rewrite HnumWaiting. done. }
        { set_solver. }
      }
      {
        iLeft.
        iIntros "Hset".
        rewrite big_sepS_union.
        {
          iDestruct "Hset" as "[Hsing Hset]".
          iApply "HworkerQ_wand" in "Hset".
          iRewrite "HQeq" in "Hset".
          rewrite big_sepS_singleton.
          iNamed "Hsing".
          iDestruct "Hsing" as "[Hsingsp Hx]".
          iDestruct (saved_prop_agree with "Hsingsp HworkerS") as "Hagree".
          iNext.
          iRewrite "Hagree" in "Hx".
          iFrame.
          iApply "HQimp" in "Hset".
          done.
        }
        { set_solver. }
      }
    }
    {
      iModIntro. iFrame "#". iFrame.
      iIntros "H". done.
    }
  }
  {
    iCombine "H2 Hjoincount" as "H2".
    iDestruct (ghost_var_valid_2 with "Hjoincount2 H2") as "[%Hvalid _]".
    done.
  }
Qed.

Lemma wp_worker_send γ ch cap P :
  {{{ is_join γ ch cap ∗
      worker γ P ∗
      P }}}
    chan.send #t #ch #(default_val V)
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#Hjoin & HWorker & HP) HΦ".
  rewrite /worker /is_join.
  iNamed "HWorker".
  iDestruct "HWorker" as "[Hfrag Hprop]".
  iDestruct "Hjoin" as "[#Hch #Hinv]".
  iApply (chan.wp_send ch cap (default_val V) γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iDestruct "Hch" as "Hch1".
  iNamed "Hinv_open".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  unfold own_join.
  iNamed "Hbar".
  iExists s. iFrame "Hch".
  iNamed "Hbar".
  destruct s; try done.
  - destruct (decide (length buff < cap)%Z).
    + iNext. iIntros "Hoc".
      iMod "Hmask".
      iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand Hbar HP Hprop Hfrag]") as "_".
      {
        iNext. iFrame.
        iSplitL ""; first done.
        rewrite big_sepL_app.
        iFrame. simpl. done.
      }
      iModIntro. iApply "HΦ". done.
    + iModIntro. done.
  - iNext. iIntros "Hoc".
    iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand Hbar HP Hprop Hfrag]") as "_".
    {
      iNext. iFrame.
      iSplitL ""; first done.
      iFrame.
    }
    {
      iModIntro.
      unfold send_au_inner.
      iInv "Hinv" as "Hinv_open2" "Hinv_close2".
      iMod (lc_fupd_elim_later with "Hlc2 Hinv_open2") as "Hinv_open2".
      iNamed "Hinv_open2".
      iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"].
      iNamed "Hbar".
      iNext. iExists s. iFrame "Hch".
      destruct s; try done.
      - iIntros "Hoc". iMod "Hmask2".
        iMod ("Hinv_close2" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand Hbar]") as "_".
        {
          iNext. iFrame.
          iSplitL ""; first done.
          iFrame.
        }
        iModIntro. iApply "HΦ". done.
    }
  - iNext. iIntros "Hoc". iMod "Hmask".
    iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand Hbar HP Hfrag Hprop]") as "_".
    {
      iNext. iFrame.
      iSplitL ""; first done.
      iFrame.
    }
    iModIntro. iApply "HΦ". done.
Qed.

Lemma wp_join_receive γ ch cap n Q :
  {{{ is_join γ ch cap ∗
      join γ (S n) Q }}}
    chan.receive #t #ch
  {{{ v, RET (v, #true); join γ n Q }}}.
Proof.
  iIntros (Φ) "(#Hjoin & HJoin & HJoinQ) HΦ".
  iNamed "HJoinQ".
  iDestruct "HJoinQ" as "[HspQ HQimp]".
  rewrite /join /is_join.
  iDestruct "Hjoin" as "[#Hch #Hinv]".
  iApply (chan.wp_receive ch cap γ.(chan_name) with "[$Hch]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv".
  iDestruct "Hch" as "Hch1".
  iNamed "Hinv_open".
  iNamed "Hbar".
  iNamed "Hbar".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iFrame.
  destruct s; try done.
  - destruct buff as [|v_rcv msgs'] eqn:Hmsgs; simpl; try easy.
    iDestruct "Hbar" as "[Hworker_P HPs]".
    iNamed "Hworker_P".
    iDestruct "Hworker_P" as "[Hworker_P HP]".
    iIntros "Hoc".
    iMod "Hmask".
    iDestruct (ghost_var_agree with "Hjoincount HJoin") as %Hcount_eq.
    assert (count = S n) as -> by done.
    iMod (ghost_var_update_halves n with "Hjoincount HJoin") as "[Hjoincount HJoin_new]".
    unfold worker.
    iDestruct "Hworker_P" as (γS) "[Hfrag Hprop]".
    iDestruct (auth_set_elem with "HsendNames_auth Hfrag") as %HγS_in_names.
    iMod ((auth_set_dealloc γ.(worker_names_name) sendNames γS) with "[$HsendNames_auth $Hfrag]") as "HsendNames_auth".
    iDestruct "HworkerQ_wand" as "[HworkerQ_wand|H2]".
    {
      iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand HPs HP Hprop]") as "_".
      {
        iNext. unfold own_join. iExists workerQ. iExists (sendNames ∖ {[γS]}). iFrame.
        iFrame "%".
        iSplitL "".
        {
          iPureIntro.
          rewrite size_difference.
          { rewrite HnumWaiting. rewrite size_singleton. lia. }
          set_solver.
        }
        iFrame.
        iLeft. iFrame.
        iIntros "H". iApply "HworkerQ_wand".
        iApply (big_sepS_delete _ _ γS).
        { auto. }
        iFrame.
      }
      iApply "HΦ".
      iModIntro. iFrame.
    }
    {
      iCombine "H2 Hjoincount" as "H2".
      iDestruct (ghost_var_valid_2 with "HJoin_new H2") as "[%Hvalid _]".
      done.
    }
  - iMod "Hmask".
    iIntros "Hoc".
    iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand]") as "_".
    {
      iNext. iFrame. done.
    }
    iModIntro.
    iInv "Hinv" as "Hinv_open" "Hinv_close".
    iMod (lc_fupd_elim_later with "Hlc2 Hinv_open") as "Hinv_open".
    iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask2"].
    iDestruct "Hbar" as "_".
    iNamed "Hinv_open".
    iNamed "Hbar".
    iNext. iFrame.
    destruct s; try done.
    + iIntros "Hoc".
      iMod "Hmask2".
      iDestruct (ghost_var_agree with "Hjoincount HJoin") as %Hcount_eq.
      assert (count0 = S n) as -> by done.
      iMod (ghost_var_update_halves n with "Hjoincount HJoin") as "[Hjoincount HJoin_new]".
      unfold worker. iNamed "Hbar".
      iDestruct "Hbar" as "[Hy HP]".
      iDestruct "Hy" as (γS0) "[Hfrag Hprop]".
      iDestruct (auth_set_elem with "HsendNames_auth Hfrag") as %HγS_in_names.
      iMod ((auth_set_dealloc γ.(worker_names_name) sendNames0 γS0) with "[$HsendNames_auth $Hfrag]") as "HsendNames_auth".
      iDestruct "HworkerQ_wand" as "[HworkerQ_wand|H2]".
      {
        iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand HP Hprop]") as "_".
        {
          iNext. unfold own_join. iExists workerQ0. iExists (sendNames0 ∖ {[γS0]}). iFrame.
          iFrame "%".
          iSplitL "".
          {
            iPureIntro.
            rewrite size_difference.
            { rewrite HnumWaiting0. rewrite size_singleton. lia. }
            set_solver.
          }
          iSplitL "HworkerQ_wand HP Hprop".
          {
            iLeft.
            iIntros "H". iApply "HworkerQ_wand".
            iApply (big_sepS_delete _ _ γS0).
            { done. }
            iFrame.
          }
          done.
        }
        iModIntro. iApply "HΦ". iFrame.
      }
      {
        iCombine "H2 Hjoincount" as "H2".
        iDestruct (ghost_var_valid_2 with "HJoin_new H2") as "[%Hvalid _]".
        done.
      }
  - iNamed "Hbar".
    iDestruct "Hbar" as "[Hworker_P HPs]".
    iNamed "Hworker_P".
    iDestruct "Hworker_P" as "[Hworker_P HP]".
    iIntros "Hoc".
    iMod "Hmask".
    iDestruct (ghost_var_agree with "Hjoincount HJoin") as %Hcount_eq.
    assert (count = S n) as -> by done.
    iMod (ghost_var_update_halves n with "Hjoincount HJoin") as "[Hjoincount HJoin_new]".
    unfold worker.
    iDestruct (auth_set_elem with "HsendNames_auth Hworker_P") as %HγS_in_names.
    iMod ((auth_set_dealloc γ.(worker_names_name) sendNames γS) with "[$HsendNames_auth $Hworker_P]") as "HsendNames_auth".
    iDestruct "HworkerQ_wand" as "[HworkerQ_wand|H2]".
    {
      iMod ("Hinv_close" with "[Hoc joinQ Hjoincount HsendNames_auth HworkerQ_wand HP HPs]") as "_".
      {
        iNext. unfold own_join. iExists workerQ. iExists (sendNames ∖ {[γS]}). iFrame.
        iFrame "%".
        iSplitL "".
        {
          iPureIntro.
          rewrite size_difference.
          { rewrite HnumWaiting. rewrite size_singleton. lia. }
          set_solver.
        }
        iFrame.
        iSplitR "".
        {
          iLeft.
          iIntros "H". iApply "HworkerQ_wand".
          iApply (big_sepS_delete _ _ γS).
          { auto. }
          iFrame.
          done.
        }
        { done. }
      }
      iApply "HΦ".
      iModIntro. iFrame.
    }
    iCombine "H2 Hjoincount" as "H2".
    iDestruct (ghost_var_valid_2 with "HJoin_new H2") as "[%Hvalid _]".
    done.
Qed.

Lemma join_finish γ ch cap Q :
  £ 1 -∗
  is_join γ ch cap -∗
  join γ 0 Q ={⊤}=∗
  ▷ Q.
Proof.
  iIntros "Hlc (#Hjoinch & #Hjoininv) Hjoin".
  rewrite /is_join /join.
  iDestruct "Hjoin" as "[Hcount Hrest]".
  iDestruct "Hrest" as (Q') "[Hsp HQimp]".
  iInv "Hjoininv" as "Hinv_open" "Hinv_close".
  iNamed "Hinv_open".
  iMod (lc_fupd_elim_later with "Hlc Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  iNamed "Hbar".
  iDestruct (ghost_var_agree with "Hjoincount Hcount") as %Hcount_eq.
  assert (count = 0) as -> by done.
  replace sendNames with (∅: gset gname).
  {
    iDestruct (saved_prop_agree with "joinQ Hsp") as "#HQeq".
    rewrite big_sepS_empty.
    iDestruct "HworkerQ_wand" as "[HworkerQ_wand|H2]".
    {
      iMod ("Hinv_close" with "[joinQ Hch Hjoincount HsendNames_auth Hcount Hbar]").
      {
        iNext.
        iFrame. iPureIntro. set_solver.
      }
      iModIntro. iApply "HQimp".
      iAssert (emp)%I as "Hemp"; iFrame.
      iDestruct ("HworkerQ_wand" with "Hemp") as "Hnew".
      iNext.
      iRewrite "HQeq" in "Hnew". iFrame.
    }
    {
      iCombine "H2 Hjoincount" as "H2".
      iDestruct (ghost_var_valid_2 with "Hcount H2") as "[%Hvalid _]".
      done.
    }
  }
  {
    rewrite size_empty_iff in HnumWaiting. set_solver.
  }
Qed.

End proof.
End join.

#[global] Typeclasses Opaque join.is_join join.join join.worker.
