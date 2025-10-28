
Require Import New.proof.proof_prelude.
From iris.base_logic Require Export lib.ghost_var mono_nat.
From iris.algebra Require Import dfrac_agree mono_list.
From New.proof.github_com.goose_lang.goose.model.channel Require Export auth_set.
From iris.base_logic Require Import ghost_map.
From iris.base_logic.lib Require Import saved_prop.
From iris.algebra Require Import excl.
From New.proof Require Import sync.


Section proof.
  Context `{hG: heapGS Σ} `{!ffi_semantics _ _}.
  Context {go_ctx: GoContext}.
End proof.

Module join.



Class joinG Σ := JoinG {
    join_saved_propG :: savedPropG Σ;
    join_auth_setG :: auth_setG Σ gname;
    join_counterG :: ghost_varG Σ nat;
    join_activeG :: ghost_varG Σ bool;
  }.

Definition joinΣ: gFunctors :=
  #[ savedPropΣ; auth_setΣ gname; ghost_varΣ nat;ghost_varΣ bool ].

#[global] Instance subG_joinG Σ : subG joinΣ Σ → joinG Σ.
Proof. solve_inG. Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!joinG Σ}.
Context `{!syncG Σ}.

Record wg_join_names := {
    wg_gamma : WaitGroup_names;
     join_prop_name: gname;
    worker_names_name: gname;
      join_counter_name: gname;
      join_active_name: gname;
}.

Implicit Type γj : wg_join_names.

(** Core predicates matching the specification *)


Definition Worker_wg γj (P : iProp Σ) : iProp Σ :=
  ∃ γS, auth_set_frag γj.(worker_names_name) γS ∗
        saved_prop_own γS DfracDiscarded P.

Definition join_wg γj (Q : iProp Σ) (n: nat) (active: bool): iProp Σ :=
  (if active then own_WaitGroup_wait_token γj.(wg_gamma) else True%I) ∗
  ghost_var γj.(join_active_name) (1/2) active ∗
  ghost_var γj.(join_counter_name) (1/2) n ∗
  ∃ Q', saved_prop_own γj.(join_prop_name) (DfracOwn (1/2)) Q' ∗ (Q' -∗ Q).


(** Invariant for join abstraction *)
Definition own_wg_join (wg : loc)   γj : iProp Σ :=
  ∃ (workerQ : iProp Σ) (workerNames : gset gname) (remaining_workers: nat) (spawned_workers: nat)
    (waiter_active: bool)
  ,
    "Hwg" ∷ own_WaitGroup γj.(wg_gamma) (W32 remaining_workers) ∗
    "HnoWaiters" ∷
      (if waiter_active then own_WaitGroup_waiters γj.(wg_gamma) (W32 1)
       else if (remaining_workers =? 0%nat ) then  (own_WaitGroup_waiters γj.(wg_gamma) (W32 0)) else True%I)  ∗
    "joinQ" ∷ saved_prop_own γj.(join_prop_name) (DfracOwn (1/2)) workerQ ∗
    "Hcounter" ∷ ghost_var γj.(join_counter_name) (1/2) spawned_workers ∗
    "Hactive" ∷ ghost_var γj.(join_active_name) (1/2) waiter_active ∗

    "HworkerNames_auth" ∷ auth_set_auth γj.(worker_names_name) workerNames ∗
    "%HnumWorkers" ∷ ⌜size workerNames = remaining_workers⌝ ∗
    "%HnumWorkersPos" ∷ ⌜0%nat ≤ remaining_workers ≤ spawned_workers⌝ ∗
    "HworkerQ_wand" ∷ ((([∗ set] γS ∈ workerNames,
                        ∃ P, saved_prop_own γS DfracDiscarded P ∗ ▷ P) -∗
                      ▷ workerQ) ∨  ghost_var γj.(join_counter_name) (1/2) spawned_workers   ) .

Definition is_wg_join (wg : loc) γj N : iProp Σ :=
  is_WaitGroup wg γj.(wg_gamma) (N.@"wg") ∗
  inv (N.@"wg_join")  ( (own_wg_join wg γj)).

#[global] Instance is_wg_join_persistent wg γj N:
  Persistent (is_wg_join wg γj N) := _.

(** ** Initialization *)

Lemma init_wg_join wg_ptr N :
  wg_ptr ↦ (default_val sync.WaitGroup.t) ={⊤}=∗
  ∃ γj,
  is_wg_join wg_ptr γj N ∗ join_wg γj True%I 0 false.
Proof.
  iIntros "H".
  iMod (init_WaitGroup (N.@"wg") with "H") as (γ) "[#Hwg [Hown Hwaiters]]".


  iMod (saved_prop_alloc True%I 1) as (join_prop_name) "HQ".
  {
    done.
  }
  iDestruct "HQ" as "[HQ1 HQ2]".
   iMod (auth_set_init (A:=gname)) as (worker_names_name) "Hworker_names".
     iMod (ghost_var_alloc 0%nat) as (join_counter_name) "[Hjoin_counter1 Hjoin_counter2]".
     iMod (ghost_var_alloc false) as (join_active_name) "[Hjoin_active1 Hjoin_active2]".

  
  set (γj := {| wg_gamma := γ;
                join_prop_name := join_prop_name;
                worker_names_name := worker_names_name;
                join_counter_name := join_counter_name;
                join_active_name := join_active_name

             |}).



  iExists γj.
  unfold is_wg_join.
   iMod ((inv_alloc (N.@"wg_join")  ⊤  ((own_wg_join wg_ptr γj))) with
          "[Hown Hwaiters  HQ1 Hworker_names Hjoin_counter1 Hjoin_active1]") as "Hinv".
   {
     iNext.
     unfold own_wg_join.
    iExists True%I.
     iExists ∅.
     iExists 0%nat. iExists 0%nat.
     iExists false.
     iFrame. rewrite size_empty.
     iSplitL "";first done.
     iSplitL "";first done.

     rewrite big_sepS_empty.
     iLeft.
      done.
   }
  iModIntro.

  iFrame.
  simpl.
 iSplitR "";first done.  done.
Qed.

Lemma wp_WaitGroup__Add_join (wg : loc) γj Q P N n :
  (S n) < 2 ^ 31 ->
  {{{ is_pkg_init sync ∗ is_wg_join wg γj N ∗
      £ 1 ∗  £ 1 ∗
      join_wg γj Q n false }}}
    wg @ (ptrT.id sync.WaitGroup.id) @ "Add" #(W64 1)
  {{{ RET #();  join_wg γj (Q ∗ P) (S n) false ∗ Worker_wg γj P }}}.
  intros Hlt.
  iIntros (Φ).
   iIntros "(#Hiswg & #Hinv & Hlc & Hlc2 & Hjoin)".
   iIntros "Hj".
   unfold is_wg_join.
   iDestruct "Hinv" as "[H1 H2]".

    wp_apply (wp_WaitGroup__Add with "[$H1]").
      iInv (N.@"wg_join")  as "Hown" "Hclose".
   iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".





  iNamed "Hown".
  unfold join_wg.
  iDestruct "Hjoin" as "[Hctr HQ]".



  (* Allocate new worker name and saved prop for P *)
  iMod (saved_prop_alloc_cofinite workerNames P DfracDiscarded) as (γS) "[%HγS_fresh HPS]".
  {
   done.
  }
  iMod (saved_prop_persist with "HPS") as "#HPS".
            iMod (lc_fupd_elim_later with "Hlc2 Hj") as "Hj".
  iDestruct "HQ" as "(HQ' & Hctr' & HQw)".
  iDestruct (ghost_var_agree with "[$Hcounter] [$Hctr']") as "%Hctr".
  iMod (ghost_var_update_2 (S n) with "Hctr' Hcounter") as "[Hctr' Hjoincount]".
  {
     rewrite Qp.half_half.
    reflexivity.
  }

  destruct waiter_active.
  {

  iDestruct (ghost_var_agree with "[$Hactive] [$HQ']") as "%Hf".
  done.
  }
  {


    iNamed "Hj".

    iMod (auth_set_alloc γS with "HworkerNames_auth") as "[HworkerNames_auth HγS_frag]".
  { set_solver. }
  iNamed "HQw".
  iDestruct "HQw" as "[HQ HQw]".



  iDestruct (saved_prop_agree with "[$joinQ] [$HQ]") as "#Heq".
  iMod (saved_prop_update_2 (Q ∗ P)%I with "[$joinQ] [$HQ]") as "[joinQ HQ'new]".
  {
    rewrite Qp.half_half.
    reflexivity.
  }


     iApply fupd_mask_intro.
  {
    solve_ndisj.
  }
   iIntros "H".

  (* First, close the wg_join invariant with updated state *)
  iFrame.
  iSplitL "". { iPureIntro. word.
                }
  destruct ( remaining_workers).
  {
    iSplitL "HnoWaiters".
    {
      iRight. done.
    }
    iIntros "Hnor".
    iIntros "Howg".
    iMod "H".
    iDestruct "HworkerQ_wand" as "[HworkerQ_wand|Hbad]".
    {



iMod ("Hclose" with "[Howg joinQ Hctr' Hnor Hactive HworkerNames_auth HworkerQ_wand HQw]") as "_".
{
  iNext.
  unfold own_wg_join.
  iExists (Q ∗ P)%I.
  iExists  ({[γS]} ∪ workerNames).
  iFrame. iExists 1%nat.
  iDestruct "Hnor" as "[%Hf|H3]".
  {
done.
  }
  simpl.

  iFrame.  iSplitL "";first done.
  iSplitL "".
  { iPureIntro. rewrite size_union. { rewrite size_singleton. rewrite HnumWorkers. done. }
    { set_solver. }
    }
    iSplitL "". { word. }
  iLeft.
  iIntros "HQs".
   rewrite big_sepS_union.
        {
          iDestruct "HQs" as "[Hsing Hset]".
          rewrite big_sepS_singleton. iNamed "Hsing".
          iDestruct "Hsing" as "[Hsingsp Hx]".
           iApply "HworkerQ_wand" in "Hset".
          iRewrite "Heq" in "Hset".



          iDestruct (saved_prop_agree with "Hsingsp HPS") as "Hagree".
          iNext.
          iRewrite "Hagree" in "Hx".
          iFrame.

          iApply "HQw" in "Hset".
          done.
        }
        {
          set_solver.
        }
        }
        {
          iModIntro. iApply "Hj".
          iFrame "#". iFrame.
          iIntros "H". done.
        }
        }
        {
          iCombine "Hbad" "Hjoincount" as "Hbad".
              iDestruct (ghost_var_valid_2 with "Hctr' Hbad") as "[%Hvalid _]".
              done.


        }
        }
        {
           iSplitL "HnoWaiters".
    {
      iLeft. iPureIntro. word.
    }

    iIntros "Hnor".
    iIntros "Howg".
    iMod "H".
          iFrame.
           iDestruct "HworkerQ_wand" as "[HworkerQ_wand|Hbad]".
    {



iMod ("Hclose" with "[Howg joinQ Hctr' Hnor Hactive HworkerNames_auth HworkerQ_wand HQw]") as "_".
{
  iNext.
  unfold own_wg_join.
  iExists (Q ∗ P)%I.
  iExists  ({[γS]} ∪ workerNames).
  iFrame. iExists (S (S n0)) .
  iDestruct "Hnor" as "[%Hf|H3]".
  {
iFrame.
replace ( (w32_word_instance.(word.add) (W32 (S n0)) (W32 (sint.Z (W64 1))))
) with ( (W32 (S (S n0))) ) by word.
iFrame.
simpl.


  iFrame.  iSplitL "";first done.
  iSplitL "".
  { iPureIntro. rewrite size_union. { rewrite size_singleton. rewrite HnumWorkers. done. }
    { set_solver. }
    }
    iSplitL "". { word. }
  iLeft.
  iIntros "HQs".
   rewrite big_sepS_union.
        {
          iDestruct "HQs" as "[Hsing Hset]".
          rewrite big_sepS_singleton. iNamed "Hsing".
          iDestruct "Hsing" as "[Hsingsp Hx]".
           iApply "HworkerQ_wand" in "Hset".
          iRewrite "Heq" in "Hset".



          iDestruct (saved_prop_agree with "Hsingsp HPS") as "Hagree".
          iNext.
          iRewrite "Hagree" in "Hx".
          iFrame.

          iApply "HQw" in "Hset".
          done.
        }
        {
          set_solver.
        }
        }
        {
          iFrame.
replace ( (w32_word_instance.(word.add) (W32 (S n0)) (W32 (sint.Z (W64 1))))
) with ( (W32 (S (S n0))) ) by word.
iFrame.
simpl.


  iFrame.  iSplitL "";first done.
  iSplitL "".
  { iPureIntro. rewrite size_union. { rewrite size_singleton. rewrite HnumWorkers. done. }
    { set_solver. }
    }
    iSplitL "". { word. }
  iLeft.
  iIntros "HQs".
   rewrite big_sepS_union.
        {
          iDestruct "HQs" as "[Hsing Hset]".
          rewrite big_sepS_singleton. iNamed "Hsing".
          iDestruct "Hsing" as "[Hsingsp Hx]".
           iApply "HworkerQ_wand" in "Hset".
          iRewrite "Heq" in "Hset".



          iDestruct (saved_prop_agree with "Hsingsp HPS") as "Hagree".
          iNext.
          iRewrite "Hagree" in "Hx".
          iFrame.

          iApply "HQw" in "Hset".
          done.
        }
        {
          set_solver.
        }
        }
        }
        {
         iModIntro. iApply "Hj".
         iFrame. 
         iFrame "#".
         iIntros "H". done.
        }
}
{

          iCombine "Hbad" "Hjoincount" as "Hbad".
              iDestruct (ghost_var_valid_2 with "Hctr' Hbad") as "[%Hvalid _]".
              done.


        }
        }
        }
Qed.




Lemma wp_WaitGroup__Wait_join (wg : loc) γj N (n:nat) Q :
  ( n%Z >? 0 ) ->
  n < 2 ^ 31 ->
  ∀ Φ,
  is_pkg_init sync ∗ is_wg_join wg γj N -∗
  £ 1 -∗
  join_wg γj Q n true -∗
  (▷ Q -∗ Φ #()) -∗
  WP wg @ (ptrT.id sync.WaitGroup.id) @ "Wait" #() {{ Φ }}.
Proof.
  intros Hngt.
  intros Hlt.
  iIntros (Φ) "[#Hinit [#Hiswg #Hinv]] Hlc Hjoin HΦ".

  iDestruct "Hjoin" as "[Hctr_out HQ]".
  replace ( n >? 0 ) with true.
  {
     iDestruct "HQ" as "(Hactive' & Hrest)".
     iDestruct "Hrest" as "(Hctr & HQ)".
  iDestruct "HQ" as (HQ') "(HQ' & HQw)".
  wp_apply ((wp_WaitGroup__Wait wg n) with "[$Hinit $Hiswg $Hctr_out]").


  (* Allocate wait token *)
  iInv "Hinv" as "Hown" "Hclose".
   iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
  iDestruct (ghost_var_agree with "[$Hactive'] [$Hactive]") as "%Hf".
  iDestruct (ghost_var_agree with "[$Hcounter] [$Hctr]") as "%Hctr".
  iDestruct (saved_prop_agree with "HQ' joinQ") as "#Hlt".
  subst waiter_active.
  iDestruct "HworkerQ_wand" as "[Hgood|Hbad]".
  {




    iApply fupd_mask_intro.
  {
    solve_ndisj.
  }


  iIntros "Hmask".
  iFrame.
  iIntros "%Hsz".
  iIntros "Hog".
  iMod "Hmask".


  iMod ("Hclose" with "[HnoWaiters Hog joinQ Hctr Hactive Hcounter HworkerNames_auth]") as "_".
  {
    iNext. iFrame.
    iSplitL ""; first done.
    iSplitL ""; first done.
    iRight. subst n.
    done.
}

     iApply fupd_mask_intro.
  {
    solve_ndisj.
  }
  iIntros "Hmask'".
  iIntros "H".

  iFrame.
  iApply "HΦ".
  assert (remaining_workers = 0%nat) by word.
  subst remaining_workers.
  assert (workerNames = ∅) as ->.
  {  apply size_empty_inv in H. set_solver. }
  rewrite big_sepS_empty.
  iApply "Hgood" in "Hmask".

iNext.
iRewrite "Hlt" in "HQw".
iApply "HQw" in "Hmask".
done.
}
{

          iCombine "Hbad" "Hctr" as "Hbad".
              iDestruct (ghost_var_valid_2 with "Hcounter Hbad") as "[%Hvalid _]".
              done.

}
}
{
  destruct n.
  {
    done.
  }
  done.
  }
  Qed.



Lemma wp_WaitGroup__Done_join (wg : loc) γj N P :
  ∀ Φ,
  is_pkg_init sync ∗ is_wg_join wg γj N -∗
  £ 1 -∗
  Worker_wg γj P -∗
  P -∗
  Φ #() -∗
  WP wg @ (ptrT.id sync.WaitGroup.id) @ "Done" #() {{ Φ }}.
Proof.
  iIntros (Φ) "[#Hinit [#Hiswg #Hinv]] Hlc Hjoin HP HΦ".

  wp_apply (wp_WaitGroup__Done with "[$Hinit $Hiswg]").

  
  iInv "Hinv" as "Hown" "Hclose".
  iNamed "Hown".
   iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".
Admitted.

Lemma prepare_join_wait wg γj N Q (n:nat) :
  n > 0 →
  is_wg_join wg γj N -∗
  £ 1 -∗
  £ 1 -∗

  join_wg γj Q n false ={⊤}=∗
  join_wg γj Q n true.
Proof.
  iIntros (Hgt) "#Hinv Hlc Hlc2 Hjoin".
  iDestruct "Hinv" as "[#Hiswg #Hinv_wg]".
  unfold join_wg.
  iDestruct "Hjoin" as "(_ & Hactive_half & Hctr & HQ)".


  iInv "Hinv_wg" as "Hown" "Hclose".
 iMod (fupd_mask_subseteq (↑ (N.@"wg"))) as "Hmask".
  { solve_ndisj. }
  iMod (lc_fupd_elim_later with "Hlc Hown") as "Hown".
  iNamed "Hown".

  (* Agreement on active flag *)
  iDestruct (ghost_var_agree with "Hactive Hactive_half") as %Heq_active.
  subst waiter_active.

  (* Update active to true *)
  iMod (ghost_var_update_2 true with "Hactive_half Hactive") as "[Hactive_half Hactive]".
  { rewrite Qp.half_half. reflexivity. }
    iNamed "HQ".
    iDestruct "HQ" as "[HspQ HQ]".
  iDestruct (saved_prop_agree with "HspQ joinQ") as "#Hlt".

  destruct remaining_workers.
  {
    simpl.



  iMod (alloc_wait_token wg (wg_gamma γj) (N.@"wg") (W32 0) with "[$Hiswg] [$HnoWaiters]") as "[Hwaiters Hwtok]".
  { word. }
  { iFrame.
    iMod "Hmask".

  (* Close invariant with updated state *)
  iMod ("Hclose" with "[Hwg HspQ Hactive_half Hcounter HworkerNames_auth  HworkerQ_wand Hwaiters]") as "_".
  {
    iNext. unfold own_wg_join.
    iExists Q'.
    iFrame.
    replace ( (w32_word_instance.(word.add) (W32 0) (W32 1))) with (W32 1) by word.
    iFrame. iSplitL "".
    { done. }
    iSplitL "";first done.

    iFrame.
    iRewrite "Hlt".
    iFrame.
    }
  iMod (lc_fupd_elim_later with "Hlc2 Hlt") as "Hlt'".
    iModIntro.
     iIntros "H".
     iApply "HQ". iRewrite "Hlt'".
     iFrame.
     }
     }
     {
       Admitted.
