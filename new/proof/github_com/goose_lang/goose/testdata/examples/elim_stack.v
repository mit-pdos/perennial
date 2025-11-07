From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_init.
From New.proof Require Import proof_prelude.
From iris.algebra Require Import auth.
From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base.
From New.golang.theory Require Import chan.
From iris.base_logic.lib Require Import saved_prop.
From New.proof Require Import strings time sync.
From New.golang.theory Require Import struct string chan.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

Import chan_spec_raw_examples.

Set Default Proof Using "Type".

Class elimStackGhostStateG Σ := ElimStackGhostStateG {
  stack_listG        : ghost_varG Σ (list (go_string));
  push_parked_propG  : savedPropG Σ;
  pop_parked_predG   : savedPredG Σ (go_string * bool);
  elim_chanG         : chanGhostStateG Σ go_string
}.

Definition elimStackGhostStateΣ : gFunctors :=
  #[ ghost_varΣ (list (go_string))
   ; savedPropΣ
   ; savedPredΣ (go_string * bool)
   ; chanGhostStateΣ go_string
   ].

#[global] Instance subG_elimStackGhostStateG Σ :
  subG elimStackGhostStateΣ Σ → elimStackGhostStateG Σ.
Proof. solve_inG. Qed.

Section elim_stack.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!elimStackGhostStateG Σ}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

#[local] Existing Instance stack_listG.
#[local] Existing Instance push_parked_propG.
#[local] Existing Instance pop_parked_predG.
#[local] Existing Instance elim_chanG.

Record stack_names := {
  stack_state_name : gname;
  exch_chan_name : chan_names;
  push_parked_prop_name : gname;
  pop_parked_pred_name : gname;
}.

#[local] Definition stack_rep (γ: gname) (q: Qp) (l: list (go_string)) : iProp Σ :=
  ghost_var γ q l.

#[local] Notation stack_rep_full γ l := (stack_rep γ 1 l).
Notation stack_rep_half γ l := (stack_rep γ (1/2)%Qp l).

Lemma stack_rep_agree γ q1 q2 l1 l2 :
  stack_rep γ q1 l1 -∗ stack_rep γ q2 l2 -∗ ⌜l1 = l2⌝.
Proof.
  iIntros "H1 H2". by iApply (ghost_var_agree with "H1 H2").
Qed.

Lemma stack_rep_update γ l l' :
  stack_rep_full γ l ==∗ stack_rep_full γ l'.
Proof. iApply ghost_var_update. Qed.

Lemma stack_rep_halves_update γ l1 l2 l' :
  stack_rep_half γ l1 -∗ stack_rep_half γ l2 ==∗
  stack_rep_half γ l' ∗ stack_rep_half γ l'.
Proof. iApply ghost_var_update_halves. Qed.

Definition push_au (s: loc) (v: go_string) (γ: gname) (Φ: iProp Σ) : iProp Σ :=
  |={⊤,∅}=> ∃ l,
    stack_rep_half γ l ∗
    (stack_rep_half γ (v :: l) ={∅,⊤}=∗ Φ).

Definition pop_au (s: loc) (γ: gname) (Φ: go_string → bool → iProp Σ) : iProp Σ :=
  |={⊤,∅}=> ∃ l,
    stack_rep_half γ l ∗
    (match l with
     | [] => stack_rep_half γ [] ={∅,⊤}=∗ Φ ""%go false
     | v::l' => stack_rep_half γ l' ={∅,⊤}=∗ Φ v true
     end).

Definition PopK (Φ : go_string → bool → iProp Σ) : (go_string * bool) → iProp Σ :=
  λ '(v,b), Φ v b.

Definition stack_inv (s: loc) (γ: stack_names) : iProp Σ :=
  ∃ (physical: list (go_string)) (slice_val: slice.t),
    "Hstack" ∷ s ↦s[(chan_spec_raw_examples.LockedStack) :: "stack"] slice_val ∗
    "Hslice" ∷ own_slice slice_val (DfracOwn 1) (reverse physical) ∗
    "Hslice_cap" ∷ own_slice_cap (go_string) slice_val (DfracOwn 1) ∗
    "Hlog2phys" ∷ stack_rep_half γ.(stack_state_name) physical .

Definition exchanger_inv (s: loc) (ch: loc) (γ: stack_names) : iProp Σ :=
  ∃ (ch_state: chan_rep.t (go_string)),
    "chan_state" ∷ own_channel ch 0 ch_state γ.(exch_chan_name) ∗
    "logical" ∷ match ch_state with
      | chan_rep.Idle =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn 1) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn 1) (PopK Φpop)
      | chan_rep.SndPending v =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn (1/2)) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn 1) (PopK Φpop) ∗
            "push_au" ∷ push_au s v γ.(stack_state_name) Φpush
      | chan_rep.RcvPending =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn 1) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn (1/2)) (PopK Φpop) ∗
            "pop_au" ∷ pop_au s γ.(stack_state_name) Φpop
      | chan_rep.SndCommit v =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn (1/2)) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn (1/2)) (PopK Φpop) ∗
            "pop_complete" ∷ Φpop v true
      | chan_rep.RcvCommit =>
          ∃ (Φpush: iProp Σ) (Φpop: go_string → bool → iProp Σ),
            "push_saved" ∷ saved_prop_own γ.(push_parked_prop_name) (DfracOwn (1/2)) Φpush ∗
            "pop_saved" ∷ saved_pred_own γ.(pop_parked_pred_name) (DfracOwn (1/2)) (PopK Φpop) ∗
            "push_complete" ∷ Φpush
      | _ => False
      end.

Definition is_exchanger (ch: loc) (γ: stack_names) : iProp Σ :=
  is_channel ch 0 γ.(exch_chan_name).

Global Instance is_exchanger_persistent ch γ : Persistent (is_exchanger ch γ).
Proof. apply _. Qed.

Definition is_elim_stack (st: loc) (γ: stack_names) : iProp Σ :=
  ∃ (mu_loc: loc) (ch_loc: loc),
    "#mu_field" ∷ st ↦s[chan_spec_raw_examples.LockedStack :: "mu"]□ mu_loc ∗
    "#ch_field" ∷ st ↦s[chan_spec_raw_examples.LockedStack :: "exchanger"]□ ch_loc ∗
    "#is_lock" ∷ is_Mutex mu_loc (stack_inv st γ) .

Global Instance is_elim_stack_persistent st γ : Persistent (is_elim_stack st γ).
Proof. apply _. Qed.

Lemma wp_NewEliminationStack :
  {{{ is_pkg_init chan_spec_raw_examples }}}
  @! chan_spec_raw_examples.NewEliminationStack #()
  {{{ (st: loc) γ, RET #st;
      is_elim_stack st γ ∗ stack_rep_half γ.(stack_state_name) []
  }}}.
Proof.
Admitted.

Lemma wp_LockedStack__Push (st: loc) (v: go_string) (γ: stack_names) Φ  :
  st ≠ null ->
  is_elim_stack st γ -∗
  is_pkg_init chan_spec_raw_examples -∗
  push_au st v γ.(stack_state_name) (Φ #()) -∗

  WP chan_spec_raw_examples.LockedStack__Pushⁱᵐᵖˡ #st #v {{ Φ }}.
Proof.
  intros H.
   iIntros "#Hic".
   iIntros "#Hinit".
   iIntros "Hau".
   wp_call.
  iNamed "Hic".
  wp_auto_lc 4.
    wp_apply (wp_Mutex__Lock with "[$is_lock]") as "[Hlocl Hstack]".
    iNamed "Hstack".
    iRename select (£1) into "Hlc1".
    wp_pures.
        iDestruct (own_slice_len with "Hslice") as %Hlen.
           iDestruct (slice.own_slice_len with "Hslice") as "[%Hlen_slice %Hslgtz]".
      iDestruct (own_slice_wf with "Hslice") as "%Hwf".
      wp_auto.
        wp_apply wp_slice_literal.
        iIntros (sl).
        iIntros "Hsl".
        wp_auto.
        wp_apply (wp_slice_append with "[$Hslice $Hslice_cap $Hsl]").
        iIntros (sl').
        iIntros "Hsl'".
        wp_auto.
        unfold push_au.
        rewrite -fupd_wp.
        iMod "Hau".
        iNamed "Hau".
        iDestruct "Hau" as "[Hsta Hclose]".
          iDestruct (ghost_var_agree with "[$Hsta] [$Hlog2phys]") as "%Hag".
        iCombine "Hsta Hlog2phys" as "Hstacklog".
        subst l.
          iMod (ghost_var_update (v :: physical) with "Hstacklog") as "[Hsl1 Hsl2]".
          iMod ("Hclose" with "[$Hsl1]").
          iModIntro.
          iDestruct "Hsl'" as "(Hsl & Hosc & Hslpt)".
             wp_apply (wp_Mutex__Unlock
                 with "[$is_lock Hstack Hsl Hosc Hsl2 $Hlocl]").
             {
             iNext. iFrame. 
             Search "reverse".
             rewrite reverse_cons.
             done
             }
done.          
             Qed.


Lemma wp_LockedStack__Pop
    (st: loc) (γ: stack_names)
   Φ  :
  st ≠ null ->
  is_pkg_init chan_spec_raw_examples -∗
  is_elim_stack st γ -∗
  pop_au st γ.(stack_state_name) (λ v ok, Φ (#v, #ok)%V) -∗
  WP chan_spec_raw_examples.LockedStack__Popⁱᵐᵖˡ #st #() {{ Φ }}.
Proof.
  intros Hne.
  iIntros "#His #Hinit HAU".
  wp_call.
  wp_auto.
  iNamed "Hinit".
  wp_auto.

  wp_apply (wp_Mutex__Lock with "[$is_lock]") as "[Hown Hinv]".
  iNamed "Hinv".                        

  wp_pures.
  iDestruct (slice.own_slice_len with "Hslice") as "[%Hlen_slice %Hsl_ge0]".
  iDestruct (own_slice_wf with "Hslice") as "%Hwf".
  wp_auto.

  wp_if_destruct.
  - 
    assert (sint.nat slice_val.(slice.len_f) = 0%nat) by word.

    unfold pop_au.
    rewrite -fupd_wp.
    iMod "HAU" as (l) "[Hhalf Hk]".
    iDestruct (ghost_var_agree with "Hhalf Hlog2phys") as %->. (* l = [] *)
  iDestruct (slice.own_slice_len with "Hslice") as "[%Hlen_slice' %Hsl_ge0']".
   rewrite H in Hlen_slice'.
   destruct physical. {
   
    iMod ("Hk" with "Hhalf") as "HΦ".                       
    iModIntro.

    wp_apply (wp_Mutex__Unlock with "[$is_lock Hown Hstack Hslice Hslice_cap Hlog2phys]").
    { iFrame.
    }
    by iApply "HΦ".
    }
    { rewrite reverse_cons in Hlen_slice'.
      rewrite length_app in Hlen_slice'.
      
      simpl in Hlen_slice'.
      lia.
      }

      -
destruct physical as [|x xs].
{ simpl in *.
word.  
}
    set (g := x). set (tail := xs). clearbody g tail.



rewrite length_reverse in Hlen_slice.
    iDestruct (slice.own_slice_len with "Hslice") as "[%Hlen_s %Hge0]".
     have Hpos : 0 ≤ sint.Z (W64 0) by word.
    Admitted.


End elim_stack.
