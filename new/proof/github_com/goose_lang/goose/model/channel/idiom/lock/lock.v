Require Import New.proof.proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.
From New.golang.theory Require Import chan.
From Perennial.algebra Require Import ghost_var.


(** * Lock Channel Idiom

    Note: If you can change the code and you aren't using select, just use a mutex.
    This pattern otherwise doesn't serve a practical purpose.

    This file provides a mutual exclusion abstraction using a buffered channel
    with capacity 1. The idiom uses channel buffer presence as the lock state:
    - Empty buffer: unlocked, resource R is available
    - One value in buffer: locked, resource R is inaccessible

    Key features:
    - Exactly one lock holder at a time (enforced by channel capacity)
    - Unbuffered and close operations are banned
    - Lock acquisition via send (blocking until buffer empty)
    - Lock release via receive (emptying the buffer)
    - Mutual exclusion guaranteed by channel's inherent single-slot capacity
*)

Section lock_channel.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chan_idiomG Σ V}.
Context `{!IntoVal V}.
Context `{!IntoValTyped V t}.
Context `{!ghost_varG Σ bool}.

Record lock_channel_names := {
  lchan_name : chan_names;      (* Underlying channel ghost state *)
  locked_name : gname;          (* Ghost bool tracking lock state *)
}.

Definition is_lock_channel (γ : lock_channel_names) (ch : loc)
                            (R : iProp Σ) : iProp Σ :=
  "#Hchan" ∷ is_chan ch γ.(lchan_name) ∗
  "#Hinv" ∷ inv nroot (
    ∃ s locked,
      "Hch" ∷ own_chan ch s γ.(lchan_name) ∗
      "%Hcap" ∷ ⌜ chan_cap γ.(lchan_name) = 1 ⌝ ∗
      "Hlocked_ghost" ∷ ghost_var γ.(locked_name) (DfracOwn (1/2)) locked ∗
      (match s with
       | chan_rep.Buffered [] =>
          ⌜locked = false⌝ ∗ ghost_var γ.(locked_name) (DfracOwn (1/2)) locked ∗ R
       | chan_rep.Buffered [v] =>
           ⌜locked = true⌝
       | _ =>
           (* Ban unbuffered and close states *)
           False
       end)
  )%I.

(** Ownership of the lock - proves the lock is currently held.

    This represents exclusive permission to the locked state. By the channel's
    capacity invariant, only one such ownership can exist at a time.
*)
Definition has_lock_channel (γ : lock_channel_names) : iProp Σ :=
  ghost_var γ.(locked_name) (DfracOwn (1/2)) true.

Lemma start_lock_channel ch (R : iProp Σ) γ :
  chan_cap γ = 1 ->
  is_chan ch γ -∗
  own_chan ch (chan_rep.Buffered []) γ -∗
  ▷ R ={⊤}=∗
    (∃ γlock, is_lock_channel γlock ch R).
Proof.
  intros Hcap.
  iIntros "#Hch Hoc HR".
   iMod (ghost_var_alloc false) as (γlocked) "[HlockedI HlockedF]".

  set (γlock := {| lchan_name := γ; locked_name := γlocked |}).


 iMod (inv_alloc nroot _ (
    ∃ s locked,
      "Hch" ∷ own_chan ch s γ ∗
      "%Hcap" ∷ ⌜ chan_cap γ = 1 ⌝ ∗
      "Hlocked_ghost" ∷ ghost_var γlock.(locked_name) (DfracOwn (1/2)) locked ∗
      (match s with
       | chan_rep.Buffered [] =>
         ⌜locked = false⌝ ∗ ghost_var γlock.(locked_name) (DfracOwn (1/2)) locked  ∗ R
       | chan_rep.Buffered [v] =>
           ⌜locked = true⌝
       | _ =>
           False
       end)
  ) with "[Hoc HlockedI HlockedF HR]") as "#Hinv".
 {
  iNext.  iFrame. replace (γlocked) with (γlock.(locked_name)) by done.  iFrame. done.
 }

  iModIntro.
  unfold has_lock_channel.
  iFrame "#".
  iExists γlock.
  unfold is_lock_channel.
  replace (γ) with (γlock.(lchan_name)) by done.
  iFrame "#".
Qed.

Lemma is_lock_channel_is_chan γ ch R :
  is_lock_channel γ ch R ⊢ is_chan ch γ.(lchan_name).
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma lock_channel_lock_au γ ch v (R : iProp Σ) :
  ∀ (Φ: iProp Σ),
  is_lock_channel γ ch R -∗
  £1 -∗
  ▷ (has_lock_channel γ ∗ R -∗ Φ) -∗
  SendAU ch v γ.(lchan_name) Φ.
Proof.
  iIntros (Φ) "#Hlock (HR & Hlc) Hcont".
  unfold has_lock_channel.
  iDestruct "Hlock" as "[#Hchan #Hinv]".

  unfold SendAU.
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] [$Hinv_open]") as "Hinv_open".
  iNamed "Hinv_open".

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iExists s. iFrame "Hch".

  destruct s; try done.
  destruct buff as [|v' rest].
  {
    iIntros "Hoc".
    iMod "Hmask".
    iDestruct "Hinv_open" as "(%Hlocked & Hgv & HR)".
    iCombine "Hgv Hlocked_ghost" as "Hgv".
      iMod (ghost_var_update (true) with "Hgv") as "[Hlock1 Hlock2]".
    iMod ("Hinv_close" with "[Hlock1 Hoc]") as "_".
    {
      iNext. iExists (chan_rep.Buffered [v]). iExists true. iFrame.
      done.
    }
    iModIntro. iApply "Hcont".
    iFrame.
  }
  {
    destruct rest; try done.
    iIntros "H".
    iDestruct (own_chan_buffer_size with "H") as "%Hbad".
    rewrite Hcap in Hbad.
    simpl in Hbad.
    done.
  }
  Qed.

Lemma wp_lock_channel_lock γ ch (v:V) (R : iProp Σ) :
  {{{ is_lock_channel γ ch R }}}
    chan.send #t #ch #v
  {{{ RET #();  has_lock_channel γ ∗ R }}}.
Proof.
  iIntros (Φ) "(#Hlock & HR) Hcont".

  unfold has_lock_channel.
  iNamed "Hlock".

  wp_apply (chan.wp_send ch v γ.(lchan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2 & Hlc3 & Hlc4)".
  iNamed "HR".

  iApply (lock_channel_lock_au with "[$Hinv] [$Hlc1] [Hcont]").
  {
    iFrame "#".
  }
  iNext. iFrame.
Qed.

Lemma lock_channel_unlock_au γ ch (R : iProp Σ) :
  ∀ Φ,
  is_lock_channel γ ch R -∗
  has_lock_channel γ -∗
  R -∗
  £1 -∗
  ▷ (∀ v, True -∗ Φ v true) -∗
  recv_au ch γ.(lchan_name) (λ (v:V) true, Φ v true).
Proof.
  iIntros (Φ) "#Hislock Hhaslock HR Hlc HΦcont".
  unfold has_lock_channel.


  unfold recv_au.
  unfold is_lock_channel.
  iNamed "Hislock".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iDestruct "Hlc" as "[Hlc1 Hrest]".
  iMod (lc_fupd_elim_later with "[$] [$Hinv_open]") as "Hinv_open".
  iNamed "Hinv_open".

  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iExists s. iFrame "Hch".

  destruct s; try done.
  destruct buff as [|v [|? ?]]; try done.

  (* Value in buffer - can unlock *)
  iIntros "Hoc".
  iMod "Hmask".
    iCombine "Hhaslock Hlocked_ghost" as "Hgv".
      iMod (ghost_var_update (false) with "Hgv") as "[Hlock1 Hlock2]".
  iMod ("Hinv_close" with "[Hoc HR Hlock1 Hlock2]") as "_".
  {
    iNext. iExists (chan_rep.Buffered []). iFrame.
    done.
  }
  iModIntro. iApply "HΦcont". done.
Qed.

Lemma wp_lock_channel_unlock γ ch (R : iProp Σ) :
  {{{ is_lock_channel γ ch R ∗ has_lock_channel γ ∗ R }}}
    chan.receive #t #ch
  {{{ (v : V), RET (#v, #true); True }}}.
Proof.
  iIntros (Φ) "(#Hlock & Hlocked) Hcont".

  unfold has_lock_channel.
  iDestruct "Hlock" as "[#Hchan #Hinv]".

  iApply (chan.wp_receive ch γ.(lchan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2)".
  iDestruct "Hlocked" as "[Hgv HR]".
  iApply ((lock_channel_unlock_au γ ch R) with "[$Hchan $Hinv] [$Hgv] [$HR] [$Hlc1]").
  iNext. iFrame.
Qed.

End lock_channel.
