Require Import New.proof.proof_prelude.
From New.golang.theory Require Import chan.
From New.proof.github_com.goose_lang.goose.model.channel.idiom Require Export base.


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
Context {sem : go.Semantics}.
Context `{!ZeroVal V} `{!TypedPointsto V} `{!IntoValTyped V t}.
Collection W := sem + IntoValTyped0.
Set Default Proof Using "W".

Record lock_channel_names := {
  lchan_name : chan_names;      (* Underlying channel ghost state *)
  locked_name : gname;          (* Ghost bool tracking lock state *)
}.

Definition is_lock_channel (γ : lock_channel_names) (ch : loc)
                            (R : iProp Σ) : iProp Σ :=
  "#Hchan" ∷ is_chan ch γ.(lchan_name) V ∗
  "#Hinv" ∷ inv nroot (
    ∃ s locked,
      "Hch" ∷ own_chan γ.(lchan_name) V s ∗
      "%Hcap" ∷ ⌜ chan_cap γ.(lchan_name) = W64 1 ⌝ ∗
      (match s with
       | chanstate.Buffered [] =>
          ⌜locked = false⌝ ∗ R
       | chanstate.Buffered [v] =>
           ⌜locked = true⌝
       | _ =>
           (* Ban unbuffered and close states *)
           False
       end)
  )%I.

Lemma start_lock_channel ch (R : iProp Σ) γ :
  chan_cap γ = W64 1 ->
  is_chan ch γ V -∗
  own_chan γ V (chanstate.Buffered []) -∗
  ▷ R ={⊤}=∗
    (∃ γlock, is_lock_channel γlock ch R).
Proof.
  intros Hcap.
  iIntros "#Hch Hoc HR".
  iMod (dghost_var_alloc false) as (γlocked) "[HlockedI HlockedF]".
  set (γlock := {| lchan_name := γ; locked_name := γlocked |}).

  iMod (inv_alloc nroot _ (
            ∃ s locked,
              "Hch" ∷ own_chan γ V s ∗
              "%Hcap" ∷ ⌜ chan_cap γ = W64 1 ⌝ ∗
              (match s with
               | chanstate.Buffered [] =>
                   ⌜locked = false⌝∗ R
               | chanstate.Buffered [v] =>
                   ⌜locked = true⌝
               | _ =>
                   False
               end)
          ) with "[Hoc HlockedI HlockedF HR]") as "#Hinv".
  {
    iNext.  iFrame. replace (γlocked) with (γlock.(locked_name)) by done.  
    iExists false. iFrame. done.
  }
  iModIntro.
  iFrame "#".
  iExists γlock.
  unfold is_lock_channel.
  replace (γ) with (γlock.(lchan_name)) by done.
  iFrame "#".
Qed.

Lemma is_lock_channel_is_chan γ ch R :
  is_lock_channel γ ch R ⊢ is_chan ch γ.(lchan_name) V.
Proof.
  iDestruct 1 as "[$ _]".
Qed.

Lemma lock_channel_lock_au γ ch (v : V) (R : iProp Σ) :
  ∀ (Φ: iProp Σ),
  is_lock_channel γ ch R -∗
  £1 -∗
  ▷ (R -∗ Φ) -∗
  send_au γ.(lchan_name) v Φ.
Proof.
  iIntros (Φ) "#Hlock (HR & Hlc) Hcont".
  iDestruct "Hlock" as "[#Hchan #Hinv]".

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
    iDestruct "Hinv_open" as "(%Hlocked & HR)".
    iMod ("Hinv_close" with "[Hoc]") as "_".
    {
      iNext. iExists (chanstate.Buffered [v]). iExists true. iFrame.
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

Lemma lock_channel_trylock_au γ ch (v : V) (R : iProp Σ)  :
∀ Φ,
  is_lock_channel  γ ch R -∗
  £1 -∗
  (R -∗ Φ) -∗
  nonblocking_send_au γ.(lchan_name) v Φ True.
Proof.
  iIntros (Φ) "#Hlock HR HΦ".
  iDestruct "Hlock" as "[#Hchan #Hinv]".
  iSplit. all: try done.
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "[$] [$Hinv_open]") as "Hinv_open".
  iNamed "Hinv_open".
  destruct s. all: try done.
  destruct buff. all: try done.
  {
    iDestruct "Hinv_open" as "(%H & H')".
    subst locked.
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iExists (chanstate.Buffered []). iFrame "Hch".  iIntros "Hoc".
  iMod "Hmask". 
    iMod ("Hinv_close" with "[ $Hoc   ]") as "H".
    {  iFrame "%". iNext. simpl. iExists true. done.   }
    iModIntro. iApply "HΦ". iFrame.  
  }
  {
    destruct buff. all: try done.
  iDestruct "Hinv_open" as "%Hlt".
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext. iFrame. iIntros "Hch".  
  iMod "Hmask". 
    iDestruct (own_chan_buffer_size with "Hch") as "%Hbad".
    rewrite Hcap in Hbad. done.
  }
Qed.

Lemma wp_lock_channel_lock γ ch (v:V) (R : iProp Σ) :
  {{{ is_lock_channel γ ch R }}}
    chan.send t #ch #v
  {{{ RET #(); R }}}.
Proof.
  iIntros (Φ) "(#Hlock & HR) Hcont".

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
  R -∗
  £1 -∗
  ▷ (∀ v, True -∗ Φ v true) -∗
  recv_au γ.(lchan_name) V (λ (v:V) true, Φ v true).
Proof.
  iIntros (Φ) "#Hislock HR Hlc HΦcont".


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
  iMod ("Hinv_close" with "[Hoc HR]") as "_".
  {
    iNext. iExists (chanstate.Buffered []). iFrame.
    iExists false. iFrame.
    iPureIntro. done.
  }
  iModIntro. iApply "HΦcont". done.
Qed.

Lemma wp_lock_channel_unlock γ ch (R : iProp Σ) :
  {{{ is_lock_channel γ ch R ∗ R }}}
    chan.receive t #ch
  {{{ (v : V), RET (#v, #true); True }}}.
Proof.
  iIntros (Φ) "(#Hlock & HR) Hcont".

  iDestruct "Hlock" as "[#Hchan #Hinv]".

  iApply (chan.wp_receive ch γ.(lchan_name) with "[$Hchan]").
  iIntros "(Hlc1 & Hlc2)".
  iApply ((lock_channel_unlock_au γ ch R) with "[$Hchan $Hinv] [$HR] [$Hlc1]").
  iNext. iFrame.
Qed.

End lock_channel.
