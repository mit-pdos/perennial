From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base chan_init.
From New.proof Require Import proof_prelude.
From New.golang.theory Require Import lock.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
Require Import New.proof.github_com.goose_lang.primitive.

#[local] Transparent is_chan own_chan.
#[local] Typeclasses Transparent is_chan own_chan.

Section new_spec.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}
  {sem : go.ChanSemantics}.
Collection Wp := sem_fn + pre_sem + sem.

Context `[!ZeroVal V] `[!TypedPointsto V] `[!IntoValTyped V t].
Collection W := Wp + IntoValTyped0.

Implicit Types (ch : loc) (γ : chan_names) (v : V).

Lemma wp_NewChannel (cap : w64) :
  {{{ ⌜ 0 ≤ sint.Z cap ⌝ }}}
    #(functions channel.NewChannel [t]) #cap
  {{{ (ch: loc) (γ: chan_names), RET #ch;
      is_chan ch γ V ∗
      ⌜chan_cap γ = cap⌝ ∗
      own_chan γ V (if decide (cap = W64 0) then chanstate.Idle else chanstate.Buffered (@nil V))
  }}}.
Proof using W.
  wp_start as "%Hle".
  wp_auto.
  wp_if_destruct.
  {
    wp_alloc mu as "mu".
    assert (sint.Z cap > 0) by word.
    rewrite -wp_fupd.
    wp_auto.
    wp_apply wp_slice_make2; first done.
    iIntros (sl) ("Hsl"). wp_auto.
    wp_alloc ch as "Hch".
    wp_auto.
    iStructNamedPrefix "Hch" "H".
    iMod (ghost_var_alloc (chanstate.Buffered []))
      as (state_gname) "[Hstate_auth Hstate_frag]".
    iMod (ghost_var_alloc (None : option (offer_lock V)))
      as (offer_lock_gname) "Hoffer_lock".
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_parked_prop_gname) "Hparked_prop".
    {
      done.
    }
    iMod (saved_prop.saved_pred_alloc (uncurry (λ (_ : V) (_ : bool),True%I))  (DfracOwn 1))
      as (offer_parked_pred_gname) "Hparked_pred";first done.
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_continuation_gname) "Hcontinuation";first done.
    set (γ := {|
               state_name := state_gname;
               offer_lock_name := offer_lock_gname;
               offer_parked_prop_name := offer_parked_prop_gname;
               offer_parked_pred_name := offer_parked_pred_gname;
               offer_continuation_name := offer_continuation_gname;
               chan_cap := cap;
             |}).
    iPersist "Hcap Hmu".
    iMod ((init_lock (chan_inv_inner ch γ V)) with "[$mu] [-HΦ Hstate_frag]") as "H".
    {
      iModIntro. unfold chan_inv_inner.
      iDestruct "Hsl" as "[Hsl Hos]".

      iExists (Buffered []). simpl.
      iFrame "#∗".

      iPureIntro.
      unfold chan_cap_valid.
      simpl. lia.

    }
    iModIntro. iApply ("HΦ" $! _ γ).
    iFrame "#". simpl.
    rewrite decide_False; [ | word ].
    unfold is_chan. iFrame "∗#". iPureIntro.
    assert (ch ≠ chan.nil) by admit. (* FIXME: non-nilness. *)
    split; first done. unfold chan_cap_valid. simpl; word.
  }
  {
    assert (cap = W64 0) by word; subst.

    rewrite -wp_fupd.
    wp_alloc mu as "mu".
    wp_auto.
    wp_apply (wp_slice_make2 (V:=V)); first done.
    iIntros (sl) ("Hsl"). wp_auto.
    wp_alloc ch as "Hch".
    wp_auto.
    iStructNamedPrefix "Hch" "H". simpl.
    iMod (ghost_var_alloc chanstate.Idle)
      as (state_gname) "[Hstate_auth Hstate_frag]".
    iMod (ghost_var_alloc (None : option (offer_lock V)))
      as (offer_lock_gname) "Hoffer_lock".
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_parked_prop_gname) "Hparked_prop".
    {
      done.
    }
    iMod (saved_prop.saved_pred_alloc (uncurry (λ (_ : V) (_ : bool),True%I))  (DfracOwn 1))
      as (offer_parked_pred_gname) "Hparked_pred";first done.
    iMod (saved_prop.saved_prop_alloc True 1) as (offer_continuation_gname) "Hcontinuation";first done.
    set (γ := {|
               state_name := state_gname;
               offer_lock_name := offer_lock_gname;
               offer_parked_prop_name := offer_parked_prop_gname;
               offer_parked_pred_name := offer_parked_pred_gname;
               offer_continuation_name := offer_continuation_gname;
               chan_cap := W64 0;
             |}).
    iPersist "Hmu Hcap".
    iMod ((init_lock (chan_inv_inner ch γ V)) with "[$mu] [-HΦ Hstate_frag]") as "H".
    {
      iModIntro. unfold chan_inv_inner.
      iDestruct "Hsl" as "[Hsl Hos]".
      iExists (@Idle V).   simpl.
      iFrame "#". iFrame.
      iPureIntro.
      rewrite /chan_cap_valid //.
    }
    iModIntro.  iApply ("HΦ" $! _ γ).
    unfold is_chan. iFrame "∗#". simpl.
    iFrame "∗#". assert (ch ≠ chan.nil) by admit. (* FIXME: non-nilness. *)
    iPureIntro. rewrite /chan_cap_valid //.
  }
Admitted.

End new_spec.