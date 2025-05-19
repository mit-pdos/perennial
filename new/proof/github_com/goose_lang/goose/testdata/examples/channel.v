
From New.proof Require Import proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_spec_inv chan_ghost_state chan_spec_api chan_spec_base.
From New.code.github_com.goose_lang.goose.testdata.examples Require Import channel.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.

From Perennial.Helpers Require Import bytes.
From Coq Require Import Program.Equality.
Set Default Proof Using "Type*".


Section proof.
    Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
   Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
   Implicit Types (v:val). 
   Context `{!ghost_varG Σ (bool * val)}.
   Context `{!goGlobalsGS Σ}.
   #[global] Program Instance : IsPkgInit chan_spec_raw_examples := ltac2:(build_pkg_init ()).

Definition hello_world_pred
(z: Z) (v: byte_string): iProp Σ :=
 (⌜ v = "hello world"%go ⌝%I) 
.

Lemma wp_SendMessage (γ: chan_names):
   {{{ is_pkg_init chan_spec_raw_examples }}}
     chan_spec_raw_examples @ "SendMessage" #()
   {{{ RET #();
       True
   }}}.
 Proof.
  wp_start; wp_auto. 
  set par := make_unbuffered_params_simple_single_sync byte_string stringT _ _ _ messageChan_ptr γ hello_world_pred. 
  unfold make_unbuffered_params_simple_single_sync in par.
  replace 0 with par.(ch_size) by trivial.
  wp_apply ((wp_NewChannelRef par) with "[]").
  iIntros (ch_ref_ptr). iIntros "Hch". iNamed "Hch". iNamed "HCh".
  wp_auto.
  iDestruct ((chan_pointsto_non_null mu_l par) with "[Hlock]") as %Hnotnull;trivial.
     assert (par.(ch_loc) ≠ null).
    {
      intro H.
      replace (par.(ch_loc)) with null in Hnotnull.
      done.
    }
  iPersist "messageChan" as "#messageChan".
  wp_apply (wp_fork with "[HSc]").
  {
    replace stringT with (par.(ch_T)) by trivial.
    replace ch_ref_ptr with (par.(ch_loc)) by trivial.
    wp_apply (( wp_Channel__Send par 0%nat "hello world"%go) with "[HSc]").
    {
      done.
    }
    {
      trivial.
    }
    {
     iFrame. iFrame "#". unfold P. iPureIntro.
    done.
    }
    {
     iIntros "H". wp_auto. done. 
    }
  }
    replace stringT with (par.(ch_T)) by trivial.
    replace ch_ref_ptr with (par.(ch_loc)) by trivial.
    wp_apply (( wp_Channel__ReceiveDiscardOk par 0%nat) with "[HRecvPerm]").
    {
      done.
    }
    {
     iFrame. iFrame "#". iPureIntro. split.
     {
      done.
     }
     done. 
    }
    iIntros (v). iIntros (ok). iIntros "HRecPost". unfold recv_post.
     wp_auto. 
     destruct ok.
     {
      unfold P. simpl. iDestruct "HRecPost" as "[%Hhwpred Hrecvperm]".
      subst v. destruct bool_decide eqn: Hobv.
      {
        wp_auto. iApply "HΦ". done.
      }
      done.
     }
     iNamed "HRecPost".
     iNamed "HRecPost".
     done.
 Qed.

End proof.