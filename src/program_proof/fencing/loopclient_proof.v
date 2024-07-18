From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.fencing Require Import loopclient.
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.grove_shared Require Export erpc_lib urpc_proof urpc_spec.
From Perennial.program_proof.fencing Require Export client_proof.
From Perennial.program_proof Require Export marshal_proof.
From iris.base_logic Require Import mono_nat.
From Perennial.goose_lang Require Import prelude.

Module loopclient.
Section loopclient_proof.
Context `{!heapGS Σ}.

Context `{!urpcregG Σ}.
Context `{!ctrG Σ}.

Definition kvN := nroot .@ "kv".

Definition kv_inv γ γm1 γm2 : iProp Σ :=
  inv kvN (
    (∃ v1,
    "Hkv1" ∷ frontend.kv_ptsto γ.(client.kv_gn) 0 v1 ∗
    "Hmono1" ∷ mono_nat_auth_own γm1 1 (uint.nat v1)) ∗
    (∃ v2,
    "Hkv2" ∷ frontend.kv_ptsto γ.(client.kv_gn) 1 v2 ∗
    "Hmono2" ∷ mono_nat_auth_own γm2 1 (uint.nat v2))
  )
.

Lemma wp_LoopOnKey γ γm1 γm2 (key:u64) config :
  key = 0 ∨ key = 1 →
  (* FIXME: existentially quantify the epoch_tok *)
  config.is_host γ.(client.config_gn) config (λ _, True) (client.config_host_inv γ) -∗
  kv_inv γ γm1 γm2 -∗
  {{{
        True
  }}}
    LoopOnKey #key #config
  {{{
        RET #(); True
  }}}.
Proof.
  intros Hkey.
  iIntros "#Hcfg #Hinv !#" (Φ) "_ HΦ".

  (* I'm just going to unwrap the definition of inv here. There should be a
     lemma for this. *)
  iAssert (∃ γm, inv kvN (∃ v, "Hkv" ∷ frontend.kv_ptsto γ.(client.kv_gn) key v ∗
               "Hmono" ∷ mono_nat_auth_own γm 1 (uint.nat v))
          )%I as "HH".
  {
    destruct Hkey as [-> | -> ].
    {
      iExists γm1.
      iApply (inv_split_l with "Hinv").
    }
    {
      iExists γm2.
      iApply (inv_split_r with "Hinv").
    }
  }

  iClear "Hinv".
  clear γm1 γm2.
  iDestruct "HH" as (γm) "Hinv".

  wp_rec. wp_pures.
  wp_apply (client.wp_MakeClerk with "Hcfg").
  iIntros (ck) "Hck".
  wp_pures.
  wp_apply (client.wp_Clerk__FetchAndIncrement with "Hck []").
  { done. }
  iModIntro.

  iInv "Hinv" as ">Hi" "Hclose".
  iApply (fupd_mask_intro).
  { set_solver. }
  iIntros "Hmask".

  iNamed "Hi".
  iExists _; iFrame.
  iIntros (Hoverflow) "Hkv".
  iMod "Hmask".
  iMod (mono_nat_own_update (uint.nat (word.add v 1)) with "Hmono") as "[Hmono #Hlb]".
  {
    word.
  }
  iMod ("Hclose" with "[Hkv Hmono]") as "_".
  {
    iNext.
    iExists _; iFrame.
  }
  iModIntro.
  iIntros "Hck".

  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (lowerBound) "HlowerBound".
  wp_pures.

    iClear "Hmask".
    (* weaken resources to loop invariant *)
    iAssert (∃ (v v':u64), ⌜uint.nat v' > uint.nat v⌝ ∗ lowerBound ↦[uint64T] #v ∗ mono_nat_lb_own γm (uint.nat v'))%I with "[HlowerBound]" as "HH".
    {
      iExists _, _; iFrame "∗#".
      iPureIntro.
      word.
    }
    iClear "Hlb".
    clear Hoverflow.
    clear v.
    wp_forBreak.

    wp_pures.

    wp_bind (client.Clerk__FetchAndIncrement _ _).
    iDestruct "HH" as (v v') "(%Hineq & HlowerBound & #Hlb)".
    wp_apply (wp_frame_wand with "HlowerBound").
    wp_apply (client.wp_Clerk__FetchAndIncrement with "Hck []").
    { auto. }
    iModIntro.

    iInv "Hinv" as ">Hi" "Hclose".
    iApply (fupd_mask_intro).
    { set_solver. }
    iIntros "Hmask".

    iNamed "Hi".
    (* Need this inequality to know that this value v1 being observed is bigger than the lower bound v *)
    iDestruct (mono_nat_lb_own_valid with "Hmono Hlb") as %[_ Hineq2].
    iExists _; iFrame.
    iIntros (Hoverflow) "Hkv".
    iMod "Hmask".

    iMod (mono_nat_own_update (uint.nat (word.add v0 1%nat)) with "Hmono") as "[Hmono #HlbNew]".
    { word. }
    iMod ("Hclose" with "[Hkv Hmono]") as "_".
    {
      iNext.
      iExists _; iFrame.
    }
    iModIntro.

    iIntros "Hck HlowerBound".
    wp_pures.
    wp_load.
    wp_pures.
    rewrite bool_decide_true; last first.
    { word. }
    wp_apply (wp_Assert).
    { done. }
    wp_pures.

    (* This code was here for logging *)
    wp_bind (@If _ _ _ _).
    wp_apply (wp_wand _ _ _ (λ v, _) with "[-]").
    {
      wp_if_destruct.
      {
        iModIntro.
        iNamedAccu.
      }
      iFrame.
      done.
    }
    iIntros (?).
    iNamed 1.

    wp_pures.
    wp_store.
    iLeft.
    iSplitL ""; first done.
    iFrame.
    iModIntro.
    iExists _, _; iFrame.
    iFrame "#".
    iPureIntro.
    word.
Qed.

End loopclient_proof.
End loopclient.
