From New.proof.github_com.goose_lang.goose.model.channel Require Export chan_au_base chan_au_send chan_au_recv.
From New.proof Require Import proof_prelude.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

#[local] Transparent is_channel own_channel.

Section select.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chanG Σ V1} `{!chanG Σ V2}.
Context `{!IntoVal V1} `{!IntoVal V2} `{!IntoValTyped V1 t1} `{!IntoValTyped V2 t2}.

Lemma wp_BlockingSelect2 (ch1: loc) (cap1: Z) (γ1: chan_names) (dir1: u64) (val1: V1)
                         (ch2: loc) (cap2: Z) (γ2: chan_names) (dir2: u64) (val2: V2):
  ∀ (Φ: val → iProp Σ),
  is_pkg_init channel ∗ is_channel (V:=V1) ch1 cap1 γ1 ∗ is_channel (V:=V2) ch2 cap2 γ2 -∗
  ((⌜dir1 = W64 0⌝ ∗ send_au_slow ch1 cap1 val1 γ1 (Φ (#(W64 0), #(default_val V1), #(default_val V2), #false)%V)) ∨
   (⌜dir1 = W64 1⌝ ∗ rcv_au_slow ch1 cap1 γ1 (λ (v:V1) ok, Φ (#(W64 0), #v, #(default_val V2), #ok)%V))) ∧
  ((⌜dir2 = W64 0⌝ ∗ send_au_slow ch2 cap2 val2 γ2 (Φ (#(W64 1), #(default_val V1), #(default_val V2), #false)%V)) ∨
   (⌜dir2 = W64 1⌝ ∗ rcv_au_slow ch2 cap2 γ2 (λ v ok, Φ (#(W64 1), #(default_val V1), #v, #ok)%V))) -∗
  WP @! channel.BlockingSelect2 #t1 #t2 #ch1 #dir1 #val1 #ch2 #dir2 #val2 {{ Φ }}.
Proof.
  wp_start.
  wp_auto. wp_for.
  wp_apply (wp_RandomUint64). iIntros (x). iIntros "H". wp_auto.
  wp_if_destruct.
  {
    wp_if_destruct.
    {
      set clauses := (((⌜W64 0 = W64 0⌝ ∗
            send_au_slow ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜W64 0 = W64 1⌝ ∗
            rcv_au_slow ch1 cap1 γ1
              (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜dir2 = W64 0⌝ ∗
              send_au_slow ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜dir2 = W64 1⌝ ∗
              rcv_au_slow ch2 cap2 γ2
                (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V)))
        ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
      iDestruct "Hpre" as "[Hpre1 Hpre2]". iNamed "Hpre1".
      iDestruct "cap" as "cap1". iDestruct "mu" as "mu1". iDestruct "lock" as "lock1".
      iNamed "Hpre2".
      wp_apply ((wp_TrySend ch1 cap1 val1 γ1 clauses) with "[][HΦ zero1 zero2]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        iDestruct (and_elim_l with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct (length buff <? cap1); try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. unfold send_au_inner. iMod "Hcont". iModIntro. iModIntro.
          iNamed "Hcont". iFrame.
          destruct s; try done.
          {
            iIntros "Hoc". iMod ("Hcontinner" with "Hoc") as "Hcontinner".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
        {
          iIntros "Hoc".
          iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. wp_for_post. iFrame.
        }
      }
      {
        iIntros "Hc". wp_auto. wp_for_post.
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        iFrame. iFrame "#".
      }
    }
    {
      iDestruct "Hpre" as "[Hpre1 Hpre2]". iNamed "Hpre1".
      iDestruct "cap" as "cap1". iDestruct "mu" as "mu1". iDestruct "lock" as "lock1".
      iNamed "Hpre2".
      set clauses := (((⌜dir1 = W64 0⌝ ∗
            send_au_slow ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜dir1 = W64 1⌝ ∗
            rcv_au_slow ch1 cap1 γ1
              (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜dir2 = W64 0⌝ ∗
              send_au_slow ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜dir2 = W64 1⌝ ∗
              rcv_au_slow ch2 cap2 γ2
                (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V)))
        ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
        ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
        recv_val_ptr ↦ IntoValTyped0.(default_val V1) ∗
        selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
      wp_apply ((wp_TryReceive (V:=V1) ch1 cap1 γ1 clauses) with "[][HΦ zero1 zero2 recv_val ok selected]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2 & Hrcv & Hok & Hsel)".
        iDestruct (and_elim_l with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct buff; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. unfold send_au_inner. iMod "Hcont". iModIntro. iModIntro.
          iNamed "Hcont". iFrame.
          destruct s; try done.
          {
            iIntros "Hoc". iMod ("Hcontinner" with "Hoc") as "Hcontinner".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
          {
            destruct draining; try done.
            {
              iIntros "Hoc". iMod ("Hcontinner" with "Hoc") as "Hcont".
              iModIntro. wp_auto. simpl. wp_for_post. iFrame.
            }
          }
        }
        {
          iIntros "Hoc".
          iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. wp_for_post. iFrame.
        }
        {
          destruct draining; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
      }
      {
        iIntros "Hc". wp_auto.
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2 & Hrcv & Hok & Hsel)".
        wp_auto.
        wp_for_post.
        iFrame. iFrame "#".
      }
    }
  }
  {
    wp_if_destruct.
    {
      set clauses := (((⌜dir1 = W64 0⌝ ∗
            send_au_slow ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜dir1 = W64 1⌝ ∗
            rcv_au_slow ch1 cap1 γ1
              (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜W64 0 = W64 0⌝ ∗
              send_au_slow ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜W64 0 = W64 1⌝ ∗
              rcv_au_slow ch2 cap2 γ2
                (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V)))
        ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
      iDestruct "Hpre" as "[Hpre1 Hpre2]". iNamed "Hpre1".
      iDestruct "cap" as "cap1". iDestruct "mu" as "mu1". iDestruct "lock" as "lock1".
      iNamed "Hpre2".
      wp_apply ((wp_TrySend ch2 cap2 val2 γ2 clauses) with "[][HΦ zero1 zero2]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        iDestruct (and_elim_r with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct (length buff <? cap2); try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. unfold send_au_inner. iMod "Hcont". iModIntro. iModIntro.
          iNamed "Hcont". iFrame.
          destruct s; try done.
          {
            iIntros "Hoc". iMod ("Hcontinner" with "Hoc") as "Hcontinner".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
        {
          iIntros "Hoc".
          iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. wp_for_post. iFrame.
        }
      }
      {
        iIntros "Hc". wp_auto. wp_for_post.
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        iFrame. iFrame "#".
      }
    }
    {
      iDestruct "Hpre" as "[Hpre1 Hpre2]". iNamed "Hpre1".
      iDestruct "cap" as "cap1". iDestruct "mu" as "mu1". iDestruct "lock" as "lock1".
      iNamed "Hpre2".
      set clauses := (((⌜dir1 = W64 0⌝ ∗
            send_au_slow ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜dir1 = W64 1⌝ ∗
            rcv_au_slow ch1 cap1 γ1
              (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜dir2 = W64 0⌝ ∗
              send_au_slow ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜dir2 = W64 1⌝ ∗
              rcv_au_slow ch2 cap2 γ2
                (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V)))
        ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
        ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
        recv_val_ptr ↦ IntoValTyped1.(default_val V2) ∗
        selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
      wp_apply ((wp_TryReceive (V:=V2) ch2 cap2 γ2 clauses) with "[][HΦ zero1 zero2 recv_val ok selected]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2 & Hrcv & Hok & Hsel)".
        iDestruct (and_elim_r with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct buff; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. unfold send_au_inner. iMod "Hcont". iModIntro. iModIntro.
          iNamed "Hcont". iFrame.
          destruct s; try done.
          {
            iIntros "Hoc". iMod ("Hcontinner" with "Hoc") as "Hcontinner".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
          {
            destruct draining; try done.
            {
              iIntros "Hoc". iMod ("Hcontinner" with "Hoc") as "Hcont".
              iModIntro. wp_auto. simpl. wp_for_post. iFrame.
            }
          }
        }
        {
          iIntros "Hoc".
          iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. wp_for_post. iFrame.
        }
        {
          destruct draining; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. wp_for_post. iFrame.
          }
        }
      }
      {
        iIntros "Hc". wp_auto.
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2 & Hrcv & Hok & Hsel)".
        wp_auto.
        wp_for_post.
        iFrame. iFrame "#".
      }
    }
  }
Qed.

Lemma wp_NonBlockingSelect2 (ch1: loc) (cap1: Z) (γ1: chan_names) (dir1: u64) (val1: V1)
                         (ch2: loc) (cap2: Z) (γ2: chan_names) (dir2: u64) (val2: V2):
  ∀ (Φ: val → iProp Σ),
  is_pkg_init channel ∗ is_channel (V:=V1) ch1 cap1 γ1 ∗ is_channel (V:=V2) ch2 cap2 γ2 -∗
  ((⌜dir1 = W64 0⌝ ∗ send_au_fast ch1 cap1 val1 γ1 (Φ (#(W64 0), #(default_val V1), #(default_val V2), #false)%V)) ∨
   (⌜dir1 = W64 1⌝ ∗ rcv_au_fast ch1 cap1 γ1 (λ (v:V1) ok, Φ (#(W64 0), #v, #(default_val V2), #ok)%V))) ∧
  ((⌜dir2 = W64 0⌝ ∗ send_au_fast ch2 cap2 val2 γ2 (Φ (#(W64 1), #(default_val V1), #(default_val V2), #false)%V)) ∨
   (⌜dir2 = W64 1⌝ ∗ rcv_au_fast ch2 cap2 γ2 (λ v ok, Φ (#(W64 1), #(default_val V1), #v, #ok)%V))) ∧
  (Φ (#(W64 2), #(default_val V1), #(default_val V2), #false)%V) -∗
  WP @! channel.NonBlockingSelect2 #t1 #t2 #ch1 #dir1 #val1 #ch2 #dir2 #val2 {{ Φ }}.
Proof.
  wp_start.
  wp_auto.
  wp_apply (wp_RandomUint64). iIntros (x). iIntros "H". wp_auto.
  wp_if_destruct.
  {
    wp_if_destruct.
    {
      set clauses := (((⌜W64 0 = W64 0⌝ ∗
            send_au_fast ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜W64 0 = W64 1⌝ ∗
            rcv_au_fast ch1 cap1 γ1
              (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜dir2 = W64 0⌝ ∗
              send_au_fast ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜dir2 = W64 1⌝ ∗
              rcv_au_fast ch2 cap2 γ2
                (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
             ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
        ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
      iDestruct "Hpre" as "[Hpre1 Hpre2]". iNamed "Hpre1".
      iDestruct "cap" as "cap1". iDestruct "mu" as "mu1". iDestruct "lock" as "lock1".
      iNamed "Hpre2".
      wp_apply ((wp_TrySend_nb ch1 cap1 val1 γ1 clauses) with "[][HΦ zero1 zero2]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        iDestruct (and_elim_l with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct (length buff <? cap1); try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. simpl. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. iFrame.
        }
      }
      {
        iIntros "Hoc". wp_auto.
        wp_if_destruct.
        {
          wp_apply ((wp_TrySend_nb ch2 cap2 val2 γ2 clauses) with "[][Hoc]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iExists s. iFrame.
            destruct s; try done.
            {
              destruct (length buff <? cap2); try done.
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. simpl. iFrame.
              }
            }
            {
              iFrame.
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
          }
          {
            iIntros "Hoc".
            wp_auto. iFrame. unfold clauses.
            iDestruct "Hoc" as "(Hc & Hzp1 & Hzp2)".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            wp_auto. iFrame.
          }
        }
        {
          unfold clauses.
          set clauses1 := (((⌜W64 0 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜W64 0 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜dir2 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜dir2 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V) ∗
            zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
            ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
            recv_val_ptr ↦ IntoValTyped1.(default_val V2) ∗
            selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
          wp_apply ((wp_TryReceive_nb (V:=V2) ch2 cap2 γ2 clauses1) with "[][Hoc recv_val ok selected]").
          { iFrame "#". }
          {
            iFrame. iIntros "Hoc".
            iDestruct "Hoc" as "(Hc & Hs & Hs1 & Hs2 & Hs3 & Hs4)".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct buff; try done.
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
            {
              destruct draining; try done.
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
          }
          {
            iIntros "Hq".
            wp_auto. unfold clauses1. iDestruct "Hq" as "(Hc & Hzp1 & Hzp2 & Hok & Hrecv & Hsel)".
            wp_auto.
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iFrame.
          }
        }
      }
    }
    {
      iDestruct "Hpre" as "[#Hpre1 #Hpre2]".
      set clauses1 := (((⌜dir1 = W64 0⌝ ∗
            send_au_fast ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜dir1 = W64 1⌝ ∗
            rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜dir2 = W64 0⌝ ∗
              send_au_fast ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜dir2 = W64 1⌝ ∗
              rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
             ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V
      ) ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
      ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
      recv_val_ptr ↦ IntoValTyped0.(default_val V1) ∗
      selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
      wp_apply ((wp_TryReceive_nb (V:=V1) ch1 cap1 γ1 clauses1) with "[][HΦ zero1 zero2 recv_val ok selected]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses1. iDestruct "Hc" as "(Hc & Hs & Hs1 & Hr & Hzp1 & Hzp2)".
        iDestruct (and_elim_l with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct buff; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. iFrame.
        }
        {
          destruct draining; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. iFrame.
          }
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. iFrame.
          }
        }
      }
      {
        iIntros "Hq".
        wp_auto. unfold clauses1. iDestruct "Hq" as "(Hc & Hzp1 & Hzp2 & Hok & Hrecv & Hsel)".
        wp_auto.
        wp_if_destruct.
        {
          set clauses := (((⌜dir1 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜dir1 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜W64 0 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜W64 0 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
          wp_apply ((wp_TrySend_nb ch2 cap2 val2 γ2 clauses) with "[][Hc Hzp1 Hzp2]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct (length buff <? cap2); try done.
              {
                iIntros "Hc". iMod ("Hcont" with "Hc") as "Hcont".
                iModIntro. wp_auto. simpl. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
          }
          {
            iIntros "Hc". wp_auto. unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
            wp_auto.
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iFrame.
          }
        }
        {
          rename ok_ptr into ok_ptr0.
          rename recv_val_ptr into recv_val_ptr0.
          rename selected_ptr into selected_ptr0.
          wp_auto.
          set clauses := (((⌜dir1 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜dir1 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜dir2 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜dir2 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V
          ) ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
          ok_ptr0 ↦true ∗ recv_val_ptr0 ↦ IntoValTyped0.(default_val V1) ∗ selected_ptr0 ↦ into_val_typed_bool.(default_val bool) ∗
          ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
          recv_val_ptr ↦ IntoValTyped1.(default_val V2) ∗
          selected_ptr ↦ false)%I.
          wp_apply ((wp_TryReceive_nb (V:=V2) ch2 cap2 γ2 clauses) with "[][Hc Hzp1 Hzp2 Hsel Hrecv Hok ok recv_val selected]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses1. iDestruct "Hc" as "(Hc & Hs & Hs1 & Hr & Hzp1 & Hzp & Hzp2 & Hzp3 & Hzp4)".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct buff; try done.
              {
                iFrame.
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
            {
              destruct draining; try done.
              {
                iFrame.
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
          }
          {
            iIntros "Hq".
            wp_auto. unfold clauses1. iDestruct "Hq" as "(Hc & Hzp1 & Hzp2 & Hok & Hrecv & Hsel & Hzp3 & Hzp4 & Hzp5)".
            wp_auto.
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iFrame.
          }
        }
      }
    }
  }
  {
    wp_if_destruct.
    {
      set clauses := (((⌜dir1 = W64 0⌝ ∗
            send_au_fast ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜dir1 = W64 1⌝ ∗
            rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜W64 0 = W64 0⌝ ∗
              send_au_fast ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜W64 0 = W64 1⌝ ∗
              rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
             ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
        ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
      iDestruct "Hpre" as "[#Hpre1 #Hpre2]".
      wp_apply ((wp_TrySend_nb ch2 cap2 val2 γ2 clauses) with "[][HΦ zero1 zero2]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        iDestruct (and_elim_r with "Hc") as "Hc".
        iDestruct (and_elim_l with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct (length buff <? cap2); try done.
          {
            iIntros "Hc". iMod ("Hcont" with "Hc") as "Hcont".
            iModIntro. wp_auto. simpl. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. iFrame.
        }
      }
      {
        iIntros "Hc". wp_auto. unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
        wp_if_destruct.
        {
          set clauses1 := (((⌜W64 0 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜W64 0 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜W64 0 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜W64 0 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
          wp_apply ((wp_TrySend_nb ch1 cap1 val1 γ1 clauses1) with "[][Hc Hzp1 Hzp2]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct (length buff <? cap1); try done.
              {
                iIntros "Hc". iMod ("Hcont" with "Hc") as "Hcont".
                iModIntro. wp_auto. simpl. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
          }
          {
            iIntros "Hc1".
            wp_auto. unfold clauses1.
            iDestruct "Hc1" as "(Hc & Hzp1 & Hzp2)".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            wp_auto.
            iFrame.
          }
        }
        {
          set clauses1 := (((⌜dir1 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜dir1 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜W64 0 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜W64 0 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V
          ) ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
          ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
          recv_val_ptr ↦ IntoValTyped0.(default_val V1) ∗
          selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
          wp_apply ((wp_TryReceive_nb (V:=V1) ch1 cap1 γ1 clauses1) with "[][Hc Hzp1 Hzp2 recv_val ok selected]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses1. iDestruct "Hc" as "(Hc & Hs & Hs1 & Hr & Hzp1 & Hzp2)".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct buff; try done.
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
            {
              destruct draining; try done.
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
          }
          {
            iIntros "Hd". wp_auto.
            unfold clauses1. iDestruct "Hd" as "(Hc & Hs & Hs1 & Hok & Hrecv & Hsel)".
            wp_auto.
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iFrame.
          }
        }
      }
    }
    {
      iDestruct "Hpre" as "[#Hpre1 #Hpre2]".
      set clauses1 := (((⌜dir1 = W64 0⌝ ∗
            send_au_fast ch1 cap1 val1 γ1
              (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∨ ⌜dir1 = W64 1⌝ ∗
            rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
           ∧ (⌜dir2 = W64 0⌝ ∗
              send_au_fast ch2 cap2 val2 γ2
                (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
              ∨ ⌜dir2 = W64 1⌝ ∗
              rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
             ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V
      ) ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
      ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
      recv_val_ptr ↦ IntoValTyped1.(default_val V2) ∗
      selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
      wp_apply ((wp_TryReceive_nb (V:=V2) ch2 cap2 γ2 clauses1) with "[][HΦ zero1 zero2 recv_val ok selected]").
      { iFrame "#". }
      {
        iFrame.
        iIntros "Hc".
        unfold clauses1. iDestruct "Hc" as "(Hc & Hs & Hs1 & Hr & Hzp1 & Hzp2)".
        iDestruct (and_elim_r with "Hc") as "Hc".
        iDestruct (and_elim_l with "Hc") as "Hc".
        iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
        iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
        destruct s; try done.
        {
          destruct buff; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. iFrame.
          }
        }
        {
          iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
          iModIntro. wp_auto. iFrame.
        }
        {
          destruct draining; try done.
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. iFrame.
          }
          {
            iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
            iModIntro. wp_auto. iFrame.
          }
        }
      }
      {
        iIntros "Hq".
        wp_auto. unfold clauses1. iDestruct "Hq" as "(Hc & Hzp1 & Hzp2 & Hok & Hrecv & Hsel)".
        wp_auto.
        wp_if_destruct.
        {
          set clauses := (((⌜W64 0 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜W64 0 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜dir2 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜dir2 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
            ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2))%I.
          wp_apply ((wp_TrySend_nb ch1 cap1 val1 γ1 clauses) with "[][Hc Hzp1 Hzp2]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct (length buff <? cap1); try done.
              {
                iIntros "Hc". iMod ("Hcont" with "Hc") as "Hcont".
                iModIntro. wp_auto. simpl. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
          }
          {
            iIntros "Hc". wp_auto. unfold clauses. iDestruct "Hc" as "(Hc & Hzp1 & Hzp2)".
            wp_auto.
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iFrame.
          }
        }
        {
          rename ok_ptr into ok_ptr0.
          rename recv_val_ptr into recv_val_ptr0.
          rename selected_ptr into selected_ptr0.
          wp_auto.
          set clauses := (((⌜dir1 = W64 0⌝ ∗
                send_au_fast ch1 cap1 val1 γ1
                  (Φ (# (W64 0), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                ∨ ⌜dir1 = W64 1⌝ ∗
                rcv_au_fast ch1 cap1 γ1 (λ (v : V1) (ok : bool), Φ (# (W64 0), # v, # IntoValTyped1.(default_val V2), # ok)%V))
               ∧ (⌜dir2 = W64 0⌝ ∗
                  send_au_fast ch2 cap2 val2 γ2
                    (Φ (# (W64 1), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V)
                  ∨ ⌜dir2 = W64 1⌝ ∗
                  rcv_au_fast ch2 cap2 γ2 (λ (v : V2) (ok : bool), Φ (# (W64 1), # IntoValTyped0.(default_val V1), # v, # ok)%V))
                 ∧ Φ (# (W64 2), # IntoValTyped0.(default_val V1), # IntoValTyped1.(default_val V2), # false)%V
          ) ∗ zero1_ptr ↦ IntoValTyped0.(default_val V1) ∗ zero2_ptr ↦ IntoValTyped1.(default_val V2) ∗
          ok_ptr0 ↦true ∗ recv_val_ptr0 ↦ IntoValTyped1.(default_val V2) ∗ selected_ptr0 ↦ false ∗
          ok_ptr ↦ into_val_typed_bool.(default_val bool) ∗
          recv_val_ptr ↦ IntoValTyped0.(default_val V1) ∗
          selected_ptr ↦ into_val_typed_bool.(default_val bool))%I.
          wp_apply ((wp_TryReceive_nb (V:=V1) ch1 cap1 γ1 clauses) with "[][Hc Hzp1 Hzp2 Hsel Hrecv Hok ok recv_val selected]").
          { iFrame "#". }
          {
            iFrame.
            iIntros "Hc".
            unfold clauses1. iDestruct "Hc" as "(Hc & Hs & Hs1 & Hr & Hzp1 & Hzp & Hzp2 & Hzp3 & Hzp4)".
            iDestruct (and_elim_l with "Hc") as "Hc".
            iDestruct "Hc" as "[[%Ht Hau]|[%Hf Hau]]"; try done.
            iMod "Hau". iModIntro. iModIntro. iNamed "Hau". iFrame.
            destruct s; try done.
            {
              destruct buff; try done.
              {
                iFrame.
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
            {
              iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
              iModIntro. wp_auto. iFrame.
            }
            {
              destruct draining; try done.
              {
                iFrame.
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
              {
                iIntros "Hoc". iMod ("Hcont" with "Hoc") as "Hcont".
                iModIntro. wp_auto. iFrame.
              }
            }
          }
          {
            iIntros "Hq".
            wp_auto. unfold clauses1. iDestruct "Hq" as "(Hc & Hzp1 & Hzp2 & Hok & Hrecv & Hsel & Hzp3 & Hzp4 & Hzp5)".
            wp_auto.
            iDestruct (and_elim_r with "Hc") as "Hc".
            iDestruct (and_elim_r with "Hc") as "Hc".
            iFrame.
          }
        }
      }
    }
  }
Qed.

End select.
