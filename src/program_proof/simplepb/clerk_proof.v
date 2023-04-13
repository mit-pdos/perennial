From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb Require Export clerk.
From Perennial.program_proof.simplepb Require Import pb_definitions pb_apply_proof pb_makeclerk_proof.
From Perennial.program_proof.simplepb Require Import config_protocol_proof.

Section clerk_proof.
Context `{!heapGS Σ}.
Context {pb_record:Sm.t}.

Notation OpType := (Sm.OpType pb_record).
Notation has_op_encoding := (Sm.has_op_encoding pb_record).
Notation has_snap_encoding := (Sm.has_snap_encoding pb_record).
Notation compute_reply := (Sm.compute_reply pb_record).
Notation pbG := (pbG (pb_record:=pb_record)).
Notation is_pb_Clerk := (pb_definitions.is_Clerk (pb_record:=pb_record)).

Context `{!pbG Σ}.
Context `{!config_proof.configG Σ}.

Definition own_Clerk ck γ : iProp Σ :=
  ∃ (confCk primaryCk:loc) γprimary,
    "HprimaryCk" ∷ ck ↦[clerk.Clerk :: "primaryCk"] #primaryCk ∗
    "#HconfCk" ∷ readonly (ck ↦[clerk.Clerk :: "confCk"] #confCk) ∗
    "#HisConfCk" ∷ is_Clerk2 confCk γ ∗ (* config clerk *)
    "#HisPrimaryCk" ∷ pb_definitions.is_Clerk primaryCk γ
.

Lemma wp_MakeClerk γ γsys configHost:
  {{{
        "#Hinv" ∷ is_inv γ ∗
        "#Hconf" ∷ is_conf_host configHost γsys
  }}}
    Make #configHost
  {{{
        (ck:loc), RET #ck; own_Clerk ck γ
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  wp_apply (wp_allocStruct).
  { repeat constructor. }
  iIntros (?) "Hl".
  iDestruct (struct_fields_split with "Hl") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_MakeClerk2 with "[$]").
  iIntros (?) "#HconfCk".
  wp_storeField.
  wp_pures.

  wp_forBreak.
  wp_pures.
  wp_loadField.
  wp_bind (config.Clerk__GetConfig _).
  wp_apply (wp_frame_wand with "[-HconfCk]").
  { iNamedAccu. }
  wp_apply (wp_Clerk__GetConfig2 with "HconfCk").
  iModIntro.
  iIntros (???) "[Hconf_sl #Hhost]".
  iNamed 1.
  wp_pures.
  wp_apply (wp_slice_len).
  wp_if_destruct.
  {
    iLeft.
    iModIntro.
    iFrame.
    done.
  }
  iDestruct (is_slice_small_sz with "Hconf_sl") as "%Hlen".
  iDestruct (big_sepL2_length with "Hhost") as %Hleneq.
  assert (length conf > 0).
  {
    rewrite Hlen.
    destruct (decide (config_sl.(Slice.sz) = 0)).
    { exfalso. rewrite e in Heqb. done. }

    destruct (decide (int.nat config_sl.(Slice.sz) = 0)).
    {
      exfalso.
      replace (config_sl.(Slice.sz)) with (U64 0) in * by word.
      done.
    }
    word.
  }

  destruct conf.
  {
    exfalso.
    simpl in *. lia.
  }
  wp_apply (wp_SliceGet with "[$Hconf_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsl".
  simpl.
  destruct confγs.
  {
    exfalso.
    simpl in *. lia.
  }

  wp_apply (wp_MakeClerk with "[]").
  {
    iDestruct (big_sepL2_cons) as "[H _]".
    iDestruct ("H" with "Hhost") as "[$ _]".
  }
  iIntros (?) "Hpbck".
  wp_storeField.
  iRight.
  iModIntro.
  iSplitR; first done.
  wp_pures.
  iApply "HΦ".
  iMod (readonly_alloc_1 with "confCk") as "#?".
  iModIntro.
  repeat iExists _.
  iFrame "∗#".
Qed.

(* FIXME: is_inv should stay internal to pb library *)
Lemma wp_Clerk__Apply γ ck op_sl op (op_bytes:list u8) (Φ:val → iProp Σ) :
has_op_encoding op_bytes op →
own_Clerk ck γ -∗
is_slice_small op_sl byteT 1 op_bytes -∗
□((|={⊤∖↑pbN,∅}=> ∃ ops, own_log γ ops ∗
  (own_log γ (ops ++ [op]) ={∅,⊤∖↑pbN}=∗
     (∀ reply_sl, is_slice_small reply_sl byteT 1 (compute_reply ops op) -∗
                  is_slice_small op_sl byteT 1 op_bytes -∗
                  own_Clerk ck γ -∗ Φ (slice_val reply_sl)%V)))) -∗
WP clerk.Clerk__Apply #ck (slice_val op_sl) {{ Φ }}.
Proof.
  iIntros (?) "Hck Hop_sl #Hupd".
  wp_call.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (ret) "Hret".
  wp_pures.

  iAssert (
      ∃ some_sl,
        "Hret" ∷ ret ↦[slice.T byteT] (slice_val some_sl)
    )%I with "[Hret]" as "HH".
  { replace (zero_val (slice.T byteT)) with (slice_val Slice.nil) by done. iExists _; iFrame. }
  wp_forBreak.
  iNamed "HH".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (err) "Herr".
  wp_pures.
  iNamed "Hck".
  wp_loadField.

  wp_bind (Clerk__Apply _ _).
  wp_apply (wp_wand with "[Hop_sl]").
  { (* apply *)
    wp_apply (pb_apply_proof.wp_Clerk__Apply with "HisPrimaryCk Hinv Hop_sl").
    { done. }
    iModIntro.
    iSplitL.
    { (* successful case *)
      iMod "Hupd" as (?) "[Hown Hupd2]".
      iModIntro.
      iExists _.
      iFrame "Hown".
      iIntros "Hown".
      iMod ("Hupd2" with "Hown") as "Hupd2".
      iModIntro.
      iIntros (?) "Hsl Hsl2".
      iDestruct ("Hupd2" with "Hsl") as "HΦ".
      instantiate (1:=(λ (v:goose_lang.val),
        (∃ (reply_sl:Slice.t),
        ⌜v = (#0, slice_val reply_sl)%V⌝ ∗ (own_Clerk ck γ -∗ Φ (slice_val reply_sl))) ∨
        (∃ (err:u64) unused_sl, is_slice_small op_sl byteT 1 op_bytes ∗ ⌜err ≠ 0⌝ ∗ ⌜v = (#err, slice_val unused_sl)%V⌝))%I).
      simpl.
      iLeft.
      iExists _.
      iSpecialize ("HΦ" with "Hsl2").
      iSplitR; first done.
      iFrame.
    }
    { (* error case *)
      iIntros (?? Herr).
      iIntros "Hop_sl".
      iRight.
      iExists err0, _.
      iSplitL; first done.
      done.
    }
  }
  iIntros (v) "H1".
  iDestruct "H1" as "[Hsuccess|Herror]".
  {
    iDestruct "Hsuccess" as (?) "[-> HΦ]".
    wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_pures.
    iRight.
    iModIntro.
    iSplitR; first done.
    wp_pures.
    wp_load.
    iApply "HΦ".
    iModIntro.
    repeat iExists _.
    iFrame "∗#".
  }
  { (* retry *)
    iDestruct "Herror" as (??) "[Hop_sl Herror]".
    iDestruct "Herror" as "[%Herr ->]".
    wp_pures.
    wp_store.
    wp_store.
    wp_load.
    wp_pures.
    wp_if_destruct.
    {
      exfalso.
      done.
    }
    wp_apply (wp_Sleep).
    wp_pures.
    wp_loadField.
    wp_bind (config.Clerk__GetConfig _).
    wp_apply (wp_frame_wand with "[-]").
    { iNamedAccu. }
    wp_apply (wp_Clerk__GetConfig2 with "HisConfCk").
    iModIntro.
    iIntros (???) "[Hconf_sl #Hhosts]".
    iNamed 1.
    wp_pures.
    iDestruct (is_slice_small_sz with "Hconf_sl") as %Hconf_sz.
    wp_apply (wp_slice_len).
    wp_pures.
    wp_if_destruct.
    {
      iDestruct (big_sepL2_length with "Hhosts") as %Hlen.
      assert (0 < length conf) as HconfNe by word.
      destruct conf.
      {
        exfalso. simpl in HconfNe. word.
      }
      destruct confγs.
      {
        exfalso. rewrite -Hlen in HconfNe. simpl in HconfNe. word.
      }
      iDestruct big_sepL2_cons  as "[Hcons _]".
      iDestruct ("Hcons" with "Hhosts") as "[His_newPrimary HH]".
      wp_apply (wp_SliceGet with "[$Hconf_sl]").
      {
        rewrite lookup_cons.
        done.
      }
      iIntros "Hconf_sl".
      simpl.
      wp_apply (pb_makeclerk_proof.wp_MakeClerk with "[$His_newPrimary]").
      iIntros (newCk) "#HnewIsPrimaryCk".
      wp_storeField.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iSplitL "HprimaryCk".
      {
        repeat iExists _.
        iFrame "∗#".
      }
      iFrame.
      iExists _.
      iFrame.
    }
    {
      wp_pures.
      iLeft.
      iModIntro.
      iSplitR; first done.
      iSplitL "HprimaryCk".
      {
        repeat iExists _.
        iFrame "∗#".
      }
      iFrame.
      iExists _.
      iFrame.
    }
  }
Qed.

End clerk_proof.
