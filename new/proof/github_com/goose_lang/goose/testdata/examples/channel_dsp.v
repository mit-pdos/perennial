From New.proof.github_com.goose_lang.goose.testdata.examples Require Import channel_examples_init.
From New.proof.github_com.goose_lang.goose.model.channel
  Require Import idiom.base dsp dsp_proofmode mpmc.
From New.code Require Import github_com.goose_lang.goose.testdata.examples.channel.
Import chan_spec_raw_examples.
From New.golang Require Import theory.
From iris.algebra Require Import gmultiset.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : chan_spec_raw_examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Instance stream_eq_dec : EqDecision chan_spec_raw_examples.streamold.t.
Proof. solve_decision. Qed.
Instance stream_countable : Countable chan_spec_raw_examples.streamold.t.
Proof.
  refine (inj_countable'
           (λ x, (streamold.req' x, streamold.res' x, streamold.f' x))
          (λ '(a, b, c), streamold.mk a b c) _).
  by intros [].
Defined.

Section dsp_examples.
Context `{!dspG Σ interface.t}.

Definition ref_prot : iProto Σ interface.t :=
  <! (l:loc) (x:Z)> MSG (interface.mk_ok (go.PointerType go.int) #l) {{ l ↦ W64 x }} ;
  <?> MSG (interface.mk_ok (go.StructType []) #()) {{ l ↦ w64_word_instance.(word.add) (W64 x) (W64 2) }} ;
  END.
Lemma wp_DSPExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.DSPExample #()
  {{{ RET #(W64 42); True }}}.
Proof using dspG0 W.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros (c γ) "(#Hic & _Hcap & Hoc)". wp_auto.
  wp_apply chan.wp_make1.
  iIntros (signal γ') "(#Hicsignal & _Hcapsignal & Hocsignal)". wp_auto.
  iMod (dsp_session_init _ _ _ _ _ _ _ ref_prot with "Hic Hicsignal Hoc Hocsignal")
                       as (γdsp1 γdsp2) "[Hc Hcsignal]";
    [by eauto|by eauto|..].
  iPersist "c signal".
  wp_apply (wp_fork with "[Hcsignal]").
  { wp_auto. wp_recv (l x) as "Hl". wp_auto.
    rewrite -> decide_True; last done. wp_auto.
    wp_send with "[$Hl]". by wp_auto.
  }
  wp_send with "[$val]". wp_auto. wp_recv as "Hl".
  wp_auto. by iApply "HΦ".
Qed.

End dsp_examples.

Section serve.
Context `{!dspG Σ go_string}.

Definition service_prot_aux (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ)
  (rec : iProto Σ _) : iProto Σ _ :=
  <! (req:go_string)> MSG req {{ Φpre req }} ;
  <? (res:go_string)> MSG res {{ Φpost req res }}; rec.

Instance service_prot_contractive Φpre Φpost : Contractive (service_prot_aux Φpre Φpost).
Proof. solve_proto_contractive. Qed.

Definition service_prot Φpre Φpost := fixpoint (service_prot_aux Φpre Φpost).

Instance service_prot_unfold Φpre Φpost :
  ProtoUnfold (service_prot Φpre Φpost)
    (service_prot_aux Φpre Φpost (service_prot Φpre Φpost)).
Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

Lemma wp_Serve (f: func.t) Φpre Φpost  :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hf_spec" ∷ □ (∀ (strng: go_string),
          Φpre strng → WP #f #strng {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}}
    @! chan_spec_raw_examples.Serve #f
  {{{ stream γ , RET #stream;
      (stream.(chan_spec_raw_examples.stream.req'),
          stream.(chan_spec_raw_examples.stream.res'))  ↣{γ} service_prot Φpre Φpost }}}.
Proof.
  wp_start. iNamed "Hpre".
  wp_auto. wp_apply chan.wp_make1.
  iIntros (res_ch γ_res) "(#Hres & _ & Hown_res)". wp_auto_lc 1.
  wp_apply chan.wp_make1. iIntros (req_ch γ_req) "(#Hreq & _ & Hown_req)".


  (* Initialize idiom *)
  wp_apply wp_fupd.
  iMod (dsp_session_init _ res_ch req_ch _ _ _ _
          (service_prot Φpre Φpost)
        with "Hres Hreq Hown_res Hown_req") as (γdsp1 γdsp2) "[Hclient Hserver]";
    [by eauto|by eauto|..].
  iModIntro.
  wp_auto.
  iPersist "s".

  wp_apply (wp_fork with "[Hserver f]").
  {
    wp_auto.
      iAssert (

    "Hprot" ∷  (req_ch, res_ch)  ↣{γdsp2}
                 iProto_dual (service_prot Φpre Φpost)
  )%I with "[s Hserver]" as "IH".
  { iFrame. }
    wp_for "IH".
  {


  wp_recv (req_val) as "Hre".
  wp_auto.
  wp_bind (#f #req_val)%E.
  iApply (wp_wand with "[Hf_spec Hre]").
  {
     iSpecialize ("Hf_spec" $! req_val). subst. iApply ("Hf_spec" with "Hre").
  }
  iIntros (v).
  iIntros "H".
  iDestruct "H" as (s') "[%Heq_v Heq_log]".
  wp_auto.
  subst.
  wp_send with "[Heq_log]".
  {
    done.
  }
  wp_auto.
  wp_for_post.
  iFrame.
  }
}
iApply "HΦ".
  done.
  Qed.

Lemma wp_appWrld (s: go_string) :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.appWrld #s
  {{{ RET #(s ++ ", World!"%go); True }}}.
Proof.
  wp_start.
  wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_Client:
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.Client #()
  {{{ RET #"Hello, World!"; True%I }}}.
Proof using dspG0 W.
  wp_start.
  wp_auto.

  wp_apply (wp_Serve _ (λ _, True%I) (λ s1 s2, ⌜s2 = s1 ++ ", World!"%go⌝%I)).
  { iIntros "!>" (s) "_". wp_apply wp_appWrld. iExists  (s ++ ", World!"%go). iPureIntro. done.
    }
  iIntros (hw γ) "Hprot".
  wp_auto.

  wp_send with "[//]".
  wp_auto.

  wp_recv (?) as "->".
  wp_auto.
  by iApply "HΦ".
Qed.

End serve.


Section muxer.
Context `{!contributionG Σ (gmultisetUR streamold.t)}.
Context `{!dspG Σ go_string}.
(* perennial ghost_var, not iris *)
Context `{!ghost_var.ghost_varG Σ bool}.

Definition mapper_service_prot_aux (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ)
  (rec : iProto Σ _) : iProto Σ _ :=
  <! (req:go_string)> MSG req {{ Φpre req }} ;
  <? (res:go_string)> MSG res {{ Φpost req res }}; rec.

Instance mapper_service_prot_contractive Φpre Φpost : Contractive (mapper_service_prot_aux Φpre Φpost).
Proof. solve_proto_contractive. Qed.
Definition mapper_service_prot Φpre Φpost := fixpoint (mapper_service_prot_aux Φpre Φpost).
Instance mapper_service_prot_unfold Φpre Φpost :
  ProtoUnfold (mapper_service_prot Φpre Φpost)
    (mapper_service_prot_aux Φpre Φpost (mapper_service_prot Φpre Φpost)).
Proof. apply proto_unfold_eq, (fixpoint_unfold _). Qed.

Definition is_mapper_stream stream : iProp Σ :=
  ∃ γ req_ch res_ch f (Φpre : go_string → iProp Σ) (Φpost : go_string → go_string → iProp Σ),
  ⌜stream = {| streamold.req' := req_ch; streamold.res' := res_ch; streamold.f' := f |}⌝ ∗
  "Hf_spec" ∷ □ (∀ (s: go_string),
      Φpre s → WP #f #s {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost s s' }}) ∗
    (res_ch, req_ch) ↣{γ} iProto_dual (mapper_service_prot Φpre Φpost).

Lemma wp_mkStream (f: func.t) Φpre Φpost :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hf_spec" ∷ □ (∀ (strng: go_string),
                        Φpre strng -∗ WP #f #strng {{ λ v, ∃ (s': go_string), ⌜v = #s'⌝ ∗ Φpost strng s' }}) }}}
    @! chan_spec_raw_examples.mkStream #f
  {{{ γ stream, RET #stream;
      is_mapper_stream stream ∗
      (stream.(streamold.req'), stream.(streamold.res')) ↣{γ} mapper_service_prot Φpre Φpost }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make1.
  iIntros (ch1). iIntros (γ1). iIntros "(#His_chan1 & _ & Hownchan1)".
  wp_auto_lc 1. wp_apply chan.wp_make1.
  iIntros (ch). iIntros (γ). iIntros "(#His_chan & _ & Hownchan)".
  wp_apply wp_fupd.

  iMod (dsp_session_init _ ch1 ch _ _ _ _
          (mapper_service_prot Φpre Φpost) with "His_chan1 His_chan Hownchan1 Hownchan")
    as (γdsp1 γdsp2) "[Hpl Hpr]";
    [by eauto|by eauto|..].
  iModIntro. wp_auto.
  iApply "HΦ".
  simpl. iSplitR "Hpl"; [ | iFrame ]. (* iSplit is for performance *)
  rewrite /is_mapper_stream /=.
  iExists _, _, _, _, _, _. iSplit; [done|].
  iDestruct "Hpre" as "#Hpre". iFrame "Hpr".
  iIntros "!>" (s) "HΦ". by iApply "Hpre".
Qed.

Lemma wp_MapServer (my_stream: streamold.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_mapper_stream my_stream }}}
    @! chan_spec_raw_examples.MapServer #my_stream
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  iNamed "Hpre".
  wp_auto.
  iDestruct "Hpre" as (Heq) "[#Hf_spec Hprot]".
  iAssert (
    "s" ∷ s_ptr ↦ my_stream ∗

    "Hprot" ∷ (my_stream.(streamold.res'), my_stream.(streamold.req')) ↣{γ}
                 iProto_dual (mapper_service_prot Φpre Φpost)
  )%I with "[s Hf_spec Hprot]" as "IH".
  { iFrame. subst. iFrame. }

  wp_for.
  iNamed "IH".
  wp_auto.

  wp_recv (req_val) as "Hreq".
  wp_auto.
  wp_pures.

  wp_bind (#my_stream.(streamold.f') #req_val)%E.
  iApply (wp_wand with "[Hf_spec Hreq]").
  { iSpecialize ("Hf_spec" $! req_val). subst. iApply ("Hf_spec" with "Hreq"). }
  iIntros (v) "Hv".
  iDestruct "Hv" as (s') "[%Heq_v Heq_log]".
  subst.
  wp_auto.
  wp_pures.
  wp_send with "[Heq_log]";first done.
  wp_auto.
  wp_for_post.
  iFrame.
Qed.

Lemma wp_MapClient (my_stream: streamold.t) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_mapper_stream my_stream }}}
    @! chan_spec_raw_examples.ClientOld #()
  {{{ RET #"Hello, World!"; True%I }}}.
Proof.
  wp_start.
  wp_auto.
    wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ ","%go⌝)%I).
    {
       iIntros (s) "!> _". wp_auto. by eauto.
    }
    iIntros (γ stream).
    iIntros "Hmapper".
    wp_auto.
    wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ "!"%go⌝)%I).
    {
       iIntros (s) "!> _". wp_auto. by eauto.
    }
    iIntros (γ' s').
    iIntros "H'".
    wp_auto.
    iDestruct "Hmapper" as "[Hmapper Hstr]".
    iDestruct "H'" as "[Hmapper' Hstr']".

  wp_apply (wp_fork with "[Hmapper]").
  {
        wp_apply (wp_MapServer with "[$Hmapper]").
done.
  }
  wp_apply (wp_fork with "[Hmapper']").
  {
        wp_apply (wp_MapServer with "[$Hmapper']").
done.
  }
  wp_send with "[//]".
  wp_auto.
  wp_send with "[//]".
  wp_auto.
  wp_recv (?) as "->". wp_auto.
  wp_recv (?) as "->". wp_auto.
  iApply "HΦ".
  done.
Qed.

Lemma wp_Muxer (c: loc) γmpmc (n_prod n_cons: nat) :
  {{{ is_pkg_init chan_spec_raw_examples ∗
      "#Hismpmc" ∷ is_mpmc γmpmc c n_prod n_cons is_mapper_stream (λ _, True) ∗
      "Hcons" ∷ mpmc_consumer γmpmc (∅ : gmultiset streamold.t) }}}
    @! chan_spec_raw_examples.Muxer #c
  {{{ RET #(); True%I }}}.
Proof.
   wp_start. wp_auto_lc 3. iNamed "Hpre".
   iAssert (∃ (received: gmultiset streamold.t) (s_val: streamold.t),
    "s" ∷ s_ptr ↦ s_val ∗
    "Hcons" ∷ mpmc_consumer γmpmc received
  )%I with "[s Hcons]" as "IH".
  { iExists ∅, _. iFrame. }

  wp_for "IH".
    wp_apply (@wp_mpmc_receive with "[$Hcons]").
    {
      iFrame "#".

    }
    iIntros (v).
    iIntros (ok).
    destruct ok.
    {
      iIntros "H". iDestruct "H" as "[Hdat Hcons]".
      iNamed "Hdat".
      wp_auto.
      wp_apply (wp_fork with "[Hdat]").
      {
        by wp_apply (wp_MapServer with "[$Hdat]").
      }
      wp_for_post.
      iFrame.
    }
    {
      iIntros "[#Hclosed Hcons]".
      wp_auto.
      wp_for_post.
      iApply "HΦ".
      done.
    }
Qed.

Lemma wp_makeGreeting :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.makeGreeting #()
  {{{ RET #"Hello, World!"; True%I }}}.
Proof using contributionG0 dspG0 W.
  wp_start. wp_auto.
  wp_apply chan.wp_make2; [done|].
  iIntros (c γ) "(#Hic & _ & Hoc)". wp_auto.
  iMod (start_mpmc _ _ _ _ 1 1 with "Hic Hoc") as (γmpmc) "[#Hmpmc [[Hprod _] [Hcons _]]]";
    [done|lia..|].
  wp_apply (wp_fork with "[Hcons]").
  { wp_apply (wp_Muxer with "[Hcons]"); [|done]. iFrame "Hmpmc Hcons". }
  wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ ","%go⌝)%I).
  { iIntros (s) "!> _". wp_auto. by eauto. }
  iIntros (γ1 stream1) "[Hstream1 Hc1]".
  wp_auto.
  wp_apply (wp_mkStream _ (λ _, True)%I (λ s1 s2, ⌜s2 = s1 ++ "!"%go⌝)%I).
  { iIntros (s) "!> _". wp_auto. by eauto. }
  iIntros (γ2 stream2) "[Hstream2 Hc2]".
  wp_auto.
  wp_apply (@wp_mpmc_send with "[$Hmpmc $Hprod $Hstream1]").
  iIntros "Hprod". wp_auto.
  wp_apply (@wp_mpmc_send with "[$Hmpmc $Hprod $Hstream2]").
  iIntros "Hprod". wp_auto. wp_send with "[//]".
  wp_auto. wp_send with "[//]". wp_auto. wp_recv (?) as "->". wp_auto.
  wp_recv (?) as "->". wp_auto.
  by iApply "HΦ".
Qed.

End muxer.
End proof.
