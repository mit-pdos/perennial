From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export  future spsc done dsp dsp_proofmode.
From New.proof Require Import time sync.
From Perennial.goose_lang Require Import lang.
From New.code.github_com.goose_lang.goose.testdata.examples Require Import channel.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.
From Perennial.goose_lang.lib Require Import slice.
From iris.base_logic Require Import ghost_map.
From New.golang.theory Require Import struct chan.

(* TODO: Move? *)
Global Instance wp_struct_make_unit {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi} 
  {Σ : gFunctors} {hG : heapGS Σ} {ffi_semantics0 : ffi_semantics ext ffi} :
  PureWp True (struct.make #(structT []) (alist_val []))%struct #().
Proof.
  erewrite <- struct_val_aux_nil.
  apply wp_struct_make; cbn; auto.
Qed.

Section hello_world.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chanGhostStateG Σ go_string}.  (* V = go_string *)
Context `{!ghost_varG Σ bool}.
Set Default Proof Using "Type".
#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Lemma wp_sys_hello_world :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.sys_hello_world #()
  {{{ RET #("Hello, World!"); True }}}.
Proof.
  wp_start. iApply "HΦ". done.
Qed.

Lemma wp_HelloWorldAsync :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_pkg_init channel  }}}
    @! chan_spec_raw_examples.HelloWorldAsync #()
  {{{ (ch: loc) (γfuture: future_names), RET #ch; is_future (V:=go_string) (t:=stringT) γfuture ch
        (λ (v : go_string), ⌜v = "Hello, World!"%go⌝)  ∗
      await_token γfuture }}}.
Proof.
  wp_start. wp_auto.
  wp_apply chan.wp_make; first done.
  iIntros (ch). iIntros (γ). iIntros "(#HisChan & Hownchan)".
  wp_auto.
  simpl in *.
  iDestruct ((start_future (V:=go_string) ch (λ v, ⌜ v = "Hello, World!"%go ⌝%I) γ) with "[$HisChan] [$Hownchan]") as ">(%γfuture & Hfut)".
  iDestruct "Hfut" as "(#Hisfut & Hawait & Hfulfill)".
  iPersist "ch".
  wp_apply (wp_fork with "[Hfulfill]").
  {
    wp_auto.
    wp_apply wp_sys_hello_world.
    iAssert (⌜"Hello, World!"%go = "Hello, World!"%go⌝)%I as "HP".
    { iPureIntro. reflexivity. }
    wp_apply (chan.wp_send with "[]") as "[Hlc _]".
    { iDestruct (future_is_channel with "Hisfut") as "$". }
  iApply (future_fulfill_au γfuture ch (λ v : go_string, ⌜v = "Hello, World!"%go⌝%I) "Hello, World!"%go
  with "[$] [$]").
    iIntros "!> _".
    wp_auto.
    done.
  }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_HelloWorldSync :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_pkg_init channel }}}
    @! chan_spec_raw_examples.HelloWorldSync #()
  {{{ RET #("Hello, World!"); True }}}.
Proof using chanGhostStateG0 ext ffi ffi_interp0 ffi_semantics0 ghost_varG0 go_ctx hG Σ.
  wp_start.
  wp_apply wp_HelloWorldAsync; first done.
  iIntros (ch γfuture) "[#Hfut Hawait]".
  wp_apply (chan.wp_receive) as "[Hlc _]".
  { iApply future_is_channel; done. }
  iApply (future_await_au (V:=go_string) (t:=stringT)  γfuture ch
               (λ (v : go_string), ⌜v = "Hello, World!"%go⌝%I) with "[$] [$Hawait $Hlc]").
  iIntros "!> %v %Heq". subst.
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End hello_world.


Section cancellable.
  Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!ghost_varG Σ bool}.
Context `{!chanGhostStateG Σ unit}.
Context `{!chanGhostStateG Σ go_string}.
Context `{!ghost_mapG Σ nat gname}.
Set Default Proof Using "Type".

#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.

Lemma wp_HelloWorldCancellable
  (done_ch : loc) (err_ptr1: loc) (err_msg: go_string)
  (γdone: done_names) :
  {{{ is_pkg_init channel ∗
        is_pkg_init chan_spec_raw_examples ∗

        is_done (V:=unit) (t:=structT []) γdone done_ch ∗
        Notified γdone (err_ptr1 ↦ err_msg)  }}}
    @! chan_spec_raw_examples.HelloWorldCancellable #done_ch #err_ptr1
    {{{
(result: go_string), RET #result;
      ⌜result = err_msg ∨ result = "Hello, World!"%go⌝
    }}}.
Proof using chanGhostStateG0 chanGhostStateG1 ghost_mapG0 ghost_varG0.

  wp_start. wp_apply wp_alloc.
  iIntros (l). iIntros "Herr".
  wp_auto_lc 4.
  wp_apply wp_HelloWorldAsync; first done.
  iIntros (ch γfuture) "[#Hfut Hawait]". wp_auto_lc 1.
  iDestruct "Hpre" as "(#H1 & H2)".
  iAssert ( is_channel (t:=structT []) done_ch 0 γdone.(chan_name)) as "#Hdonech".
  {
    iFrame "#".
    unfold is_done.
    iDestruct "H1" as "[#Hdone #Hinv]". iFrame "#".

  }
  iDestruct "Hfut" as "[#Hfut #Hinv1]". iFrame "#".
  wp_apply chan.wp_select_blocking.
  simpl.
    iSplit.
    {
      iFrame "Hfut".
      iRename select (£1) into "Hlc".
      iApply ((future_await_au  (V:=go_string) γfuture ch   )
               with " [$Hfut $Hinv1] [$Hawait $Hlc]").
      iNext. iIntros (v). iIntros "%Hw".
      wp_auto.
      subst v.
      iApply "HΦ".
      iPureIntro.
      right. done. }
    {
      iFrame "Hdonech".

      iApply ((done_receive_au  (V:=unit) γdone done_ch  (err_ptr1 ↦ err_msg)%I )
               with " [$H1] [H2] [HΦ Herr] [$]").
      {
        iFrame.
       }
       {

        iNext. iIntros "Herr'".
      wp_auto. iApply "HΦ". iLeft. done.
      }
      }

Qed.


Lemma wp_HelloWorldWithTimeout :
  {{{ is_pkg_init channel ∗
      is_pkg_init chan_spec_raw_examples
  }}}
    @!  chan_spec_raw_examples.HelloWorldWithTimeout #()
  {{{ (result: go_string), RET #result;
      ⌜result = "Hello, World!"%go ∨
        result = "operation timed out"%go⌝
  }}}.
  Proof using chanGhostStateG0 chanGhostStateG1 ext ffi ffi_interp0 ffi_semantics0 ghost_mapG0
ghost_varG0 go_ctx hG Σ.
  wp_start.
  wp_auto.
  wp_apply (chan.wp_make (t:=structT [])); first done.
  iIntros (ch γ) "[#Hchan Hoc]".
  simpl.
  iDestruct (start_done ch γ with "Hchan") as "Hstart".
iMod ("Hstart" with "Hoc") as (γdone) "(#Hdone & Hnot)".
wp_auto.
iPersist "done".

iMod (done_alloc_notified (t:=structT []) γdone ch True (errMsg_ptr ↦ "operation timed out"%go)%I
      with "[$Hdone] [$Hnot]") as "[HNotify HNotified]".
wp_apply (wp_fork with "[HNotify errMsg done]").
{ wp_auto.
  wp_apply wp_Sleep.
  wp_apply (chan.wp_close (V:=()) with "[]") as "(Hlc1 & Hlc2 & Hlc3 & _)".
  { iApply (done_is_channel with "Hdone"). }
  iApply (done_close_au (V:=()) with "[$] [$] [$HNotify errMsg]").
  { iFrame. }
  iNext.
  wp_auto.
  done. }

wp_apply (wp_HelloWorldCancellable with "[$Hdone $HNotified][HΦ]").
{
  done.
}
{
  iIntros (result).
  iIntros "%Hres".
  wp_auto.
  iApply "HΦ".
  iPureIntro. destruct Hres; auto. }
Qed.

End cancellable.


Section fibonacci_examples.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chanGhostStateG Σ w64}.
Context `{!ghost_varG Σ (list w64)}.
Set Default Proof Using "Type".

#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Fixpoint fib (n: nat) : w64 :=
  match n with
  | 0%nat => W64 0
  | 1%nat => W64 1
  | S (S n' as n'') => word.add (fib n'') (fib n')
  end.

Definition fib_list (n: nat) : list w64 :=
  map fib (seq 0 n).

Lemma fib_list_succ (n: nat) :
  fib_list (S n) = fib_list n ++ [fib n].
Proof.
  unfold fib_list.
  rewrite seq_S.
  rewrite map_app.
  simpl. reflexivity.
Qed.

Lemma fib_list_length (n: nat) :
  length (fib_list n) = n.
Proof.
  unfold fib_list.
  rewrite map_length.
  apply seq_length.
Qed.

Lemma fib_succ (k:nat) :
  fib (S k) =
    match k with 0%nat => W64 1 | S k' => word.add (fib (S k')) (fib k') end.
Proof. destruct k; simpl; reflexivity. Qed.

Open Scope Z_scope.

Lemma wp_fibonacci (n: nat) (c_ptr: loc) γ:
  0 < n < 2^63 ->
  {{{ is_pkg_init channel ∗
      is_pkg_init chan_spec_raw_examples ∗

      is_spsc γ c_ptr (λ i v, ⌜v = fib (Z.to_nat i)⌝)
                  (λ sent, ⌜sent = fib_list  n⌝) ∗
      spsc_producer γ []
  }}}
    @! chan_spec_raw_examples.fibonacci #(W64 n) #c_ptr
  {{{ RET #(); True }}}.
Proof.
  intros Hn.
  wp_start.
  iDestruct "Hpre" as "(#Hspsc & Hprod)".
  rename c_ptr into c_ptr0.
  wp_alloc_auto.
  wp_auto.

 iAssert (∃ (i: nat) (sent: list w64),
           "Hprod" ∷ spsc_producer γ sent ∗
           "x"     ∷ x_ptr ↦ fib i ∗
           "y"     ∷ y_ptr ↦ fib (S i) ∗
           "i"     ∷ i_ptr ↦ W64 i ∗
           "c"     ∷ c_ptr ↦ c_ptr0 ∗
           "%Hil"  ∷ ⌜i = length sent⌝ ∗
           "%Hsl"  ∷ ⌜sent = fib_list i⌝ ∗
           "%Hi"   ∷ ⌜0 ≤ i ≤ n⌝)%I
  with "[x y i c Hprod]" as "IH".
{
  iFrame.
  iExists 0%nat.
  iFrame.
  iPureIntro. simpl. unfold fib_list.
  simpl.
  split;first done.
  split;first done.
  lia.
}

    wp_for "IH".
  wp_if_destruct.
  {

     wp_apply (wp_spsc_send (V:=w64) (t:=intT) γ c_ptr0
             (λ (i : Z) (v : w64), ⌜v = fib (Z.to_nat i)⌝%I)
              (λ sent0 : list w64, ⌜sent0 = fib_list n⌝%I) sent

              with "[ Hspsc Hprod]").
     { iFrame "#".  iFrame.  simpl.
       replace (Z.to_nat (length sent)) with (length sent) by lia.
       word.
       }
     iIntros "Hprod".
     wp_auto.
     wp_for_post.
     iFrame.
      iExists ((length sent) + 1)%nat.
      iFrame.

      iFrame.
      replace (length sent + 1)%nat with (S (length sent)) by lia.
      destruct (length sent) eqn: H.
      {
        iFrame.  iPureIntro. rewrite app_length.  rewrite H. simpl. unfold fib_list. simpl.
        split;first done.
        rewrite Hsl.
        split;first done.
        lia.
      }
      iFrame.

(* y: turn the add(...) form into fib (S (length sent + 1)) *)
     (* add (fib (S k)) (fib k) → fib (S (S k)) *)
    replace   (w64_word_instance.(word.add)
                  (fib (S n0))
                  (w64_word_instance.(word.add)
                     (fib (S n0))
                     (fib n0)))
                with  (fib (S (S (S n0)))).
    {
      iFrame.
      replace ( w64_word_instance.(word.add) (W64 (S n0)) (W64 1)) with (W64 (S (S n0))).
      {
        iFrame. iPureIntro.
        split.
        { rewrite length_app.  rewrite singleton_length.  rewrite H. lia.
          }
          split.
        {


          subst sent.
          rewrite <- fib_list_succ.
          done.

      }
      {
        word.
      }
    }
    {
      word.
    }
    }
    {
      rewrite fib_succ.
      rewrite fib_succ.
      word.
    }
    }
    {
    wp_apply (wp_spsc_close (V:=w64) (t:=intT) γ c_ptr0
             (λ (i : Z) (v : w64), ⌜v = fib (Z.to_nat i)⌝%I)
              (λ sent0 : list w64, ⌜sent0 = fib_list n⌝%I) sent

              with "[ $Hspsc $Hprod]").
    { iFrame "#".   iPureIntro. rewrite Hsl.
      assert ((length sent) = n).
      {
       assert  (sint.Z (W64 n) ≤  sint.Z (W64 (length sent))) by word.
       assert   ((sint.Z (W64 (length sent))) ≤ (sint.Z (W64 n))).
       {
          word.
       }
       assert (length sent < 2^64). { lia. }

       word.
      }
 destruct (length sent) eqn: H1.
      { word.

      }
      rewrite H. done.
        }
    iApply "HΦ". done.
}
Qed.

Lemma wp_fib_consumer:
  {{{ is_pkg_init channel ∗ is_pkg_init chan_spec_raw_examples
  }}}
   @! chan_spec_raw_examples.fib_consumer #()
  {{{ sl, RET #(sl);
      sl ↦* (fib_list 10)


  }}}.
  Proof using chanGhostStateG0 ext ffi ffi_interp0 ffi_semantics0 ghost_varG0 go_ctx hG Σ.
  wp_start. wp_auto.
  wp_apply (chan.wp_make); first done.
  iIntros (c γ) "[#Hchan Hown]".
  wp_auto.
   iMod (start_spsc c 10  (λ i v, ⌜v = fib (Z.to_nat i)⌝%I)
                  (λ sent, ⌜sent = fib_list 10 ⌝%I)  γ
    with "[Hchan] [Hown]") as (γspsc) "(#Hspsc & Hprod & Hcons)".
   {
      iFrame "#".
   }
   {
     iFrame.
     }
  wp_apply (chan.wp_cap with "[$Hchan]").
  wp_apply (wp_fork with "[Hprod]").
   {

   wp_apply ((wp_fibonacci 10 c γspsc) with "[$Hprod]").
   {
     done.
   }
   {
     iFrame "#".
   }
   done.
   }
  iDestruct (theory.slice.own_slice_nil  (DfracOwn 1)) as "Hnil".
   iDestruct (theory.slice.own_slice_cap_nil (V:=w64)) as "Hnil_cap".
   simpl.
 iAssert (∃ (i: nat) (i_v: w64) sl,
             "i" ∷ i_ptr ↦ i_v ∗
            "c"  ∷ c_ptr ↦ c ∗
  "Hcons"  ∷ spsc_consumer γspsc (fib_list i) ∗
  "Hsl"  ∷ sl ↦* (fib_list i) ∗
  "results"  ∷ results_ptr ↦ sl ∗
  "oslc"  ∷ theory.slice.own_slice_cap w64 sl (DfracOwn 1)
)%I
  with "[ i c Hcons results]" as "IH".
{
  iExists 0%nat.
  iFrame.
  unfold fib_list. iFrame "#".
}


  rewrite /chan.for_range.
  wp_auto.
  wp_for "IH".
   wp_apply ((wp_spsc_receive (t:=intT) γspsc c γspsc (λ i v, ⌜v = fib (Z.to_nat i)⌝%I)
                  (λ sent, ⌜sent = fib_list 10 ⌝%I) (fib_list i) _) with "[Hcons]").
   { iFrame "#".  iFrame.   }
   iIntros (v ok).
   destruct ok.
   {
     iIntros "[%Hfib Hcons]".


      wp_auto.
      iDestruct (slice.own_slice_len with "Hsl") as "[%Hl %Hcap]".
      iDestruct (slice.own_slice_len with "Hsl") as "[%Hlen_slice %Hslgtz]".


wp_apply wp_slice_literal. iIntros (sl0) "Hsl0".
      iDestruct (slice.own_slice_len with "Hsl0") as "[%Hl0 %Hcap0]".
      iDestruct (slice.own_slice_len with "Hsl0") as "[%Hlen_slice0 %Hslgtz0]".
wp_auto.
wp_apply (wp_slice_append (t:=intT)
          sl (fib_list i)
          sl0 [v]
          (DfracOwn 1)
          with "[$Hsl $Hsl0 $oslc ]").

     iIntros (sl') "Hsl'".
     wp_auto.
     wp_for_post.
     iFrame.
     iExists (S i).
     iDestruct "Hsl'" as "(Hsl & Hcap & Hsl0)".
     rewrite Hfib.
     iFrame.
iSplitL "Hcons".
{
  rewrite fib_list_length.
  rewrite Nat2Z.id.
  rewrite <- fib_list_succ.
  iFrame.
}
{
  rewrite fib_list_length.
  rewrite Nat2Z.id.
  rewrite <- fib_list_succ.
  iFrame.
}
}
iIntros "%Hfl". wp_auto. wp_for_post. iFrame.
   iApply "HΦ".
   rewrite Hfl. iFrame "Hsl".
Qed.

End fibonacci_examples.

Section dsp_examples.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.
Context `{!chanGhostStateG Σ interface.t}.
Context `{!dspG Σ interface.t}.
Set Default Proof Using "Type".
#[global] Instance : IsPkgInit strings := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf strings := build_get_is_pkg_init_wf.
#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Definition ref_prot : iProto Σ interface.t :=
  <! (l:loc) (x:Z)> MSG (interface.mk (ptrT.id intT.id) #l) {{ l ↦ W64 x }} ;
  <?> MSG (interface.mk (structT.id []) #()) {{ l ↦ w64_word_instance.(word.add) (W64 x) (W64 2) }} ;
  END.
Lemma wp_DSPExample :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_pkg_init channel }}}
    @! chan_spec_raw_examples.DSPExample #()
  {{{ RET #(W64 42); True }}}.
Proof using chanGhostStateG0 ext ffi ffi_interp0 ffi_semantics0 globalsGS0 go_ctx hG dspG0
Σ.
  (* TODO: Simplify the above [Proof] *)
  wp_start. wp_auto.
  wp_apply (chan.wp_make (V:=interface.t) (t:=interfaceT) 0); [done|].
  iIntros (c γ) "[#Hic Hoc]". wp_auto.
  wp_apply (chan.wp_make (V:=interface.t) (t:=interfaceT) 0); [done|].
  iIntros (signal γ') "[#Hicsignal Hocsignal]". wp_auto.
  iMod (dsp_session_init _ _ _ _ _ _ _ _ _ ref_prot with "Hic Hicsignal Hoc Hocsignal")
                       as "[Hc Hcsignal]";
    [by eauto|by eauto|..].
  iPersist "c signal".
  wp_apply (wp_fork with "[Hcsignal]").
  { wp_auto.
    wp_recv with "Hcsignal" as (l x) "Hl".
    wp_auto.
    wp_apply wp_interface_type_assert; [done|].
    wp_send with "Hcsignal" and "[Hl]".
    by wp_auto. }
  wp_send with "Hc" and (val_ptr 40) "[val]".
  wp_auto.
  wp_recv with "Hc" as "Hl".
  wp_auto. by iApply "HΦ".
Qed.

End dsp_examples.
