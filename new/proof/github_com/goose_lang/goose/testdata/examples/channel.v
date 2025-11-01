From New.proof Require Export proof_prelude.
From New.proof.github_com.goose_lang.goose.model.channel
     Require Export simple future spsc done dsp.
From New.proof Require Import strings time sync.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import channel.
From iris.base_logic Require Import ghost_map.
From New.golang.theory Require Import struct string chan.

Import chan_spec_raw_examples.

Set Default Proof Using "Type".

(* TODO: Move? *)
Global Instance wp_struct_make_unit {ext : ffi_syntax} {ffi : ffi_model} {ffi_interp0 : ffi_interp ffi} 
  {Σ : gFunctors} {hG : heapGS Σ} {ffi_semantics0 : ffi_semantics ext ffi} :
  PureWp True (struct.make #(structT []) (alist_val []))%struct #().
Proof.
  erewrite <- struct_val_aux_nil.
  apply wp_struct_make; cbn; auto.
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit chan_spec_raw_examples := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf chan_spec_raw_examples := build_get_is_pkg_init_wf.

Section hello_world.
Context `{!chanGhostStateG Σ go_string}.
Context `{!ghost_varG Σ bool}.

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
Context `{!ghost_varG Σ bool}.
Context `{!chanGhostStateG Σ unit}.
Context `{!chanGhostStateG Σ go_string}.
Context `{!ghost_mapG Σ nat gname}.

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
Context `{!chanGhostStateG Σ w64}.
Context `{!ghost_varG Σ (list w64)}.

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
Context `{!chanGhostStateG Σ interface.t}.
Context `{!dspG Σ interface.t}.

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
    (* BEGIN: Will be simplified to tactic [wp_recv (l x) as "Hl"] *)
    wp_apply (dsp_recv (tV:=interfaceT) (TT:=[tele loc Z]) signal c
              (tele_app (λ l x, interface.mk (ptrT.id intT.id) (# l)))
              (tele_app (λ l x, l ↦ W64 (x)))%I
              (tele_app (λ l x, iProto_dual
                                  (<?> MSG (interface.mk (structT.id []) #())
                                     {{ l ↦ w64_word_instance.(word.add)
                                                  (W64 x) (W64 2) }} ; END))) with "[Hcsignal]").
    { iApply (iProto_pointsto_le with "Hcsignal").
      rewrite /ref_prot. rewrite iProto_dual_message /=.
      iIntros "!>".
      rewrite !iMsg_dual_exist. iIntros (l).
      rewrite !iMsg_dual_exist. iIntros (x).
      rewrite iMsg_dual_base. iExists l, x.
      iIntros "HP". iFrame "HP".
      iApply iProto_le_base. iApply iProto_le_refl. }
    simpl.
    iIntros (lx).
    epose proof (tele_arg_S_inv lx) as [l [[x []] ->]]. simpl.
    iIntros "[Hcsignal Hl]".
    wp_auto.
    (* END: Will be simplified to tactic [wp_recv (l x) as "Hl"] *)
    wp_apply wp_interface_type_assert; [done|].
    (* BEGIN: Will be simplified to tactic [wp_send with "[$Hl]"] *)
    iDestruct (iProto_pointsto_le _ _ (<!> MSG (interface.mk (structT.id []) #()) ; END)
                with "Hcsignal [Hl]") as "Hcsignal".
    { rewrite iProto_dual_message /= iMsg_dual_base.
      iIntros "!>". iFrame "Hl". rewrite iProto_dual_end. iApply iProto_le_refl. }
    wp_apply (dsp_send with "[$Hcsignal]").
    (* END: Will be simplified to tactic [wp_send with "[$Hl]"] *)
    iIntros "Hc". by wp_auto. }
  (* BEGIN: Will be simplified to tactic [wp_send with "[$val]"] *)
  iDestruct (iProto_pointsto_le with "[$Hc] [val]") as "Hc".
  { iExists val_ptr, 40%Z. iFrame "val". iApply iProto_le_refl. }
  wp_apply (dsp_send with "[$Hc]").
  (* END: Will be simplified to tactic [wp_send with "[$val]"] *)
  iIntros "Hc". wp_auto.
  (* BEGIN: Will be simplified to tactic [wp_recv as "Hl"] *)
  wp_apply (dsp_recv (tV:=interfaceT) (TT:=[tele]) c signal
              (λ _, interface.mk (structT.id []) (# ()))
              (λ _, val_ptr ↦ W64 (40 + 2))%I
              (λ _, END%proto)
             with "[Hc]").
  { simpl. iApply (iProto_pointsto_le with "Hc").
    iIntros "!> HP". iFrame. done. }
  iIntros (_) "[Hc Hl]".
  (* END: Will be simplified to tactic [wp_recv as "Hl"] *)
  wp_auto. by iApply "HΦ".
Qed.

End dsp_examples.

Section select_panic.
Context `{!chanGhostStateG Σ unit}.

(** Invariant: channel must be Idle, all other states are False *)
Definition is_select_nb_only (γ : chan_names) (ch : loc) : iProp Σ :=
  "#Hch" ∷ is_channel (V:=unit)  ch 0 γ ∗
  "#Hinv" ∷ inv nroot (
    ∃ (s : chan_rep.t unit),
      "Hoc" ∷ own_channel  ch 0 s γ ∗
      match s with
      | chan_rep.Idle => True
      | _ => False
      end
  ).


(** Create the idiom from a channel in Idle state *)
Lemma start_select_nb_only (ch : loc) (γ : chan_names) :
  is_channel ch 0 γ -∗
  own_channel ch 0 chan_rep.Idle γ ={⊤}=∗
  ∃ γnb, is_select_nb_only γnb ch.
Proof.
  iIntros "#Hch Hoc".
  iMod (inv_alloc nroot with "[Hoc]") as "$".
  { iNext. iFrame. }
  simpl.
  by iFrame "#".
  Qed.

(** Nonblocking send AU - vacuous since we ban all send preconditions *)
Lemma select_nb_only_send_au γ ch v  :
  ∀ Φ,
  is_select_nb_only γ ch -∗
  ( False -∗  Φ) -∗
         £1 ∗ £1 -∗
  send_au_fast ch 0 v γ Φ.
Proof.
   intros Φ.
  iIntros "#Hnb".
  iIntros "HΦ".
  iIntros "[Hlc1 Hlc2]".
  iNamed "Hnb".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  destruct s; try done.
  (* Only Idle case remains - all others give False from invariant *)
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iFrame.
  Qed.



(** Nonblocking receive AU - vacuous since we ban all receive preconditions *)
Lemma select_nb_only_rcv_au γ ch :
   ∀ (Φ: unit → bool → iProp Σ),
  is_select_nb_only  γ ch -∗
  ( ∀ (v:unit), False -∗ Φ v true) -∗
         £1 ∗ £1 -∗
  rcv_au_fast ch 0 γ (λ (v:unit) (ok:bool), Φ v ok).
Proof.
  intros Φ.
  iIntros "#Hnb".
  iIntros "HΦ".
  iIntros "[Hlc1 Hlc2]".
  iNamed "Hnb".
  iInv "Hinv" as "Hinv_open" "Hinv_close".
  iMod (lc_fupd_elim_later with "Hlc1 Hinv_open") as "Hinv_open".
  iNamed "Hinv_open".
  destruct s; try done.
  (* Only Idle case remains - all others give False from invariant *)
  iApply fupd_mask_intro; [solve_ndisj|iIntros "Hmask"].
  iNext.
  iFrame.
Qed.


Lemma wp_select_nb_no_panic :
  {{{ is_pkg_init chan_spec_raw_examples}}}
    @! chan_spec_raw_examples.select_nb_no_panic #()
  {{{ RET #(); True }}}.
  wp_start. wp_auto_lc 2.
  wp_apply chan.wp_make. { done. }
  iIntros (ch). iIntros (γ). iIntros "(#HisChan & Hownchan)".
  iRename select (£1) into "Hlc1".
  wp_auto_lc 2.
  iRename select (£1) into "Hlc2".
  simpl.
  iPersist "ch".
  do 2 (iRename select (£1) into "Hlc4").
  iMod (start_select_nb_only ch with "[$HisChan] [$Hownchan]") as (γnb) "#Hnb".
  wp_apply (wp_fork with "[Hnb]").
  {
  wp_auto_lc 4.
  wp_apply chan.wp_select_nonblocking.
    simpl.
    iSplitL.
  - (* Prove the receive case - will be vacuous *)
    iSplitL.
    +
      iExists 0. iExists γnb. iExists unit. iExists _, _, _.
      iFrame.
      iSplit.
      { (* Show is_channel matches *)
        iNamed "Hnb". iFrame "#". }
      (* Now use our select_nb_only_rcv_au lemma *)
      iRename select (£1) into "Hlc1".
      iApply (select_nb_only_rcv_au with " [$Hnb]").
      {
      iIntros (v).
      iIntros "Hf".
      done.
      }
      iFrame.
    + (* True case *)
      done.
  - (* Prove the default case *)
    wp_auto.
    done.
  }
  {

  wp_apply chan.wp_select_nonblocking.
    simpl.
    iSplitL "Hlc1 Hlc4".
  - (* Prove the receive case - will be vacuous *)
    iSplitL.
    +
      iExists 0. iExists unit. iExists γnb. iExists _, _, _, _.
      iFrame.
      iSplit.
      { (* Show is_channel matches *)
        iNamed "Hnb". iFrame "#". iPureIntro. done.  }
      (* Now use our select_nb_only_rcv_au lemma *)
       iSplit.
      { (* Show is_channel matches *)
        iNamed "Hnb". iFrame "#". }
      iFrame "#".
      iApply (select_nb_only_send_au γnb ch () with " [$Hnb] []").
      {
        iIntros "Hf".
          done.
      }
      iFrame.
    + (* True case *)
      done.
  - (* Prove the default case *)
    wp_auto.
    iApply "HΦ".
    done.
  }
Qed.

End select_panic.

Section higher_order_example.
Context `{!chanGhostStateG Σ request.t}.
Context `{!chanGhostStateG Σ go_string}.
Context `{!ghost_varG Σ bool}.

Definition do_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "Hf" ∷ WP #r.(request.f') #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} ∗
  "#Hfut" ∷ is_future γfut r.(request.result') Q ∗
  "Hfut_tok" ∷ fulfill_token γfut.

Definition await_request (r: request.t) γfut (Q: go_string → iProp Σ) : iProp Σ :=
  "#Hfut" ∷ is_future γfut r.(request.result') Q ∗
  "Hfut_await" ∷ await_token γfut.

Lemma wp_mkRequest {f: func.t} (Q: go_string → iProp Σ) :
  {{{ is_pkg_init chan_spec_raw_examples ∗ WP #f #() {{ λ v, ∃ (s: go_string), ⌜v = #s⌝ ∗ Q s }} }}}
    @! chan_spec_raw_examples.mkRequest #f
  {{{ γfut (r: request.t), RET #r; do_request r γfut Q ∗ await_request r γfut Q }}}.
Proof.
  wp_start as "Hf".
  wp_auto.
  wp_apply chan.wp_make.
  { word. }
  iIntros (ch γ) "[His Hown]".
  simpl. (* for decide *)
  iMod (start_future with "His Hown") as (γfuture) "(#Hfut & Hawait & Hfulfill)".
  wp_auto.
  iApply "HΦ".
  iFrame "Hfut ∗".
Qed.

#[local] Lemma wp_get_response (r: request.t) γfut Q :
  {{{ await_request r γfut Q }}}
    chan.receive #stringT #r.(request.result')
  {{{ (s: go_string), RET (#s, #true); Q s }}}.
Proof.
  wp_start as "Hawait". iNamed "Hawait".
  wp_apply (wp_future_await with "[$Hfut $Hfut_await]").
  iIntros (v) "HQ".
  iApply "HΦ". done.
Qed.

Definition is_request_chan γ (ch: loc): iProp Σ :=
  is_simple (V:=request.t) γ ch 0 (λ r, ∃ γfut Q, do_request r γfut Q)%I.

Lemma wp_ho_worker γ ch :
  {{{ is_pkg_init chan_spec_raw_examples ∗ is_request_chan γ ch }}}
    @! chan_spec_raw_examples.ho_worker #ch
  {{{ RET #(); True }}}.
Proof.
  wp_start as "#His".
  rewrite /is_request_chan.
  wp_auto.
  rewrite /chan.for_range.
  iPersist "c".
  wp_auto.
  iAssert (∃ (r0: request.t),
      "r" ∷ r_ptr ↦ r0
    )%I with "[$r]" as "IH".
  wp_for "IH".
  wp_apply (wp_simple_receive (V:=request.t) with "[$His]") as "%r Hreq".
  iNamed "Hreq".
  wp_bind (#r.(request.f') _)%E.
  iApply (wp_wand with "[Hf]").
  { iApply "Hf". }
  iIntros (v) "HQ".
  iDestruct "HQ" as (s) "[-> HQ]".
  wp_auto.
  wp_apply (wp_future_fulfill with "[$Hfut $Hfut_tok HQ]").
  { done. }
  wp_for_post.
  iFrame.
Qed.

Lemma wp_HigherOrderExample :
  {{{ is_pkg_init chan_spec_raw_examples }}}
    @! chan_spec_raw_examples.HigherOrderExample #()
  {{{ (s:slice.t), RET #s; s ↦* ["hello world"%go; "HELLO"%go; "world"%go] }}}.
Proof using chanGhostStateG0 chanGhostStateG1 ghost_varG0.
  wp_start.
  (* TODO: why is the string unfolded here? *)
  wp_auto.
  wp_apply (chan.wp_make (V:=request.t)).
  { done. }
  iIntros (req_ch γ) "[His Hown]".
  simpl.
  iMod (start_simple with "His Hown") as "[%γdone #Hch]".
  iAssert (is_request_chan γdone req_ch) with "[$Hch]" as "#Hreqs".
  wp_auto.
  wp_apply (wp_fork).
  {
    wp_apply (wp_ho_worker).
    { iFrame "#". }
    done.
  }
  wp_apply (wp_fork).
  {
    wp_apply (wp_ho_worker).
    { iFrame "#". }
    done.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "hello world"%go⌝)%I) as "%γfut1 %r1 [Hdo_r1 Hawait_r1]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "HELLO"%go⌝)%I) as "%γfut2 %r2 [Hdo_r2 Hawait_r2]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_mkRequest (λ s, ⌜s = "world"%go⌝)%I) as "%γfut3 %r3 [Hdo_r3 Hawait_r3]".
  {
    wp_auto.
    eauto.
  }
  wp_apply (wp_simple_send (V:=request.t) with "[$Hch $Hdo_r1]").
  wp_apply (wp_simple_send (V:=request.t) with "[$Hch $Hdo_r2]").
  wp_apply (wp_simple_send (V:=request.t) with "[$Hch $Hdo_r3]").
  wp_apply (wp_get_response with "[$Hawait_r1]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r2]") as "%s %Heq".
  subst.
  wp_apply (wp_get_response with "[$Hawait_r3]") as "%s %Heq".
  subst.
  wp_apply wp_slice_literal.
  iIntros (sl) "Hresponse".
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End higher_order_example.

End proof.
