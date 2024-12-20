From Perennial.program_proof.tulip.invariance Require Import read.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_value_responded gcoord_attached_with gcoord_send.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__ReadSession 
    (gcoord : loc) (rid : u64) (tsW : u64) (key : byte_string) gid γ :
    let ts := uint.nat tsW in
    rid ∈ rids_all ->
    safe_read_req gid ts key ->
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__ReadSession #gcoord #rid #tsW #(LitString key)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts Hrid Hsafe) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ReadSession(rid uint64, ts uint64, key string) { @*)
    (*@     for !gcoord.ValueResponded(rid, key) && gcoord.AttachedWith(ts) {   @*)
    (*@         gcoord.SendRead(rid, ts, key)                                   @*)
    (*@         primitive.Sleep(params.NS_RESEND_READ)                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_pures.
    wp_apply (wp_forBreak_cond (λ _, True)%I with "[] []"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> _ HΦ".
      wp_apply (wp_GroupCoordinator__ValueResponded with "Hgcoord").
      iIntros (resped) "_".
      wp_pures.
      destruct resped; wp_pures.
      { by iApply "HΦ". }
      wp_apply (wp_GroupCoordinator__AttachedWith with "Hgcoord").
      iIntros (attached) "_".
      destruct attached; wp_pures; last first.
      { by iApply "HΦ". }
      iNamed "Hgcoord".
      iAssert (⌜dom addrm = rids_all⌝)%I as %Hdomaddrm.
      { iNamed "Hgcoord". iNamed "Haddrm". by rewrite -Hrps Hdomaddrm. }
      wp_apply (wp_GroupCoordinator__SendRead with "Hgcoord").
      { apply Hsafe. }
      { by rewrite Hdomaddrm. }
      wp_apply wp_Sleep.
      wp_pures.
      by iApply "HΦ".
    }

    (*@     // Either replica @rid has already responded with its value, or the value @*)
    (*@     // for @key has already been determined. In either case, the corresponding @*)
    (*@     // read session could terminate.                                    @*)
    (*@ }                                                                       @*)
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
