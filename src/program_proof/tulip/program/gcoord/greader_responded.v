From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import greader_repr.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupReader__responded (grd : loc) (rid : u64) (key : byte_string) ts γ :
    {{{ own_greader grd ts γ }}}
      GroupReader__responded #grd #rid #(LitString key)
    {{{ (responded : bool), RET #responded; own_greader grd ts γ }}}.
  Proof.
    iIntros (Φ) "Hgrd HΦ".
    wp_rec.

    (*@ func (grd *GroupReader) responded(rid uint64, key string) bool {        @*)
    (*@     _, final := grd.valuem[key]                                         @*)
    (*@     if final {                                                          @*)
    (*@         // The final value is already determined.                       @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgrd". iNamed "Hvaluem".
    wp_loadField.
    wp_apply (wp_MapGet with "Hvaluem").
    iIntros (v final) "[%Hfinal Hvaluem]".
    wp_pures.
    destruct final; wp_pures.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     qread, ok := grd.qreadm[key]                                        @*)
    (*@     if !ok {                                                            @*)
    (*@         return false                                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hqreadm".
    wp_loadField.
    wp_apply (wp_MapGet with "HqreadmM").
    iIntros (qreadP ok) "[%Hok HqreadmM]".
    wp_pures.
    destruct ok; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ # %". }

    (*@     _, responded := qread[rid]                                          @*)
    (*@     if responded {                                                      @*)
    (*@         // The replica has already responded with its latest version.   @*)
    (*@         return true                                                     @*)
    (*@     }                                                                   @*)
    (*@     return false                                                        @*)
    (*@ }                                                                       @*)
    apply map_get_true in Hok.
    iDestruct (big_sepM2_dom with "Hqreadm") as %Hdomqreadm.
    assert (is_Some (qreadm !! key)) as [qread Hqread].
    { by rewrite -elem_of_dom -Hdomqreadm elem_of_dom. }
    iDestruct (big_sepM2_lookup_acc with "Hqreadm") as "[Hqr HqreadmC]".
    { apply Hok. }
    { apply Hqread. }
    wp_apply (wp_MapGet with "Hqr").
    clear Hfinal v.
    iIntros (v responded) "[%Hresponded Hqr]".
    wp_pures.
    iDestruct ("HqreadmC" with "Hqr") as "Hqreadm".
    by destruct responded; wp_pures; iApply "HΦ"; iFrame "∗ # %".
  Qed.

End program.
