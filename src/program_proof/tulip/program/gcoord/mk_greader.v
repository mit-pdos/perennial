From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  greader_repr greader_reset.
  
Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_mkGroupReader (nrps : u64) γ :
    uint.nat nrps = size rids_all ->
    {{{ True }}}
      mkGroupReader #nrps
    {{{ (grd : loc), RET #grd; own_greader grd O γ }}}.
  Proof.
    iIntros (Hrid Φ) "_ HΦ".
    wp_rec.

    (*@ func mkGroupReader(nrps uint64) *GroupReader {                          @*)
    (*@     grd := &GroupReader{ nrps : nrps }                                  @*)
    (*@     grd.reset()                                                         @*)
    (*@     return grd                                                          @*)
    (*@ }                                                                       @*)
    wp_apply (wp_allocStruct).
    { by auto 10. }
    iIntros (grd) "Hgrd".
    wp_pures.
    wp_apply (wp_GroupReader__reset with "[Hgrd]").
    { iDestruct (struct_fields_split with "Hgrd") as "Hgrd".
      iNamed "Hgrd".
      by iFrame.
    }
    iIntros "Hgrd".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
