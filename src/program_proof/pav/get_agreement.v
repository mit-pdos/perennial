From Perennial.program_proof.pav Require Import prelude.

From Perennial.program_proof.pav Require Import
  client core cryptoffi msv serde.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma get_None_to_msv ep aud_ep γcli vrf_pk uid γaudit :
  uint.Z ep < uint.Z aud_ep →
  is_get_post_None γcli vrf_pk uid ep -∗
  logical_audit_post γcli γaudit vrf_pk aud_ep -∗
  msv γaudit vrf_pk ep uid None.
Proof.
  iIntros (?) "#Hpost #Haudit". iNamed "Haudit".
  iPoseProof "Hpost" as "Hentry". iNamed "Hpost".
  list_elem gs (uint.nat ep) as m. destruct m as [m ?].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; try done.
  iFrame "#".
  iDestruct ("Hmap_transf" with "[$Hentry //]") as "H".
  iNamedSuffix "H" "0".
  iDestruct (is_vrf_out_det with "Hvrf_out Hvrf_out0") as %->.
  inv Henc_val0.
  by simplify_option_eq.
Qed.

Lemma get_Some_to_msv ep aud_ep γcli vrf_pk uid pk γaudit :
  uint.Z ep < uint.Z aud_ep →
  is_get_post_Some γcli vrf_pk uid ep pk -∗
  logical_audit_post γcli γaudit vrf_pk aud_ep -∗
  ∃ ep', msv γaudit vrf_pk ep uid (Some (ep', pk)).
Proof.
  iIntros (?) "#Hpost #Haudit". iNamed "Hpost". iNamed "Haudit".
  list_elem gs (uint.nat ep) as m. destruct m as [m ?].
  iDestruct (mono_list_idx_own_get with "Hlb_gs") as "Hidx"; try done.
  iFrame "#".
  iExists ep', (word.add (W64 $ length hist) (W64 1)).
  repeat iSplit.
  - iIntros (??).
    list_elem hist (uint.nat ver) as a_hist.
    iDestruct (big_sepL_lookup with "Hhist") as "Hentry"; try done.
    replace (W64 (uint.nat _)) with ver by word.
    iDestruct ("Hmap_transf" with "[$Hentry //]") as "H".
    iNamed "H". iFrame "#".
    inv Henc_val. simplify_option_eq. naive_solver.
  - iDestruct ("Hmap_transf" with "[$His_lat //]") as "H".
    iNamed "H".
    replace (word.sub _ _) with (W64 $ length hist) by word.
    iFrame "#".
    iExists (_, _). iFrame "#". iSplit; try done.
    inv Henc_val. simplify_option_eq.
    destruct H0 as [??]. simpl in *.
    opose proof (MapValPre.inj [] [] Henc H2 _) as ?; try done.
    intuition. by simplify_eq/=.
  - iDestruct ("Hmap_transf" with "[$His_bound //]") as "H".
    iNamed "H". iFrame "#".
    inv Henc_val. by simplify_option_eq.
Qed.

End proof.
