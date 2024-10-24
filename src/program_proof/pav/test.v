From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From iris.base_logic Require Import mono_nat.
From Perennial.program_proof.pav Require Import advrpc auditor basictest core client cryptoffi history rpc serde server.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Import waitgroup.

Module alice.
Record t :=
  mk {
    cli: client.Client.t;
    hist: list HistEntry.t;
  }.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ ptr_cli sl_hist dim0_hist,
  "Hown_cli" ∷ client.Client.own ptr_cli obj.(cli) ∗
  "#Hptr_cli" ∷ ptr ↦[alice :: "cli"]□ #ptr_cli ∗
  "Hptr_hist" ∷ ptr ↦[alice :: "hist"] (slice_val sl_hist) ∗
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;obj.(hist), HistEntry.own p o) ∗
  "#His_keys" ∷ ([∗ list] ver ↦ x ∈ obj.(hist),
    (* aliceUid = 0. *)
    is_my_key obj.(cli).(Client.γ) (W64 0) (W64 ver)
      x.(HistEntry.Epoch) x.(HistEntry.HistVal)).

End defs.
End alice.

Module bob.
Record t :=
  mk {
    cli: client.Client.t;
    epoch: w64;
    isReg: bool;
    alicePk: list w8;
  }.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own ptr obj : iProp Σ :=
  ∃ ptr_cli sl_alicePk,
  "Hown_cli" ∷ client.Client.own ptr_cli obj.(cli) ∗
  "#Hptr_cli" ∷ ptr ↦[bob :: "cli"]□ #ptr_cli ∗
  "Hptr_epoch" ∷ ptr ↦[bob :: "epoch"] #obj.(epoch) ∗
  "Hptr_isReg" ∷ ptr ↦[bob :: "isReg"] #obj.(isReg) ∗
  "Hptr_alicePk" ∷ ptr ↦[bob :: "alicePk"] (slice_val sl_alicePk) ∗
  "#Hsl_alicePk" ∷ own_slice_small sl_alicePk byteT DfracDiscarded obj.(alicePk).
End defs.
End bob.

Section proof.
Context `{!heapGS Σ, !pavG Σ, !waitGroupG Σ}.

Lemma wp_updAdtrsAll (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs
  }}}
  updAdtrsAll #servAddr (slice_val sl_adtrAddrs)
  {{{ RET #(); True }}}.
Proof. Admitted.

Definition alice_post ptr_al al : iProp Σ :=
  "Hown_al" ∷ alice.own ptr_al al ∗
  "%Hlen_hist" ∷ ⌜ length al.(alice.hist) = 20 ⌝.

Lemma wp_alice__run ptr_al al :
  {{{
    "Hown_al" ∷ alice.own ptr_al al ∗
    "%Hlen_hist" ∷ ⌜ length al.(alice.hist) = 0 ⌝
  }}}
  alice__run #ptr_al
  {{{
    al', RET #();
    alice_post ptr_al al'
  }}}.
Proof. Admitted.

Definition bob_post ptr_bob bob : iProp Σ :=
  "Hown_bob" ∷ bob.own ptr_bob bob ∗
  "#Hknow_key" ∷ (if bob.(bob.isReg) then
    (* aliceUid = 0. *)
    "#His_key" ∷ is_other_key bob.(bob.cli).(Client.γ) (W64 0) bob.(bob.epoch) bob.(bob.alicePk)
  else
    "#His_no_key" ∷ is_no_other_key bob.(bob.cli).(Client.γ) (W64 0) bob.(bob.epoch)).

Lemma wp_bob__run ptr_bob bob :
  {{{
    "Hown_bob" ∷ bob.own ptr_bob bob
  }}}
  bob__run #ptr_bob
  {{{
    bob', RET #();
    bob_post ptr_bob bob'
  }}}.
Proof. Admitted.

Lemma wp_testAll ptr_setup setup :
  {{{
    "#Hsetup" ∷ setupParams.valid ptr_setup setup false true
  }}}
  testAll #ptr_setup
  {{{ RET #(); True }}}.
Proof using Type*.
  rewrite /testAll. iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hsetup".
  iClear "His_good_serv". do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk"). iIntros (ptr_cli_al) "*". iNamedSuffix 1 "_al".
  wp_apply wp_allocStruct; [val_ty|]. iIntros (ptr_al) "Hptr_al". do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk"). iIntros (ptr_cli_bob) "*". iNamedSuffix 1 "_bob".
  wp_apply wp_allocStruct; [val_ty|]. iIntros (ptr_bob) "Hptr_bob".

  wp_apply (wp_NewWaitGroup nroot (λ wg_id,
    match uint.Z wg_id with
    | 0%Z => ∃ al, alice_post ptr_al al
    | 1%Z => ∃ bob, bob_post ptr_bob bob
    | _ => True
    end)%I).
  iIntros "* Hown_wg".
  wp_apply (wp_WaitGroup__Add with "[$Hown_wg]"); [word|]. iIntros "[Hown_wg Hown_tok0]".
  wp_apply (wp_WaitGroup__Add with "[$Hown_wg]"); [word|]. iIntros "[Hown_wg Hown_tok1]".
  replace (word.add (word.add (W64 0) (W64 1)) (W64 1)) with (W64 2); [|word].
  iDestruct (own_WaitGroup_to_is_WaitGroup with "[$Hown_wg]") as "#His_wg".

  iDestruct (struct_fields_split with "Hptr_al") as "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "cli") as "#Hptr_cli_al".
  wp_apply (wp_fork with "[Hown_cli_al hist Hown_tok0]").
  { iIntros "!>".
    wp_apply (wp_alice__run _ (alice.mk _ []) with "[$Hown_cli_al $Hptr_cli_al hist]").
    { iSplit; [|done]. iExists Slice.nil, [].
      iDestruct (own_slice_zero) as "H0". iFrame "∗#". simpl. by iSplit. }
    iIntros "*". iNamed 1.
    by wp_apply (wp_WaitGroup__Done with "[$His_wg $Hown_tok0 $Hown_al //]"). }

  iDestruct (struct_fields_split with "Hptr_bob") as "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "cli") as "#Hptr_cli_bob".
  wp_apply (wp_fork with "[Hown_cli_bob epoch isReg alicePk Hown_tok1]").
  { iIntros "!>".
    wp_apply (wp_bob__run _ (bob.mk _ _ _ _) with "[$Hown_cli_bob $Hptr_cli_bob $epoch $isReg alicePk]").
    { iExists Slice.nil.
      iDestruct (own_slice_zero) as "H0".
      iDestruct (own_slice_to_small with "H0") as "H1". iFrame "∗#". }
    iIntros "*". iNamed 1.
    by wp_apply (wp_WaitGroup__Done with "[$His_wg $Hown_tok1 $Hown_bob //]"). }

  wp_apply (wp_WaitGroup__Wait with "[$Hown_wg]"). iIntros "H".
  iDestruct (big_sepS_delete _ _ (W64 0) with "H") as "[H0 H]"; [set_solver|].
  iDestruct (big_sepS_delete _ _ (W64 1) with "H") as "[H1 _]"; [set_solver|].
  iDestruct "H0" as "[%|H0]". { exfalso. word. }
  iDestruct "H1" as "[%|H1]". { exfalso. word. }
  iSimpl in "H0 H1".
  iRename "Hptr_cli_al" into "Hptr0". iRename "Hptr_cli_bob" into "Hptr1".
  iDestruct "H0" as (?) "H0". iNamed "H0". iNamedSuffix "Hown_al" "_al".
  iDestruct "H1" as (?) "H1". iNamed "H1". iNamedSuffix "Hown_bob" "_bob".
  iDestruct (struct_field_pointsto_agree with "Hptr0 Hptr_cli_al") as %->.
  iDestruct (struct_field_pointsto_agree with "Hptr1 Hptr_cli_bob") as %->.
  iClear "His_wg Hptr0 Hptr1".

  wp_loadField. wp_apply (wp_Client__SelfMon with "Hown_cli_al").
  iIntros (selfMonEp ? err) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al".
  destruct err.(clientErr.err). { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al".
  wp_loadField. wp_apply wp_Assume. iIntros "%Hlt_ep".
  do 2 wp_loadField. wp_apply (wp_updAdtrsAll with "Hsl_adtrAddrs").
  do 3 wp_loadField.
  iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %Hlen0.
  wp_apply (wp_doAudits with "[$Hown_cli_al $Hsl_adtrAddrs $Hsl_adtrPks $Hdim0_adtrPks]").
  { iPureIntro. lia. }
  iNamedSuffix 1 "_al". do 3 wp_loadField.
  wp_apply (wp_doAudits with "[$Hown_cli_bob $Hsl_adtrAddrs $Hsl_adtrPks $Hdim0_adtrPks]").
  { iPureIntro. lia. }
  iNamedSuffix 1 "_bob". do 2 wp_loadField.


Admitted.

End proof.
