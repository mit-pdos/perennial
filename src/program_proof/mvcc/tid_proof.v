From Perennial.base_logic Require Import ghost_map saved_prop.
From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_ghost.
From Goose.github_com.mit_pdos.go_mvcc Require Import tid.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

Definition gentid_ns := nroot .@ "gentid".

Local Definition gentid_au (γ : mvcc_names) (sid : u64) (Φ : val → iProp Σ) : iProp Σ :=
  (|NC={⊤ ∖ ∅,∅}=>
    ∃ ts : nat, ts_auth γ ts ∗
       ((∃ ts' : nat, ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝) -∗
         |NC={∅,⊤ ∖ ∅}=> ∀ tid : u64, ⌜int.nat tid = ts⌝ ∗ sid_own γ sid -∗ Φ #tid)).

Local Definition reserved_inv γ now (ts : u64) γr : iProp Σ :=
  ∃ Φ, let sid := word.modu ts (U64 N_TXN_SITES) in
    saved_pred_own γr DfracDiscarded Φ ∗
    sid_own γ sid ∗
    if bool_decide (int.nat ts ≤ now)%nat then
      (* This ts has already happened *)
      sid_own γ sid -∗ Φ #ts
    else
      (* This ts is still in the future *)
      gentid_au γ sid Φ
    .

Local Definition gentid_inv (γ : mvcc_names) : iProp Σ :=
  ∃ now (reserved : gmap u64 gname),
    ts_auth γ now ∗ tsc_lb now ∗
    ghost_map_auth γ.(mvcc_gentid_reserved) 1 reserved ∗
    [∗ map] ts ↦ 'γr ∈ reserved,
      reserved_inv γ now ts γr.

Definition have_gentid (γ : mvcc_names) : iProp Σ :=
  inv gentid_ns (gentid_inv γ).

Local Definition tid_reserved γ γr ts (Φ : val → iProp Σ) : iProp Σ :=
  ghost_map_elem γ.(mvcc_gentid_reserved) ts (DfracOwn 1) γr ∗
  saved_pred_own γr DfracDiscarded Φ.

Global Instance have_gentid_persistent γ : Persistent (have_gentid γ).
Proof. apply _. Qed.

Lemma init_GenTID γ E :
  mvcc_gentid_init γ -∗
  |={E}=> have_gentid γ.
Proof. Admitted.

Local Lemma gentid_reserve γ sid Φ :
  gentid_inv γ -∗
  sid_own γ sid -∗
  gentid_au γ sid Φ -∗
  |==> ∃ clock, tsc_lb clock ∗
    (* The user can pick a timestamp with the right sid, but only gets something
    out of this if they pick one that is strictly greater than [clock]. *)
    (∀ ts, ⌜sid = word.modu ts (U64 N_TXN_SITES)⌝ ==∗
       (if decide (clock < int.Z ts) then ∃ γr, tid_reserved γ γr ts Φ else True) ∗
       gentid_inv γ).
Proof. Admitted.

(**
 * [int.nat tid = ts] means no overflow, which we would have to assume.
 * It takes around 120 years for TSC to overflow on a 4-GHz CPU.
 *)
(*****************************************************************)
(* func GenTID(sid uint64) uint64                                *)
(*****************************************************************)
Theorem wp_GenTID (sid : u64) γ :
  ⊢ have_gentid γ -∗
    {{{ sid_own γ sid }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      GenTID #sid @ ∅
    <<< ∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; ⌜int.nat tid = ts⌝ ∗ sid_own γ sid }}}.
Proof.
  iIntros "#Hinv !>" (Φ) "Hsid HAU".
  wp_call.

  (***********************************************************)
  (* var tid uint64                                          *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "Htid".
  wp_pure1_credit "LC".
  wp_pures.

  (***********************************************************)
  (* tid = GetTSC()                                          *)
  (***********************************************************)
  wp_apply (wp_GetTSC).
  iInv "Hinv" as "Hgentid" "Hclose".
  iMod (lc_fupd_elim_later with "LC Hgentid") as "Hgentid".
  iMod (gentid_reserve with "Hgentid Hsid HAU") as (clock) "[Hclock Hcont]".
  iApply ncfupd_mask_intro.
  { solve_ndisj. }
  iIntros "Hclose2".
  iExists _. iFrame "Hclock".
  iIntros (clock2) "[%Hclock Hclock2]".
  iMod "Hclose2" as "_".
  set reserved_ts := word.add clock2 (U64 1). (* FIXME use the actual ID here *)
  iMod ("Hcont" $! reserved_ts with "[]") as "[Hreserved Hgentid]".
  { iPureIntro. admit. }
  iMod ("Hclose" with "Hgentid") as "_".
  iIntros "!> _".

  (************************************************************************)
  (* tid = ((tid + config.N_TXN_SITES) & ^(config.N_TXN_SITES - 1)) + sid *)
  (************************************************************************)
  wp_store.
  wp_load.
  wp_store.
  wp_pures.
  set tid := (word.add _ _).

  (***********************************************************)
  (* for GetTSC() <= tid {                                   *)
  (* }                                                       *)
  (***********************************************************)
  set P := λ (b : bool), (if b then True else tsc_lb (int.nat tid))%I.
  wp_apply (wp_forBreak_cond P).
  { admit. }
  { done. }
  iIntros "HP". unfold P. clear P.
  wp_load.

  (***********************************************************)
  (* return tid                                              *) 
  (***********************************************************)
Admitted.

End program.

Global Typeclasses Opaque have_gentid.
