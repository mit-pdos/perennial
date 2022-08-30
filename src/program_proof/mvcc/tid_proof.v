From Perennial.program_proof.mvcc Require Import mvcc_prelude mvcc_ghost.
From Goose.github_com.mit_pdos.go_mvcc Require Import tid.

Section program.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(**
 * [int.nat tid = ts] means no overflow, which we would have to assume.
 * It takes around 120 years for TSC to overflow on a 4-GHz CPU.
 *)
(*****************************************************************)
(* func GenTID(sid uint64) uint64                                *)
(*****************************************************************)
Theorem wp_GenTID (sid : u64) γ :
  ⊢ {{{ True }}}
    <<< ∀∀ (ts : nat), ts_auth γ ts >>>
      GenTID #sid @ ∅
    <<< ∃ ts', ts_auth γ ts' ∗ ⌜(ts < ts')%nat⌝ >>>
    {{{ (tid : u64), RET #tid; ⌜int.nat tid = ts⌝ }}}.
Proof.
  iIntros "!>" (Φ) "Hpre HAU".
  wp_call.

  (***********************************************************)
  (* var tid uint64                                          *)
  (***********************************************************)
  wp_apply wp_ref_of_zero; first done.
  iIntros (tidRef) "Htid".
  wp_pures.

  (***********************************************************)
  (* tid = GetTSC()                                          *)
  (***********************************************************)
  (* This is a hack *)
  iMod tsc_lb_0 as "Hlb".
  wp_apply (wp_GetTSC).
  (* XXX: We're wasting the fupd here since we're not opening any invariant. *)
  iApply ncfupd_mask_intro; first done.
  iIntros "HfupdC".
  iExists 0%nat.
  iFrame.
  iIntros (new_time) "[%Hnew Hlb]".
  iMod "HfupdC".
  iModIntro.
  iIntros "_".

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
