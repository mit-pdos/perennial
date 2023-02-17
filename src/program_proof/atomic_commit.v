From Perennial.program_proof Require Import grove_prelude.
From iris.base_logic Require Export lib.ghost_var.
From Perennial.program_proof.grove_shared Require Import urpc_proof urpc_spec.
From Goose.github_com.mit_pdos.gokv Require Import tutorial.

Module decision.
  Inductive t := Unknown | Commit | Abrt.
  Definition is_byte (x:t) (b: u8) :=
    match x with
    | Unknown => b = U8 0
    | Commit => b = U8 1
    | Abrt => b = U8 2
    end.
End decision.

(* PLAN:

- start by giving the participant a spec
- will have a single piece of ghost state for the global preferences

One gname for each participant
participant ghost state is a single agree(bool) for its preference

also a global decision ghost variable that reflects all of the preferences

Three parallel lists at the coordinator:
- physical list of decisions
- physical list of participant clerks
- ghost list of participant gnames

coordinator's one-shot decision

 *)

Module global_names.
  Record t :=
    mk { decision: gname; }.
End global_names.

Module participant_names.
  Record t :=
    mk { preference: gname;
         urpc: server_chan_gnames; }.
End participant_names.

Module coordinator_names.
  Record t :=
    mk { participants: list gname;
         globals: global_names.t;
        }.
End coordinator_names.

Section iris.
  Context `{!heapGS Σ}.
  Context `{!urpcregG Σ}.
  Context `{inG Σ (agreeR boolO)}.

  Definition is_preference (γ: participant_names.t) (pref: bool) : iProp Σ :=
    own γ.(participant_names.preference) (to_agree pref).

  Definition is_decision (γ: coordinator_names.t) (decision: bool) : iProp Σ :=
    own γ.(coordinator_names.globals).(global_names.decision) (to_agree decision).

  Program Definition GetPreference_spec (γ: participant_names.t)
    : list u8 → (list u8 -d> iProp Σ) -d> iProp Σ :=
    λ reqData, λne (Φ: list u8 -d> iPropO Σ),
      (* ignore request *)
      (∀ (pref: bool), is_preference γ pref -∗
      Φ (if pref then [U8 1] else [U8 0]))%I.
  Next Obligation. solve_proper. Defined.

  Definition is_participant_host (γ: participant_names.t) (host:u64) : iProp Σ :=
    "#H0" ∷ handler_spec γ.(participant_names.urpc) host (U64 0) (GetPreference_spec γ) ∗
    "#Hdom" ∷ handlers_dom γ.(participant_names.urpc) {[ (U64 0) ]}.

  Definition is_participant_clerk (ck: loc) (γ: participant_names.t) : iProp Σ :=
    ∃ (cl:loc) host,
      "#client" ∷ readonly (ck ↦[ParticipantClerk :: "client"] #cl) ∗
      "#Hhost" ∷ is_participant_host γ host ∗
      "#His_cl" ∷ is_uRPCClient cl host.

  Lemma wp_byteToPref (n: u8) :
    {{{ True }}}
      byteToPref #n
    {{{ (pref: bool), RET #pref; ⌜if decide (int.Z n = 1)%Z then pref = true else pref = false⌝ }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iPureIntro.
    destruct (decide _); subst.
    - rewrite bool_decide_eq_true //.
      f_equal.
      f_equal.
      admit.
    - rewrite bool_decide_eq_false //.
      admit.
  Admitted.

  Lemma wp_ParticipantClerk_GetPreference ck γ :
    is_participant_clerk ck γ -∗
    {{{ True }}}
      ParticipantClerk__GetPreference #ck
    {{{ (pref: bool), RET #pref;
        is_preference γ pref
    }}}.
  Proof.
    iIntros "#Hclerk".
    iIntros (Φ) "!> _ HΦ".

    wp_lam.

    wp_apply (wp_frame_wand with "HΦ").

    wp_apply wp_NewSlice. iIntros (req_s) "Hreq".
    wp_pures.
    wp_apply wp_NewSlice. iIntros (reply_s) "Hreply".
    rewrite replicate_0.
    wp_apply wp_ref_to.
    { val_ty. }
    iIntros (reply_l) "Hreply_l".
    wp_pures.
    iNamed "Hclerk".
    wp_loadField.

    wp_apply (wp_Client__Call2 with "[] [] [Hreq] Hreply_l").
    { iFrame "#". }
    { iNamed "Hhost".
      iFrame "#". }
    { iApply (is_slice_to_small with "Hreq"). }
    - iIntros "!> !>".
      cbn.
      iIntros (pref) "#Hpref _".
      iIntros (?) "reply_l Hrep_s".
      wp_step.
      wp_apply wp_Assume.
      iIntros "_". (* already true? *)
      wp_step.
      wp_load.
      wp_apply (wp_SliceGet _ _ _ _ _ _ _ (U8 (if pref then 1 else 0)%Z) with "[$Hrep_s]").
      { iPureIntro.
        destruct pref; reflexivity. }
      iIntros "Hrep_s".
      wp_pures.

      wp_apply wp_byteToPref.
      iIntros (pref').
      iIntros (Hpref').
      iIntros "HΦ".
      iApply "HΦ".

      assert (pref = pref').
      { (* U8/word nonsense *)
        revert Hpref'. destruct (decide _), pref; auto; exfalso.
        - admit. (* word failure; contradiction with e (after compute) *)
        - admit. (* word failure; contradiction with e (after compute) *)
      }

      subst; iFrame "#".
  Admitted.

  Definition is_coord_clerk (ck: loc) (γ: coordinator_names.t) : iProp Σ := True.

  Lemma wp_CoordinatorClerk_GetDecision ck γ :
    is_coord_clerk ck γ -∗
    {{{ True }}}
      CoordinatorClerk__GetDecision #ck
    {{{ (decision: decision.t) (b: u8), RET #b;
        ⌜decision.is_byte decision b⌝ ∗
        match decision with
        | decision.Commit => is_decision γ true
        | decision.Abrt => is_decision γ false
        | decision.Unknown => True
        end
    }}}.
  Proof.
  Admitted.

End iris.
