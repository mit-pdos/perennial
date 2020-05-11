From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.program_proof Require Import wal.circ_proof_crash.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!lockG Σ}.
Context `{!walG Σ}.
Context `{!crashG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names (Σ:=Σ)).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Theorem wp_MkLog_init d (bs: list Block) :
  {{{ 0 d↦∗ repeat block0 513 ∗
      513 d↦∗ bs ∗
      P (log_state.mk (list_to_map (imap (λ i x, (513 + Z.of_nat i, x)) bs)) [(U64 0, [])] 0 0)  }}}
    MkLog #d
  {{{ γ l, RET #l; is_wal P l γ }}}.
Proof.
Admitted.

(* XXX: this used to have a postcondition that would give you some σ' which was
   the crash of σ:

      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗

   However, I think simulating the crash to σ' should be
   done using post_crash modality at the time when we initially
   crashed. mkLog_recover is itself a no-op at the spec level. *)

Theorem wpc_mkLog_recover k E2 d γ σ :
  {{{ is_wal_inner_durable γ σ }}}
    mkLog #d @ NotStuck; k; ⊤; E2
  {{{ γ' l, RET #l;
       is_wal_inv_pre l γ' σ ∗
       (* XXX whatever it is that background threads needs *)
       True}}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "Hcs HΦ".
  rewrite /mkLog.

  Ltac show_crash1 := eauto.

  wpc_pures; first by show_crash1.
  iNamed "Hcs".
  iNamed "Hdisk".
  wpc_bind (recoverCircular _).

  Ltac show_crash2 :=
    try (crash_case); iExists _;
    iSplitL ""; first auto;
    iFrame; iExists _, _, _; iFrame; iFrame "#".

  wpc_apply (wpc_recoverCircular with "[$]").
  iSplit.
  { iIntros "Hcirc". show_crash2. }

  iNext. iIntros (γ' c diskStart diskEnd bufSlice upds).
  iIntros "(Hupd_slice&Hcirc&Happender&Hstart&Hdisk&%&%&%)".
  iDestruct (is_circular_state_wf with "Hcirc") as %Hwf_circ.

  wpc_frame_compl "Hupd_slice".
  { crash_case. iExists (set circ_name (λ _, γ') γ). destruct γ.
    rewrite /is_wal_inner_durable. simpl. rewrite /is_durable_txn/is_installed_txn/is_durable//=.
    simpl. iSplitL ""; first auto. rewrite /txns_ctx.
    (* XXX: need to somehow show that all of these predicates do not depend on the circ_name... *)
    admit.
  }
  wp_pures.
  wp_apply (wp_new_free_lock); iIntros (ml) "Hlock".
  wp_pures.
  iDestruct (updates_slice_to_frag with "[$]") as "Hupd_slice".
  wp_apply (wp_mkSliding with "[$]").
  { destruct Hwf_circ as (?&?). subst; lia. }
  iIntros (lslide) "Hsliding".
  wp_apply wp_allocStruct; first by auto.
  iIntros (st) "Hwal_state".
  wp_pures.
  iMod (alloc_lock _ _ _ (wal_linv st γ) with "[$] [-]").
  { rewrite /wal_linv.
    iExists {| diskEnd := diskEnd; memLog := _ |}. iSplitL "Hwal_state Hsliding".
    { iExists {| memLogPtr := _; shutdown := _; nthread := _ |}.
      iDestruct (struct_fields_split with "Hwal_state") as "Hwal_state".
      iDestruct "Hwal_state" as "(?&?&?&?&_)".
      iFrame. iPureIntro. rewrite /locked_wf//=.
      { destruct Hwf_circ as (?&?). subst. split.
        * split; first lia.
          (* XXX: This constraint seems unprovable (?) but maybe I need to exploit the fact
             that we should assume the is_wal_state in the precondition is a post-crash state ?? *)
          admit.
        * rewrite /slidingM.wf //=; split; try lia.
      }
    }
    (* XXX: need to create a whole bunch of ghost state earlier *)
    admit.
  }
Abort.


Theorem wpc_MkLog_recover stk k E1 E2 d γ σ :
  {{{ is_wal_inner_durable γ σ }}}
    MkLog #d @ stk; k; E1; E2
  {{{ σ' γ' l, RET #l;
      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗
       is_wal_inv_pre l γ' σ' }}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ }}}.
Proof.
Abort.

End goose_lang.
