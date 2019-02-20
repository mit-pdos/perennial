From iris.algebra Require Import auth gmap list.
Require Export CSL.Refinement.
Require Import AtomicPairAPI AtomicPair.ImplShadow ExMach.WeakestPre ExMach.RefinementAdequacy.
Unset Implicit Arguments.

Definition recv : proc ExMach.Op _ := Ret tt.

(* TODO: move *)
Section ghost_var_helpers.
Context {A: ofeT} `{@LeibnizEquiv _ A.(ofe_equiv)} `{OfeDiscrete A}.
Context {Σ} {Hin: inG Σ (authR (optionUR (exclR A)))}.

Lemma ghost_var_agree γ (a1 a2: A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) -∗ ⌜ a1 = a2 ⌝.
Proof.
  iIntros "Hγ1 Hγ2".
  iDestruct (own_valid_2 with "Hγ1 Hγ2") as "H".
  iDestruct "H" as %[<-%Excl_included%leibniz_equiv _]%auth_valid_discrete_2.
  done.
Qed.

Lemma ghost_var_update γ (a1' a1 a2 : A) :
  own γ (● (Excl' a1)) -∗ own γ (◯ (Excl' a2)) ==∗
    own γ (● (Excl' a1')) ∗ own γ (◯ (Excl' a1')).
Proof.
  iIntros "Hγ● Hγ◯".
  iMod (own_update_2 _ _ _ (● Excl' a1' ⋅ ◯ Excl' a1') with "Hγ● Hγ◯") as "[$$]".
  { by apply auth_update, option_local_update, exclusive_local_update. }
  done.
Qed.
End ghost_var_helpers.

Set Default Proof Using "Type".
Section refinement_triples.
  Context `{!exmachG Σ, lockG Σ, !@cfgG (AtomicPair.Op) (AtomicPair.l) Σ,
            !inG Σ (authR (optionUR (exclR (prodC natC natC)))),
            !inG Σ (authR (optionUR (exclR natC)))}.
  Context (ρ : thread_pool AtomicPair.Op * AtomicPair.l.(State)).

  Import ExMach.

  (* TODO: this should work, but the invariant is too global: ideally, 
     most threads should not care about the value in the non-pointed to
     copy, and a writer who holds the lock should be able to modify it freely
     without opening this invariant up prior to updating the pointer *)
  Definition ptr_map (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat) :=
    (ptr_addr d↦ ptr_val ∗
     (read_addrs ptr_val).1 d↦ pcurr.1 ∗
     (read_addrs ptr_val).2 d↦ pcurr.2 ∗
     (write_addrs ptr_val).1 d↦ pother.1 ∗
     (write_addrs ptr_val).2 d↦ pother.2)%I.

  Definition ExecInner γ1 γ2 γ3 :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) (pother: nat * nat),
        own γ1 (● (Excl' ptr_val))
            ∗ own γ2 (● (Excl' pcurr))
            ∗ own γ3 (● (Excl' pother))
            ∗ source_state pcurr ∗
            ptr_map ptr_val pcurr pother)%I.
            

  (* Holding the lock guarantees the value of the atomic pair/pointer will not
     change out from underneath you -- this is enforced by granting ownership of
     appropriate ghost variables *)
  Definition ExecLockInv γ1 γ2 γ3 :=
    (∃ ptr_val (pcurr : nat * nat) (pother: nat * nat),
        own γ1 (◯ (Excl' ptr_val))
            ∗ own γ2 (◯ (Excl' pcurr))
            ∗ own γ3 (◯ (Excl' pother))
    )%I.

  (* Post-crash, pre recovery we know the ptr mapping is in a good state w.r.t the
     abstract state, and the lock must have been reset 0 *)

  Definition CrashInner :=
    (∃ (ptr_val : nat) (pcurr: nat * nat) pother,
        source_state pcurr ∗ ptr_map ptr_val pcurr pother ∗ lock_addr m↦ 0)%I.


  Definition lN : namespace := (nroot.@"lock").
  Definition iN : namespace := (nroot.@"inner").

  Definition ExecInv :=
    (source_ctx ρ ∗ ∃ γlock γ1 γ2 γ3, is_lock lN γlock lock_addr (ExecLockInv γ1 γ2 γ3)
                                           ∗ inv iN (ExecInner γ1 γ2 γ3))%I.


  (* Extends the iExist tactic to make it easier to re-prove invariants after steps *)
  Instance from_exist_left_sep {A} (Φ : A → iProp Σ) Q :
    FromExist (▷ (∃ a, Φ a) ∗ Q) (λ a, ▷ Φ a ∗ Q)%I .
  Proof. rewrite /FromExist. iIntros "H". iDestruct "H" as (?) "(?&$)". iExists _; eauto. Qed.

  Ltac destruct_einner H :=
    iDestruct "H" as (? (?&?) (?&?)) ">(Hown1&Hown2&Hown3&Hsource&Hmap)";
    iDestruct "Hmap" as "(Hptr&Hcase)";
    try (iDestruct (ghost_var_agree with "Hown1 [$]") as %?; subst; []);
    try (iDestruct (ghost_var_agree with "Hown2 [$]") as %Hp; inversion_clear Hp; subst; []);
    try (iDestruct (ghost_var_agree with "Hown3 [$]") as %Hp; inversion_clear Hp; subst; []).

  Lemma read_of_swap ptr_val :
    (read_addrs (swap_ptr ptr_val)) = write_addrs ptr_val.
  Proof. destruct ptr_val => //=. Qed.
  
  Lemma write_of_swap ptr_val :
    (write_addrs (swap_ptr ptr_val)) = read_addrs ptr_val.
  Proof. destruct ptr_val => //=. Qed.

  Lemma write_refinement {T} j K `{LanguageCtx AtomicPair.Op unit T AtomicPair.l K} p:
    {{{ j ⤇ K (Call (AtomicPair.Write p)) ∗ ExecInv }}} write p {{{ v, RET v; j ⤇ K (Ret v) }}}.
  Proof.
    iIntros (Φ) "(Hj&#Hsource_inv&Hinv) HΦ".
    iDestruct "Hinv" as (γlock γ1 γ2 γ3) "(#Hlockinv&#Hinv)".
    wp_bind. iApply (wp_lock with "[$]").
    iIntros "!> (Hlocked&HEL)".
    iDestruct "HEL" as (ptr_val pcurr pother) "(Hptr_ghost&Hpair_ghost&Hother_ghost)".
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iApply (wp_read_disk with "[$]"). iIntros "!> Haddr".
    iModIntro; iExists _, _, _; iFrame.
    destruct p as (new_fst&new_snd).
    wp_bind.
    (* iInv fails for mysterious type class reasons that I cannot debug *)
    iApply wp_atomic.
    iMod (inv_open with "Hinv") as "(H&Hclo)"; first by set_solver+; iModIntro.
    destruct_einner "H".

    iDestruct "Hcase" as "(?&?&Hfst&Hsnd)".
    iModIntro.
    iApply (wp_write_disk with "Hfst"). iIntros "!> Hfst".
    iMod (ghost_var_update γ3 (new_fst, n2) with "Hown3 [$]") as "(Hown3&Hother_ghost)".
    iMod ("Hclo" with "[-Hj HΦ Hlocked Hptr_ghost Hpair_ghost Hother_ghost]").
    { iModIntro. iExists ptr_val. simpl. iExists _, _; iFrame.
      simpl. iFrame. }

    iModIntro.
    wp_bind.
    iInv "Hinv" as "H".
    destruct_einner "H".
    iDestruct "Hcase" as "(Ho1&Ho2&Hfst&Hsnd)".
    iApply (wp_write_disk with "Hsnd"). iIntros "!> Hsnd".
    iMod (ghost_var_update γ3 (new_fst, new_snd) with "Hown3 [$]") as "(Hown3&Hother_ghost)".
    iModIntro; iExists _, _; iFrame.
    simpl.
    iExists (_, _). iFrame. 

    (* iInv fails for mysterious type class reasons that I cannot debug *)
    wp_bind.
    iApply wp_atomic.
    iMod (inv_open with "Hinv") as "(H&Hclo)"; first by set_solver+; iModIntro.
    destruct_einner "H".
    iModIntro.
    iMod (ghost_var_update γ1 (swap_ptr ptr_val) with "Hown1 [$]") as "(Hown1&Hptr_ghost)".
    iMod (ghost_var_update γ2 (new_fst, new_snd) with "Hown2 [$]") as "(Hown2&Hpair_ghost)".
    iMod (ghost_var_update γ3 (n, n0) with "Hown3 [$]") as "(Hown3&Hother_ghost)".
    iMod (ghost_step_lifting with "Hj Hsource_inv Hsource") as "(Hj&Hsource&_)".
    { do 2 eexists; split; last by eauto. econstructor. }
    { solve_ndisj. }

    iApply (wp_write_disk with "Hptr"). iIntros "!> Hsnd".
    iMod ("Hclo" with "[-Hj HΦ Hlocked Hptr_ghost Hpair_ghost Hother_ghost]").
    { iModIntro. iExists (swap_ptr ptr_val). simpl. iExists _, _; iFrame.
      iFrame. iDestruct "Hcase" as "(Ho1&Ho2&Hfst'&Hsnd')".
      rewrite ?read_of_swap ?write_of_swap; iFrame.
    }

    iModIntro.
    iApply (wp_unlock with "[-HΦ Hj]"); iFrame.
    { iFrame "Hlockinv". iExists _, _, _. iFrame. } 
    iIntros "!> _". by iApply "HΦ".
  Qed.
End refinement_triples.