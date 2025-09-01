From iris.proofmode Require Import proofmode environments.
From Perennial.Helpers Require Import NamedProps.

(** * Caching and re-using Iris proofs.

    Tactics for saving an Iris proof using a collection of hypotheses.

    Usage:

    [iCache P with "H1 H2..."] asks the user to prove [P] using hypotheses H1
    H2... from the context. It creates a cached proof in the persistent context.

    Later, [iFromCache] attempts to prove the goal using a matching cache and
    the exact same hypotheses (including names).
 *)

(** Implementation details:

    A cache [c] for a result [R] remembers an [env] ([c.(cache_prop)]) and a
    list of names used, and the persistent statement in the context is:

    □ ([∗] c -∗ R)

    Constructing the proof just involves setting up this statement. It uses
    [iNamed] to serialize/deserialize the hypotheses while retaining names. See
    [cached_make] for where the naming comes from, and [iCache_go] for some
    cleanup after iApplying that theorem.

    To restore the cache, we just split the environment with [envs_split] using
    the list of names in the cache and match exactly with the cache's
    environment. This works well because it uses a canonical order specified in
    the cache, so after splitting we can look for equality. See
    [tac_cached_use].

    Finally, we use a cute trick to make the caches look pleasant: a
    printing-only notation in [cache_hide_scope] that doesn't print the
    environment and only shows the goal and hypotheses. It's possible to hide
    things using implicits instead, but this solution has some advantages:

    - Caches are displayed as [cache_for!], which tells you something funny is
      going on.
    - We have a little more control over the display (for example, it says
      [cache_for! ... with ...] as a hint for what the second argument means).
    - Caches can be temporarily displayed with [Local Close Scope cache_hide_scope].

 *)

Section bi.
  Context {PROP: bi}.
  Context `{!BiAffine PROP}.

  Record cache (R: PROP) :=
    Cache { cache_prop :> env PROP;
            cache_names: list ident; }.

  Arguments cache_names {R} c.
  Arguments cache_prop {R} c.

  Definition cached_def {R} (c: cache R): PROP :=
    (□ ([∗] c -∗ R))%I.
  Definition cached_aux : seal (@cached_def). by eexists. Qed.
  Definition cached := unseal cached_aux.
  Definition cached_eq : @cached = @cached_def := seal_eq cached_aux.
  Arguments cached {R} c.

  Ltac unseal := rewrite cached_eq /cached_def.

  Global Instance cached_Persistent {R} c : Persistent (@cached R c).
  Proof. unseal. apply _. Qed.

  Lemma cached_elim R (c: cache R) Δs :
    Δs.(env_spatial) = c.(cache_prop) →
    cached c -∗
    of_envs Δs -∗
    R.
  Proof.
    unseal.
    iIntros (Hsubenv) "#Hcache HΔ".
    iDestruct (envs_clear_spatial_sound with "HΔ") as "(HΔ'&HΔs)".
    iApply "Hcache".
    rewrite -Hsubenv.
    iAssumption.
  Qed.

  Local Theorem tac_cached_use {Δ: envs PROP} i {R} (c: cache R) :
    envs_lookup i Δ = Some (true, cached c) →
    match envs_split base.Left c.(cache_names) Δ with
    | Some (Γs, _) => Γs.(env_spatial) = c.(cache_prop)
    | None => False
    end →
    envs_entails Δ R.
  Proof.
    iIntros (Hlookup Hsubenv).
    destruct_with_eqn (envs_split base.Left c.(cache_names) Δ); [ | contradiction ].
    destruct p as [Γs Γ'].
    rewrite envs_entails_unseal.
    iIntros "HΔ".
    iDestruct (envs_lookup_intuitionistic_sound _ _ _ Hlookup with "HΔ") as
        "[#Hcache HΔ]".
    iDestruct (envs_split_sound with "HΔ") as "[HΔ1 HΔ2]"; eauto.
    iApply (cached_elim with "Hcache HΔ1"); auto.
  Qed.

  Local Theorem cached_make R (c: cache R) :
    □ (env_to_named_prop c -∗ R) -∗
    cached c.
  Proof.
    unseal.
    iIntros "#HR !>".
    rewrite env_to_named_prop_sound //.
  Qed.
End bi.

Arguments cached {PROP R} c.
Arguments cache_names {PROP R} c.
Arguments cache_prop {PROP R} c.

(* following the pattern from proofmode/reduction.v *)
Declare Reduction cached_eval :=
  cbv [ env_to_named_prop env_to_named_prop_go cache_prop ].
Ltac cached_eval t :=
  eval cached_eval in t.
Ltac cached_reduce :=
  match goal with |- ?u => let v := cached_eval u in change_no_check v end.

Ltac iCache_go P Hs pat :=
  let Hs := String.words Hs in
  let Hs := (eval vm_compute in (INamed <$> Hs)) in
  let Δ := iGetCtx in
  let js := reduction.pm_eval (envs_split base.Left Hs Δ) in
  match js with
  | Some (?Δ, _) => let Γs := (eval cbv [env_spatial] in Δ.(env_spatial)) in
                    iAssert (cached (Cache P Γs Hs)) as pat;
                    [ iApply cached_make; iModIntro;
                      cached_reduce;
                      iNamed 1
                    | ]
  | None => fail 1 "hypotheses not found"
  end.

Tactic Notation "iCache" constr(P) "with" constr(Hs) :=
  iCache_go P Hs "#?".

Ltac iFromCache :=
  lazymatch goal with
  | [ |- envs_entails (Envs ?Γp _ _) ?P ] =>
    first [ match Γp with
            | context[Esnoc _ ?i (@cached _ P ?c)] =>
              apply (tac_cached_use i c);
              [ reflexivity (* lookup should always succeed, found by context match *)
              | reduction.pm_reduce;
                reflexivity ]
            end
          | lazymatch Γp with
            | context[Esnoc _ _ (@cached _ P _)] =>
              fail 1 "iFromCache: could not find hypotheses for any cache"
            | _ =>
              fail 1 "iFromCache: no matching caches"
            end
          ]
  end.

Declare Scope cache_hide_scope.
Notation "'cache_for!' P 'with' Hs" := (cached (Cache P _ Hs))
                                         (at level 29, only printing) : cache_hide_scope.
Open Scope cache_hide_scope.

Module examples.
  Section bi.
    Context {PROP:bi} `{!BiAffine PROP}.
    Context (P P1 P2 Q R: PROP).
    Context (HP: P -∗ P1 ∗ P2).
    Context (HQ: P1 -∗ Q).

    Example make_and_use_cache :
      P -∗
      P1 ∗ (P -∗ P1).
    Proof.
      iIntros "HP".
      iCache P1 with "HP".
      { iDestruct (HP with "HP") as "[$ _]". }
      iSplitL "HP".
      - iFromCache.
      - iIntros "HP".
        iFromCache.
    Qed.

    Example multiple_caches_for_goal :
      P ∗ Q -∗
      Q ∗ Q.
    Proof.
      iIntros "[HP HQ]".
      iCache Q with "HP".
      { iDestruct (HP with "HP") as "[HP1 _]".
        iDestruct (HQ with "HP1") as "$". }
      iCache Q with "HQ".
      { auto. }
      iSplitL "HP".
      (* these goals are identical, so one of them requires backtracking on
      which cache to use *)
      - iFromCache.
      - iFromCache.
    Qed.

    Example reordered_hypotheses :
      P ∗ Q -∗
      Q ∗ P.
    Proof.
      iIntros "[HP HQ]".
      iCache (Q ∗ P)%I with "HQ HP".
      { iFrame. }
      (* we need to grab the goals from the context in the opposite order that
      they appear; the current implementation uses envs_split driven by a list
      of hypotheses in the cache itself to guide the splitting and order *)
      iFromCache.
    Qed.

    Example fail_no_hyps :
      P -∗ P.
    Proof.
      iIntros "HP".
      iCache P with "HP"; first by iFrame.
      iRename "HP" into "HP'".
      Fail iFromCache. (* this should report a useful error *)
    Abort.

    Example fail_wrong_hyps :
      P ∗ Q -∗ P.
    Proof.
      iIntros "[HP HQ]".
      iCache P with "HP"; first by iFrame.
      iClear "HP". iRename "HQ" into "HP".
      Fail iFromCache. (* this should report a useful error *)
    Abort.

    Example fail_no_cache :
      P -∗ P.
    Proof.
      iIntros "HP".
      Fail iFromCache. (* this should report a useful error *)
    Abort.

  End bi.
End examples.
