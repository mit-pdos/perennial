From New.generatedproof Require Import math.bits.
From New.proof Require Import proof_prelude unsafe.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : bits.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) bits := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) bits := build_get_is_pkg_init_wf.

Lemma wp_initialize' get_is_pkg_init :
  get_is_pkg_init_prop bits get_is_pkg_init →
  {{{ own_initializing get_is_pkg_init }}}
    bits.initialize' #()
  {{{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init bits }}}.
Proof using W.
  intros Hinit. wp_start as "Hown".
  wp_apply (wp_package_init with "[$Hown] HΦ") as "Hown".
  { destruct Hinit as (-> & ?); done. }
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "?".
  wp_apply wp_GlobalAlloc as "H1".
  wp_apply wp_GlobalAlloc as "H2".
  wp_apply (unsafe.wp_initialize' with "Hown") as "[Hown #?]" --no-auto; first naive_solver.
  progress (do 64 wp_pure).
  progress (do 64 wp_pure).
  progress (do 64 wp_pure).
  rewrite /Z.add /Pos.add /Pos.succ /=.
  wp_pures.
  wp_store.
  iClear "H2".
  progress (do 64 wp_pure).
  progress (do 64 wp_pure).
  progress (do 64 wp_pure).
  wp_pures.
  wp_store.
  iClear "H1".
  wp_auto.
  iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".
  iModIntro.
  iFrame "#". done.
Qed.

Lemma wp_Len64 (x : w64) :
  {{{ True }}}
    @! bits.Len64 #x
  {{{ (l : w64), RET #l; True }}}.
Proof using W.
  wp_start. wp_auto.
  wp_if_join (λ v, ∃ (x n : w64), "->" ∷ ⌜ v = execute_val ⌝ ∗
                                  "x" ∷ x_ptr ↦ x ∗ "n" ∷ n_ptr ↦ n ∗
                                  "%Hx32" ∷ ⌜ uint.Z x < 2^32 ⌝)%I with "[x n]";
    [iFrame; [iSplit; try done; word] ..|].
  iIntros "% @". wp_auto. (* TODO: add this to [wp_if_join]? *)
  wp_if_join (λ v, ∃ (x n : w64), "->" ∷ ⌜ v = execute_val ⌝ ∗
                                  "x" ∷ x_ptr ↦ x ∗ "n" ∷ n_ptr ↦ n ∗
                                  "%Hx16" ∷ ⌜ uint.Z x < 2^16 ⌝)%I with "[x n]";
    [iFrame; [iSplit; try done; word] ..|].
  iIntros "% @". wp_auto.
  wp_if_join (λ v, ∃ (x n : w64), "->" ∷ ⌜ v = execute_val ⌝ ∗
                                  "x" ∷ x_ptr ↦ x ∗ "n" ∷ n_ptr ↦ n ∗
                                  "%Hx8" ∷ ⌜ uint.Z x < 2^8 ⌝)%I with "[x n]";
    [iFrame; [iSplit; try done; word] ..|].
  iIntros "% @". wp_auto.

  destruct lookup eqn:Hlookup.
  2:{ exfalso. apply lookup_ge_None in Hlookup. simpl in Hlookup. word. }
  wp_auto. wp_end.
Qed.

Lemma wp_Len (x : w64) :
  {{{ True }}}
    @! bits.Len #x
  {{{ (l : w64), RET #l; True }}}.
Proof using W.
  wp_start. wp_auto. wp_apply wp_Len64 as "% _". wp_end.
Qed.

End wps.
