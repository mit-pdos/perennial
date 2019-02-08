From iris.proofmode Require Export tactics.

From RecoveryRefinement Require Export CSL.WeakestPre CSL.Lifting.

From RecoveryRefinement Require Import Database.Proof.BaseMachine.

Section lifting.
  Context `{!baseG Σ}.

  Theorem wp_newIORef T (x:T) (r: IORef T) :
    {{{ emp }}}
      Data.newIORef x
      {{{ RET r; r ↦ x }}}.
  Proof.
  Admitted.

  Theorem wp_readIORef T (r: IORef T) (x ret:T) :
    {{{ r ↦ x }}}
      Data.readIORef r
      {{{ RET ret; ⌜ret = x⌝ ∗ r ↦ x }}}.
  Proof.
  Admitted.

  Theorem wp_writeIORef T (r: IORef T) (x x':T) :
    {{{ r ↦ x }}}
      Data.writeIORef r x'
      {{{ RET (); r ↦ x' }}}.
  Proof.
  Admitted.

End lifting.
