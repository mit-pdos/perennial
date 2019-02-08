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
    {{{ ▷ r ↦ x }}}
      Data.readIORef r
      {{{ RET ret; ⌜ret = x⌝ ∗ r ↦ x }}}.
  Proof.
  Admitted.

  Theorem wp_writeIORef T (r: IORef T) (x x':T) :
    {{{ ▷ r ↦ x }}}
      Data.writeIORef r x'
      {{{ RET (); r ↦ x' }}}.
  Proof.
  Admitted.

  Theorem wp_newArray T (r:Array T) :
    {{{ emp }}}
      Data.newArray T
      {{{ RET r; r ↦ [] }}}.
  Proof.
  Admitted.

  Theorem wp_arrayLength T (r:Array T) (v: list T) (l:uint64) :
    {{{ ▷ r ↦ v }}}
      Data.arrayLength r
      {{{ RET l; ⌜l = fromNum (length v)⌝ ∗ r ↦ v }}}.
  Proof.
  Admitted.

  Theorem wp_arrayGet T (r:Array T) (v: list T) (i:uint64) (x:T) :
    {{{ ▷ r ↦ v ∗ ⌜toNum i < length v⌝ }}}
      Data.arrayGet r i
      {{{ RET x; ⌜List.nth_error v i.(toNum) = Some x⌝ ∗ r ↦ v }}}.
  Proof.
  Admitted.

  Theorem wp_arrayAppend T (r:Array T) (v: list T) (x:T) :
    {{{ ▷ r ↦ v }}}
      Data.arrayAppend r x
      {{{ RET (); r ↦ (v ++ [x]) }}}.
  Proof.
  Admitted.

  Theorem wp_newHashTable V (r:HashTable V) :
    {{{ emp }}}
      Data.newHashTable V
      {{{ RET r; r ↦ ∅ }}}.
  Proof.
  Admitted.

  Theorem wp_hashTableLookup V (r:HashTable V) (v:Data.hashtableM V) k mv :
    {{{ r ↦ v }}}
      Data.hashTableLookup r k
      {{{ RET mv; ⌜mv = v !! k⌝ ∗ r ↦ v }}}.
  Proof.
  Admitted.

  Theorem wp_hashTableAlter V (r:HashTable V) (v:Data.hashtableM V) k f :
    {{{ r ↦ v }}}
      Data.hashTableAlter r k f
      {{{ RET (); r ↦ (Data.alter_map v k f) }}}.
  Proof.
  Admitted.

  Theorem wp_hashTableReadAll V (r:HashTable V) (v:Data.hashtableM V) (ents: Array (uint64*V)):
    {{{ r ↦ v }}}
      Data.hashTableReadAll r
      {{{ RET ents; ents ↦ map_to_list v ∗ r ↦ v }}}.
  Proof.
  Admitted.

End lifting.
