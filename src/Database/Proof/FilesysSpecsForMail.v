From iris.proofmode Require Export tactics.
From iris.algebra Require Import auth frac_auth.

From RecoveryRefinement Require Export CSL.WeakestPre CSL.Lifting.

From RecoveryRefinement Require Import Database.Proof.BaseMachine.

Implicit Types (p:Path) (fh:Fd) (bs:ByteString).

Definition path_dec : forall (a b : Path), {a=b}+{a<>b} := string_dec.

Section lifting.
  Context `{!baseG Σ}.
  Context `{!inG Σ (authR (optionUR (exclR boolC)))}.

  (* TODO: should really be a set of paths, or invariant to permutation;
  currently ignoring this complication entirely *)
  Definition dirents (G: gmap Path gname) : iProp Σ.
  Admitted.

  Theorem wp_create G p g :
    {{{ ▷ (dirents G ∗ own g (◯ (Excl' false))) ∗ ⌜G !! p = Some g⌝ }}}
      FS.create p
      {{{ fh, RET fh; dirents G ∗ own g (◯ (Excl' true)) ∗ p ↦ BS.empty ∗ fh ↦ (p, FS.Write) }}}.
  Admitted.

  Theorem wp_append fh bs' p bs :
    {{{ ▷ (p ↦ bs ∗ fh ↦ (p, FS.Write)) }}}
      FS.append fh bs'
      {{{ RET (); p ↦ (BS.append bs bs') ∗ fh ↦ (p, FS.Write) }}}.
  Admitted.

  Theorem wp_close fh p m :
    {{{ ▷ fh ↦ (p, m) }}}
      FS.close fh
      {{{ RET (); emp }}}.
  Admitted.

  (* TODO: is this the right spec? should [p ↦ bs] be in the precondition? how
  are [p ↦ ?] facts related to dirents S? *)
  Theorem wp_open G p bs :
    {{{ ▷ (dirents G ∗ p ↦ bs) }}}
      FS.open p
      {{{ fh, RET fh; dirents G ∗ p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
  Admitted.

  Theorem wp_readAt fh off len p bs :
    {{{ ▷ (p ↦ bs ∗ fh ↦ (p, FS.Read)) }}}
      FS.readAt fh off len
      {{{ bs_r, RET bs_r; ⌜bs_r = BS.take len (BS.drop off bs)⌝ ∗ p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
  Admitted.

  Theorem wp_size fh p bs :
    {{{ ▷ (p ↦ bs ∗ fh ↦ (p, FS.Read)) }}}
      FS.size fh
      {{{ len, RET len; ⌜len = BS.length bs⌝ ∗ p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
  Admitted.

  (* TODO: constrain result [r] in terms of owned ghost variables from g *)
  Theorem wp_list G :
    {{{ ▷ dirents G }}}
      FS.list
      {{{ r, RET r; dirents G }}}.
  Admitted.

  (* TODO: require no open FDs for the deleted file? *)
  Theorem wp_delete G p g bs :
    {{{ ▷ (dirents G ∗ own g (◯ (Excl' true)) ∗ p ↦ bs) ∗ ⌜G !! p = Some g⌝ }}}
      FS.delete p
      {{{ RET (); dirents G ∗ own g (◯ (Excl' false)) }}}.
  Admitted.

  Theorem wp_link G (src dst : Path) g bs :
    {{{ ▷ (dirents G ∗ src ↦ bs) }}}
      FS.link src dst
      {{{ ok, RET ok;
        match ok with
        | false => dirents G ∗ src ↦ bs
        | true => dirents G ∗ src ↦ bs ∗ dst ↦ bs ∗ own g (◯ (Excl' true)) ∗ ⌜G !! dst = Some g⌝
        end }}}.
  Admitted.

  Theorem wp_random :
    {{{ True }}}
      FS.random
      {{{ r, RET r; True }}}.
  Admitted.

End lifting.

(*
Section DerivedSpecs.
  Context `{baseG Σ}.

  Local Open Scope bi_scope.

  Definition appendFile p fh bs := p ↦ bs ∗ fh ↦ (p, FS.Write).
  Definition readFile p fh bs := p ↦ bs ∗ fh ↦ (p, FS.Read).

  Theorem create_ok S p fh :
    {{{ ▷ dirents S ∗ ⌜~p ∈ S⌝ }}}
      FS.create p
      {{{ RET fh; dirents (p::S) ∗ appendFile p fh BS.empty }}}.
  Proof.
    iIntros (Φ).
    iApply wp_create.
  Qed.

  Theorem append_ok fh bs' p bs :
    {{{ ▷ appendFile p fh bs }}}
      FS.append fh bs'
      {{{ RET (); appendFile p fh (BS.append bs bs') }}}.
  Proof.
    iIntros (Φ).
    iApply wp_append.
  Qed.

  Theorem append_close_ok fh p bs :
    {{{ ▷ appendFile p fh bs }}}
      FS.close fh
      {{{ RET (); p ↦ bs }}}.
  Proof.
    iIntros (Φ) "!> Hpre Post".
    iDestruct "Hpre" as "(Hp & Hfh)".
    iApply (wp_close with "Hfh").
    iIntros "!> _".
    iApply ("Post" with "Hp").
  Qed.

  Theorem read_close_ok fh p bs :
    {{{ ▷ readFile p fh bs }}}
      FS.close fh
      {{{ RET (); p ↦ bs }}}.
  Proof.
    iIntros (Φ) "!> Hpre Post".
    iDestruct "Hpre" as "(Hp & Hfh)".
    iApply (wp_close with "Hfh").
    iIntros "!> _".
    iApply ("Post" with "Hp").
  Qed.

  Theorem open_ok S p fh bs :
    {{{ ▷ (dirents S ∗ p ↦ bs) ∗ ⌜p ∈ S⌝ }}}
      FS.open p
      {{{ RET fh; dirents S ∗ readFile p fh bs }}}.
  Proof.
    iIntros (Φ).
    iApply wp_open.
  Qed.

  Theorem readAt_ok fh off len p bs bs_r :
    {{{ ▷ readFile p fh bs }}}
      FS.readAt fh off len
      {{{ RET bs_r; ⌜bs_r = BS.take len (BS.drop off bs)⌝ ∗ readFile p fh bs }}}.
  Proof.
    iIntros (Φ).
    iApply wp_readAt.
  Qed.

End DerivedSpecs.

Global Opaque appendFile readFile.
*)
