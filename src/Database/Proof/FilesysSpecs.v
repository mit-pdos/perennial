From iris.proofmode Require Export tactics.

From RecoveryRefinement Require Export CSL.WeakestPre CSL.Lifting.

From RecoveryRefinement Require Import Database.Proof.BaseMachine.

Implicit Types (p:Path) (fh:Fd) (bs:ByteString).

Definition path_dec : forall (a b : Path), {a=b}+{a<>b} := string_dec.

Section lifting.
  Context `{!baseG Σ}.

  (* TODO: should really be a set of paths, or invariant to permutation;
  currently ignoring this complication entirely *)
  Definition dirents (S: list Path) : iProp Σ.
  Admitted.

  Theorem wp_create S p :
    {{{ ▷ dirents S ∗ ⌜~p ∈ S⌝ }}}
      FS.create p
      {{{ fh, RET fh; dirents (p::S) ∗ p ↦ BS.empty ∗ fh ↦ (p, FS.Write) }}}.
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
  Theorem wp_open S p bs :
    {{{ ▷ (dirents S ∗ p ↦ bs) ∗ ⌜p ∈ S⌝ }}}
      FS.open p
      {{{ fh, RET fh; dirents S ∗ p ↦ bs ∗ fh ↦ (p, FS.Read) }}}.
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

  (* TODO: handle permutation here *)
  Theorem wp_list S :
    {{{ ▷ dirents S }}}
      FS.list
      {{{ r, RET r; ⌜r = S⌝ ∗ dirents S}}}.
  Admitted.

  (* TODO: require no open FDs for the deleted file? *)
  Theorem wp_delete S p bs :
    {{{ ▷ dirents S ∗ ⌜p ∈ S⌝ ∗ p ↦ bs }}}
      FS.delete p
      {{{ RET (); dirents (remove path_dec p S) }}}.
  Admitted.

  Theorem wp_link (src dst : Path) S bs :
    {{{ ▷ (dirents S ∗ src ↦ bs) }}}
      FS.link src dst
      {{{ ok, RET ok;
        match ok with
        | false => dirents S ∗ src ↦ bs
        | true => dirents (dst::S) ∗ src ↦ bs ∗ dst ↦ bs
        end }}}.
  Admitted.

  Theorem wp_random :
    {{{ True }}}
      FS.random
      {{{ r, RET r; True }}}.
  Admitted.

End lifting.

Section DerivedSpecs.
  Context `{baseG Σ}.

  Local Open Scope bi_scope.

  Definition appendFile p fh bs := p ↦ bs ∗ fh ↦ (p, FS.Write).
  Definition readFile p fh bs := p ↦ bs ∗ fh ↦ (p, FS.Read).

  Theorem create_ok S p :
    {{{ ▷ dirents S ∗ ⌜~p ∈ S⌝ }}}
      FS.create p
      {{{ fh, RET fh; dirents (p::S) ∗ appendFile p fh BS.empty }}}.
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

  Theorem open_ok S p bs :
    {{{ ▷ (dirents S ∗ p ↦ bs) ∗ ⌜p ∈ S⌝ }}}
      FS.open p
      {{{ fh, RET fh; dirents S ∗ readFile p fh bs }}}.
  Proof.
    iIntros (Φ).
    iApply wp_open.
  Qed.

  Theorem readAt_ok fh off len p bs :
    {{{ ▷ readFile p fh bs }}}
      FS.readAt fh off len
      {{{ bs_r, RET bs_r; ⌜bs_r = BS.take len (BS.drop off bs)⌝ ∗ readFile p fh bs }}}.
  Proof.
    iIntros (Φ).
    iApply wp_readAt.
  Qed.

End DerivedSpecs.

Global Opaque appendFile readFile.
