From New.proof.github_com.mit_pdos.tulip Require Import program_prelude.
From New.proof Require Import grove_prelude.

From New.generatedproof.github_com.mit_pdos.tulip Require Import quorum.

(* Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. *)

Section cquorum.
  Context `{!heapGS Σ} `{!goGlobalsGS Σ}.

  #[global] Program Instance : IsPkgInit quorum := ltac2:(build_pkg_init ()).

  Theorem wp_ClassicQuorum (n : u64) :
    {{{ is_pkg_init quorum }}}
      quorum @ "ClassicQuorum" #n
    {{{ (x : u64), RET #x; ⌜uint.Z x = (uint.Z n / 2 + 1)%Z⌝ }}}.
  Proof.
    (*@ func ClassicQuorum(n uint64) uint64 {                                   @*)
    (*@     // floor(n / 2) + 1                                                 @*)
    (*@     return n / 2 + 1                                                    @*)
    (*@ }                                                                       @*)
    wp_start as "_".
    wp_auto.
    iApply "HΦ".
    word.
  Qed.

  (* The precondition enforces no overflow. *)
  Theorem wp_FastQuorum (n : u64) :
    uint.Z n < 2 ^ 62 ->
    {{{ is_pkg_init quorum }}}
      quorum @ "FastQuorum" #n
    {{{ (x : u64), RET #x; ⌜uint.Z x = ((3 * uint.Z n + 3) / 4)%Z⌝ }}}.
  Proof.
    (*@ func FastQuorum(n uint64) uint64 {                                      @*)
    (*@     // ceiling(3n / 4)                                                  @*)
    (*@     return (3 * n + 3) / 4                                              @*)
    (*@ }                                                                       @*)
    iIntros (Hn).
    wp_start as "_".
    wp_auto.
    iApply "HΦ".
    word.
  Qed.

  Theorem wp_Half (n : u64) :
    uint.Z n < 2 ^ 64 - 1 ->
    {{{ is_pkg_init quorum }}}
      quorum @ "Half" #n
    {{{ (x : u64), RET #x; ⌜uint.Z x = ((uint.Z n + 1) / 2)%Z⌝ }}}.
  Proof.
    (*@ func Half(n uint64) uint64 {                                            @*)
    (*@     // ceiling(n / 2)                                                   @*)
    (*@     return (n + 1) / 2                                                  @*)
    (*@ }                                                                       @*)
    iIntros (Hn).
    wp_start as "_".
    wp_auto.
    iApply "HΦ".
    word.
  Qed.

End cquorum.
