Require Import New.code.github_com.mit_pdos.go_journal.util.
Require Import New.generatedproof.github_com.mit_pdos.go_journal.util.
Require Import New.proof.proof_prelude.
Require Import New.proof.github_com.goose_lang.primitive.disk.
Require Import New.proof.github_com.mit_pdos.go_journal.common.
Require Import New.proof.log.

From Perennial.Helpers Require Import ModArith.

Section proof.
Context `{!heapGS Σ} `{!goGlobalsGS Σ}.
Context `{!util.GlobalAddrs}.
Context `{!ghost_varG Σ ()}.

Local Instance wp_globals_alloc_inst :
  WpGlobalsAlloc util.vars' (@util.GlobalAddrs) (@util.var_addrs) (λ _, util.own_allocated).
Proof.
  solve_wp_globals_alloc.
Qed.

(* More realistically, we might want to put this as a non-persistent fact inside
 * the invariant, to reason about changing the Debug value, but we currently don't
 * prove any WPs about code that modifies Debug, so ignore that technicality for now.
 *)
Definition is_initialized `{!util.GlobalAddrs} : iProp Σ :=
  ∃ (level: w64),
    "Hglobal_debug" ∷ util.Debug ↦□ level.

#[global] Instance is_pkg_init_util : IsPkgInit (PROP:=iProp Σ) util.
  (* XXX how to inherit the defaults from [build_pkg_init]? *)
  refine {|
    is_pkg_init_def := (
      "#Hdef" ∷ is_pkg_defined util ∗
      "#Hlog" ∷ is_pkg_init log ∗
      "#Hinit" ∷ is_initialized
    );
    is_pkg_init_persistent := _
  |}.
Defined.

Implicit Types (v:val).

Theorem wp_Min_l (n m: u64) :
  {{{ is_pkg_init util ∗
      ⌜ uint.Z n <= uint.Z m ⌝ }}}
    util@"Min" #n #m
  {{{ RET #n; True }}}.
Proof.
  wp_start as "%Hmin".
  wp_alloc mptr as "Hm".
  wp_pures.
  wp_alloc nptr as "Hn".
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_if_destruct.
  - wp_load. wp_pures.
    iApply "HΦ". done.
  - wp_load. wp_pures.
    replace m with n by word.
    iApply "HΦ". done.
Qed.

Theorem wp_Min_r (n m: u64) :
  {{{ is_pkg_init util ∗
      ⌜ uint.Z n >= uint.Z m ⌝ }}}
    util@"Min" #n #m
  {{{ RET #m; True }}}.
Proof.
  wp_start as "%Hmin".
  wp_alloc mptr as "Hm".
  wp_pures.
  wp_alloc nptr as "Hn".
  wp_pures.
  wp_load.
  wp_pures.
  wp_load.
  wp_pures.
  wp_if_destruct.
  - wp_load. wp_pures.
    replace n with m by word.
    iApply "HΦ". done.
  - wp_load. wp_pures.
    iApply "HΦ". done.
Qed.

Theorem wp_DPrintf (level: u64) (msg: go_string) (arg: slice.t) :
  {{{ is_pkg_init util ∗
      True }}}
    util@"DPrintf" #level #msg #arg
  {{{ T (_: IntoVal T) (v: T), RET #v; True }}}.
Proof.
  (* XXX if I use [wp_start], then I can't name the [is_pkg_init] fact to extract [is_initialized].. *)
  (* wp_start as "_". *)
  iIntros (Φ) "[#Hpkg _] HΦ".
  wp_func_call. wp_call.

  wp_alloc aptr as "Ha".
  wp_pures.
  wp_alloc msgptr as "Hmsg".
  wp_pures.
  wp_alloc lptr as "Hl".
  wp_pures.
  wp_load.

  wp_globals_get.

  (* Annoying that [iNamed "Hpkg"] doesn't work directly.. *)
  rewrite /is_pkg_init /is_pkg_init_util.
  iNamed "Hpkg".
  iNamed "Hinit".
  wp_load.
  wp_pures.
  wp_if_destruct.
  - wp_load.
    wp_pures.
    wp_load.
    wp_pures.
    wp_apply wp_Printf.
    iApply "HΦ". done.
  - iApply "HΦ". done.
Qed.

Theorem wp_SumOverflows (x y: u64) :
  {{{ is_pkg_init util }}}
    util@"SumOverflows" #x #y
  {{{ (ok: bool), RET #ok; ⌜ok = bool_decide (uint.Z x + uint.Z y >= 2^64)⌝ }}}.
Proof.
  wp_start as "_".
  wp_auto.
  iApply "HΦ".
  iPureIntro.
  apply bool_decide_ext, sum_overflow_check.
Qed.

Theorem wp_CloneByteSlice (s:slice.t) q (vs:list w8) :
  {{{ is_pkg_init util ∗
      own_slice s q vs }}}
    util@"CloneByteSlice" #s
  {{{ (s':slice.t), RET #s';
      own_slice s q vs ∗
      own_slice s' (DfracOwn 1) vs }}}.
Proof.
  wp_start as "Hs".
  wp_auto.
  wp_apply wp_slice_make2. iIntros (s') "[Hs' _]".
  wp_auto.
  wp_apply (wp_slice_copy with "[$Hs $Hs']"). iIntros (n) "[% [Hs' Hs]]".
  wp_auto.
  iDestruct (own_slice_len with "Hs") as "%Hlen".
  autorewrite with len. rewrite -Hlen. rewrite firstn_all.
  rewrite drop_ge.
  2: { rewrite length_replicate. done. }
  rewrite app_nil_r.
  iApply "HΦ". iFrame.
Qed.

End proof.
