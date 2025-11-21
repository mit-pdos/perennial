From New.proof Require Import fmt.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.primitive Require Import disk.
From New.proof.github_com.goose_lang Require Import std.
From New.proof Require Import log.
From New.proof Require Import sync.
From New.proof Require Import disk_prelude.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples Require Import unittest.
From New.generatedproof Require Import fmt.
From New.generatedproof.github_com.goose_lang.goose.testdata.examples
  Require Import unittest.
From New.proof Require Import proof_prelude.

Unset Printing Records.

Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx : GoContext}.

#[global] Instance : IsPkgInit unittest := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf unittest := build_get_is_pkg_init_wf.

Lemma wp_BasicNamedReturn :
  {{{ is_pkg_init unittest }}}
    @! unittest.BasicNamedReturn #()
  {{{ RET #"ok"; True }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

Lemma wp_VoidButEndsWithReturn :
  {{{ is_pkg_init unittest }}}
    @! unittest.VoidButEndsWithReturn #()
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  wp_apply wp_BasicNamedReturn.
  by iApply "HΦ".
Qed.

Lemma wp_VoidImplicitReturnInBranch (b: bool) :
  {{{ is_pkg_init unittest }}}
    @! unittest.VoidImplicitReturnInBranch #b
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  destruct b; wp_auto.
  - by iApply "HΦ".
  - wp_apply wp_BasicNamedReturn.
    by iApply "HΦ".
Qed.

Lemma wp_typeAssertInt (x: interface.t) (v: w64) :
  {{{ is_pkg_init unittest ∗ ⌜x = interface.mk intT.id #v⌝ }}}
    @! unittest.typeAssertInt #x
  {{{ RET #v; True }}}.
Proof.
  wp_start as "->". wp_auto.
  wp_apply wp_interface_type_assert.
  { done. }
  by iApply "HΦ".
Qed.

Lemma wp_wrapUnwrapInt :
  {{{ is_pkg_init unittest }}}
    @! unittest.wrapUnwrapInt #()
  {{{ RET #(W64 1); True }}}.
Proof.
  wp_start as "_".
  wp_apply wp_typeAssertInt.
  { done. }
  by iApply "HΦ".
Qed.

Lemma wp_checkedTypeAssert (x: interface.t) :
  {{{ is_pkg_init unittest ∗
        ⌜match x with
        | interface.mk type_id' v0 =>
            (* a technical side condition is required to show that if i has the
               correct type identity, then the value it holds has the expected type
               V *)
            uint64T.id = type_id' →
            ∃ (v: w64), v0 = #v
        |  interface.nil => True
        end⌝
  }}}
    @! unittest.checkedTypeAssert #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  wp_apply (wp_interface_checked_type_assert _ (V:=w64)).
  { auto. }
  iIntros (y ok Hpost).
  wp_auto.
  destruct ok; subst; wp_auto.
  - by iApply "HΦ".
  - by iApply "HΦ".

  Unshelve.
  apply _.
Qed.

Lemma wp_basicTypeSwitch (x: interface.t) :
  {{{ is_pkg_init unittest ∗
      ⌜match x with
      | interface.mk type_id v =>
          (type_id = intT.id → ∃ (v': w64), v = #v') ∧
          (type_id = stringT.id → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    @! unittest.basicTypeSwitch #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  wp_apply wp_interface_checked_type_assert.
  {
    destruct x; intuition.
  }
  iIntros (???).
  wp_auto.
  destruct ok; subst; wp_auto.
  { by iApply "HΦ". }
  wp_apply wp_interface_checked_type_assert.
  {
    destruct x; intuition.
  }
  iIntros (???).
  wp_auto.
  destruct ok; wp_auto.
  { by iApply "HΦ". }
  by iApply "HΦ".
  Unshelve.
  all: apply _.
Qed.

Lemma wp_fancyTypeSwitch (x: interface.t) :
  {{{ is_pkg_init unittest ∗
      ⌜match x with
      | interface.mk type_id v =>
          (type_id = intT.id → ∃ (v': w64), v = #v') ∧
          (type_id = stringT.id → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    @! unittest.fancyTypeSwitch #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  {
    destruct x; intuition.
  }
  iIntros (???); wp_auto.
  destruct ok; subst; wp_auto.
  { by iApply "HΦ". }
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  {
    destruct x; intuition.
  }
  iIntros (???); wp_auto.
  destruct ok; subst; wp_auto.
  { by iApply "HΦ". }
  wp_if_destruct.
  { rewrite bool_decide_true //. wp_auto. by iApply "HΦ". }
  rewrite bool_decide_false //. wp_auto.
  by iApply "HΦ".
Qed.

Lemma wp_multiTypeSwitch x :
  {{{ is_pkg_init unittest ∗
      ⌜match x with
      | interface.mk type_id v =>
          (type_id = intT.id → ∃ (v': w64), v = #v') ∧
          (type_id = stringT.id → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    @! unittest.multiTypeSwitch #x
  {{{ (x : w64), RET #x; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { destruct x; intuition. }
  iIntros (???). wp_auto.
  destruct ok; subst; wp_auto.
  { by iApply "HΦ". }
  unshelve wp_apply wp_interface_checked_type_assert; try tc_solve.
  { destruct x; intuition. }
  iIntros (???). wp_auto.
  destruct ok; subst; wp_auto; by iApply "HΦ".
Qed.

Lemma wp_testSwitchMultiple (x: w64) :
  {{{ is_pkg_init unittest }}}
    @! unittest.testSwitchMultiple #x
  {{{ (y:w64), RET #y;
      ⌜(uint.Z x = 10 → sint.Z y = 1) ∧
       (uint.Z x = 1 → sint.Z y = 1) ∧
       (uint.Z x = 0 → sint.Z y = 2) ∧
       (10 < uint.Z x → sint.Z y = 3)⌝
  }}}.
Proof.
  wp_start. wp_auto.
  wp_if_destruct.
  { by iApply "HΦ". }
  wp_if_destruct.
  { by iApply "HΦ". }
  wp_if_destruct.
  { by iApply "HΦ". }
  iApply "HΦ".
  word.
Qed.

Lemma wp_Point__IgnoreReceiver (p : unittest.Point.t) :
  {{{ is_pkg_init unittest }}}
    p @ unittest.Point.id @ "IgnoreReceiver" #()
  {{{ RET #"ok"; True }}}.
Proof.
  wp_start. by iApply "HΦ".
Qed.

Lemma wp_mapGetCall :
  {{{ is_pkg_init unittest }}}
    @! unittest.mapGetCall #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto. unshelve wp_apply (wp_map_make (K:=w64) (V:=func.t)); try tc_solve.
  { done. }
  iIntros "* Hm". wp_auto. wp_apply (wp_map_insert with "Hm") as "Hm".
  wp_apply (wp_map_get with "Hm") as "Hm".
  rewrite lookup_insert_eq. wp_auto. iApply "HΦ".
  done.
Qed.

Lemma wp_mapLiteralTest :
  {{{
        is_pkg_init unittest
  }}}
    @! unittest.mapLiteralTest #()
  {{{
        l, RET #l; l ↦$ {["a"%go := (W64 97); "b"%go := (W64 98); "c"%go := (W64 99)]}
  }}}.
Proof.
  wp_start. wp_auto.
  wp_apply wp_map_literal; first done.
  iIntros (?) "Hmap". wp_auto.
  iApply "HΦ". iFrame.
Qed.

Lemma wp_useNilField :
  {{{ is_pkg_init unittest }}}
    @! unittest.useNilField #()
  {{{ l, RET #l; l ↦ (unittest.containsPointer.mk null) }}}.
Proof.
  wp_start. wp_alloc x as "Hx". wp_auto. iApply "HΦ". iFrame.
Qed.

Lemma wp_testU32NewtypeLen :
  {{{ is_pkg_init unittest }}}
    @! unittest.testU32NewtypeLen #()
  {{{ RET #true; True }}}.
Proof.
  wp_start. wp_auto. wp_apply (wp_slice_make2 (V:=w8)) as "* [? ?]".
  { word. }
  iDestruct (own_slice_len with "[$]") as "%". rewrite bool_decide_true.
  2:{ revert H. len. }
  by iApply "HΦ".
Qed.

Lemma wp_signedMidpoint (x y: w64) :
  {{{ is_pkg_init unittest ∗ ⌜-2^63 < sint.Z x + sint.Z y < 2^63⌝ }}}
    @! unittest.signedMidpoint #x #y
  {{{ (z: w64), RET #z; ⌜sint.Z z = (sint.Z x + sint.Z y) `quot` 2⌝ }}}.
Proof.
  wp_start as "%H". wp_auto.
  iApply "HΦ".
  iPureIntro.
  rewrite word.signed_divs_nowrap; try word.
  change (sint.Z (W64 2)) with 2.
  rewrite word.signed_add.
  rewrite swrap_small; [ | word ].
  word.
Qed.

Lemma wp_useFloat :
  {{{ is_pkg_init unittest }}}
    @! unittest.useFloat #()
  {{{ (f : w64), RET #f; True }}}.
Proof.
  wp_start. wp_auto.
  repeat wp_apply wp_make_nondet_float64 as "% _".
  by iApply "HΦ".
Qed.

Lemma wp_intSliceLoop (s: slice.t) (xs: list w64) :
  {{{ is_pkg_init unittest ∗ s ↦* xs }}}
    @! unittest.intSliceLoop #s
  {{{ (z: w64), RET #z; s ↦* xs }}}.
Proof.
  wp_start as "Hs". wp_auto.
  iDestruct (own_slice_len with "Hs") as %Hs_len.
  iDestruct (own_slice_wf with "Hs") as %Hs_wf.
  iAssert (∃ (i sum: w64),
      "i" ∷ i_ptr ↦ i ∗
      "xs" ∷ xs_ptr ↦ s ∗
      "sum" ∷ sum_ptr ↦ sum ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len_f s)⌝
    )%I with "[$i $sum $xs]" as "IH".
  { word. }
  wp_for "IH".
  wp_if_destruct.
  - wp_pure; first word.
    list_elem xs (sint.nat i) as x_i.
    wp_apply (wp_load_slice_elem with "[$Hs]") as "Hs"; first word.
    { eauto. }
    wp_for_post.
    iFrame.
    word.
  - iApply "HΦ". iFrame.
Qed.

Lemma wp_pointerAny :
  {{{ is_pkg_init unittest }}}
    @! unittest.pointerAny #()
  {{{ (l:loc), RET #l; l ↦ interface.nil }}}.
Proof.
  wp_start.
  wp_auto.
  wp_alloc p as "Hp".
  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

Lemma wp_useRuneOps (r0: w32) :
  {{{ is_pkg_init unittest }}}
    @! unittest.useRuneOps #r0
  {{{ (r: w32), RET #r; ⌜r = W32 98⌝ }}}.
Proof.
  wp_start.
  wp_auto.
  iApply "HΦ".
  done.
Qed.

End proof.
