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

Section proof.
Context `{hG: !heapGS Σ} `{!goGlobalsGS Σ} `{unittest.GlobalAddrs}.

#[global] Program Instance : IsPkgInit unittest := ltac2:(build_pkg_init ()).

Lemma wp_BasicNamedReturn :
  {{{ is_pkg_init unittest }}}
    unittest@"BasicNamedReturn" #()
  {{{ RET #"ok"; True }}}.
Proof.
  wp_start. wp_auto. by iApply "HΦ".
Qed.

Lemma wp_VoidButEndsWithReturn :
  {{{ is_pkg_init unittest }}}
    unittest@"VoidButEndsWithReturn" #()
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  wp_apply wp_BasicNamedReturn.
  by iApply "HΦ".
Qed.

Lemma wp_VoidImplicitReturnInBranch (b: bool) :
  {{{ is_pkg_init unittest }}}
    unittest@"VoidImplicitReturnInBranch" #b
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto.
  destruct b; wp_auto.
  - by iApply "HΦ".
  - wp_apply wp_BasicNamedReturn.
    by iApply "HΦ".
Qed.

Lemma wp_typeAssertInt (x: interface.t) (v: w64) :
  {{{ is_pkg_init unittest ∗ ⌜x = interface.mk (""%go, "int"%go) #v⌝ }}}
    unittest@"typeAssertInt" #x
  {{{ RET #v; True }}}.
Proof.
  wp_start as "->". wp_auto.
  wp_apply wp_interface_type_assert.
  { done. }
  by iApply "HΦ".
Qed.

Lemma wp_wrapUnwrapInt :
  {{{ is_pkg_init unittest }}}
    unittest@"wrapUnwrapInt" #()
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
            (""%go, "uint64"%go) = type_id' →
            ∃ (v: w64), v0 = #v
        |  interface.nil => True
        end⌝
  }}}
    unittest@"checkedTypeAssert" #x
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
          (type_id = (""%go, "int"%go) → ∃ (v': w64), v = #v') ∧
          (type_id = (""%go, "string"%go) → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    unittest@"basicTypeSwitch" #x
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
          (type_id = (""%go, "int"%go) → ∃ (v': w64), v = #v') ∧
          (type_id = (""%go, "string"%go) → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    unittest@"fancyTypeSwitch" #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  wp_apply wp_interface_checked_type_assert.
  {
    destruct x; intuition.
  }
  iIntros (???); wp_auto.
  destruct ok; subst; wp_auto.
  { by iApply "HΦ". }
  wp_apply wp_interface_checked_type_assert.
  {
    destruct x; intuition.
  }
  iIntros (???); wp_auto.
  wp_alloc y' as "y'".
  wp_auto.
  destruct ok; subst; wp_auto.
  { by iApply "HΦ". }
  by iApply "HΦ".

  Unshelve.
  all: apply _.
Qed.

Lemma wp_testSwitchMultiple (x: w64) :
  {{{ is_pkg_init unittest }}}
    unittest@"testSwitchMultiple" #x
  {{{ (y:w64), RET #y;
      ⌜(uint.Z x = 10 → sint.Z y = 1) ∧
       (uint.Z x = 1 → sint.Z y = 1) ∧
       (uint.Z x = 0 → sint.Z y = 2) ∧
       (10 < uint.Z x → sint.Z y = 3)⌝
  }}}.
Proof.
  wp_start. wp_auto.
  wp_if_destruct; try wp_auto.
  { by iApply "HΦ". }
  wp_if_destruct; try wp_auto.
  { by iApply "HΦ". }
  wp_if_destruct; try wp_auto.
  { by iApply "HΦ". }
  iApply "HΦ".
  word.
Qed.

End proof.
