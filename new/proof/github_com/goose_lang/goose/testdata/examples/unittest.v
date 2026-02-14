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

Section wps.
Context `{!heapGS Σ}.
Context {sem : go.Semantics} {package_sem : unittest.Assumptions}.
Local Set Default Proof Using "All".

#[global] Instance : IsPkgInit (iProp Σ) unittest := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) unittest := build_get_is_pkg_init_wf.

Lemma wp_BasicNamedReturn :
  {{{ is_pkg_init unittest }}}
    @! unittest.BasicNamedReturn #()
  {{{ RET #"ok"; True }}}.
Proof.
  wp_start.
  wp_auto. by iApply "HΦ".
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
  {{{ is_pkg_init unittest ∗ ⌜ x = interface.mk_ok go.int #v ⌝ }}}
    @! unittest.typeAssertInt #x
  {{{ RET #v; True }}}.
Proof.
  wp_start as "->". wp_auto.
  rewrite -> decide_True; last done.
  wp_end.
Qed.

Lemma wp_wrapUnwrapInt :
  {{{ is_pkg_init unittest }}}
    @! unittest.wrapUnwrapInt #()
  {{{ RET #(W64 1); True }}}.
Proof.
  wp_start as "_".
  wp_apply wp_typeAssertInt.
  { done. }
  wp_end.
Qed.

Lemma wp_checkedTypeAssert (x: interface.t) :
  {{{ is_pkg_init unittest ∗
        ⌜match x with
        | interface.ok i =>
            if decide (i.(interface.ty) = go.uint64) then
              ∃ (v: w64), i.(interface.v) = #v
            else True
        |  interface.nil => True
        end⌝
  }}}
    @! unittest.checkedTypeAssert #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto. destruct x.
  - destruct decide in *; subst.
    + destruct Htype as [? ->]. wp_auto. rewrite bool_decide_true; last done. wp_auto. wp_end.
    + wp_auto. rewrite bool_decide_false; last done. wp_auto. wp_end.
  - wp_auto. wp_end.
Qed.

Lemma wp_basicTypeSwitch (x: interface.t) :
  {{{ is_pkg_init unittest ∗
      ⌜ (match x with
         | interface.ok (interface.mk ty v) =>
             (ty = go.int → ∃ (v': w64), v = #v') ∧
             (ty = go.string → ∃ (v': go_string), v = #v')
         | _ => True
         end) ⌝
  }}}
    @! unittest.basicTypeSwitch #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  destruct x as [[]|].
  - simpl. rewrite bool_decide_decide. destruct decide; subst; wp_auto.
    { wp_end. }
    rewrite bool_decide_decide. destruct decide; subst; wp_auto; wp_end.
  - wp_auto. wp_end.
Qed.

Lemma wp_fancyTypeSwitch (x: interface.t) :
  {{{ is_pkg_init unittest ∗
      ⌜match x with
      | interface.ok (interface.mk ty v) =>
          (ty = go.int → ∃ (v': w64), v = #v') ∧
          (ty = go.string → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    @! unittest.fancyTypeSwitch #x
  {{{ (y: w64), RET #y; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  destruct x as [[]|].
  - simpl. rewrite bool_decide_decide. destruct decide.
    + wp_auto. destruct Htype as [Htype _]. destruct (Htype ltac:(done)) as [? ?]. subst.
      wp_auto. wp_end.
    + wp_auto. destruct Htype as [_ Htype].
      rewrite bool_decide_decide. destruct decide.
      * destruct (Htype ltac:(done)) as [? ?]. subst.
        wp_auto. wp_end.
      * wp_auto. wp_end.
  - wp_auto. wp_end.
Qed.

Lemma wp_multiTypeSwitch x :
  {{{ is_pkg_init unittest ∗
      ⌜match x with
      | interface.ok (interface.mk ty v) =>
          (ty = go.int → ∃ (v': w64), v = #v') ∧
          (ty = go.string → ∃ (v': go_string), v = #v')
      | _ => True
      end⌝
  }}}
    @! unittest.multiTypeSwitch #x
  {{{ (x : w64), RET #x; True }}}.
Proof.
  wp_start as "%Htype". wp_auto.
  destruct x as [[]|].
  - rewrite bool_decide_decide. destruct decide; wp_auto.
    + wp_end.
    + rewrite bool_decide_decide. destruct decide; wp_auto; wp_end.
  - wp_auto. wp_end.
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
    p @! unittest.Point @! "IgnoreReceiver" #()
  {{{ RET #"ok"; True }}}.
Proof.
  wp_start. wp_end.
Qed.

Lemma wp_mapGetCall :
  {{{ is_pkg_init unittest }}}
    @! unittest.mapGetCall #()
  {{{ RET #(); True }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_map_make1 as "* Hm".
  wp_apply (wp_map_insert with "Hm") as "Hm".
  wp_bind. wp_bind (map.lookup1 _ _ _ _). wp_apply (wp_map_lookup1 with "Hm") as "Hm".
  rewrite lookup_insert_eq. wp_auto. wp_end.
Qed.

Lemma wp_mapLiteralTest :
  {{{
        is_pkg_init unittest
  }}}
    @! unittest.mapLiteralTest #()
  {{{
        l, RET #l; l ↦$ {["c"%go := (W64 99); "b"%go := (W64 98); "a"%go := (W64 97)]}
  }}}.
Proof.
  wp_start. wp_auto. wp_apply wp_map_make1 as "% Hm".
  repeat wp_apply (wp_map_insert with "Hm") as "Hm".
  rewrite -insert_empty. wp_end.
Qed.

Lemma wp_testConversionLiteral :
  {{{ is_pkg_init unittest }}}
    @! unittest.testConversionLiteral #()
  {{{ RET #true; True }}}.
Proof.
  wp_start.
  wp_auto.
  wp_apply wp_map_make1 as "* Hm".
  wp_apply (wp_map_insert with "Hm") as "Hm".
  { constructor. iIntros. wp_auto. done. }
  wp_apply (wp_map_insert with "Hm") as "Hm".
  { constructor. iIntros. wp_auto. done. }
  wp_apply (wp_map_insert with "Hm") as "Hm".
  { constructor. iIntros "* HΦ". wp_auto. rewrite -> decide_True; last done.
    wp_auto. wp_end. }
  wp_apply (wp_map_lookup1 with "Hm") as "Hm".
  { constructor. iIntros "* HΦ". wp_auto. rewrite -> decide_True; last done.
    wp_auto. wp_end. }
  rewrite insert_empty.
  rewrite lookup_insert_eq /=.
  wp_apply (wp_map_lookup1 with "Hm") as "Hm".
  { constructor. iIntros. wp_auto. done. }
  rewrite lookup_insert_ne; last done. rewrite lookup_insert_eq. simpl.
  rewrite -> decide_True; last done. wp_auto. wp_end.
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
  wp_start. wp_auto. wp_apply wp_slice_make2 as "* [? ?]".
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
  wp_start. wp_auto. wp_end.
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
      "%Hi" ∷ ⌜0 ≤ sint.Z i ≤ sint.Z (slice.len s)⌝
    )%I with "[$i $sum $xs]" as "IH".
  { word. }
  wp_for "IH".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat i) as x_i.
    wp_apply (wp_load_slice_index with "[$Hs]") as "Hs"; first word.
    { eauto. }
    wp_for_post.
    iFrame.
    word.
  - iApply "HΦ". iFrame.
Qed.

Lemma wp_useEmbeddedMethod (d : unittest.embedD.t) (b : unittest.embedB.t) :
  {{{ is_pkg_init unittest ∗ d.(unittest.embedD.embedC').(unittest.embedC.embedB') ↦ b }}}
    @! unittest.useEmbeddedMethod #d
  {{{ RET #true; True }}}.
Proof.
  wp_start. wp_auto.
  wp_method_call. wp_auto.
  wp_method_call. wp_auto.
  wp_method_call. wp_auto.
  wp_method_call. repeat wp_call. wp_auto.
  wp_method_call. repeat wp_call. wp_auto.
  rewrite bool_decide_true //.  wp_end.
Qed.

Lemma wp_pointerAny :
  {{{ is_pkg_init unittest }}}
    @! unittest.pointerAny #()
  {{{ (l:loc), RET #l; l ↦ interface.nil }}}.
Proof.
  wp_start.
  wp_alloc p as "Hp".
  wp_auto. wp_end.
Qed.

Lemma wp_useRuneOps (r0: w32) :
  {{{ is_pkg_init unittest }}}
    @! unittest.useRuneOps #r0
  {{{ (r: w32), RET #r; ⌜r = W32 98⌝ }}}.
Proof.
  wp_start.
  wp_auto.
  wp_end.
Qed.

Lemma wp_ifJoinDemo (arg1 arg2: bool) :
  {{{ is_pkg_init unittest }}}
    @! unittest.ifJoinDemo #arg1 #arg2
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  wp_auto.
  wp_apply wp_slice_literal as "% _"; [iIntros; by wp_auto | ].
  iPersist "arg2".
  wp_if_join (λ v, ⌜v = execute_val⌝ ∗
                   ∃ (sl: slice.t) (xs: list w64),
                     "arr" ∷ arr_ptr ↦ sl ∗
                     "Hsl" ∷ sl ↦* xs ∗
                     "Hsl_cap" ∷ own_slice_cap w64 sl (DfracOwn 1))%I
         with "[arr]".
  { wp_apply wp_slice_literal as "% Hsl"; first (iIntros; by wp_auto).
    wp_apply (wp_slice_append with "[Hsl]") as "%sl1 (Hsl & Hsl_cap & _)".
    {
      iFrame. simpl in *.
      iDestruct (own_slice_empty) as "$"; simpl; [by len..|].
      iDestruct (own_slice_cap_empty) as "$"; simpl; try by len.
    }
    iSplit; [ done | ].
    iFrame. }
  { iSplit; [ done | ].
    iFrame.
    iExists [].
    iDestruct (own_slice_empty) as "$"; simpl; [by len..|].
    iDestruct (own_slice_cap_empty) as "$"; simpl; by len. }
  iIntros (v) "[% @]". subst.
  wp_auto. wp_if_destruct.
  - wp_apply wp_slice_literal as "% Hsl2"; first (iIntros; by wp_auto).
    wp_apply (wp_slice_append with "[$Hsl $Hsl_cap $Hsl2]") as "%sl1 (Hsl & Hsl_cap & _)".
    wp_end.
  - wp_end.
Qed.

Lemma wp_repeatLocalVars :
  {{{ is_pkg_init unittest }}}
    @! unittest.repeatLocalVars #()
  {{{ RET #(); True }}}.
Proof.
  wp_start.
  wp_auto.
  wp_end.
Qed.

End wps.
