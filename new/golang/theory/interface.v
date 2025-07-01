From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import struct typing proofmode globals.
From New.golang.defn Require Import interface globals.

Set Default Proof Using "Type".

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_interface_get (i : interface.t) (method : go_string) type_id v :
  PureWp (i = interface.mk type_id v)
    (interface.get #method #i)
    (#(method_callv type_id.1 type_id.2 method v)).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #i]to_val_unseal interface.get_unseal.
  wp_call_lc "?". rewrite H.
  wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_make (v : val) (pkg_name type_name : go_string) :
  PureWp (True) (interface.make (#pkg_name, #type_name)%V v) #(interface.mk (pkg_name, type_name) v).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #(_ : interface.t)]to_val_unseal interface.make_unseal.
  wp_call_lc "?". wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_eq_nil_r (i : interface.t) :
  PureWp (True) (interface.eq #i #interface.nil) #(bool_decide (i = interface.nil)).
Proof.
  pose proof wp_eq_val.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal.
  wp_call_lc "?".
  rewrite to_val_unseal.
  destruct i as [|].
  - wp_pures. wp_pures. rewrite bool_decide_false //. by iApply "Hwp".
  - wp_pures. rewrite bool_decide_true //. by iApply "Hwp".
Qed.

Global Instance wp_interface_eq_nil_l (i : interface.t) :
  PureWp (True) (interface.eq #interface.nil #i) #(bool_decide (interface.nil = i)).
Proof.
  pose proof wp_eq_val.
  iIntros (?????) "Hwp".
  rewrite to_val_unseal.
  wp_call_lc "?".
  rewrite to_val_unseal.
  destruct i as [|].
  - wp_pures. wp_pures. rewrite bool_decide_false //. by iApply "Hwp".
  - wp_pures. rewrite bool_decide_true //. by iApply "Hwp".
Qed.

Global Instance wp_type_id_eq (pkg1 type1 pkg2 type2: go_string) :
  PureWp (True) (interface.type_id_eq (#pkg1, #type1)%V (#pkg2, #type2)%V)
    #(bool_decide ((pkg1, type1) = (pkg2, type2))).
Proof.
  pose proof wp_eq_val.
  iIntros (?????) "Hwp".
  wp_call_lc "?".
  rewrite [in #pkg1]to_val_unseal.
  rewrite [in #pkg2]to_val_unseal.
  wp_pures.
  iDestruct ("Hwp" with "[$]") as "Hwp".
  destruct (decide (pkg1 = pkg2)); subst.
  {
    rewrite (bool_decide_eq_true_2 (LitV (LitString _) = _)) //.
    wp_pures.
    rewrite to_val_unseal.
    wp_pures.
    iExactEq "Hwp".
    rewrite to_val_unseal //=. repeat f_equal.
    destruct (decide (type1 = type2)); subst.
    - rewrite !bool_decide_eq_true_2 //.
    - rewrite !bool_decide_eq_false_2; congruence.
  }
  rewrite (bool_decide_eq_false_2 (LitV (LitString _) = _)); [ | congruence ].
  wp_pures.
  rewrite bool_decide_eq_false_2; [ | congruence ].
  iApply "Hwp".
Qed.

Lemma wp_interface_type_assert (i : interface.t) {V} `{!IntoVal V} pkg_name type_name (x: V) :
  {{{ ⌜i = interface.mk (pkg_name, type_name) #x⌝ }}}
    interface.type_assert #i (#pkg_name, #type_name)%V
  {{{ RET #x; True }}}.
Proof.
  iIntros (Φ) "-> HΦ".
  wp_call.
  rewrite {1}[in #(interface.mk _ _)]to_val_unseal /=.
  wp_pures.
  rewrite bool_decide_eq_true_2 //.
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_interface_try_type_coerce (i : interface.t)
  (pkg_name type_name: go_string) :
  {{{ True }}}
    interface.try_type_coerce #i (#pkg_name, #type_name)%V
  {{{ (y: val) (ok: bool), RET (y, #ok);
      ⌜if ok then i = interface.mk (pkg_name, type_name) y
      else match i with
      | interface.mk type_id' _ => (pkg_name, type_name) ≠ type_id'
      | interface.nil => True
      end⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  destruct i as [[pkg_name' type_id'] y'|].
  - rewrite {1}[in #(interface.mk _ _)]to_val_unseal /=.
    wp_pures.
    match goal with
    | |- context[bool_decide ?P] => destruct (bool_decide_reflect P)
    end; wp_pures.
    {
      match goal with
      | H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
      end.
      iApply "HΦ".
      iPureIntro.
      eauto.
    }
    iApply "HΦ".
    iPureIntro.
    auto.
  - rewrite {1}[in #(interface.nil)]to_val_unseal /=.
    wp_pures.
    iApply "HΦ".
    done.
Qed.

Lemma wp_interface_checked_type_assert (i : interface.t) {V} `{!IntoVal V} t `{!IntoValTyped V t}
  (pkg_name type_name: go_string) :
  {{{ ⌜match i with
      | interface.mk type_id' v0 =>
          (* a technical side condition is required to show that if i has the
          correct type identity (which is a string), then the value it holds has
          the expected type V *)
          (pkg_name, type_name) = type_id' →
          ∃ (v: V), v0 = #v
      |  interface.nil => True
      end ⌝ }}}
    interface.checked_type_assert #t #i (#pkg_name, #type_name)%V
  {{{ (y: V) (ok: bool), RET (#y, #ok);
      ⌜if ok then i = interface.mk (pkg_name, type_name) #y
      else match i with
      | interface.mk type_id' _ => (pkg_name, type_name) ≠ type_id'
      | interface.nil => True
      end ∧ y = default_val V⌝
  }}}.
Proof.
  iIntros (Φ) "%Htype HΦ".
  wp_call.
  wp_apply wp_interface_try_type_coerce.
  iIntros (y ok) "%Hpost".
  destruct ok; subst; wp_pures.
  - destruct Htype as [v ?]; subst; auto.
    by iApply "HΦ".
  - rewrite -default_val_eq_zero_val.
    iApply "HΦ".
    iPureIntro; auto.
Qed.

#[export] Typeclasses Opaque interface.type_assert interface.checked_type_assert.
#[global] Opaque interface.type_assert interface.checked_type_assert.

End wps.
