From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import struct typing proofmode globals.
From New.golang.defn Require Import interface globals.

Set Default Proof Using "Type".

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_interface_get (i : interface.t) (method : go_string) pkg_name type_name v :
  PureWp (i = interface.mk pkg_name type_name v)
    (interface.get #method #i)
    (#(method_callv pkg_name type_name method v)).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #i]to_val_unseal interface.get_unseal.
  wp_call_lc "?". rewrite H.
  wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_make (v : val) pkg_name type_name :
  PureWp (True) (interface.make #pkg_name #type_name v) #(interface.mk pkg_name type_name v).
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

Lemma wp_interface_type_assert (i : interface.t) {V} `{!IntoVal V} pkg_name type_name (x: V) :
  {{{ ⌜i = interface.mk pkg_name type_name #x⌝ }}}
    interface.type_assert #i #pkg_name #type_name
  {{{ RET #x; True }}}.
Proof.
  iIntros (Φ) "-> HΦ".
  wp_call.
  rewrite {1}[in #(interface.mk _ _ _)]to_val_unseal /=.
  wp_pures.
  rewrite bool_decide_eq_true_2 //.
  wp_pures.
  rewrite bool_decide_eq_true_2 //.
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma wp_interface_checked_type_assert (i : interface.t) {V} `{!IntoVal V} t `{!IntoValTyped V t}
  pkg_name type_name :
  {{{ ⌜match i with
      | interface.mk pkg_name' type_name' v0 =>
          (* a technical side condition is required to show that if i has the
          correct type identity (which is a string), then the value it holds has
          the expected type V *)
          (pkg_name', type_name') = (pkg_name, type_name) →
          ∃ (v: V), v0 = #v
      |  interface.nil => True
      end ⌝ }}}
    interface.checked_type_assert #t #i #pkg_name #type_name
  {{{ (y: V) (ok: bool), RET (#y, #ok);
      ⌜if ok then i = interface.mk pkg_name type_name #y
      else match i with
      | interface.mk pkg_name' type_name' _ => (pkg_name', type_name') ≠ (pkg_name, type_name)
      | interface.nil => True
      end ∧ y = default_val V⌝
  }}}.
Proof.
  iIntros (Φ) "%Htype HΦ".
  wp_call.
  destruct i as [pkg_name' type_name' y'|].
  - rewrite {1}[in #(interface.mk _ _ _)]to_val_unseal /=.
    wp_pures.
    destruct (bool_decide_reflect (pkg_name' = pkg_name)); subst; wp_pures.
    {
      destruct (bool_decide_reflect (type_name' = type_name)); subst; wp_pures.
      { destruct Htype as [v ->]; [ done | ].
        iApply "HΦ".
        done. }
      rewrite -default_val_eq_zero_val.
      iApply "HΦ".
      iPureIntro.
      split; congruence.
    }
    rewrite -default_val_eq_zero_val.
    iApply "HΦ".
    iPureIntro.
    split; congruence.
  - rewrite {1}[in #(interface.nil)]to_val_unseal /=.
    wp_pures.
    rewrite -default_val_eq_zero_val.
    iApply "HΦ".
    done.
Qed.

End wps.
