From Perennial.goose_lang Require Import notation.
From New.golang.theory Require Import typing proofmode pkg.
From New.golang.defn Require Import interface.

Set Default Proof Using "Type".

Section wps.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Global Instance wp_interface_get (i : interface.t) (method : go_string) type_id v :
  PureWp (i = interface.mk type_id v)
    (interface.get #method #i)
    (#(method_callv type_id method v)).
Proof.
  iIntros (?????) "Hwp".
  rewrite [in #i]to_val_unseal interface.get_unseal.
  wp_call_lc "?". rewrite H.
  wp_pures. by iApply "Hwp".
Qed.

Global Instance wp_interface_make (v : val) (type_id : go_string) :
  PureWp (True) (interface.make #type_id v) #(interface.mk type_id v).
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

Lemma wp_interface_type_assert (i : interface.t) {V} `{!IntoVal V} type_id (x: V) :
  {{{ ⌜i = interface.mk type_id #x⌝ }}}
    interface.type_assert #i #type_id%V
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

Lemma wp_interface_try_type_coerce (i : interface.t) (type_id : go_string) :
  {{{ True }}}
    interface.try_type_coerce #i #type_id
  {{{ (y: val) (ok: bool), RET (y, #ok);
      ⌜if ok then i = interface.mk type_id y
      else match i with
      | interface.mk type_id' _ => type_id ≠ type_id'
      | interface.nil => True
      end⌝
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_call.
  destruct i as [type_id' y'|].
  - rewrite {1}[in #(interface.mk _ _)]to_val_unseal /=.
    wp_pures. case_bool_decide; wp_pures.
    { subst. by iApply "HΦ". }
    by iApply "HΦ".
  - rewrite {1}[in #(interface.nil)]to_val_unseal /=.
    wp_pures.
    iApply "HΦ".
    done.
Qed.

Lemma wp_interface_checked_type_assert (i : interface.t) {V} `{!IntoVal V} t `{!IntoValTyped V t}
  (type_id : go_string) :
  {{{ ⌜match i with
      | interface.mk type_id' v0 =>
          (* a technical side condition is required to show that if i has the
          correct type identity (which is a string), then the value it holds has
          the expected type V *)
          type_id = type_id' →
          ∃ (v: V), v0 = #v
      |  interface.nil => True
      end ⌝ }}}
    interface.checked_type_assert t #i #type_id
  {{{ (y: V) (ok: bool), RET (#y, #ok);
      ⌜if ok then i = interface.mk type_id #y
      else match i with
      | interface.mk type_id' _ => type_id ≠ type_id'
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
  - iApply "HΦ". iPureIntro; auto.
Qed.

#[export] Typeclasses Opaque interface.type_assert interface.checked_type_assert.
#[global] Opaque interface.type_assert interface.checked_type_assert.

End wps.
