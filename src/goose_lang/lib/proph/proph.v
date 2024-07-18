From Perennial.goose_lang Require Import notation typing.
From Perennial.goose_lang Require Import proofmode lifting lib.into_val.
From Perennial.goose_lang.lib Require Export proph.impl.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context {ext_ty: ext_types ext}.

(** list-based prophecy variables (the most general underlying primitive) *)

Theorem wp_NewProph_list :
  {{{ True }}}
    NewProph #()
  {{{ (p : proph_id) pvs, RET #p; proph p pvs }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_rec.
  wp_apply wp_new_proph. iIntros (pvs v). by iApply "HΦ".
Qed.

Theorem wp_ResolveProph_list E (p : proph_id) pvs v :
  {{{ proph p pvs }}}
    ResolveProph (#p) (Val v) @ E
  {{{ pvs', RET (LitV LitUnit); ⌜pvs = v::pvs'⌝ ∗ proph p pvs' }}}.
Proof.
  iIntros (Φ) "Hp HΦ". wp_rec.
  wp_apply (wp_resolve_proph with "Hp"). auto.
Qed.

(** typed assign-once prophecy variables *)
Section once.
  Context `{!IntoVal T}.

  Definition proph_once (p : proph_id) (x : T) : iProp Σ :=
    ∃ pvs : list val, proph p pvs ∗
               ⌜match v ← head pvs; from_val v with
                | Some x' => x=x'
                | None => True
                end⌝.

  Theorem wp_NewProph_once :
    {{{ True }}}
      NewProph #()
    {{{ (p : proph_id) (x : T), RET #p; proph_once p x }}}.
  Proof.
    iIntros (Φ) "_ HΦ". iApply wp_NewProph_list; first done.
    iIntros "!> %p %pvs Hp".
    iApply ("HΦ" $! p (default (IntoVal_def T) (v ← head pvs; from_val v))).
    iExists pvs. iFrame. iPureIntro.
    destruct (head pvs); simpl; last done.
    destruct (from_val v); done.
  Qed.

  Theorem wp_ResolveProph_once (p : proph_id) (x y : T) v :
    from_val v = Some y →
    {{{ proph_once p x }}}
      ResolveProph (#p) (Val v)
    {{{ RET (LitV LitUnit); ⌜x = y⌝ }}}.
  Proof.
    iIntros (Hv Φ) "(%pvs & Hp & %Hpvs) HΦ".
    iApply (wp_ResolveProph_list with "Hp").
    iIntros "!> %pvs' [%Hpvs' _]". iApply "HΦ". iPureIntro.
    subst pvs. simpl in Hpvs.
    rewrite Hv in Hpvs. done.
  Qed.

End once.

End goose_lang.
