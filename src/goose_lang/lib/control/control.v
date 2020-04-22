From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import proofmode.
From Perennial.goose_lang Require Import lang.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.

(** A proof principle for if e { do_stuff(); } where do_stuff() is optional and
does something irrelevant to the proof using resources R. Allows to re-use the
proof for both branches, carrying on with resources R. *)
Theorem wp_If_optional stk E (R: iProp Σ) (b: bool) e :
  (∀ (Φ': val → iProp Σ), R -∗ ▷ (R -∗ Φ' #()) -∗ WP e @ stk; E {{ Φ' }}) -∗
  ∀ Φ, R -∗ ▷ (R -∗ Φ #()) -∗ WP If #b e #() @ stk; E {{ Φ }}.
Proof.
  iIntros "Hwp" (Φ) "HR HΦ".
  wp_if_destruct.
  - wp_apply ("Hwp" with "[$HR]").
    iFrame.
  - iApply ("HΦ" with "HR").
Qed.

End goose_lang.
