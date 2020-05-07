From Perennial.goose_lang Require Import lifting.

Section goose_lang.
Context `{ffi_semantics: ext_semantics}.
Context `{!ffi_interp ffi}.

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             @P hG').
*)

Definition post_crash `{hG: !heapG Σ} (P: forall hG', iProp Σ) : iProp Σ :=
  (∀ σ σ' hG', ffi_crash_rel Σ (heapG_ffiG (hG := hG)) σ (heapG_ffiG (hG := hG')) σ' -∗
                             (P hG')).

(*
Definition post_crash `{hG: !heapG Σ} (P: forall {hG': heapG Σ}, iProp Σ) : iProp Σ :=
  (∀ σ σ' new, ffi_crash_rel Σ hG σ (ffi_update Σ hG new) σ' -∗
                             @P (ffi_update Σ hG new)).
*)

Section post_crash_prop.
Context `{!heapG Σ}.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.
Implicit Types v : val.

Existing Instances ffi_crash_rel_pers.

Lemma post_crash_prop_sep P Q:
  post_crash P -∗ post_crash Q -∗ post_crash (λ hG, P hG ∗ Q hG).
Proof.
  iIntros "HP HQ". iIntros (???) "#Hrel".
  iDestruct ("HP" with "[$]") as "$".
  iDestruct ("HQ" with "[$]") as "$".
Qed.

End post_crash_prop.
End goose_lang.
