From Perennial.goose_lang.lib Require Import proph.proph.
From Perennial.goose_lang.trusted.github_com.mit_pdos.gokv Require Import trusted_proph.
From Perennial.program_proof Require Import grove_prelude.

Section proph.
Context `{!heapGS Σ}.

(** Computes a dbmap from its representation as a GooseLang value.
If decoding fails, returns some arbitrary nonsense value. *)
Local Fixpoint decode_bytes (v : val) : (list u8) :=
  match v with
  | (#(LitByte u), tail)%V => (decode_bytes tail) ++ [u]
  | _ => []
  end.

(* XXX: can't use typed proph_once here *)
Definition proph_once_bytes (p : proph_id) (b : list u8) : iProp Σ :=
  ∃ (pvs : list val), proph p pvs ∗
               ⌜match head pvs  with
                | Some v => decode_bytes v = b
                | None => True
                end⌝.

Global Instance proph_bytes_timeless p b :
  Timeless (proph_once_bytes p b).
Proof. apply _. Qed.

Lemma wp_NewProphActions :
  {{{ True }}}
    NewProph #()
  {{{ (p : proph_id) b, RET #p; proph_once_bytes p b }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_call.
  wp_apply wp_new_proph. iIntros (pvs p) "Hp".
  destruct pvs.
  { iApply ("HΦ" $! p).
    instantiate (1:=[]).
    iExists _; iFrame.
  }
  { iApply ("HΦ" $! p).
    iExists _; iFrame.
    done.
  }
Qed.

Local Lemma wp_BytesToVal sl b q :
  {{{ is_slice sl byteT q b }}}
    BytesToVal (slice_val sl)
  {{{ v, RET v; ⌜decode_bytes v = b⌝ ∗ is_slice sl byteT q b }}}.
Proof.
  iIntros (?) "Hsl HΦ". wp_call.
  wp_apply wp_alloc_untyped. { done. }
  iIntros (l) "Hl". wp_apply (wp_store with "Hl"). iIntros "Hl". wp_pures.
  iDestruct (is_slice_sz with "Hsl") as %Hsz.
  iDestruct (is_slice_split with "Hsl") as "[Hsl Hc]".
  wp_apply (wp_forSlice (λ i, ∃ b' v, ⌜decode_bytes v = b' ∧ b' = take (int.nat i) b⌝ ∗ l ↦ v)%I
    with "[] [Hl $Hsl]").
  2:{ iExists [], _. iFrame. iPureIntro. done. }
  { clear Φ. iIntros (i x Φ) "!# (I & %Hi & %Hx) HΦ".
    iDestruct "I" as (b' v) "([%Hdecode %Hb'] & Hl)".
    wp_pures.
    wp_apply (wp_load with "Hl"). iIntros "Hl".
    wp_apply (wp_store with "Hl"). iIntros "Hl".
    iApply "HΦ".
    iExists (b' ++ [x]), _. iFrame.
    iPureIntro. split.
    1:{ by rewrite -Hdecode. }
    { replace (int.nat (word.add i 1)) with (S (int.nat i)) by word.
      erewrite take_S_r.
      2:{ done. }
      by rewrite Hb'.
    }
  }
  iIntros "[(% & % & % & Hl) Hsl]".
  wp_pures. wp_apply (wp_load with "Hl"). iIntros "Hl".
  iApply "HΦ". iFrame. iPureIntro. destruct H as [? ?].
  subst. rewrite H0. rewrite firstn_all2; first done. word.
Qed.
End proph.

Global Typeclasses Opaque proph_once_bytes.
