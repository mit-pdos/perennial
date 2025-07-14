From New.proof.github_com.sanjit_bhat.pav Require Import prelude.
From New.generatedproof.github_com.sanjit_bhat.pav Require Import hashchain.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import cryptoffi cryptoutil.
From New.proof.github_com.goose_lang Require Import std.

Module hashchain.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !goGlobalsGS Σ}.
Context `{!cryptoffi.GlobalAddrs, !cryptoutil.GlobalAddrs, !std.GlobalAddrs}.

#[global]
Program Instance is_pkg_init_hashchain : IsPkgInit hashchain := ltac2:(build_pkg_init ()).
#[global] Opaque is_pkg_init_hashchain.
#[local] Transparent is_pkg_init_hashchain.

Local Fixpoint is_chain_aux (boot : list w8) (l : list $ list w8) (h : list w8) : iProp Σ :=
  match l with
  | [] =>
    "->" ∷ ⌜ boot = h ⌝ ∗
    "%Hlen" ∷ ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝
  | x :: l' =>
    ∃ h',
    "#Hrecur" ∷ is_chain_aux boot l' h' ∗
    "#His_hash" ∷ cryptoffi.is_hash (h' ++ x) h
  end.
#[global] Opaque is_chain_aux.
#[local] Transparent is_chain_aux.

#[global]
Instance is_chain_aux_pers b l h : Persistent (is_chain_aux b l h).
Proof. revert h. induction l; apply _. Qed.

Lemma is_chain_aux_len b l h :
  is_chain_aux b l h -∗
  ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝.
Proof.
  destruct l; simpl; iNamed 1.
  - done.
  - by iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
Qed.

(* a full chain. *)
Definition is_chain l h : iProp Σ :=
  ∃ he,
  "#He" ∷ cryptoffi.is_hash [] he ∗
  "#His_chain" ∷ is_chain_aux he l h.

(* a bootstrapped chain. *)
Definition is_chain_boot l h : iProp Σ :=
  ∃ boot,
  "#His_chain" ∷ is_chain_aux boot l h.

(* we can't prove inj bw two bootstrapped chains bc of cycles.
i.e., when Hash(boot, v) = boot, which makes
Chain(boot, []) look indistinguishable from Chain(boot, [v...]).
one fix is to track a max list limit (XXX: pin down core logic).
this takes a different approach, stating inj with a "complete"
chain, which prevents cycles by starting with an empty pre-img. *)
Lemma is_chain_inj l0 l1 h :
  is_chain l0 h -∗
  is_chain_boot l1 h -∗
  ⌜ l1 `prefix_of` l0 ⌝.
Proof.
  iInduction l0 as [|??] forall (l1 h); destruct l1;
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1"; [done|..]; simpl;
    iNamedSuffix "His_chain0" "0";
    iNamedSuffix "His_chain1" "1".
  - iDestruct (is_chain_aux_len with "Hrecur1") as %?.
    iDestruct (cryptoffi.is_hash_inj with "He0 His_hash1") as %Heq.
    apply (f_equal length) in Heq.
    autorewrite with len in *.
    word.
  - iPureIntro. apply prefix_nil.
  - iDestruct (is_chain_aux_len with "Hrecur0") as %?.
    iDestruct (is_chain_aux_len with "Hrecur1") as %?.
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %Heq.
    opose proof (app_inj_1 _ _ _ _ _ Heq) as [-> ->]; [lia|].
    iDestruct ("IHl0" with "[$He0 $Hrecur0] [$Hrecur1]") as %?.
    iPureIntro. by apply prefix_cons.
Qed.

Local Lemma is_chain_inj_aux l0 l1 h :
  is_chain l0 h -∗
  is_chain l1 h -∗
  ⌜ l0 = l1 ⌝.
Proof.
  iNamedSuffix 1 "0"; iNamedSuffix 1 "1".
  iDestruct (is_chain_inj with "[$He0 $His_chain0] [$His_chain1]") as %?.
  iDestruct (is_chain_inj with "[$He1 $His_chain1] [$His_chain0]") as %?.
  iPureIntro.
  apply prefix_length_eq; [done|].
  by apply prefix_length.
Qed.

Lemma wp_GetEmptyLink :
  {{{ is_pkg_init hashchain }}}
  hashchain @ "GetEmptyLink" #()
  {{{
    sl h, RET #sl;
    "Hsl_hash" ∷ sl ↦* h ∗
    "#His_chain" ∷ is_chain [] h
  }}}.
Proof using H.
  wp_start.
  wp_apply (cryptoutil.wp_Hash _ inhabitant) as "* @".
  { iApply own_slice_nil. }
  iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
  iApply "HΦ". by iFrame "∗#".
Qed.

Lemma wp_GetNextLink sl_prevLink d0 prevLink sl_nextVal d1 nextVal :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal
  }}}
  hashchain @ "GetNextLink" #sl_prevLink #sl_nextVal
  {{{
    sl h, RET #sl;
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "Hsl_nextVal" ∷ sl_nextVal ↦*{d1} nextVal ∗
    "Hsl_hash" ∷ sl ↦* h ∗
    "#His_hash" ∷ cryptoffi.is_hash (prevLink ++ nextVal) h
  }}}.
Proof using H.
  wp_start. iNamed "Hpre".
  wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply (cryptoffi.wp_Hasher__Write with "[$Hown_hr $Hsl_prevLink]").
  iNamedSuffix 1 "0". wp_auto.
  wp_apply (cryptoffi.wp_Hasher__Write with "[$Hown_hr0 $Hsl_nextVal]").
  iNamedSuffix 1 "1". wp_auto.
  wp_apply (cryptoffi.wp_Hasher__Sum with "[$Hown_hr1]").
  { iApply own_slice_nil. }
  iIntros "*". iNamed 1.
  wp_auto.
  iApply "HΦ". iFrame "∗#".
Qed.

Definition wish_Verify (proof : list w8) new_vals : iProp Σ :=
  "%Hlen_vals" ∷ ([∗ list] v ∈ new_vals,
    ⌜ Z.of_nat $ length v = cryptoffi.hash_len ⌝) ∗
  "%Henc_vals" ∷ ⌜ proof = concat new_vals ⌝.

Lemma wp_Verify :
  {{{
    is_pkg_init hashchain ∗
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof ∗
    "#His_chain" ∷ is_chain_boot l prevLink
  }}}
  hashchain @ "Verify" #sl_prevLink #sl_proof
  {{{
    extLen sl_newVal newVal sl_newLink newLink err,
    RET (#extLen, #sl_newVal, #sl_newLink, #err);
    "Hsl_prevLink" ∷ sl_prevLink ↦*{d0} prevLink ∗
    "#Hsl_newVal" ∷ sl_newVal ↦*□ newVal ∗
    "Hsl_newLink" ∷ sl_newLink ↦* newLink ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ ∃ new_vals, wish_Verify proof new_vals) ∗
    "Herr" ∷ (∀ new_vals, wish_Verify proof new_vals -∗
      "->" ∷ ⌜ newVal = default [] (last new_vals) ⌝ ∗
      "#His_chain" ∷ is_chain_boot (l ++ new_vals) newLink)
  }}}.
Proof. Admitted.

End proof.
End hashchain.
