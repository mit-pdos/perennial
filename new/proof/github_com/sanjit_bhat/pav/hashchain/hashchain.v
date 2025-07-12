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

End proof.
End hashchain.
