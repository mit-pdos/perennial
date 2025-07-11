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

Local Fixpoint is_chain (l : list $ list w8) (h : list w8) : iProp Σ :=
  match l with
  | [] =>
    "#His_hash" ∷ cryptoffi.is_hash [] h
  | x :: l' =>
    ∃ h',
    "#Hrecur" ∷ is_chain l' h' ∗
    "#His_hash" ∷ cryptoffi.is_hash (h' ++ x) h
  end.

Local Instance is_chain_pers l h : Persistent (is_chain l h).
Proof. Admitted.

Lemma is_chain_len l h :
  is_chain l h -∗
  ⌜ Z.of_nat $ length h = cryptoffi.hash_len ⌝.
Proof.
  destruct l; simpl; iNamed 1;
    by iDestruct (cryptoffi.is_hash_len with "His_hash") as %?.
Qed.

Lemma is_chain_inj l0 l1 h : is_chain l0 h -∗ is_chain l1 h -∗ ⌜ l0 = l1 ⌝.
Proof.
  iInduction l0 as [|??] forall (l1 h); destruct l1; simpl;
    iNamedSuffix 1 "0"; iNamedSuffix 1 "1"; try done;
    iDestruct (cryptoffi.is_hash_inj with "His_hash0 His_hash1") as %Heq.
  - iDestruct (is_chain_len with "Hrecur1") as %?.
    apply (f_equal length) in Heq.
    (* TODO: len tactic should maybe rewrite in *. *)
    autorewrite with len in *.
    word.
  - iDestruct (is_chain_len with "Hrecur0") as %?.
    apply (f_equal length) in Heq.
    autorewrite with len in *.
    word.
  - iDestruct (is_chain_len with "Hrecur0") as %?.
    iDestruct (is_chain_len with "Hrecur1") as %?.
    opose proof (app_inj_1 _ _ _ _ _ Heq) as [-> ->]; [lia|].
    by iDestruct ("IHl0" with "Hrecur0 Hrecur1") as %->.
Qed.

End proof.
End hashchain.
