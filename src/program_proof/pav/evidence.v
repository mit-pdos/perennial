From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.

Module chainSepSome.
Record t :=
  mk {
    epoch: w64;
    prevLink: list w8;
    data: list w8;
  }.

Definition encodesF (o : t) : list w8 :=
  [(W8 1)] ++ u64_le o.(epoch) ++ o.(prevLink) ++ o.(data).
Definition encodes (b : list w8) (o : t) : Prop :=
  b = encodesF o.
End chainSepSome.

Module servSepLink.
Record t :=
  mk {
    link: list w8;
  }.

Definition encodesF (o : t) : list w8 :=
  [(W8 0)] ++ o.(link).
Definition encodes (b : list w8) (o : t) : Prop :=
  b = encodesF o.
End servSepLink.

Module servSepPut.
Record t :=
  mk {
    epoch: w64;
    id: list w8;
    val: list w8;
  }.

Definition encodesF (o : t) : list w8 :=
  [(W8 1)] ++ u64_le o.(epoch) ++ o.(id) ++ o.(val).
Definition encodes (b : list w8) (o : t) : Prop :=
  b = encodesF o.
End servSepPut.

Section evidence.
Context `{!heapGS Σ, !mono_listG (list w8) Σ}.

Definition serv_sigpred_link γ (data : servSepLink.t) : iProp Σ :=
  ∃ (links : list (list w8)) (epoch : w64) (prevLink : list w8) (currDig : list w8),
  "#Hlinks" ∷ mono_list_lb_own γ links ∗
  "#Hlink" ∷ is_hash data.(servSepLink.link) (chainSepSome.encodesF (chainSepSome.mk epoch prevLink currDig)) ∗
  "%HlookPrev" ∷ ⌜links !! (uint.nat epoch - 1) = Some prevLink⌝ ∗
  "%HlookCurr" ∷ ⌜links !! uint.nat epoch = Some data.(servSepLink.link)⌝.

(* Note: False for now so we don't have to consider put promises. *)
Definition serv_sigpred_put (γ : gname) (data : servSepPut.t) : iProp Σ := False.

Definition serv_sigpred γ : (list w8 → iProp Σ) :=
  λ data,
    ((
      ∃ dataSepLink,
        ⌜servSepLink.encodes data dataSepLink⌝ ∗
        serv_sigpred_link γ dataSepLink
    )%I
    ∨
    (
      ∃ dataSepPut,
        ⌜servSepPut.encodes data dataSepPut⌝ ∗
        serv_sigpred_put γ dataSepPut
    )%I)%I.

End evidence.
