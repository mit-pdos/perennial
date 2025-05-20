From Perennial.program_proof.pav Require Import prelude.

From Perennial.program_proof.pav Require Import cryptoffi serde.

(* data at two different levels of opaqueness might both be (list w8)'s.
these notations provide a reference for their logical meaning. *)
Notation uid_ty := w64 (only parsing).
Notation ver_ty := w64 (only parsing).
Notation map_label_ty := (uid_ty * ver_ty)%type (only parsing).
Notation opaq_label_ty := (list w8) (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation commit_ty := (list w8) (only parsing).
Notation map_val_ty := (pk_ty) (only parsing).
Notation opaq_val_ty := (commit_ty) (only parsing).

Notation epoch_ty := w64 (only parsing).
Notation dig_ty := (list w8) (only parsing).
Notation merkle_map_ty := (gmap opaq_label_ty opaq_val_ty) (only parsing).

Notation enc_label_pre uid ver := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver).
Notation enc_sigdig ep dig := (PreSigDig.encodesF $ PreSigDig.mk ep dig).

Section defs.

Class pavG Σ :=
  {
    #[global] pavG_serv_ep :: mono_natG Σ;
    #[global] pavG_serv_vers :: ghost_mapG Σ uid_ty ver_ty;
    #[global] pavG_adtr :: mono_listG (merkle_map_ty * dig_ty) Σ;
    #[global] pavG_cli :: mono_listG (option dig_ty) Σ;
  }.

Context `{!heapGS Σ}.

Definition is_map_label pk uid ver label : iProp Σ :=
  is_vrf_out pk (enc_label_pre uid ver) label.

Definition is_commit (val : pk_ty) (commit : commit_ty) : iProp Σ :=
  ∃ rand enc,
  "%Henc" ∷ ⌜ CommitOpen.encodes enc (CommitOpen.mk val rand) ⌝ ∗
  "#Hhash" ∷ is_hash enc commit.

Lemma is_commit_inj val0 val1 commit :
  is_commit val0 commit -∗ is_commit val1 commit -∗ ⌜ val0 = val1 ⌝.
Proof.
  iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_hash_inj with "Hhash0 Hhash1") as %->.
  opose proof (CommitOpen.inj [] [] Henc0 Henc1 _) as ?; [done|].
  naive_solver.
Qed.

End defs.
