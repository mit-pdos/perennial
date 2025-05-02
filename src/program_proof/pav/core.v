From Perennial.program_proof.pav Require Import prelude.

From Perennial.program_proof.pav Require Import cryptoffi serde.

(* TODO: for same reason not using alias's in go code,
prob shouldn't define all these notations. *)
Notation commit_ty := (list w8) (only parsing).
Notation dig_ty := (list w8) (only parsing).
Notation uid_ty := w64 (only parsing).
Notation ver_ty := w64 (only parsing).
Notation epoch_ty := w64 (only parsing).
Notation pk_ty := (list w8) (only parsing).
Notation map_label_ty := (uid_ty * ver_ty)%type (only parsing).
Notation opaque_label_ty := (list w8) (only parsing).
Notation map_val_ty := (epoch_ty * pk_ty)%type (only parsing).
Notation map_ty := (gmap map_label_ty map_val_ty) (only parsing).
Notation merkle_map_ty := (gmap (list w8) (list w8)) (only parsing).
Notation opaque_map_val_ty := (epoch_ty * commit_ty)%type (only parsing).
Notation adtr_map_ty := (gmap opaque_label_ty opaque_map_val_ty) (only parsing).
Notation cli_map_val_ty := (option (epoch_ty * commit_ty)) (only parsing).
Notation cli_map_ty := (gmap map_label_ty cli_map_val_ty) (only parsing).
Notation lat_val_ty := (option map_val_ty) (only parsing).
Notation lat_opaque_val_ty := (option opaque_map_val_ty) (only parsing).

Notation enc_label_pre uid ver := (MapLabelPre.encodesF $ MapLabelPre.mk uid ver).
Notation enc_val ep commit := (MapValPre.encodesF $ MapValPre.mk ep commit).
Notation enc_sigdig ep dig := (PreSigDig.encodesF $ PreSigDig.mk ep dig).

Section defs.

Class pavG Σ :=
  {
    #[global] pavG_serv_ep :: mono_natG Σ;
    #[global] pavG_serv_digs ::
      mono_listG ((gmap (list w8) (w64 * list w8)) * list w8) Σ;
    #[global] pavG_serv_map :: ghost_mapG Σ w64 w64;
    #[global] pavG_adtr ::
      mono_listG ((gmap opaque_label_ty (epoch_ty * commit_ty)) * dig_ty) Σ;
    #[global] pavG_cli :: mono_listG (option dig_ty) Σ;
  }.

Context `{!heapGS Σ}.

Definition is_map_label pk uid ver label : iProp Σ :=
  is_vrf_out pk (MapLabelPre.encodesF $ MapLabelPre.mk uid ver) label.

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

Definition get_lat (hist : list map_val_ty) (ep : w64) : lat_val_ty :=
  last $ filter (λ x, uint.Z x.1 ≤ uint.Z ep) hist.

End defs.
