From Perennial.program_proof Require Import grove_prelude.

Section defs.
Context `{!heapGS Σ}.

Definition is_Slice2D (sl_dim0 : Slice.t) (obj_dim0 : list (list w8)) : iProp Σ :=
  ∃ list_dim0,
  "#Hsl_dim0" ∷ own_slice_small sl_dim0 (slice.T byteT) DfracDiscarded list_dim0 ∗
  "#Hsep_dim0" ∷ ([∗ list] sl_dim1;obj_dim1 ∈ list_dim0;obj_dim0,
    "#Hsl_dim1" ∷ own_slice_small sl_dim1 byteT DfracDiscarded obj_dim1).

Definition is_Slice3D (sl_dim0 : Slice.t) (obj_dim0 : list (list (list w8))) : iProp Σ :=
  ∃ list_dim0,
  "#Hsl_dim0" ∷ own_slice_small sl_dim0 (slice.T (slice.T byteT)) DfracDiscarded list_dim0 ∗
  "#Hsep_dim0" ∷ ([∗ list] sl_dim1;obj_dim1 ∈ list_dim0;obj_dim0,
    ∃ list_dim1,
    "#Hsl_dim1" ∷ own_slice_small sl_dim1 (slice.T byteT) DfracDiscarded list_dim1 ∗
    "#Hsep_dim1" ∷ ([∗ list] sl_dim2;obj_dim2 ∈ list_dim1;obj_dim1,
      "#Hsl_dim2" ∷ own_slice_small sl_dim2 byteT DfracDiscarded obj_dim2)).

End defs.
