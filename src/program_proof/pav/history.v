From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

Module HistEntry.
Record t :=
  mk {
    Epoch: w64;
    HistVal: list w8;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_HistVal,
  "Hptr_Epoch" ∷ ptr ↦[HistEntry :: "Epoch"] #obj.(Epoch) ∗
  "Hptr_HistVal" ∷ ptr ↦[HistEntry :: "HistVal"] (slice_val sl_HistVal) ∗
  "#Hsl_HistVal" ∷ own_slice_small sl_HistVal byteT DfracDiscarded obj.(HistVal).
End defs.
End HistEntry.

(* logical history. this may be the same as the physical history.
but lets leave it abstract for now, so we can fill in details later
once we know the use case. *)
Module hist.
Definition t : Type. Admitted.
(* TODO: the core invariant about the logical history. *)
Definition inv (obj : t) : Prop. Admitted.
(* relation bw physical and logical st.  *)
Definition phys_relate (obj : t) (hist : list HistEntry.t) : Prop. Admitted.
End hist.

Section defs.
Context `{!heapGS Σ}.
Definition own_hist sl_hist (hist : list HistEntry.t) : iProp Σ :=
  ∃ dim0_hist,
  "Hsl_hist" ∷ own_slice sl_hist ptrT (DfracOwn 1) dim0_hist ∗
  "Hdim0_hist" ∷ ([∗ list] p;o ∈ dim0_hist;hist, HistEntry.own p o) ∗
  "Hrelate" ∷ hist.phys_relate log_hist hist ∗
  "Hhist_inv" ∷ inv hist.
End defs.

Section wps.
Context `{!heapGS Σ}.
Lemma wp_GetHist sl_hist hist (epoch : w64) :
  {{{
    "Hown_hist" ∷ own_hist sl_hist hist
  }}}
  GetHist (slice_val sl_hist) #epoch
  {{{
    (is_reg : bool) sl_lat_val (lat_val : list w8), RET (#is_reg, slice_val sl_lat_val);
    (* could directly say that lat_val is an element in the hist that corresponds to the max epoch
    less than the one queried. *)
    (* or, could say that the output matches whatever is returned by some logical object.
    ultimately, it's prob easier to reason about the logical object with other things,
    e.g., msv's, so let's have the output match that. *)
    (* secondly, what logical state do we wanna use?
    before, i explicitly made the logical object basically the same thing.
    and i made the get fn something.
    can i be more abstract here?
    there exists some logical object, and this thing is tied into it.
    and that object has a get fn.
    *)
  }}}.
End wps.
