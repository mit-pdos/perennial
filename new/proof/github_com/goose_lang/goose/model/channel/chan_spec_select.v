From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.
From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_ghost_state chan_spec_inv chan_spec_base.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof Require Import proof_prelude.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}. 
Context `{!closePropTrackerG Σ,  !inG Σ (authR (optionUR (prodR fracR natR)))}.
Context `{!ghost_varG Σ (bool * val)}.
   Context `{!goGlobalsGS Σ}.
#[global] Program Instance : IsPkgInit channel := ltac2:(build_pkg_init ()).

(* Parameterized select case logical function *)
Definition own_select_case_logical
  (params: chan) (dir: select_dir)
  (v: params.(ch_T')) (selected: bool) (i: nat) (ok: bool) : iProp Σ :=
match selected with
| false =>
    match dir with
    | SelectSend => send_pre params i v
    | SelectRecv => recv_pre params i
    end
| true =>
    match dir with
    | SelectSend => send_post params i
    | SelectRecv => recv_post params i ok v
    end
end.

Definition nil_select_case : loc := null.

Definition own_select_case
  (dir: select_dir) (params: chan) (case_ptr: loc) (selected: bool) (i: nat) (v': val) : iProp Σ :=
  if bool_decide (case_ptr = nil_select_case) then
    (* For nil case, precondition is True, postcondition is False *)
    (if selected then False%I else True%I)%I
  else
    (let T' := params.(ch_T') in
    let T := params.(ch_T) in
    let IntoVal_inst := params.(ch_IntoVal) in
    let IntoValTyped_inst := params.(ch_IntoValTyped) in
    let Hbounded := params.(ch_Hbounded) in
    ∃  (v: T') (ok: bool),
      "%Hvalconv" ∷ ⌜v' = to_val v⌝ ∗  (* This connects v' to a properly typed v *)
      "channel" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "channel"] params.(ch_loc) ∗
      "dir" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "dir"] (select_dir_to_word dir) ∗
      "Value" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "Value"] v ∗
      "Ok" ∷ case_ptr ↦s[(channel.SelectCase.ty T) :: "Ok"] ok ∗ 
      "Hlogicalselect" ∷ own_select_case_logical params dir v selected i ok)%I.

Definition own_selected_case_multi
  (blocking: bool) (selected_index: nat)
  (params1 params2 params3 params4 params5: chan)
  (dir1 dir2 dir3 dir4 dir5: select_dir) 
  (case1 case2 case3 case4 case5: loc) 
  (v1 v2 v3 v4 v5: val) 
  (i1 i2 i3 i4 i5: nat) : iProp Σ :=
  let cases := [case1; case2; case3; case4; case5] in
  if (bool_decide (selected_index < 5)) then
    ("%Hindlt5" ∷ ⌜selected_index < 5⌝ ∗
     ("Hselcase" ∷ match selected_index with
     | 0%nat => own_select_case dir1 params1 case1 true i1 v1
     | 1%nat => own_select_case dir2 params2 case2 true i2 v2
     | 2%nat => own_select_case dir3 params3 case3 true i3 v3
     | 3%nat => own_select_case dir4 params4 case4 true i4 v4
     | 4%nat => own_select_case dir5 params5 case5 true i5 v5
     | _ => False
     end)%I ∗
     ("Hcase1" ∷ (if decide(selected_index ≠ 0%nat) then  own_select_case dir1 params1 case1 false i1 v1 else True)) ∗
     ("Hcase2" ∷ (if decide(selected_index ≠ 1%nat) then  own_select_case dir2 params2 case2 false i2 v2 else True)) ∗
     ("Hcase3" ∷ (if decide(selected_index ≠ 2%nat) then  own_select_case dir3 params3 case3 false i3 v3 else True)) ∗
     ("Hcase4" ∷ (if decide(selected_index ≠ 3%nat) then  own_select_case dir4 params4 case4 false i4 v4 else True)) ∗
     ("Hcase5" ∷ (if decide(selected_index ≠ 4%nat) then  own_select_case dir5 params5 case5 false i5 v5 else True)) )%I
  else
    ⌜selected_index = 5%nat ∧ ¬ blocking⌝%I.

Definition own_selected_case_params1
  (dir1: select_dir) (params1: chan) (blocking: bool) (selected_index: nat) 
  (case1: loc) (v1: val) (i1: nat) : iProp Σ :=
  own_selected_case_multi blocking selected_index 
    params1 params1 params1 params1 params1
    dir1 dir1 dir1 dir1 dir1
    case1 nil_select_case nil_select_case nil_select_case nil_select_case
    v1 v1 v1 v1 v1
    i1 i1 i1 i1 i1.


Definition own_selected_case_params2
  (dir1 dir2: select_dir) (params1 params2: chan) (blocking: bool) (selected_index: nat) 
  (case1 case2: loc) (v1 v2: val) (i1 i2: nat) : iProp Σ :=
  own_selected_case_multi blocking selected_index 
    params1 params2 params1 params1 params1
    dir1 dir2 dir1 dir1 dir1
    case1 case2 nil_select_case nil_select_case nil_select_case
    v1 v2 v1 v1 v1
    i1 i2 i1 i1 i1.

Definition own_selected_case_params3
    (dir1 dir2 dir3: select_dir)
    (params1 params2 params3: chan)
    (blocking: bool) (selected_index: nat)
    (case1 case2 case3: loc)
    (v1 v2 v3: val) (i1 i2 i3: nat) : iProp Σ :=
    own_selected_case_multi blocking selected_index 
      params1 params2 params3 params1 params1
      dir1 dir2 dir3 dir1 dir1
      case1 case2 case3 nil_select_case nil_select_case
      v1 v2 v3 v1 v1
      i1 i2 i3 i1 i1.
  
Definition own_selected_case_params4
  (dir1 dir2 dir3 dir4: select_dir)
  (params1 params2 params3 params4: chan)
  (blocking: bool) (selected_index: nat)
  (case1 case2 case3 case4: loc)
  (v1 v2 v3 v4: val) (i1 i2 i3 i4: nat) : iProp Σ :=
  own_selected_case_multi blocking selected_index 
    params1 params2 params3 params4 params1
    dir1 dir2 dir3 dir4 dir1
    case1 case2 case3 case4 nil_select_case
    v1 v2 v3 v4 v1
    i1 i2 i3 i4 i1.

Definition own_selected_case_params5
  (dir1 dir2 dir3 dir4 dir5: select_dir)
  (params1 params2 params3 params4 params5: chan)
  (blocking: bool) (selected_index: nat)
  (case1 case2 case3 case4 case5: loc)
  (v1 v2 v3 v4 v5: val) (i1 i2 i3 i4 i5: nat) : iProp Σ :=
  own_selected_case_multi blocking selected_index 
    params1 params2 params3 params4 params5
    dir1 dir2 dir3 dir4 dir5
    case1 case2 case3 case4 case5
    v1 v2 v3 v4 v5
    i1 i2 i3 i4 i5.

Lemma wp_multiSelect
    (params1 params2 params3 params4 params5: chan)
    (dir1 dir2 dir3 dir4 dir5: select_dir) 
    (case1 case2 case3 case4 case5 : loc)
    (v1 v2 v3 v4 v5: val)
    (i1 i2 i3 i4 i5: nat)
    (blocking : bool) :
  {{{
      is_pkg_init channel ∗ 
  own_select_case dir1 params1 case1 false i1 v1 ∗
      own_select_case dir2 params2 case2 false i2 v2 ∗
      own_select_case dir3 params3 case3 false i3 v3 ∗
      own_select_case dir4 params4 case4 false i4 v4 ∗
      own_select_case dir5 params5 case5 false i5 v5 }}}
    channel @ "multiSelect" #params1.(ch_T) #params2.(ch_T) #params3.(ch_T) #params4.(ch_T) #params5.(ch_T)  #case1 #case2 #case3 #case4 #case5 #blocking
  {{{ (selected_index : nat), RET #(W64 selected_index); 
      own_selected_case_params5 dir1 dir2 dir3 dir4 dir5 params1 params2 params3 params4 params5
       blocking selected_index 
                               case1 case2 case3 case4 case5 v1 v2 v3 v4 v5 i1 i2 i3 i4 i5 }}}.
  Proof.
  wp_start. wp_auto. 
  Admitted.

Lemma wp_TrySelectAt
  (params: chan)
  (dir: select_dir)
  (case_ptr : loc)
  (i: nat) (v: val)
  :
  {{{ is_pkg_init channel ∗  own_select_case dir params case_ptr false i v }}}
    channel @ "TrySelectAt" #params.(ch_T) #case_ptr
  {{{ (selected : bool), RET #selected;
      own_select_case dir params case_ptr selected i v }}}.
Proof.
  wp_start. wp_auto.
Admitted.

Definition is_perm_0_5 (order : list nat) : Prop :=
  Permutation order [0%nat;1%nat;2%nat;3%nat;4%nat].

Definition nats_to_u64s (ns : list nat) : list u64 :=
  List.map (λ n, W64 (Z.of_nat n)) ns.

Definition own_order_slice (s: slice.t) (order: list nat) : iProp Σ :=
  ⌜is_perm_0_5 order⌝ ∗
  own_slice s (DfracOwn 1) (nats_to_u64s order).

(* Helper function to select the right params, index, and value based on index *)
Definition select_case_info_by_index 
  (idx: nat) 
  (params1 params2 params3 params4 params5: @chan _ Σ)
  (dir1 dir2 dir3 dir4 dir5: select_dir) 
  (i1 i2 i3 i4 i5: nat)
  (v1 v2 v3 v4 v5: val) : 
  (chan * select_dir * nat * val) :=
  match idx with
  | 0%nat => (params1, dir1, i1, v1)
  | 1%nat => (params2, dir2, i2, v2)
  | 2%nat => (params3, dir3, i3, v3)
  | 3%nat => (params4, dir4, i4, v4)
  | _ => (params5, dir5, i5, v5)
  end.

Lemma wp_TrySelectCase
  (params1 params2 params3 params4 params5: chan)
  (dir1 dir2 dir3 dir4 dir5: select_dir) 
  (i1 i2 i3 i4 i5: nat)
  (v1 v2 v3 v4 v5: val)
  (idx : nat) (case1 case2 case3 case4 case5 : loc):
  0 ≤ idx < 5 →
  let '(params_i, dir_i, i, v) := select_case_info_by_index idx params1 params2 params3 params4 params5 dir1 dir2 dir3 dir4 dir5 i1 i2 i3 i4 i5 v1 v2 v3 v4 v5 in
  {{{ is_pkg_init channel ∗  own_select_case dir_i params_i (List.nth idx [case1; case2; case3; case4; case5] case1) false i v }}}
    channel @ "TrySelectCase"  #params1.(ch_T) #params2.(ch_T) #params3.(ch_T) #params4.(ch_T) #params5.(ch_T)  #(W64 idx) #case1 #case2 #case3 #case4 #case5
  {{{ (selected : bool), RET #selected;
      own_select_case dir_i params_i (List.nth idx [case1; case2; case3; case4; case5] case1) selected i v }}}.
Proof.
  intros Hind.
    unfold select_case_info_by_index.
  destruct idx.
  {
    wp_start. wp_auto.
Admitted.
      
Lemma wp_TryCasesInOrder
  (params1 params2 params3 params4 params5: chan)
  (dir1 dir2 dir3 dir4 dir5: select_dir) 
  (i1 i2 i3 i4 i5: nat)
  (v1 v2 v3 v4 v5: val)
  (case1 case2 case3 case4 case5 : loc)
  (order : slice.t)
  (order_rep : list nat) :
{{{ 
  is_pkg_init channel ∗ 
  own_order_slice order order_rep ∗
  [∗ list] j ∈ order_rep, 
    let '(params_j, dir_j, i_j, v_j) := select_case_info_by_index j params1 params2 params3 params4 params5 dir1 dir2 dir3 dir4 dir5 i1 i2 i3 i4 i5 v1 v2 v3 v4 v5 in
    own_select_case dir_j params_j (List.nth j [case1; case2; case3; case4; case5] case1) false i_j v_j
}}}
  channel @ "TryCasesInOrder"  #params1.(ch_T) #params2.(ch_T) #params3.(ch_T) #params4.(ch_T) #params5.(ch_T)
    #order #case1 #case2 #case3 #case4 #case5
{{{ (selected_idx : nat), RET #(W64 selected_idx);
    ⌜selected_idx ≤ 5⌝ ∗
    ([∗ list] j↦_ ∈ order_rep,
     let '(params_j, dir_j, i_j, v_j) := select_case_info_by_index j params1 params2 params3 params4 params5 dir1 dir2 dir3 dir4 dir5 i1 i2 i3 i4 i5 v1 v2 v3 v4 v5 in
     if j =? selected_idx then
       own_select_case dir_j params_j (List.nth j [case1; case2; case3; case4; case5] case1) true i_j v_j
     else
       own_select_case dir_j params_j (List.nth j [case1; case2; case3; case4; case5] case1) false i_j v_j)
}}}.
Proof.
  wp_start. wp_auto.
Admitted.

End proof.
