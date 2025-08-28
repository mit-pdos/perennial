From New.proof.github_com.goose_lang.goose.model.channel Require Import chan_au_base chan_au_send chan_au_recv.
From New.proof Require Import proof_prelude.
Require Export New.code.github_com.goose_lang.goose.model.channel.
From New.generatedproof.github_com.goose_lang.goose Require Import model.channel.
From New.proof.github_com.goose_lang Require Import primitive.
From New.proof.github_com.goose_lang.std Require Import std_core.

Section atomic_specs.

(* The select specs are currently unvetted ideas but an example of what I'm hoping for:
1. Goose translates blocking select from go to something like 
Select2 #t1 #t2 #(NewSendCase #t1 #ch1 #v1) #(NewRecvCase #t2 #ch2) #true;
< standard switch logic on 0 and 1 for the case expressions would go here >
2. User has is_chan in persistent context for ch1 and ch2
3. User calls wp_select tactic 
4. User must step through each case
  a. consume the atomic update for the operation with a lemma based on a protocol that 
  the user declares for how they will use the channel i.e. single prod/cons pipeline
  and gain the associated updated resources
  b. prove the continuation with the case index, which wp_auto should reduce to the switch
  statement logic for the given case 
*)
(*
Inductive chan_select_case :=
| chan_select_send (ch: loc) (v: V) (γ: chan_names)  
| chan_select_receive (ch: loc) (γ: chan_names).

Definition select_case (t: go_type) (ch: loc) (v_opt: option val) (γ: chan_names) : chan_select_case :=
  match v_opt with
  | Some v => chan_select_send ch (extract_typed_val t v) γ
  | None => chan_select_receive ch γ
  end.
  Definition chan_select_blocking_update (cases : list chan_select_case) (Φ : nat → iProp Σ) : iProp Σ :=
  [∨ list] i ↦ case ∈ cases,
    match case with
    | chan_select_send ch v γ =>
        chan_send_atomic_update ch v γ (Φ i)
    | chan_select_receive ch γ =>
        chan_receive_atomic_update ch γ (λ v ok, Φ (#v, #ok)%V)
    end.

(* Convert math case back to physical syntax (for verification) *)
Definition case_math_to_phys (sel_case: chan_select_case) : val :=
  match sel_case with
  | chan_select_send ch v γ => NewSendCase (type_of v) ch (to_val v)
  | chan_select_receive ch γ => NewRecvCase (type_of_chan ch) ch
  end.

Lemma wp_chan_select2 
  (t1 t2: go_type) (ch1 ch2: loc) (v1 v2: option val) (γ1 γ2: chan_names) :
  ∀ Φ,
  is_pkg_init channel ∗ is_channel ch1 γ1 ∗ is_channel ch2 γ2  -∗
  let case1 := select_case t1 ch1 v1 γ1 in
  let case2 := select_case t2 ch2 v2 γ2 in
  chan_select_blocking_update [case1; case2] Φ -∗
  WP @! channel.Select2 #t1 #t2 #(case_math_to_phys case1) #(case_math_to_phys case2) #true
  {{ λ index, Φ (uint.nat index) }}.

*)


End atomic_specs.
