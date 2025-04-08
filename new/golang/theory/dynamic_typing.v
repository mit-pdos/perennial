From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Equality.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export dynamic_typing.
From New.golang.theory Require Import typing.

Set Default Proof Using "Type".

Section goose_lang.
Context `{ffi_syntax}.

#[global] Instance to_val_w64_inj : Inj eq eq (λ (n: w64), #n).
Proof.
  rewrite to_val_unseal /to_val_def /=.
  intros n1 n2. inv 1. auto.
Qed.

#[global] Instance to_val_string_inj : Inj eq eq (λ (s: byte_string), #s).
Proof.
  rewrite to_val_unseal /to_val_def /=.
  intros s1 s2. inv 1. auto.
Qed.

#[global] Instance type_to_val_inj : Inj eq eq type_to_val.
Proof.
  intros t1 t2.
  generalize dependent t2.
  induction t1 using go_type_ind; simpl;
    destruct t2; simpl; intros; auto;
    repeat lazymatch goal with
    | H: InjLV _ = InjLV _ |- _ => inv H
    | H: InjRV _ = InjRV _ |- _ => inv H
    | H: InjLV _ = InjRV _ |- _ => solve [ exfalso; inv H ]
    | H: InjRV _ = InjLV _ |- _ => solve [ exfalso; inv H ]
    | H: # (W64 _) = # (W64 _) |- _ =>
        solve [ exfalso; apply inj in H; lia ]
    end.
  - (* arrayT *)
    naive_solver.
  - (* structT *)
    generalize dependent decls0.
    induction decls as [|[d t] decls]; intros decls' Heq.
    + destruct decls' as [|[d' t']]; simpl in *; try congruence.
    + destruct decls' as [|[d' t']]; simpl in *; try congruence.
      inversion Heq as [[Hd Ht Hdecls]].
      apply (inj _) in Hd; subst d.
      apply Hfields in Ht; subst; auto.
      apply IHdecls in Hdecls; [ inv Hdecls; auto | auto ].
Qed.

End goose_lang.
