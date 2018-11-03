(** * 6.826 lab assignments infrastructure

    This file provides common infrastructure for the lab assignments for
    6.826 (Principles of Computer Systems).  You can explore this common
    infrastructure by browsing the coqdoc documentation for the libraries
    imported here.  Click on the module name after the [Require Export]
    statement to navigate to the documentation for that module.

    All of the code you will be writing for 6.826 lab assignments will
    import all of this common infrastructure using [Require Import POCS],
    which you will see at the top of the files we will be giving you for
    the labs.
  *)

(** We include some libraries from the Coq standard library.
    [List] provides linked lists, and [Omega] provides a tactic for
    proving simple arithmetic facts.
  *)

Require Export List.
Require Export Omega.

(** [Helpers.Helpers] has some definitions to augment the standard library, as well as a
variety of proof automation (Ltac) used to simplify writing proofs with the POCS
infrastructure. *)

Require Export Helpers.Helpers.

(** [Spec.Proc] defines [proc], the type of the programs you'll write in 6.826.
We also describe how these programs run, including how programs can crash and
how the system can run a recovery procedure afterward. *)

Require Export Spec.Proc.

(** [Spec.Abstraction] defines how we write specifications in terms of
abstraction relations. *)

Require Export Spec.Abstraction.

(** [Spec.Recovery] proves a number of theorems for reasoning about recovery
across abstraction layers. *)

Require Export Spec.Recovery.
