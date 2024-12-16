From New.golang.theory Require Import exception mem typing.
From New.golang.defn Require Import globals.
From iris.base_logic.lib Require Import ghost_map ghost_var.
From Coq Require Import Ascii.

Class goGlobals_preG (Σ: gFunctors) : Set :=
  {
    #[global] go_globals_inG :: ghost_mapG Σ (string * string) loc ;
    #[global] go_package_initialized_inG :: ghost_mapG Σ string () ;
  }.

Class goGlobalsGS Σ : Set :=
  GoGlobalsGS {
      #[global] go_globals_pre_inG :: goGlobals_preG Σ ;
      go_globals_name : gname ;
      go_package_initialized_name : gname ;
      go_package_postcond_tok_name : gname ;
    }.

Section definitions.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Context `{!goGlobalsGS Σ}.

Local Definition is_valid_package_name_prop (pkg_name : string) : Prop :=
  " "%char ∉ (String.list_ascii_of_string pkg_name).

Fixpoint is_valid_package_name (pkg_name : string) : bool :=
  match pkg_name with
  | EmptyString => true
  | String a s => negb (Ascii.eqb a " "%char) && is_valid_package_name s
  end.

Local Notation encode_var_name := (globals.globals.encode_var_name).

(* The only concurrent access to globals is to read the address of global
   variables, so that's the only thing this invariant is concerned with. *)
Local Definition own_globals_inv : iProp Σ :=
  ∃ g (addrs : gmap (string * string) loc),
  "Hglobals_i" ∷ own_globals (DfracOwn (1/2)) g ∗
  "Haddrs" ∷ ghost_map_auth go_globals_name 1%Qp addrs ∗
  "%Hvars" ∷ (⌜ ∀ pkg_name var_name,
                is_valid_package_name pkg_name →
                # <$> addrs !! (pkg_name, var_name) = g !! (encode_var_name pkg_name var_name) ⌝).

Local Definition is_globals_inv : iProp Σ :=
  inv nroot own_globals_inv.

(* This must be owned by the `init` thread. *)
Definition own_globals_tok_def (pending_packages : gset string)
  (pkg_postconds : gmap string (iProp Σ)): iProp Σ :=
  ∃ g pkg_initialized,
  "Hglobals" ∷ own_globals (DfracOwn (1/2)) g ∗
  "Hpkg_initialized" ∷ ghost_map_auth go_package_initialized_name 1%Qp pkg_initialized ∗
  "%Hpkg" ∷ (⌜ ∀ pkg_name,
               is_valid_package_name pkg_name →
               pkg_name ∈ pending_packages ∨
               # <$> pkg_initialized !! pkg_name = g !! pkg_name ⌝) ∗
  "#Hinited" ∷ ([∗ map] pkg_name ↦ _ ∈ pkg_initialized,
                  pkg_name ↪[go_package_initialized_name]□ () ∗
                  match (pkg_postconds !! pkg_name) with
                  | None => False
                  | Some P =>
                      inv nroot (pkg_name ↪[go_package_postcond_tok_name] () ∨ P)
                  end
    ).
Program Definition own_globals_tok := unseal (_:seal (@own_globals_tok_def)). Obligation 1. by eexists. Qed.
Definition own_globals_tok_unseal : own_globals_tok = _ := seal_eq _.

Definition own_package_init_post_tok_def (pkg_name : string) : iProp Σ :=
  pkg_name ↪[go_package_postcond_tok_name] ().
Program Definition own_package_init_post_tok := unseal (_:seal (@own_package_init_post_tok_def)). Obligation 1. by eexists. Qed.
Definition own_package_init_post_tok_unseal : own_package_init_post_tok = _ := seal_eq _.

Definition is_initialized_def (pkg_name : string) (P : iProp Σ) : iProp Σ :=
  inv nroot (pkg_name ↪[go_package_postcond_tok_name] () ∨ P).
Program Definition is_initialized := unseal (_:seal (@is_initialized_def)). Obligation 1. by eexists. Qed.
Definition is_initialized_unseal : is_initialized = _ := seal_eq _.

Definition is_global_addr_def (var_id : string * string) (addr : loc) : iProp Σ :=
  is_globals_inv ∗ var_id ↪[go_globals_name]□ addr.
Program Definition is_global_addr := unseal (_:seal (@is_global_addr_def)). Obligation 1. by eexists. Qed.
Definition is_global_addr_unseal : is_global_addr = _ := seal_eq _.

Definition own_unused_vars_def (pkg_name : string) (used_var_names : gset string) : iProp Σ :=
  ∃ g,
    "Hglobals" ∷ own_globals (DfracOwn (1/2)) g ∗
    "%Hused_vars_dom" ∷ (⌜ ∀ var_name,
                           is_Some (g !! (encode_var_name pkg_name var_name)) ↔
                           var_name ∈ used_var_names ⌝
      ) ∗
    "#Hinv" ∷ is_globals_inv
.
Program Definition own_unused_vars := unseal (_:seal (@own_unused_vars_def)). Obligation 1. by eexists. Qed.
Definition own_unused_vars_unseal : own_unused_vars = _ := seal_eq _.

Local Ltac unseal := rewrite
  ?is_global_addr_unseal
  ?is_initialized_unseal
  ?own_package_init_post_tok_unseal
  ?own_unused_vars_unseal.

Global Instance is_global_addr_persistent x a:
  Persistent (is_global_addr x a).
Proof. unseal. apply _. Qed.

Lemma encode_var_name_inj pkg_name1 pkg_name2 var_name1 var_name2 :
  is_valid_package_name pkg_name1 →
  is_valid_package_name pkg_name2 →
  encode_var_name pkg_name1 var_name1 = encode_var_name pkg_name2 var_name2 →
  pkg_name1 = pkg_name2 ∧ var_name1 = var_name2.
Proof.
Admitted.

Lemma encode_var_name_package_name_ne pkg_name' pkg_name var_name :
  is_valid_package_name pkg_name' →
  pkg_name' ≠ encode_var_name pkg_name var_name.
Proof.
Admitted.

Lemma wp_globals_put var_id used_var_names (addr : loc) :
  var_id.2 ∉ used_var_names →
  {{{ own_unused_vars var_id.1 used_var_names }}}
    globals.put var_id #addr
  {{{ RET #();
      own_unused_vars var_id.1 ({[ var_id.2 ]} ∪ used_var_names) ∗
      is_global_addr var_id addr
  }}}.
Proof.
  iIntros (??) "Hu HΦ".
  wp_call_lc "Hlc".
  rewrite to_val_unseal.
  simpl.
  unseal.
  iNamed "Hu".
  unseal.
  iInv "Hinv" as "Hi" "Hclose".
  iMod (lc_fupd_elim_later with "Hlc Hi") as "Hi".
  iNamed "Hi".
Admitted.

Lemma wp_globals_get var_id (addr : loc) :
  {{{ is_global_addr var_id addr }}}
    globals.get var_id #()
  {{{ RET #addr; True }}}.
Proof.
  iIntros (?) "Hu HΦ".
  destruct var_id as [pkg_name var_name].
Admitted.

Lemma wp_package_init pending postconds (pkg_name : string) (init_func : val) P Φ :
  is_valid_package_name pkg_name →
  postconds !! pkg_name = Some P →
  own_globals_tok pending postconds -∗
  (own_unused_vars pkg_name ∅ -∗
   (∀ vars, own_unused_vars pkg_name vars -∗ own_globals_tok ({[ pkg_name ]} ∪ pending) postconds) -∗
   WP init_func #()
     {{ _, P ∗
           own_globals_tok ({[ pkg_name ]} ∪ pending) postconds
     }}
  ) -∗
  (is_initialized pkg_name P -∗ own_globals_tok pending postconds -∗ Φ #()) -∗
  WP (globals.package_init pkg_name init_func) {{ Φ }}.
Proof.
Admitted.

End definitions.
