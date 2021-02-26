From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Export ffi.disk_prelude.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Perennial.algebra Require Import auth_map.
Require Import Decimal Ascii String DecimalString.

Axiom Read : val.
Axiom Write : val.
Axiom U64ToString : val.
Axiom GetServer : val.
Axiom AllocServer : val.

Section grove_ffi.
Context `{!heapG Σ}.

Class filesysG Σ := FileSysG {
  filesys_gname : gname ; (* Name of str -> []byte authmap used for filesys ffi *)
  filesys_inG :> mapG Σ string (list byte)
}.

Definition file_mapsto {fG:filesysG Σ} (s:string) (c:list byte) (q:Qp): iProp Σ :=
  s [[filesys_gname]]↦{q} c.

Context `{!filesysG Σ}.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.

Axiom wpc_Read : ∀ {k} filename (q:Qp) content,
  {{{
      filename f↦{q} content
  }}}
    grove_ffi.Read #(str filename) @ k ; ⊤
  {{{
       s, RET slice_val s; typed_slice.is_slice s byteT 1 content ∗
                           filename f↦{q} content
  }}}
  {{{
      filename f↦{q} content
  }}}.

Axiom wpc_Write : ∀ {k} filename content_old content (content_sl:Slice.t) q,
  {{{
      filename f↦ content_old ∗
      typed_slice.is_slice content_sl byteT q content
  }}}
    grove_ffi.Write #(str filename) (slice_val content_sl) @ k ; ⊤
  {{{
       RET #(); filename f↦ content ∗
      typed_slice.is_slice content_sl byteT q content
  }}}
  {{{
      filename f↦ content_old ∨
      filename f↦ content
  }}}.

Definition u64_to_string : u64 -> string := λ u, NilZero.string_of_int (Z.to_int (int.Z u)).

(* Spec for U64ToString will be annoying *)
Axiom wp_U64ToString : ∀ (u:u64),
  {{{
       True
  }}}
    grove_ffi.U64ToString #u
  {{{
       RET #(str u64_to_string u); True
  }}}.

Class rpcregG Σ := RpcRegG {
  rpcreg_gname : gname ;
  rpcreg_inG :> mapG Σ u64 (gmap u64 val)
}.

Context `{!rpcregG Σ}.

Axiom wp_GetServer : ∀ (host : u64) (rpcid : u64) (handlers : gmap u64 val) (rpcf : val) k,
  {{{
      host [[rpcreg_gname]]↦ro handlers ∗
      ⌜ handlers !! rpcid = Some rpcf ⌝
  }}}
    grove_ffi.GetServer #host #rpcid @ k ; ⊤
  {{{
      RET rpcf; True
  }}}.

Axiom wp_AllocServer : ∀ (handlers : gmap u64 val) (mref : loc) (def : val) k,
  {{{
      map.is_map mref (handlers, def)
  }}}
    grove_ffi.AllocServer #mref @ k ; ⊤
  {{{
      (host : u64),
      RET #host;
      host [[rpcreg_gname]]↦ro handlers
  }}}.

End grove_ffi.

Notation "s f↦{ q } c" := (file_mapsto s c q)
(at level 20, q at level 50, format "s  f↦{ q } c") : bi_scope.

Notation "s f↦ c" := (s f↦{1} c)%I
(at level 20, format "s  f↦ c") : bi_scope.
