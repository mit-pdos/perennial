From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.tutorial.objectstore Require Export chunk dir client.
From Perennial.base_logic.lib Require Import ghost_map.

(*
  map keyname → chunkhandle

  global monotonic map: chunkhandle → chunkdata.
  All points-tos are persistent (related to hashing plan).

  { True }
    PrepareWrite()
  { writeId, RET #writeId; ownership of writeId }
  ownership of writeId is:
    for each index, a points-to with value chunkhandle. Initially points-to nil.

  Just before the client sends a chunk for a particular index to a chunk server,
  it updates the points-to for that index to a frozen points-to with value equal
  to that chunk server+content hash.
  This persistent points-to is precondition of dir.RecordChunk().

  Client-side ghost state is map from string to (list u8).

  PrepareWrite returns ownership of the ongoing write value.
  AppendChunk changes this value.
  Done takes ownership of the ongoing value, and (logically) atomically updates
  the "real" value of that keyname to be the ongoing value.

  Key invariant about top-level ghost state:
    auth_map (1/2) m ∗
    if m !! k = Some v →
      ∃ chunkhandles,
      k ↦[γdir] chunkhandles ∗
      (there's a way to split up v into chunks such that
       chunk_handle[j].content_hash ↦[γhash]□ v_chunks[j]

 *)

(* Hashing plan:
   1. Real Go code does hashing.
   2. GooseLang model is a Go hashing service, which checks for duplicates.
   3. Spec is monotonic map:
      { True }
       Hash(content)
      { content_hash:string, RET #content_hash; content_hash ↦[γhash]□ content }
*)

Module PreparedWrite.
Record t := mk
  {
    Id: u64;
    ChunkAddrs: list chan;
  }.

End PreparedWrite.

Module RecordChunkArgs.
  Record t := mk
    {
      WriteId: u64;
      Index: u64;
      Server: chan;
      ContentHash: string;
    }.
End RecordChunkArgs.

Module FinishWriteArgs.
  Record t := mk
    {
      WriteId: u64;
      Keyname: string;
    }.
End FinishWriteArgs.

Module ChunkHandle.
  Record t :=
    mk { addr: chan;
         content_hash: string;
      }.

  #[global]
  Instance into_val : IntoVal t.
  Proof.
    refine {| to_val x := (#(LitInt x.(addr)),
                            (#(LitString x.(content_hash)),
                              #()))%V;
             from_val v :=
               match v with
               | (#(LitInt a), (#(LitString s), #()))%V => Some (mk a s)
               | _ => None
               end;
             IntoVal_def := mk (U64 0) ""
           |}.
    move => [] //=.
  Defined.
End ChunkHandle.

Module DirServer.
  Record t :=
    mk { ongoing: gmap u64 (gmap u64 ChunkHandle.t);
         data: gmap u64 (list ChunkHandle.t);
         nextWriteId: u64;
      }
  .
End DirServer.

Section proof.

Context `{!heapGS Σ}.
Context `{ghost_mapG Σ nat (chan * list u8)}.
Context `{ghost_mapG Σ (u64 * nat) unit}.
Context `{ghost_mapG Σ u64 gname}.

Record dir_names :=
  {
    writeId_gn:gname; (* ghost_map writeId → gname *)
    recorded_gn:gname; (* ghost_map (writeId:u64, index:nat) → unit *)
  }
.

Definition own_PreparedWrite (v:val) (x:PreparedWrite.t) : iProp Σ :=
  ∃ (addrs_sl:Slice.t),
  ⌜v = (#x.(PreparedWrite.Id), (slice_val addrs_sl, #() ))%V⌝ ∗
  readonly (is_slice_small addrs_sl uint64T 1%Qp x.(PreparedWrite.ChunkAddrs))
  (* [∗ list] index ↦ '(addr, _) ∈ chunkhandles, is_chunk_host γchunk? addr *)
.

Implicit Type γd : dir_names.

(* This owned by the client, and is used to decide what the data for this WriteID will be *)
Definition own_WriteId γd (id:u64) (chunkhandles:list (chan * (list u8) )) : iProp Σ :=
  ∃ γid,
    "#Hγid" ∷ id ↪[γd.(writeId_gn)]□ γid ∗
    "Hauth" ∷ ghost_map_auth γid 1 (map_seq 0 chunkhandles)
  (* [∗ list] index ↦ '(addr, _) ∈ chunkhandles, is_chunk_host γchunk? addr *)
.

Definition own_PartialValue (v: val) (x: Map.t ChunkHandle.t) : iProp Σ :=
  ∃ (l: loc), ⌜v = (#l, #())%V⌝ ∗ is_map l 1 x.

Definition own_Value (v: val) (x: list ChunkHandle.t) : iProp Σ :=
  ∃ sl, ⌜v = slice_val sl⌝ ∗
  is_slice sl (struct.t ChunkHandle) 1 x.

Definition own_Server_mem (s: loc) (st: DirServer.t) : iProp Σ :=
    ∃ (ongoing_l: loc) (ongoing_vals: gmap u64 val),
    "ongoing" ∷ s ↦[dir.Server :: "ongoing"] #ongoing_l ∗
    "Hongoing" ∷ map.is_map ongoing_l 1 (ongoing_vals, zero_val (struct.t PartialValue)) ∗
    "Hpartial" ∷ ([∗ map] writeId ↦ v; handle ∈ ongoing_vals; st.(DirServer.ongoing),
                          own_PartialValue v handle) ∗
    "nextWriteId" ∷ s ↦[dir.Server :: "nextWriteId"] #st.(DirServer.nextWriteId)
.

Definition own_Server (s:loc) γd : iProp Σ :=
  ∃ (names: gmap u64 gname) (st: DirServer.t)
    (ongoing_l: loc) (ongoing_vals: gmap u64 val),
    "Hnames" ∷ ghost_map_auth γd.(writeId_gn) 1 names ∗
    "Hmem" ∷ own_Server_mem s st ∗
    "_" ∷ True.


Definition is_Clerk (ck:loc) γd : iProp Σ := True.

Lemma wp_Clerk__PrepareWrite (ck:loc) γd :
  {{{
        is_Clerk ck γd
  }}}
    Clerk__PrepareWrite #ck
  {{{
        v x, RET v; own_PreparedWrite v x ∗
                     own_WriteId γd x.(PreparedWrite.Id) []
  }}}
.
Proof.
Admitted.

(* This is a witness that the client has decided on the data/server at an index for a writeId *)
Definition is_client_writeId_index γd (id:u64) (index:nat) (chunkhandle:chan * list u8) : iProp Σ :=
  ∃ γid, (* id + γ should determine the γid *)
  index ↪[γid]□ chunkhandle
.

Lemma decide_writeId_index γd (id:u64) chunkhandles newchunkhandle :
  own_WriteId γd id chunkhandles ==∗
  own_WriteId γd id (chunkhandles ++ [newchunkhandle]) ∗
  is_client_writeId_index γd id (length chunkhandles) newchunkhandle.
Proof.
Admitted.

Definition is_dir_writeId_index_recorded γd (id:u64) (index:nat) : iProp Σ :=
  (id, index) ↪[γd.(recorded_gn)]□ ()
.

Lemma wp_Clerk__RecordChunk γd (ck:loc) args data :
  {{{
        is_Clerk ck γd ∗
        is_client_writeId_index γd args.(RecordChunkArgs.WriteId) (int.nat args.(RecordChunkArgs.Index))
                           (args.(RecordChunkArgs.Server), data)
        (* own args *)
        (* witness that args.(RecordChunkArgs.Server) stores data with args.(RecordChunkArgs.ContentHash) *)
  }}}
    Clerk__RecordChunk #ck (* #args *)
  {{{
        RET #(); is_dir_writeId_index_recorded γd args.(RecordChunkArgs.WriteId)
                                                         (int.nat args.(RecordChunkArgs.Index))
  }}}
.
Proof.
Admitted.

Definition is_finished_writeId γd (id:u64) chunkhandles : iProp Σ :=
  (* XXX: should be able to to have DfracDiscarded in place of (1:Qp) *)
  ∃ γid, readonly (ghost_map_auth γid 1 (map_seq 0 chunkhandles))
.

Definition object_ptsto γd (key:string) (data:list (list u8)) : iProp Σ :=
 True
.

(* The code is not exactly-once because FinishWrite might run many times. The
   spec cannot take and return ownership of the object_ptsto. *)
Lemma wp_Clerk__FinishWrite γd (ck:loc) args chunkhandles (data newdata : list (list u8)) :
  {{{
        is_Clerk ck γd ∗
        is_finished_writeId γd args.(FinishWriteArgs.WriteId) chunkhandles ∗
        ([∗ list] index ↦ _ ∈ chunkhandles,
          is_dir_writeId_index_recorded γd args.(FinishWriteArgs.WriteId) index) ∗
        ⌜chunkhandles.*2 = newdata⌝ ∗
        object_ptsto γd args.(FinishWriteArgs.Keyname) data
  }}}
    Clerk__FinishWrite #ck (* #args *)
  {{{
        RET #(); object_ptsto γd args.(FinishWriteArgs.Keyname) newdata
  }}}
.
Proof.
Admitted.

End proof.
