From Perennial.program_proof Require Import grove_prelude.

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
