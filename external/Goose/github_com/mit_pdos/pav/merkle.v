(* autogenerated from github.com/mit-pdos/pav/merkle *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_com.goose_lang.std.
From Goose Require github_com.mit_pdos.pav.cryptoffi.
From Goose Require github_com.mit_pdos.pav.cryptoutil.
From Goose Require github_com.mit_pdos.pav.marshalutil.
From Goose Require github_com.tchajed.marshal.

Section code.
Context `{ext_ty: ext_types}.

(* merkle.go *)

Definition emptyNodeTag : expr := #(U8 0).

Definition leafNodeTag : expr := #(U8 1).

Definition innerNodeTag : expr := #(U8 2).

Definition Tree := struct.decl [
  "ctx" :: ptrT;
  "root" :: ptrT
].

(* node contains the union of different node types, which distinguish as:
    1. empty node. if node ptr is nil.
    2. leaf node. if child0 and child1 nil. has hash, label, and val.
    3. inner node. else. has hash. *)
Definition node := struct.decl [
  "hash" :: slice.T byteT;
  "child0" :: ptrT;
  "child1" :: ptrT;
  "label" :: slice.T byteT;
  "val" :: slice.T byteT
].

Definition context := struct.decl [
  "emptyHash" :: slice.T byteT
].

Definition compLeafHash: val :=
  rec: "compLeafHash" "label" "val" :=
    let: "hr" := cryptoffi.NewHasher #() in
    cryptoffi.Hasher__Write "hr" (SliceSingleton leafNodeTag);;
    cryptoffi.Hasher__Write "hr" (marshal.WriteInt slice.nil (slice.len "label"));;
    cryptoffi.Hasher__Write "hr" "label";;
    cryptoffi.Hasher__Write "hr" (marshal.WriteInt slice.nil (slice.len "val"));;
    cryptoffi.Hasher__Write "hr" "val";;
    cryptoffi.Hasher__Sum "hr" slice.nil.

Definition setLeafHash: val :=
  rec: "setLeafHash" "n" :=
    struct.storeF node "hash" "n" (compLeafHash (struct.loadF node "label" "n") (struct.loadF node "val" "n"));;
    #().

(* getBit returns false if the nth bit of b is 0.
   if n exceeds b, it returns false.
   this is fine as long as the code consistently treats labels as
   having variable length. *)
Definition getBit: val :=
  rec: "getBit" "b" "n" :=
    let: "slot" := "n" `quot` #8 in
    (if: "slot" < (slice.len "b")
    then
      let: "off" := "n" `rem` #8 in
      let: "x" := SliceGet byteT "b" "slot" in
      ("x" `and` (#(U8 1) ≪ "off")) ≠ #(U8 0)
    else #false).

(* getChild returns a child and its sibling child,
   relative to the bit referenced by label and depth. *)
Definition getChild: val :=
  rec: "getChild" "n" "label" "depth" :=
    (if: (~ (getBit "label" "depth"))
    then (struct.fieldRef node "child0" "n", struct.loadF node "child1" "n")
    else (struct.fieldRef node "child1" "n", struct.loadF node "child0" "n")).

Definition getNodeHash: val :=
  rec: "getNodeHash" "n" "c" :=
    (if: "n" = #null
    then struct.loadF context "emptyHash" "c"
    else struct.loadF node "hash" "n").

Definition compInnerHash: val :=
  rec: "compInnerHash" "child0" "child1" "h" :=
    let: "hr" := cryptoffi.NewHasher #() in
    cryptoffi.Hasher__Write "hr" (SliceSingleton innerNodeTag);;
    cryptoffi.Hasher__Write "hr" "child0";;
    cryptoffi.Hasher__Write "hr" "child1";;
    cryptoffi.Hasher__Sum "hr" "h".

Definition setInnerHash: val :=
  rec: "setInnerHash" "n" "c" :=
    let: "child0" := getNodeHash (struct.loadF node "child0" "n") "c" in
    let: "child1" := getNodeHash (struct.loadF node "child1" "n") "c" in
    struct.storeF node "hash" "n" (compInnerHash "child0" "child1" slice.nil);;
    #().

Definition put: val :=
  rec: "put" "n0" "depth" "label" "val" "ctx" :=
    let: "n" := ![ptrT] "n0" in
    (if: "n" = #null
    then
      let: "leaf" := struct.new node [
        "label" ::= "label";
        "val" ::= "val"
      ] in
      "n0" <-[ptrT] "leaf";;
      setLeafHash "leaf";;
      #()
    else
      (if: ((struct.loadF node "child0" "n") = #null) && ((struct.loadF node "child1" "n") = #null)
      then
        (if: std.BytesEqual (struct.loadF node "label" "n") "label"
        then
          struct.storeF node "val" "n" "val";;
          setLeafHash "n";;
          #()
        else
          let: "inner" := struct.new node [
          ] in
          "n0" <-[ptrT] "inner";;
          let: ("leafChild", <>) := getChild "inner" (struct.loadF node "label" "n") "depth" in
          "leafChild" <-[ptrT] "n";;
          let: ("recurChild", <>) := getChild "inner" "label" "depth" in
          "put" "recurChild" ("depth" + #1) "label" "val" "ctx";;
          setInnerHash "inner" "ctx";;
          #())
      else
        let: ("c", <>) := getChild "n" "label" "depth" in
        "put" "c" ("depth" + #1) "label" "val" "ctx";;
        setInnerHash "n" "ctx";;
        #())).

(* Put adds (label, val) to the tree, storing immutable references to both.
   for liveness (not safety) reasons, it returns an error
   if the label does not have a fixed length. *)
Definition Tree__Put: val :=
  rec: "Tree__Put" "t" "label" "val" :=
    (if: (slice.len "label") ≠ cryptoffi.HashLen
    then #true
    else
      put (struct.fieldRef Tree "root" "t") #0 "label" "val" (struct.loadF Tree "ctx" "t");;
      #false).

Definition getProofLen: val :=
  rec: "getProofLen" "depth" :=
    (((((#8 + ("depth" * cryptoffi.HashLen)) + #1) + #8) + cryptoffi.HashLen) + #8) + #32.

(* find returns whether label path was found (and if so, the found label and val)
   and the sibling proof. *)
Definition find: val :=
  rec: "find" "label" "getProof" "ctx" "n" "depth" :=
    (if: "n" = #null
    then
      let: "proof" := ref (zero_val (slice.T byteT)) in
      (if: "getProof"
      then "proof" <-[slice.T byteT] (NewSliceWithCap byteT #8 (getProofLen "depth"))
      else #());;
      (#false, slice.nil, slice.nil, ![slice.T byteT] "proof")
    else
      (if: ((struct.loadF node "child0" "n") = #null) && ((struct.loadF node "child1" "n") = #null)
      then
        let: "proof" := ref (zero_val (slice.T byteT)) in
        (if: "getProof"
        then "proof" <-[slice.T byteT] (NewSliceWithCap byteT #8 (getProofLen "depth"))
        else #());;
        (#true, struct.loadF node "label" "n", struct.loadF node "val" "n", ![slice.T byteT] "proof")
      else
        let: ("child", "sib") := getChild "n" "label" "depth" in
        let: ((("f", "fl"), "fv"), "proof0") := "find" "label" "getProof" "ctx" (![ptrT] "child") ("depth" + #1) in
        let: "proof" := ref_to (slice.T byteT) "proof0" in
        (if: "getProof"
        then "proof" <-[slice.T byteT] (SliceAppendSlice byteT (![slice.T byteT] "proof") (getNodeHash "sib" "ctx"))
        else #());;
        ("f", "fl", "fv", ![slice.T byteT] "proof"))).

Definition Tree__prove: val :=
  rec: "Tree__prove" "t" "label" "getProof" :=
    let: ((("found", "foundLabel"), "foundVal"), "proof0") := find "label" "getProof" (struct.loadF Tree "ctx" "t") (struct.loadF Tree "root" "t") #0 in
    let: "proof" := ref_to (slice.T byteT) "proof0" in
    (if: "getProof"
    then UInt64Put (![slice.T byteT] "proof") ((slice.len (![slice.T byteT] "proof")) - #8)
    else #());;
    (if: (~ "found")
    then
      (if: "getProof"
      then
        "proof" <-[slice.T byteT] (marshal.WriteBool (![slice.T byteT] "proof") #false);;
        "proof" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "proof") #0);;
        "proof" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "proof") #0)
      else #());;
      (#false, slice.nil, ![slice.T byteT] "proof")
    else
      (if: (~ (std.BytesEqual "foundLabel" "label"))
      then
        (if: "getProof"
        then
          "proof" <-[slice.T byteT] (marshal.WriteBool (![slice.T byteT] "proof") #true);;
          "proof" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "proof") (slice.len "foundLabel"));;
          "proof" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "proof") "foundLabel");;
          "proof" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "proof") (slice.len "foundVal"));;
          "proof" <-[slice.T byteT] (marshal.WriteBytes (![slice.T byteT] "proof") "foundVal")
        else #());;
        (#false, slice.nil, ![slice.T byteT] "proof")
      else
        (if: "getProof"
        then
          "proof" <-[slice.T byteT] (marshal.WriteBool (![slice.T byteT] "proof") #false);;
          "proof" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "proof") #0);;
          "proof" <-[slice.T byteT] (marshal.WriteInt (![slice.T byteT] "proof") #0)
        else #());;
        (#true, "foundVal", ![slice.T byteT] "proof"))).

(* Get returns if label is in the tree and if so, the val. *)
Definition Tree__Get: val :=
  rec: "Tree__Get" "t" "label" :=
    let: (("in", "val"), <>) := Tree__prove "t" "label" #false in
    ("in", "val").

(* Prove returns if label is in tree (and if so, the val) and
   a cryptographic proof of this. *)
Definition Tree__Prove: val :=
  rec: "Tree__Prove" "t" "label" :=
    Tree__prove "t" "label" #true.

(* MerkleProof from serde.go *)

(* MerkleProof has non-nil leaf data for non-membership proofs
   that terminate in a different leaf. *)
Definition MerkleProof := struct.decl [
  "Siblings" :: slice.T byteT;
  "FoundOtherLeaf" :: boolT;
  "LeafLabel" :: slice.T byteT;
  "LeafVal" :: slice.T byteT
].

(* MerkleProofDecode from serde.out.go *)

Definition MerkleProofDecode: val :=
  rec: "MerkleProofDecode" "b0" :=
    let: (("a1", "b1"), "err1") := marshalutil.ReadSlice1D "b0" in
    (if: "err1"
    then (slice.nil, slice.nil, #true)
    else
      let: (("a2", "b2"), "err2") := marshalutil.ReadBool "b1" in
      (if: "err2"
      then (slice.nil, slice.nil, #true)
      else
        let: (("a3", "b3"), "err3") := marshalutil.ReadSlice1D "b2" in
        (if: "err3"
        then (slice.nil, slice.nil, #true)
        else
          let: (("a4", "b4"), "err4") := marshalutil.ReadSlice1D "b3" in
          (if: "err4"
          then (slice.nil, slice.nil, #true)
          else
            (struct.new MerkleProof [
               "Siblings" ::= "a1";
               "FoundOtherLeaf" ::= "a2";
               "LeafLabel" ::= "a3";
               "LeafVal" ::= "a4"
             ], "b4", #false))))).

(* compEmptyHash from merkle.go *)

Definition compEmptyHash: val :=
  rec: "compEmptyHash" <> :=
    cryptoutil.Hash (SliceSingleton emptyNodeTag).

Definition verifySiblings: val :=
  rec: "verifySiblings" "label" "lastHash" "siblings" "dig" :=
    let: "sibsLen" := slice.len "siblings" in
    (if: ("sibsLen" `rem` cryptoffi.HashLen) ≠ #0
    then #true
    else
      let: "currHash" := ref_to (slice.T byteT) "lastHash" in
      let: "hashOut" := ref_to (slice.T byteT) (NewSliceWithCap byteT #0 cryptoffi.HashLen) in
      let: "maxDepth" := "sibsLen" `quot` cryptoffi.HashLen in
      let: "depthInv" := ref (zero_val uint64T) in
      Skip;;
      (for: (λ: <>, (![uint64T] "depthInv") < "maxDepth"); (λ: <>, "depthInv" <-[uint64T] ((![uint64T] "depthInv") + #1)) := λ: <>,
        let: "begin" := (![uint64T] "depthInv") * cryptoffi.HashLen in
        let: "end" := ((![uint64T] "depthInv") + #1) * cryptoffi.HashLen in
        let: "sib" := SliceSubslice byteT "siblings" "begin" "end" in
        let: "depth" := ("maxDepth" - (![uint64T] "depthInv")) - #1 in
        (if: (~ (getBit "label" "depth"))
        then "hashOut" <-[slice.T byteT] (compInnerHash (![slice.T byteT] "currHash") "sib" (![slice.T byteT] "hashOut"))
        else "hashOut" <-[slice.T byteT] (compInnerHash "sib" (![slice.T byteT] "currHash") (![slice.T byteT] "hashOut")));;
        "currHash" <-[slice.T byteT] (SliceAppendSlice byteT (SliceTake (![slice.T byteT] "currHash") #0) (![slice.T byteT] "hashOut"));;
        "hashOut" <-[slice.T byteT] (SliceTake (![slice.T byteT] "hashOut") #0);;
        Continue);;
      (~ (std.BytesEqual (![slice.T byteT] "currHash") "dig"))).

(* Verify verifies proof against the tree rooted at dig
   and returns an error upon failure.
   there are two types of inputs:
   if inTree, (label, val) should be in the tree.
   if !inTree, label should not be in the tree. *)
Definition Verify: val :=
  rec: "Verify" "inTree" "label" "val" "proof" "dig" :=
    let: (("proofDec", <>), "err0") := MerkleProofDecode "proof" in
    (if: "err0"
    then #true
    else
      (if: (struct.loadF MerkleProof "FoundOtherLeaf" "proofDec") && (std.BytesEqual "label" (struct.loadF MerkleProof "LeafLabel" "proofDec"))
      then #true
      else
        let: "lastHash" := ref (zero_val (slice.T byteT)) in
        (if: "inTree"
        then "lastHash" <-[slice.T byteT] (compLeafHash "label" "val")
        else
          (if: struct.loadF MerkleProof "FoundOtherLeaf" "proofDec"
          then "lastHash" <-[slice.T byteT] (compLeafHash (struct.loadF MerkleProof "LeafLabel" "proofDec") (struct.loadF MerkleProof "LeafVal" "proofDec"))
          else "lastHash" <-[slice.T byteT] (compEmptyHash #())));;
        verifySiblings "label" (![slice.T byteT] "lastHash") (struct.loadF MerkleProof "Siblings" "proofDec") "dig")).

Definition Tree__Digest: val :=
  rec: "Tree__Digest" "t" :=
    getNodeHash (struct.loadF Tree "root" "t") (struct.loadF Tree "ctx" "t").

Definition NewTree: val :=
  rec: "NewTree" <> :=
    let: "c" := struct.new context [
      "emptyHash" ::= compEmptyHash #()
    ] in
    struct.new Tree [
      "ctx" ::= "c"
    ].

(* serde.go *)

(* serde.out.go *)

(* Auto-generated from spec "github.com/mit-pdos/pav/merkle/serde.go"
   using compiler "github.com/mit-pdos/pav/serde". *)

Definition MerkleProofEncode: val :=
  rec: "MerkleProofEncode" "b0" "o" :=
    let: "b" := ref_to (slice.T byteT) "b0" in
    "b" <-[slice.T byteT] (marshalutil.WriteSlice1D (![slice.T byteT] "b") (struct.loadF MerkleProof "Siblings" "o"));;
    "b" <-[slice.T byteT] (marshal.WriteBool (![slice.T byteT] "b") (struct.loadF MerkleProof "FoundOtherLeaf" "o"));;
    "b" <-[slice.T byteT] (marshalutil.WriteSlice1D (![slice.T byteT] "b") (struct.loadF MerkleProof "LeafLabel" "o"));;
    "b" <-[slice.T byteT] (marshalutil.WriteSlice1D (![slice.T byteT] "b") (struct.loadF MerkleProof "LeafVal" "o"));;
    ![slice.T byteT] "b".

End code.
