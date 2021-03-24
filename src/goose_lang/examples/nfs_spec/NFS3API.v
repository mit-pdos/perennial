From stdpp Require Import decidable countable gmap.
From Coq Require Import List String.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
From Perennial.Helpers Require Import Transitions Integers.
Require Import Extraction.
Set Implicit Arguments.
Open Scope string_scope.

Module NFS3.

Notation "x <- p1 ; p2" := (bind p1 (fun x => p2))
                            (at level 20, p1 at level 100, p2 at level 200, right associativity).
Existing Instance fallback_genBool | 99.

(** Basic types used in NFS operations *)
Inductive err :=
| ERR_PERM
| ERR_NOENT
| ERR_IO
| ERR_NXIO
| ERR_ACCES
| ERR_EXIST
| ERR_XDEV
| ERR_NODEV
| ERR_NOTDIR
| ERR_ISDIR
| ERR_INVAL
| ERR_FBIG
| ERR_NOSPC
| ERR_ROFS
| ERR_MLINK
| ERR_NAMETOOLONG
| ERR_NOTEMPTY
| ERR_DQUOT
| ERR_STALE
| ERR_REMOTE
| ERR_BADHANDLE
| ERR_NOT_SYNC
| ERR_BAD_COOKIE
| ERR_NOTSUPP
| ERR_TOOSMALL
| ERR_SERVERFAULT
| ERR_BADTYPE
| ERR_JUKEBOX
.

Inductive ftype :=
| NF3REG
| NF3DIR
| NF3BLK
| NF3CHR
| NF3LNK
| NF3SOCK
| NF3FIFO
.

Axiom fh : Type.
Axiom fh_eq : fh -> fh -> bool.
Axiom writeverf : Type.
Axiom writeverf_gt : writeverf -> writeverf -> bool.
Axiom writeverf_inc: writeverf -> writeverf.
Axiom createverf : Type.
Axiom createverf_eq : createverf -> createverf -> bool.
Parameter createverfinstance : createverf. (* XXX *)
Axiom cookieverf : Type.
Definition filename := string.

Definition fileid := u64.
Definition cookie := u64.

Record time := {
  time_sec : u32;
  time_nsec : u32;
}.

Global Instance EqDec_time : EqDecision time.
  intro; intros.
  destruct x, y.
  destruct (Z.eq_dec (int.Z time_sec0) (int.Z time_sec1));
  destruct (Z.eq_dec (int.Z time_nsec0) (int.Z time_nsec1)).
(*
  - left; subst; auto.
  - right; subst; congruence.
  - right; subst; congruence.
Defined.
*)
Admitted.

Record major_minor := {
  major : u32;
  minor : u32;
}.

Record fattr := {
  fattr_type : ftype;
  fattr_mode : u32;
  fattr_nlink : u32;
  fattr_uid : u32;
  fattr_gid : u32;
  fattr_size : u64;
  fattr_used : u64;
  fattr_rdev : major_minor;
  fattr_fsid : u64;
  fattr_fileid : fileid;
  fattr_atime : time;
  fattr_mtime : time;
  fattr_ctime : time;
}.

Record wcc_attr := {
  wcc_size : u64;
  wcc_mtime : time;
  wcc_ctime : time;
}.

Record wcc_data := {
  wcc_before : option wcc_attr;
  wcc_after : option wcc_attr;
}.

Definition wcc_data_none := Build_wcc_data None None.

Inductive set_time :=
| SET_TO_CLIENT_TIME (t : time)
| SET_TO_SERVER_TIME
.

Record sattr := {
  sattr_mode : option u32;
  sattr_uid : option u32;
  sattr_gid : option u32;
  sattr_size : option u64;
  sattr_atime : option set_time;
  sattr_mtime : option set_time;
}.

Record dirop := {
  dirop_dir : fh;
  dirop_fn : filename;
}.

Inductive stable :=
| UNSTABLE
| DATA_SYNC
| FILE_SYNC
.

Inductive createhow :=
| UNCHECKED (_ : sattr)
| GUARDED (_ : sattr)
| EXCLUSIVE (_ : createverf)
.

Inductive mknod_type :=
| mknod_chr (_ : major_minor)
| mknod_blk (_ : major_minor)
| mknod_sock
| mknod_fifo
.

Definition post_op_attr := option fattr.
Definition post_op_fh := option fh.

(** Buffers define chunks of data for reads and writes,
    and also the state of a file. *)

(* implicit variables for section --> arguments for section/importer of file *)
Context {buf : Type}.
Context `{!EqDecision buf}.

Parameter read_buf : buf -> u64 -> u32 -> buf.
Parameter write_buf : buf -> u64 -> buf -> buf.
Parameter len_buf : buf -> u64.
Parameter empty_buf : buf.
Parameter resize_buf : u64 -> buf -> buf. (* fill with zero if growing *)

Record async `{Countable T} := { (* {T} {EqDec: DqDecision T} {H: Countable T} *)
  latest : T;
  pending : list T;
}.

Arguments async T {_ _}.
Arguments Build_async {_ _ _}.

Definition possible `{Countable T} (ab : async T) :=
  latest ab :: pending ab.

Definition sync `{Countable T} (v : T) : async T :=
  Build_async v nil.

Definition async_put `{Countable T} (v : T) (a : async T) :=
  Build_async v (possible a).

(** return type wrappers that include an error code *)

Inductive res A T :=
| OK (always : A) (v : T)
| Err (always : A) (e : err)
.

Arguments Err {A T}.

(** Result types of different operations, when the operation
    returns more than one thing *)
Definition res2 A T1 T2 := res A (T1 * T2).
Definition OK2 `(always : A) `(v1 : T1) `(v2 : T2) := OK always (v1, v2).

Record write_ok := {
  write_ok_count : u32;
  write_ok_committed : stable;
  write_ok_verf : writeverf;
}.

Record readdir_entry := {
  readdir_entry_id : fileid;
  readdir_entry_name : filename;
  readdir_entry_cookie : cookie;
}.

Record readdir_ok := {
  readdir_ok_cookieverf : cookieverf;
  readdir_ok_eof : bool;
  readdir_ok_ents : list readdir_entry;
}.

Record readdirplus_entry := {
  readdirplus_entry_id : fileid;
  readdirplus_entry_name : filename;
  readdirplus_entry_cookie : cookie;
  readdirplus_entry_attr : post_op_attr;
  readdirplus_entry_fh : post_op_fh;
}.

Record readdirplus_ok := {
  readdirplus_ok_cookieverf : cookieverf;
  readdirplus_ok_eof : bool;
  readdirplus_ok_ents : list readdirplus_entry;
}.

Record fsstat_ok := {
  fsstat_ok_tbytes : u64;
  fsstat_ok_fbytes : u64;
  fsstat_ok_abytes : u64;
  fsstat_ok_tfiles : u64;
  fsstat_ok_ffiles : u64;
  fsstat_ok_afiles : u64;
  fsstat_ok_invarsec : u32;
}.

Record fsinfo_ok := {
  fsinfo_ok_rtmax : u32;
  fsinfo_ok_rtpref : u32;
  fsinfo_ok_rtmult : u32;
  fsinfo_ok_wtmax : u32;
  fsinfo_ok_wtpref : u32;
  fsinfo_ok_wtmult : u32;
  fsinfo_ok_dtpref : u32;
  fsinfo_ok_maxfilesize : u64;
  fsinfo_ok_time_delta : time;
  fsinfo_ok_properties_link : bool;
  fsinfo_ok_properties_symlink : bool;
  fsinfo_ok_properties_homogeneous : bool;
  fsinfo_ok_properties_cansettime : bool;
}.

Record pathconf_ok := {
  pathconf_ok_linkmax : u32;
  pathconf_ok_name_max : u32;
  pathconf_ok_no_trunc : bool;
  pathconf_ok_chown_restricted : bool;
  pathconf_ok_case_insensitive : bool;
  pathconf_ok_case_preserving : bool;
}.

Inductive Op : Type -> Type :=
| NULL :
    Op unit
| GETATTR (_ : fh) :
    Op (res unit fattr)
| SETATTR (_ : fh) (a : sattr) (ctime_guard : option time) :
    Op (res wcc_data unit)
| LOOKUP (_ : dirop) :
    Op (res2 post_op_attr fh post_op_attr)
| ACCESS (_ : fh) (a : u32) :
    Op (res post_op_attr u32)
| READLINK (_ : fh) :
    Op (res post_op_attr string)
| READ (_ : fh) (off : u64) (count : u32) :
    Op (res2 post_op_attr bool buf)
| WRITE (_ : fh) (off : u64) (_ : stable) (data : buf) :
    Op (res wcc_data write_ok)
| CREATE (_ : dirop) (_ : createhow) :
    Op (res2 wcc_data post_op_fh post_op_attr)
| MKDIR (_ : dirop) (_ : sattr) :
    Op (res2 wcc_data post_op_fh post_op_attr)
| SYMLINK (_ : dirop) (_ : sattr) (_ : filename) :
    Op (res2 wcc_data post_op_fh post_op_attr)
| MKNOD (_ : dirop) (_ : mknod_type) (_ : sattr) :
    Op (res2 wcc_data post_op_fh post_op_attr)
| REMOVE (_ : dirop) :
    Op (res wcc_data unit)
| RMDIR (_ : dirop) :
    Op (res wcc_data unit)
| RENAME (from : dirop) (to : dirop) :
    Op (res (wcc_data * wcc_data) unit)
| LINK (_ : fh) (link : dirop) :
    Op (res (wcc_data * post_op_attr) unit)
| READDIR (_ : fh) (_ : cookie) (_ : cookieverf) (count : u32) :
    Op (res post_op_attr readdir_ok)
| READDIRPLUS (_ : fh) (_ : cookie) (_ : cookieverf) (dircount : u32) (maxcount : u32) :
    Op (res post_op_attr readdirplus_ok)
| FSSTAT (_ : fh) :
    Op (res post_op_attr fsstat_ok)
| FSINFO (_ : fh) :
    Op (res post_op_attr fsinfo_ok)
| PATHCONF (_ : fh) :
    Op (res post_op_attr pathconf_ok)
| COMMIT_BEGIN (_ : fh) (off : u64) (count : u32) :
    Op (res wcc_data Z)
| COMMIT_END (_ : fh) (checkpt : Z) :
    Op (res wcc_data writeverf)
.

Inductive inode_type_state :=
| Ifile (_ : buf) (_ : createverf)
| Idir (_ : gmap filename fh)
| Iblk (_ : major_minor)
| Ichr (_ : major_minor)
| Isymlink (_ : filename)
| Isock
| Ififo
.

Record inode_meta := {
  inode_meta_nlink : u32;
  inode_meta_mode : u32;
  inode_meta_uid : u32;
  inode_meta_gid : u32;
  inode_meta_fileid : fileid;
  inode_meta_atime : time;
  inode_meta_mtime : time;
  inode_meta_ctime : time;
}.

Global Instance eta_inode_meta : Settable _ :=
  settable! Build_inode_meta
    < inode_meta_nlink;
      inode_meta_mode;
      inode_meta_uid;
      inode_meta_gid;
      inode_meta_fileid;
      inode_meta_atime;
      inode_meta_mtime;
      inode_meta_ctime >.

Record inode_state := {
  inode_state_meta : inode_meta;
  inode_state_type : inode_type_state;
  ctr : Z;
}.

Global Instance eta_inode_state : Settable _ :=
  settable! Build_inode_state
    < inode_state_meta; inode_state_type; ctr >.

Global Instance eq_dec_inode_meta : EqDecision inode_meta.
Admitted.

Global Instance eq_dec_inode_state : EqDecision inode_state.
Admitted.

Global Instance countable_inode_state : Countable inode_state.
Admitted.

Global Instance eq_dec_fh : EqDecision fh.
Admitted.

Global Instance countable_fh : Countable fh.
Admitted.

Record State := {
  fhs : gmap fh (async inode_state);
  verf : writeverf;
  clock : time;
  global_ctr : Z;
}.

Global Instance eta_State : Settable _ :=
  settable! Build_State
    < fhs; verf; clock; global_ctr >.

Definition inode_wcc (i : inode_state) : wcc_attr :=
  let m := inode_state_meta i in
  Build_wcc_attr
    ( match (inode_state_type i) with
      | Ifile b _ => len_buf b
      | _ => U64 0
      end )
    (inode_meta_mtime m)
    (inode_meta_ctime m).

Definition inode_crash (i i' : async inode_state) : bool :=
  (existsb (fun (i: inode_state) => bool_decide (i = (latest i'))) (possible i))
  && bool_decide (pending i' = nil).

Definition inode_finish (s : async inode_state) : async inode_state :=
  sync (latest s). (* XXX don't need to update counter here *)

(** Step definitions for each RPC opcode *)
Section SymbolicStep.
  Definition result_bind {A T T'} x (fx: T -> transition State (res A T'))
  : transition State (res A T') :=
    bind x (fun (r : res A T) =>
      match r with
      | OK a v => fx v
      | Err a e => ret (@Err A T' a e) (*undefined*)
      end).

  Notation "x <~- p1 ; p2" := (result_bind p1 (fun x => p2))
                                (at level 54, right associativity, only parsing).

  Definition symBool := suchThatBool (fun (_: State) (_ : bool) => true).
  Definition symU32 := suchThatBool (fun (_: State) (_ : u32) => true).
  Definition symU64 := suchThatBool (fun (_: State) (_ : u64) => true).
  Definition fid_does_not_exist (s: State) (fid: fileid) : bool :=
    fold_left (fun acc x =>
                 match x with
                 | (f,i) => acc && bool_decide (int.Z i.(latest).(inode_state_meta).(inode_meta_fileid) <> int.Z fid)
                 end)
              (gmap_to_list s.(fhs)) true.
  Definition fh_does_not_exist (s: State) (f: fh) : bool :=
    fold_left (fun acc x =>
                 match x with
                 | (f',_) => acc && negb(fh_eq f f')
                 end)
              (gmap_to_list s.(fhs)) true.

  Definition symFID := suchThatBool fid_does_not_exist.
  Definition symFH := suchThatBool fh_does_not_exist.
  Definition symAssert (b:bool): transition State unit := check b.
  Definition call_reads {T : Type} (read_f : State -> T) :=
    s <- reads (fun s => s);
    ret (read_f s).

  Definition call_puts (put_f : State -> State) :=
    s <- reads (fun s => s);
    modify (fun _ => (put_f s)).

  Definition symTime :=
    ts <- symU32;
    tn <- symU32;
    ret (Build_time ts tn).

  Definition null_step : transition State unit :=
    ret tt.

  Definition get_fh {A} (f : fh) (a : A) : transition State (res A inode_state) :=
    i <- call_reads (fun s => s.(fhs) !! f);
    match i with
    | None =>
      z <- symBool;
      if z then
        ret (Err a ERR_STALE)
      else
        ret (Err a ERR_BADHANDLE)
    | Some i => ret (OK a (latest i))
    end.


  Definition inode_attrs (i : inode_state) : transition State fattr :=
    used <- symU64;
    fsid <- symU64;
    non_file_len <- symU64;
    let m := inode_state_meta i in
    let res := Build_fattr
      ( match (inode_state_type i) with
        | Ifile _ _ => NF3REG
        | Idir _ => NF3DIR
        | Iblk _ => NF3BLK
        | Ichr _ => NF3CHR
        | Isymlink _ => NF3LNK
        | Isock => NF3SOCK
        | Ififo => NF3FIFO
        end )
      (inode_meta_mode m)
      (inode_meta_nlink m)
      (inode_meta_uid m)
      (inode_meta_gid m)
      ( match (inode_state_type i) with
        | Ifile b _ => len_buf b
        | _ => non_file_len
        end )
      used
      ( match (inode_state_type i) with
        | Iblk mm => mm
        | Ichr mm => mm
        | _ => Build_major_minor (U32 0) (U32 0)
        end )
      fsid
      (inode_meta_fileid m)
      (inode_meta_atime m)
      (inode_meta_mtime m)
      (inode_meta_ctime m) in
    ret res.

  Definition getattr_step (f : fh) : transition State (res unit fattr) :=
    i <~- get_fh f tt;
    attrs <- inode_attrs i;
    ret (OK tt attrs).

  Definition check_ctime_guard {A} (i : inode_state) (ctime_guard : option time) (a : A)
    : transition State (res A unit) :=
    match ctime_guard with
    | None => ret (OK a tt)
    | Some ct =>
      if (decide (ct = i.(inode_state_meta).(inode_meta_ctime))) then
        ret (OK a tt)
      else
        ret (Err a ERR_NOT_SYNC)
    end.

  Definition time_ge (t t' : time) : bool :=
    orb (bool_decide (int.Z t.(time_sec) <= int.Z t'.(time_sec)))
        (andb (bool_decide (t'.(time_sec) = t.(time_sec)))
              (orb (bool_decide (t'.(time_nsec) = t.(time_nsec)))
                    (bool_decide (int.Z t.(time_nsec) <= int.Z t'.(time_nsec))))).

  Definition get_time : transition State time :=
    t <- call_reads (clock);
    t' <- symTime;
    _ <- symAssert (time_ge t t');
    _ <- call_puts (set clock (const t'));
    ret t'.

  Definition checkpt_ctr : transition State Z :=
    ctr <- call_reads (global_ctr);
    ret ctr.

  Definition get_ctr : transition State Z :=
    ctr <- call_reads (global_ctr);
    _ <- call_puts (set global_ctr (fun _ => ctr + 1));
    ret (ctr + 1).

  Definition set_attr_one {F} (i : inode_state) (now : time)
                              (f : inode_meta -> F)
                              `{!Setter f}
                              (sattr_req : option F) :
                              inode_state :=
    match sattr_req with
    | None => i
    | Some v =>
      i <| inode_state_meta ::=
          fun m => m <| inode_meta_ctime := now |> <| f := v |> |>
    end.

  Definition set_attr_time (i : inode_state) (now : time)
                            (f : inode_meta -> time)
                            `{!Setter f}
                            (sattr_req : option set_time) :
                            inode_state :=
    match sattr_req with
    | None => i
    | Some v =>
      let newtime := match v with
                      | SET_TO_CLIENT_TIME t => t
                      | SET_TO_SERVER_TIME => now
                      end in
      i <| inode_state_meta ::=
            fun m => m <| f := newtime |> <| inode_meta_ctime := now |> |>
    end.

  Definition truncate {A} (i : inode_state) (now : time)
                            (sattr_req : option u64)
                            (a : A)
                            : transition State (res A inode_state) :=
    match sattr_req with
    | None => ret (OK a i)
    | Some len =>
      match i.(inode_state_type) with
      | Ifile buf cverf =>
        outOfSpace <- symBool;
        if andb (bool_decide (int.Z len >? int.Z (len_buf buf))) outOfSpace then
          ret (Err a ERR_NOSPC)
        else
          ret (OK a (i <| inode_state_type := Ifile (resize_buf len buf) cverf |>
                <| inode_state_meta ::= set inode_meta_mtime (const now) |>))
      | _ =>
        ret (Err a ERR_INVAL)
      end
    end.

  Definition update_fh_sync (f : fh) (i : inode_state) : transition State unit :=
    ctr_val <- get_ctr;
    let i := i <| ctr ::= fun val => ctr_val |> in
    ia <- call_reads (fun s => s.(fhs) !! f);
    match ia with
    | None => ret tt
    | Some ia =>
      call_puts (set fhs (fun x => <[f := sync i]> x))
    end.

  Definition sync_at_ctr (checkpt_ctr : Z) (a : async inode_state) :=
    (* flush all pending writes that are older than the inode state to commit *)
    let new_pending := filter (fun (i : inode_state) => checkpt_ctr <=? i.(ctr))
                              (pending a)
    in Build_async (latest a) new_pending.

  Definition put_fh_sync_at_ctr (f : fh) (ctr : Z) : transition State unit :=
    (* don't update the global counter---just flushing some values *)
    ia <- call_reads (fun s => s.(fhs) !! f);
    match ia with
    | None => ret tt
    | Some ia =>
      call_puts (set fhs (fun x => <[f := sync_at_ctr ctr ia]> x))
    end.

  Definition update_fh_async (f : fh) (i : inode_state) : transition State unit :=
    ctr_val <- get_ctr;
    let i := i <| ctr ::= fun val => ctr_val |> in
    ia <- call_reads (fun s => s.(fhs) !! f);
    match ia with
    | None => ret tt
    | Some ia =>
      call_puts (set fhs (fun x => <[f := async_put i ia]> x))
    end.

  Definition set_attr_nonlen (i : inode_state) (now : time) (a : sattr) : inode_state :=
    let i := set_attr_one i now (f := inode_meta_mode) a.(sattr_mode) in
    let i := set_attr_one i now (f := inode_meta_uid) a.(sattr_uid) in
    let i := set_attr_one i now (f := inode_meta_gid) a.(sattr_gid) in
    let i := set_attr_time i now (f := inode_meta_atime) a.(sattr_atime) in
    let i := set_attr_time i now (f := inode_meta_mtime) a.(sattr_mtime) in
    i.

  Definition setattr_step (f : fh) (a : sattr) (ctime_guard : option time) : transition State (res wcc_data unit) :=
    i <~- get_fh f wcc_data_none;
    let wcc_before := inode_wcc i in
    _ <~- check_ctime_guard i ctime_guard (Build_wcc_data (Some wcc_before) (Some wcc_before));
    t <- get_time;
    (*i <~- truncate i t a.(sattr_size) (Build_wcc_data (Some wcc_before) (Some wcc_before));*)
    let i := set_attr_nonlen i t a in
    _ <- update_fh_sync f i;
    ret (OK (Build_wcc_data (Some wcc_before) (Some (inode_wcc i))) tt).

  Definition get_dir {A} (i : inode_state) (a : A) : transition State (res A (gmap filename fh)) :=
      match i.(inode_state_type) with
      | Idir dmap => ret (OK a dmap)
      | _ => ret (Err a ERR_NOTDIR)
      end.

  Definition lookup_step (a : dirop) : transition State (res2 post_op_attr fh post_op_attr) :=
    d <~- get_fh a.(dirop_dir) (@None fattr);
    dattr <- inode_attrs d;
    dm <~- get_dir d (Some dattr);
    match dm !! a.(dirop_fn) with
    | None => ret (Err (Some dattr) ERR_NOENT)
    | Some ffh =>
      i <- call_reads (fun s => s.(fhs) !! ffh);
      match i with
      | None => ret (OK2 (Some dattr) ffh None)
      | Some i =>
        iattr <- inode_attrs (latest i);
        ret (OK2 (Some dattr) ffh (Some iattr))
      end
    end.

  Definition access_step (f : fh) (a : u32) : transition State (res post_op_attr u32) :=
    i <~- get_fh f (@None fattr);
    iattr <- inode_attrs i;
    ret (OK (Some iattr) a).

  Definition readlink_step (f : fh) : transition State (res post_op_attr string) :=
    i <~- get_fh f (@None fattr);
    iattr <- inode_attrs i;
    match i.(inode_state_type) with
    | Isymlink data => ret (OK (Some iattr) data)
    | _ => ret (Err (Some iattr) ERR_INVAL)
    end.

  (* XXX we are ignoring atime on read (and every other operation).
    if we do introduce atime, then we should make it async to avoid
    disk writes on every read. *)
  Definition read_step (f : fh) (off : u64) (count : u32) : transition State (res2 post_op_attr bool buf) :=
    i <~- get_fh f (@None fattr);
    iattr <- inode_attrs i;
    match i.(inode_state_type) with
    | Ifile buf _ =>
      let res := read_buf buf off count in
      let eof := if decide (int.Z (len_buf buf) >? (int.Z off + int.Z count)) then false else true in
      ret (OK2 (Some iattr) eof res)
    | _ => ret (Err (Some iattr) ERR_INVAL)
    end.


  Definition check_space (wcc_before : wcc_attr) (buf buf' : buf) : transition State (res wcc_data Prop) :=
      if (decide (int.Z (len_buf buf') >? int.Z (len_buf buf)))
       then ret (Err (Build_wcc_data (Some wcc_before) (Some wcc_before)) ERR_NOSPC)
       else ret (OK (Build_wcc_data (Some wcc_before) (Some wcc_before)) True).

  Definition write_step (f : fh) (off : u64) (s : stable) (data : buf) : transition State (res wcc_data write_ok) :=
    i <~- get_fh f wcc_data_none;
    let wcc_before := inode_wcc i in
    match i.(inode_state_type) with
    | Ifile buf cverf =>
      t <- get_time;
      wverf <- call_reads verf;
      let buf' := write_buf buf off data in
      _ <~- check_space wcc_before buf buf';
      let i' := i <| inode_state_type := Ifile buf' cverf |>
                  <| inode_state_meta ::= set inode_meta_mtime (const t) |> in
      let wcc := Build_wcc_data (Some (inode_wcc i)) (Some (inode_wcc i')) in
      let wok := Build_write_ok (u32_from_u64 (len_buf data)) s wverf in
      match s with
      | UNSTABLE =>
        _ <- update_fh_async f i';
        ret (OK wcc wok)
      | _ =>
        _ <- update_fh_sync f i';
        ret (OK wcc wok)
      end
    | _ => ret (Err (Build_wcc_data (Some wcc_before) (Some wcc_before)) ERR_INVAL)
    end.

  Definition new_inode_meta : transition State inode_meta :=
    now <- get_time;
    fid <- symFID;
    ret (Build_inode_meta
      (U32 0)(* XXX nlink? *)
      (U32 420) (* mode 0644 *)
      (U32 0)(* uid *)
      (U32 0)(* gid *)
      fid
      now
      now
      now).

  Definition dir_link (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) (f : fh) : transition State unit :=
    now <- get_time;
    ctr_val <- get_ctr;
    let dirmeta := dirmeta <| inode_meta_mtime := now |> in
    let dm := <[a.(dirop_fn) := f]> dm in
    call_puts (set fhs (insert a.(dirop_dir) (sync (Build_inode_state dirmeta (Idir dm) ctr_val)))).

  Definition dir_unlink (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State unit :=
    now <- get_time;
    ctr_val <- get_ctr;
    let dirmeta := dirmeta <| inode_meta_mtime := now |> in
    let dm := delete a.(dirop_fn) dm in
    call_puts (set fhs (insert a.(dirop_dir) (sync (Build_inode_state dirmeta (Idir dm) ctr_val)))).

  Definition create_unchecked_step (a : dirop) (attr : sattr) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res2 unit post_op_fh post_op_attr) :=
    ctr_val <- get_ctr;
    f <- match dm !! a.(dirop_fn) with
          | Some curfh => ret curfh
          | None =>
            f <- symFH;
            m <- new_inode_meta;
            _ <- call_puts (set fhs (insert f (sync (Build_inode_state m (Ifile empty_buf createverfinstance) ctr_val))));
            _ <- dir_link a dirmeta dm f;
            ret f
          end;
    i <- call_reads (fun s => s.(fhs) !! f);
    match i with
    | None => ret (Err tt ERR_SERVERFAULT)
    | Some i =>
      now <- get_time;
      let i := i.(latest) in
      let i := match attr.(sattr_size) with
                | None => i
                | Some len =>
                  match i.(inode_state_type) with
                  | Ifile buf cverf =>
                    i <| inode_state_type := Ifile (resize_buf len buf) cverf |>
                      <| inode_state_meta ::= set inode_meta_mtime (const now) |>
                  | _ => i
                  end
                end in
      let i := set_attr_nonlen i now attr in
      _ <- update_fh_sync f i;
      iattr <- inode_attrs i;
      ret (OK2 tt (Some f) (Some iattr))
    end.

  Definition create_guarded_step (a : dirop) (attr : sattr) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res2 unit post_op_fh post_op_attr) :=
    ctr_val <- get_ctr;
    match dm !! a.(dirop_fn) with
    | Some curfh => ret (Err tt ERR_EXIST)
    | None =>
      f <- symFH;
      m <- new_inode_meta;
      now <- get_time;
      let i := match attr.(sattr_size) with
                | None => Build_inode_state m (Ifile empty_buf createverfinstance) ctr_val
                | Some len => Build_inode_state m (Ifile (resize_buf len empty_buf) createverfinstance) ctr_val
                end in
      let i := set_attr_nonlen i now attr in
      _ <- update_fh_sync f i;
      _ <- dir_link a dirmeta dm f;
      iattr <- inode_attrs i;
      ret (OK2 tt (Some f) (Some iattr))
    end.

  Definition create_exclusive_step (a : dirop) (cverf : createverf)
             (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res2 unit post_op_fh post_op_attr) :=
    match dm !! a.(dirop_fn) with
    | Some curfh =>
      i <- call_reads (fun s => s.(fhs) !! curfh);
      match i with
      | None => ret (Err tt ERR_SERVERFAULT)
      | Some i => let i := i.(latest) in
        match i.(inode_state_type) with
        | Ifile _ v =>
          if (createverf_eq v cverf) then
            iattr <- inode_attrs i;
            ret (OK2 tt (Some curfh) (Some iattr))
          else
            ret (Err tt ERR_EXIST)
        | _ =>
          ret (Err tt ERR_EXIST)
        end
      end
    | None =>
      f <- symFH;
      m <- new_inode_meta;
      ctr_val <- get_ctr;
      let i := Build_inode_state m (Ifile empty_buf cverf) ctr_val in
      _ <- update_fh_sync f i;
      _ <- dir_link a dirmeta dm f;
      iattr <- inode_attrs i;
      ret (OK2 tt (Some f) (Some iattr))
    end.

  Definition create_like_core (a : dirop) (core : inode_meta -> gmap filename fh -> transition State (res2 unit post_op_fh post_op_attr))
    : transition State (res2 wcc_data post_op_fh post_op_attr) :=
      d <~- get_fh a.(dirop_dir) wcc_data_none;

      let wcc_before := Some (inode_wcc d) in
      let wcc_ro := Build_wcc_data wcc_before wcc_before in

      plus (ret (Err wcc_ro ERR_NOSPC))
           (
             dm <~- get_dir d wcc_ro;
             r <- core d.(inode_state_meta) dm;

             d_after <- call_reads (fun s => s.(fhs) !! a.(dirop_dir));
             let wcc_after := match d_after with
                              | None => None
                              | Some d_after => Some (inode_wcc d_after.(latest))
                              end in
             let wcc := Build_wcc_data wcc_before wcc_after in

             ret (match r with
                | Err _ e => Err wcc e
                | OK _ v => OK wcc v
                  end)
           ).

  Definition create_step (a : dirop) (h : createhow) : transition State (res2 wcc_data post_op_fh post_op_attr) :=
    create_like_core a
      (match h with
        | GUARDED attr => create_guarded_step a attr
        | UNCHECKED attr => create_unchecked_step a attr
        | EXCLUSIVE cv => create_exclusive_step a cv
        end).

  Definition mkdir_core (a : dirop) (attr : sattr)
             (dirmeta : inode_meta) (dm : gmap filename fh)
    : transition State (res2 unit post_op_fh post_op_attr) :=
    match dm !! a.(dirop_fn) with
    | Some curfh => ret (Err tt ERR_EXIST)
    | None =>
      h <- symFH;
      m <- new_inode_meta;
      now <- get_time;
      ctr_val <- get_ctr;
      let dm := ∅ in
      let dm := <["." := h]> dm in
      let dm := <[".." := a.(dirop_dir)]> dm in
      let i := Build_inode_state m (Idir dm) ctr_val in
      let i := set_attr_nonlen i now attr in
      _ <- update_fh_sync h i;
      _ <- dir_link a dirmeta dm h;
      iattr <- inode_attrs i;
      ret (OK2 tt (Some h) (Some iattr))
    end.

  Definition mkdir_step (a : dirop) (attr : sattr) : transition State (res2 wcc_data post_op_fh post_op_attr) :=
    create_like_core a (mkdir_core a attr).

  Definition symlink_core (a : dirop) (attr : sattr) (data : filename) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res2 unit post_op_fh post_op_attr) :=
    match dm !! a.(dirop_fn) with
    | Some curfh => ret (Err tt ERR_EXIST)
    | None =>
      h <- symFH;
      m <- new_inode_meta;
      now <- get_time;
      ctr_val <- get_ctr;
      let i := Build_inode_state m (Isymlink data) ctr_val in
      let i := set_attr_nonlen i now attr in
      _ <- update_fh_sync h i;
      _ <- dir_link a dirmeta dm h;
      iattr <- inode_attrs i;
      ret (OK2 tt (Some h) (Some iattr))
    end.

  Definition symlink_step (a : dirop) (attr : sattr) (data : filename) : transition State (res2 wcc_data post_op_fh post_op_attr) :=
    create_like_core a (symlink_core a attr data).

  Definition mknod_core (a : dirop) (attr : sattr) (ft : mknod_type) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res2 unit post_op_fh post_op_attr) :=
    match dm !! a.(dirop_fn) with
    | Some curfh => ret (Err tt ERR_EXIST)
    | None =>
      h <- symFH;
      m <- new_inode_meta;
      now <- get_time;
      ctr_val <- get_ctr;
      let t := match ft with
                | mknod_chr mm => Ichr mm
                | mknod_blk mm => Iblk mm
                | mknod_sock => Isock
                | mknod_fifo => Ififo
                end in
      let i := Build_inode_state m t ctr_val in
      let i := set_attr_nonlen i now attr in
      _ <- update_fh_sync h i;
      _ <- dir_link a dirmeta dm h;
      iattr <- inode_attrs i;
      ret (OK2 tt (Some h) (Some iattr))
    end.

  Definition mknod_step (a : dirop) (ft : mknod_type) (attr : sattr) : transition State (res2 wcc_data post_op_fh post_op_attr) :=
    create_like_core a (mknod_core a attr ft).

  Definition remove_like_core (a : dirop) (core : inode_meta -> gmap filename fh -> transition State (res unit unit)) : transition State (res wcc_data unit) :=
    d <~- get_fh a.(dirop_dir) wcc_data_none;

    let wcc_before := Some (inode_wcc d) in
    let wcc_ro := Build_wcc_data wcc_before wcc_before in

    dm <~- get_dir d wcc_ro;
    r <- core d.(inode_state_meta) dm;

    d_after <- call_reads (fun s => s.(fhs) !! a.(dirop_dir));
    let wcc_after := match d_after with
                      | None => None
                      | Some d_after => Some (inode_wcc d_after.(latest))
                      end in
    let wcc := Build_wcc_data wcc_before wcc_after in

    ret (match r with
          | Err _ e => Err wcc e
          | OK _ v => OK wcc v
          end).

  Definition count_links_dir (count_fh : fh) (dir_fh : fh) : Z :=
    if (decide (count_fh = dir_fh)) then 1 else 0.

  Definition add_up `{Countable T} (m : gmap T Z) : Z :=
    map_fold (fun k v acc => acc + v) 0 m.

  Definition count_links (fh : fh) (i : inode_state) : Z :=
    match inode_state_type i with
    | Idir d => add_up ((count_links_dir fh) <$> d)
    | _ => 0
    end.

  Definition gc_fh (h : fh) : transition State unit :=
    nlink <- call_reads (fun s => add_up ((count_links h) <$> (latest <$> s.(fhs))));
    if (decide (nlink = 0)) then call_puts (set fhs (delete h)) else ret tt.

  Definition remove_core (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res unit unit) :=
    match dm !! a.(dirop_fn) with
    | None => ret (Err tt ERR_NOENT)
    | Some curfh =>
      i <- call_reads (fun s => s.(fhs) !! curfh);
      match i with
      | None => ret (Err tt ERR_SERVERFAULT)
      | Some i => let i := i.(latest) in
        match i.(inode_state_type) with
        | Idir _ => ret (Err tt ERR_INVAL) (* XXX oddly, not allowed in RFC1813?? *)
        | _ =>
          _ <- dir_unlink a dirmeta dm;
          _ <- gc_fh curfh;
          ret (OK tt tt)
        end
      end
    end.

  Definition remove_step (a : dirop) : transition State (res wcc_data unit) :=
    remove_like_core a (remove_core a).

  Definition rmdir_core (a : dirop) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res unit unit) :=
    if (decide (a.(dirop_fn) = ".")) then ret (Err tt ERR_INVAL) else
    if (decide (a.(dirop_fn) = "..")) then ret (Err tt ERR_INVAL) else
    match dm !! a.(dirop_fn) with
    | None => ret (Err tt ERR_NOENT)
    | Some curfh =>
      i <- call_reads (fun s => s.(fhs) !! curfh);
      match i with
      | None => ret (Err tt ERR_SERVERFAULT)
      | Some i => let i := i.(latest) in
        match i.(inode_state_type) with
        | Idir m =>
          let names := dom (gset filename) m in
          if (decide ((size names) = Z.to_nat 2)) then
            _ <- dir_unlink a dirmeta dm;
            _ <- gc_fh curfh;
            ret (OK tt tt)
          else
            ret (Err tt ERR_NOTEMPTY)
        | _ => ret (Err tt ERR_NOTDIR)
        end
      end
    end.

  Definition rmdir_step (a : dirop) : transition State (res wcc_data unit) :=
    remove_like_core a (rmdir_core a).

  Definition rename_core (from to : dirop) (from_dirmeta to_dirmeta : inode_meta)
             (from_dm to_dm : gmap filename fh)
    : transition State (res unit unit) :=
    plus (ret (Err tt ERR_NOSPC))
    (if (decide (from.(dirop_fn) = ".")) then ret (Err tt ERR_INVAL) else
      if (decide (from.(dirop_fn) = "..")) then ret (Err tt ERR_INVAL) else
      if (decide (to.(dirop_fn) = ".")) then ret (Err tt ERR_INVAL) else
      if (decide (to.(dirop_fn) = "..")) then ret (Err tt ERR_INVAL) else
      match from_dm !! from.(dirop_fn) with
      | None => ret (Err tt ERR_NOENT)
      | Some src_h =>
        match to_dm !! to.(dirop_fn) with
        | None =>
          _ <- dir_link to to_dirmeta to_dm src_h;
          _ <- dir_unlink from from_dirmeta from_dm;
          ret (OK tt tt)
        | Some dst_h =>
          src_i <- call_reads (fun s => s.(fhs) !! src_h);
          dst_i <- call_reads (fun s => s.(fhs) !! dst_h);
          match src_i, dst_i with
          | Some src_i, Some dst_i =>
            let src_i := src_i.(latest) in
            let dst_i := dst_i.(latest) in

            match src_i.(inode_state_type), dst_i.(inode_state_type) with
            | Idir src_dm, Idir dst_dm =>
              let dst_names := dom (gset filename) dst_dm in
              if (decide (size dst_names = Z.to_nat 2)) then
                _ <- dir_unlink to to_dirmeta to_dm;
                _ <- dir_unlink from from_dirmeta from_dm;
                _ <- dir_link to to_dirmeta to_dm src_h;
                _ <- gc_fh dst_h;
                ret (OK tt tt)
              else
                ret (Err tt ERR_EXIST)
            | Idir _, _ => ret (Err tt ERR_EXIST)
            | _, Idir _ => ret (Err tt ERR_EXIST)
            | _, _ =>
              _ <- dir_unlink to to_dirmeta to_dm;
              _ <- dir_unlink from from_dirmeta from_dm;
              _ <- dir_link to to_dirmeta to_dm src_h;
              _ <- gc_fh dst_h;
              ret (OK tt tt)
            end
          | _, _ => ret (Err tt ERR_SERVERFAULT)
          end
        end
      end).

  (* XXX rename allows a client to form loops in the directory structure,
    and to make it unreachable from the root. *)

  Definition rename_step (from to : dirop) : transition State (res (wcc_data * wcc_data) unit) :=
    from_d <~- get_fh from.(dirop_dir) (wcc_data_none, wcc_data_none);
    to_d <~- get_fh to.(dirop_dir) (wcc_data_none, wcc_data_none);

    let wcc_from_before := Some (inode_wcc from_d) in
    let wcc_to_before := Some (inode_wcc to_d) in
    let wcc_ro := ( Build_wcc_data wcc_from_before wcc_from_before,
                    Build_wcc_data wcc_to_before wcc_to_before ) in

    from_dm <~- get_dir from_d wcc_ro;
    to_dm <~- get_dir to_d wcc_ro;

    r <- rename_core from to from_d.(inode_state_meta) to_d.(inode_state_meta) from_dm to_dm;

    from_d_after <- call_reads (fun s => s.(fhs) !! from.(dirop_dir));
    to_d_after <- call_reads (fun s => s.(fhs) !! to.(dirop_dir));
    let wcc_from_after := match from_d_after with
                          | None => None
                          | Some from_d_after => Some (inode_wcc from_d_after.(latest))
                          end in
    let wcc_to_after := match to_d_after with
                        | None => None
                        | Some to_d_after => Some (inode_wcc to_d_after.(latest))
                        end in
    let wcc := ( Build_wcc_data wcc_from_before wcc_from_after,
                  Build_wcc_data wcc_to_before wcc_to_after ) in

    ret (match r with
          | Err _ e => Err wcc e
          | OK _ v => OK wcc v
          end).

  Definition link_core (link : dirop) (h : fh) (i : inode_state) (dirmeta : inode_meta) (dm : gmap filename fh) : transition State (res unit unit) :=
    plus (ret (Err tt ERR_NOSPC))
    (match i.(inode_state_type) with
      | Idir _ => ret (Err tt ERR_INVAL)
      | _ =>
        match dm !! link.(dirop_fn) with
        | None =>
          _ <- dir_link link dirmeta dm h;
          ret (OK tt tt)
        | Some curfh =>
          ret (Err tt ERR_EXIST)
        end
      end).

  Definition link_step (h : fh) (link : dirop) : transition State (res (wcc_data * post_op_attr) unit) :=
    i <~- get_fh h (wcc_data_none, (@None fattr));
    d <~- get_fh link.(dirop_dir) (wcc_data_none, (@None fattr));

    let wcc_before := Some (inode_wcc d) in
    let wcc_ro := (Build_wcc_data wcc_before wcc_before, (@None fattr)) in

    dm <~- get_dir d wcc_ro;
    r <- link_core link h i d.(inode_state_meta) dm;

    d_after <- call_reads (fun s => s.(fhs) !! link.(dirop_dir));
    let wcc_after := match d_after with
                      | None => None
                      | Some d_after => Some (inode_wcc d_after.(latest))
                      end in
    iattr_after <- inode_attrs i;
    let wcc := (Build_wcc_data wcc_before wcc_after, Some iattr_after) in

    ret (match r with
          | Err _ e => Err wcc e
          | OK _ v => OK wcc v
          end).

  Definition readdir_step (h : fh) (c : cookie) (cv : cookieverf) (count : u32) : transition State (res post_op_attr readdir_ok) :=
    ret (Err None ERR_NOTSUPP).

  Definition readdirplus_step (h : fh) (c : cookie) (cv : cookieverf) (dircount : u32) (maxcount : u32) : transition State (res post_op_attr readdirplus_ok) :=
    ret (Err None ERR_NOTSUPP).

  Definition fsstat_step (h : fh) : transition State (res post_op_attr fsstat_ok) :=
    i <~- get_fh h (@None fattr);
    iattr <- inode_attrs i;
    st <- suchThatBool (fun _ st => bool_decide
      (int.Z st.(fsstat_ok_fbytes) <= int.Z st.(fsstat_ok_tbytes) ∧
      int.Z st.(fsstat_ok_abytes) <= int.Z st.(fsstat_ok_fbytes) ∧
      int.Z st.(fsstat_ok_ffiles) <= int.Z st.(fsstat_ok_tfiles) ∧
      int.Z st.(fsstat_ok_afiles) <= int.Z st.(fsstat_ok_ffiles)));
    ret (OK (Some iattr) st).

  Definition fsinfo_step (h : fh) : transition State (res post_op_attr fsinfo_ok) :=
    i <~- get_fh h (@None fattr);
    iattr <- inode_attrs i;
    info <- suchThatBool (fun _ info =>
      (bool_decide (info.(fsinfo_ok_time_delta) = (Build_time (U32 0) (U32 1)))) &&
      info.(fsinfo_ok_properties_link) &&
      info.(fsinfo_ok_properties_symlink) &&
      info.(fsinfo_ok_properties_homogeneous) &&
      info.(fsinfo_ok_properties_cansettime));
    ret (OK (Some iattr) info).

  Definition pathconf_step (h : fh) : transition State (res post_op_attr pathconf_ok) :=
    i <~- get_fh h (@None fattr);
    iattr <- inode_attrs i;
    pc <- suchThatBool (fun _ pc =>
      pc.(pathconf_ok_no_trunc) &&
      negb pc.(pathconf_ok_case_insensitive) &&
      pc.(pathconf_ok_case_preserving));
    ret (OK (Some iattr) pc).

  Definition commit_begin_step (h : fh) (off: u64) (count: u32): transition State (res wcc_data Z) :=
    i_before <~- get_fh h wcc_data_none;
    checkpt <- checkpt_ctr;
    let wcc_before := inode_wcc i_before in
    let wcc := Build_wcc_data (Some wcc_before) (Some wcc_before) in
    ret (OK wcc checkpt).

  Definition commit_end_step (h : fh) (checkpt: Z) : transition State (res wcc_data writeverf) :=
    i_after <~- get_fh h wcc_data_none;
    let wcc_after := inode_wcc i_after in
    let wcc := Build_wcc_data (Some wcc_after) (Some wcc_after) in
    wverf <- call_reads verf;
    match i_after.(inode_state_type) with
    | Ifile buf cverf =>
      _ <- put_fh_sync_at_ctr h checkpt;
      ret (OK wcc wverf)
    | _ =>
      ret (OK wcc wverf)
    end.
End SymbolicStep.

Definition states_inodes_crash_consistent (s s': State) : bool :=
    (fold_left (fun acc x =>
                 match x with
                 | (f,i) => acc && match (s'.(fhs) !! f) with
                             | Some i' => inode_crash i i'
                             | None => false
                                  end
                 end)
              (gmap_to_list s.(fhs)) true) &&
    (fold_left (fun acc x =>
                 match x with
                 | (f,i) => acc && match (s.(fhs) !! f) with
                             | Some i' => inode_crash i i'
                             | None => false
                                  end
               end)
              (gmap_to_list s'.(fhs)) true).

Definition nfs_crash_step : transition State unit :=
  s' <- suchThatBool (fun (s s' : State) =>
    states_inodes_crash_consistent s s' &&
    writeverf_gt s'.(verf) s.(verf) &&
    time_ge s.(clock) s'.(clock));
  _ <- call_puts (fun _ => s');
  ret tt.

Definition nfs_finish_step : transition State unit :=
  _ <- call_puts (fun s =>
    let s := s <| fhs ::= base.fmap inode_finish |> in
    let s := s <| verf ::= fun x => writeverf_inc x |> in
    s);
  ret tt.

Definition OpSemantics Op State := forall T, Op T -> relation.t State T.
Definition CrashSemantics State := relation.t State unit.
Definition FinishSemantics State := relation.t State unit.

Record Dynamics Op State :=
  { step: OpSemantics Op State;
    crash_step: CrashSemantics State;
    finish_step: FinishSemantics State;
  }.

Extraction Language JSON.
(*Recursive Extraction setattr_step getattr_step. (*getattr_step setattr_step commit_step.*)*)

Definition nfs3op_to_transition {T} (op : Op T): transition State T :=
  match op with
        | NULL => null_step
        | GETATTR h => getattr_step h
        | SETATTR h attr ctime_guard => setattr_step h attr ctime_guard
        | LOOKUP a => lookup_step a
        | ACCESS h a => access_step h a
        | READLINK h => readlink_step h
        | READ h off count => read_step h off count
        | WRITE h off stab data => write_step h off stab data
        | CREATE a how => create_step a how
        | MKDIR a attr => mkdir_step a attr
        | SYMLINK a attr name => symlink_step a attr name
        | MKNOD a ft attr => mknod_step a ft attr
        | REMOVE a => remove_step a
        | RMDIR a => rmdir_step a
        | RENAME from to => rename_step from to
        | LINK h link => link_step h link
        | READDIR h c cverf count => readdir_step h c cverf count
        | READDIRPLUS h c cverf dircount maxcount => readdirplus_step h c cverf dircount maxcount
        | FSSTAT h => fsstat_step h
        | FSINFO h => fsinfo_step h
        | PATHCONF h => pathconf_step h
        | COMMIT_BEGIN h off count => commit_begin_step h off count
        | COMMIT_END h checkpt => commit_end_step h checkpt
  end.


Definition nfs3step : OpSemantics Op State := fun T (op : Op T) => relation.denote (nfs3op_to_transition op).

Definition dynamics : Dynamics Op State :=
  {| step := nfs3step;
      crash_step := relation.denote nfs_crash_step;
      finish_step := relation.denote nfs_finish_step;
  |}.

Lemma getattr_always_err (s: State) (f: fh) a2 e2 s1 s2 ret1 ret2 :
  (dynamics.(step) (GETATTR f)) s s1 ret1->
  (dynamics.(step) (GETATTR f)) s1 s2 ret2 ->
  ret2 = (Err a2 e2) ->
  exists a1 e1, ret1 = (Err a1 e1).
Proof.
  intros.
  inversion H0; subst.
  destruct x as [x | x].
  (* 2nd step returns OK, clearly wrong *)
  - repeat (monad_inv; simpl in *). discriminate.
  (* 2nd step returns ERR, remember resulting state for first step *)
  - repeat (simpl in *; monad_inv).
    inversion H3; subst.
    destruct ((fhs s1) !! f) eqn:He.
    * repeat (monad_inv; simpl in *). discriminate.
    * inversion H; subst.
              assert (s = s1).
              {
                assert (s2 = s).
                {
                  repeat (simpl in H1; monad_inv).
                  destruct (fhs s !! f) eqn:Hes;
                  repeat (simpl in H1; monad_inv); auto.
                  destruct H5; repeat (simpl in H1; monad_inv); auto.
                } subst.
                destruct x0 as [x0 | x0]; repeat (simpl in *; monad_inv); auto.
              }
              subst.
              destruct x0 as [x0 | x0]; repeat (simpl in *; monad_inv); rewrite He in *;
              simpl in H1; monad_inv.
              -- destruct x5; simpl in H1; monad_inv; discriminate.
              -- destruct x2; eauto.
Qed.

Lemma crash_total_ok (s: State):
  exists s', dynamics.(crash_step) s s' tt.
Proof.
  (*repeat (eexists; econstructor).
  instantiate (1 := base.fmap inode_finish s).
  rewrite lookup_fmap.
  destruct (s !! fh) eqn:He; rewrite He; simpl; auto.
  destruct i; simpl; auto.
  destruct f; simpl; auto.
  intuition.
  eapply elem_of_union; right.
  eapply elem_of_singleton; auto.*)
Admitted.

(*Lemma crash_non_err_ok (s: State) ret:
  dynamics.(crash_step) s ret () -> ret ≠ Err.
Proof.
  (*
  intros.
  destruct ret; try congruence.
  repeat intuition || match goal with
  | H: _ _ Err |- _ => inversion H; clear H
  | H: _ _ _ Err |- _ => inversion H; clear H
  | H: ∃ _, _ |- _ => destruct H
  end.*)
Admitted.

Lemma finish_total_ok (s: State):
  exists s', dynamics.(finish_step) s (Val s' tt).
Proof.
  repeat (eexists; econstructor).
Qed.

Lemma finish_non_err_ok (s: State) ret:
  dynamics.(finish_step) s ret -> ret ≠ Err.
Proof.
  intros.
  destruct ret; try congruence.
  repeat intuition || match goal with
  | H: _ _ Err |- _ => inversion H; clear H
  | H: _ _ _ Err |- _ => inversion H; clear H
  | H: ∃ _, _ |- _ => destruct H
  end.
Qed.

Definition l : Layer Op :=
  {| Layer.OpState := State;
      sem := dynamics;
      trace_proj := fun _ => nil;
      crash_preserves_trace := fun _ _ _ => eq_refl;
      crash_total := crash_total_ok;
      finish_total := finish_total_ok;
      crash_non_err := crash_non_err_ok;
      finish_non_err := finish_non_err_ok;
      initP := fun s => s = ∅ |}.
*)
End NFS3.
