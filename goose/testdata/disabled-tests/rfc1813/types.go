package rfc1813

const PROGRAM uint32 = 100003
const VERSION uint32 = 3
const NFS3_FHSIZE uint32 = 64
const NFS3_COOKIEVERFSIZE uint32 = 8
const NFS3_CREATEVERFSIZE uint32 = 8
const NFS3_WRITEVERFSIZE uint32 = 8

type Uint64 uint64
type Uint32 uint32
type Filename3 string
type Nfspath3 string
type Fileid3 Uint64
type Cookie3 Uint64
type Cookieverf3 [NFS3_COOKIEVERFSIZE]byte
type Createverf3 [NFS3_CREATEVERFSIZE]byte
type Writeverf3 [NFS3_WRITEVERFSIZE]byte
type Uid3 Uint32
type Gid3 Uint32
type Size3 Uint64
type Offset3 Uint64
type Mode3 Uint32
type Count3 Uint32
type Nfsstat3 uint32

const NFS3_OK Nfsstat3 = 0
const NFS3ERR_PERM Nfsstat3 = 1
const NFS3ERR_NOENT Nfsstat3 = 2
const NFS3ERR_IO Nfsstat3 = 5
const NFS3ERR_NXIO Nfsstat3 = 6
const NFS3ERR_ACCES Nfsstat3 = 13
const NFS3ERR_EXIST Nfsstat3 = 17
const NFS3ERR_XDEV Nfsstat3 = 18
const NFS3ERR_NODEV Nfsstat3 = 19
const NFS3ERR_NOTDIR Nfsstat3 = 20
const NFS3ERR_ISDIR Nfsstat3 = 21
const NFS3ERR_INVAL Nfsstat3 = 22
const NFS3ERR_FBIG Nfsstat3 = 27
const NFS3ERR_NOSPC Nfsstat3 = 28
const NFS3ERR_ROFS Nfsstat3 = 30
const NFS3ERR_MLINK Nfsstat3 = 31
const NFS3ERR_NAMETOOLONG Nfsstat3 = 63
const NFS3ERR_NOTEMPTY Nfsstat3 = 66
const NFS3ERR_DQUOT Nfsstat3 = 69
const NFS3ERR_STALE Nfsstat3 = 70
const NFS3ERR_REMOTE Nfsstat3 = 71
const NFS3ERR_BADHANDLE Nfsstat3 = 10001
const NFS3ERR_NOT_SYNC Nfsstat3 = 10002
const NFS3ERR_BAD_COOKIE Nfsstat3 = 10003
const NFS3ERR_NOTSUPP Nfsstat3 = 10004
const NFS3ERR_TOOSMALL Nfsstat3 = 10005
const NFS3ERR_SERVERFAULT Nfsstat3 = 10006
const NFS3ERR_BADTYPE Nfsstat3 = 10007
const NFS3ERR_JUKEBOX Nfsstat3 = 10008

type Ftype3 uint32

const NF3REG Ftype3 = 1
const NF3DIR Ftype3 = 2
const NF3BLK Ftype3 = 3
const NF3CHR Ftype3 = 4
const NF3LNK Ftype3 = 5
const NF3SOCK Ftype3 = 6
const NF3FIFO Ftype3 = 7

type Specdata3 struct {
	Specdata1 Uint32
	Specdata2 Uint32
}
type Nfs_fh3 struct {
	Data []byte
}
type Nfstime3 struct {
	Seconds  Uint32
	Nseconds Uint32
}
type Fattr3 struct {
	Ftype  Ftype3
	Mode   Mode3
	Nlink  Uint32
	Uid    Uid3
	Gid    Gid3
	Size   Size3
	Used   Size3
	Rdev   Specdata3
	Fsid   Uint64
	Fileid Fileid3
	Atime  Nfstime3
	Mtime  Nfstime3
	Ctime  Nfstime3
}
type Post_op_attr struct {
	Attributes_follow bool
	Attributes        Fattr3
}
type Wcc_attr struct {
	Size  Size3
	Mtime Nfstime3
	Ctime Nfstime3
}
type Pre_op_attr struct {
	Attributes_follow bool
	Attributes        Wcc_attr
}
type Wcc_data struct {
	Before Pre_op_attr
	After  Post_op_attr
}
type Post_op_fh3 struct {
	Handle_follows bool
	Handle         Nfs_fh3
}
type Time_how uint32

const DONT_CHANGE Time_how = 0
const SET_TO_SERVER_TIME Time_how = 1
const SET_TO_CLIENT_TIME Time_how = 2

type Set_mode3 struct {
	Set_it bool
	Mode   Mode3
}
type Set_uid3 struct {
	Set_it bool
	Uid    Uid3
}
type Set_gid3 struct {
	Set_it bool
	Gid    Gid3
}
type Set_size3 struct {
	Set_it bool
	Size   Size3
}
type Set_atime struct {
	Set_it Time_how
	Atime  Nfstime3
}
type Set_mtime struct {
	Set_it Time_how
	Mtime  Nfstime3
}
type Sattr3 struct {
	Mode  Set_mode3
	Uid   Set_uid3
	Gid   Set_gid3
	Size  Set_size3
	Atime Set_atime
	Mtime Set_mtime
}
type Diropargs3 struct {
	Dir  Nfs_fh3
	Name Filename3
}

const NFS_PROGRAM uint32 = 100003
const NFS_V3 uint32 = 3
const NFSPROC3_NULL uint32 = 0
const NFSPROC3_GETATTR uint32 = 1
const NFSPROC3_SETATTR uint32 = 2
const NFSPROC3_LOOKUP uint32 = 3
const NFSPROC3_ACCESS uint32 = 4
const NFSPROC3_READLINK uint32 = 5
const NFSPROC3_READ uint32 = 6
const NFSPROC3_WRITE uint32 = 7
const NFSPROC3_CREATE uint32 = 8
const NFSPROC3_MKDIR uint32 = 9
const NFSPROC3_SYMLINK uint32 = 10
const NFSPROC3_MKNOD uint32 = 11
const NFSPROC3_REMOVE uint32 = 12
const NFSPROC3_RMDIR uint32 = 13
const NFSPROC3_RENAME uint32 = 14
const NFSPROC3_LINK uint32 = 15
const NFSPROC3_READDIR uint32 = 16
const NFSPROC3_READDIRPLUS uint32 = 17
const NFSPROC3_FSSTAT uint32 = 18
const NFSPROC3_FSINFO uint32 = 19
const NFSPROC3_PATHCONF uint32 = 20
const NFSPROC3_COMMIT uint32 = 21

type GETATTR3args struct {
	Object Nfs_fh3
}
type GETATTR3resok struct {
	Obj_attributes Fattr3
}
type GETATTR3res struct {
	Status Nfsstat3
	Resok  GETATTR3resok
}
type Sattrguard3 struct {
	Check     bool
	Obj_ctime Nfstime3
}
type SETATTR3args struct {
	Object         Nfs_fh3
	New_attributes Sattr3
	Guard          Sattrguard3
}
type SETATTR3resok struct {
	Obj_wcc Wcc_data
}
type SETATTR3resfail struct {
	Obj_wcc Wcc_data
}
type SETATTR3res struct {
	Status  Nfsstat3
	Resok   SETATTR3resok
	Resfail SETATTR3resfail
}
type LOOKUP3args struct {
	What Diropargs3
}
type LOOKUP3resok struct {
	Object         Nfs_fh3
	Obj_attributes Post_op_attr
	Dir_attributes Post_op_attr
}
type LOOKUP3resfail struct {
	Dir_attributes Post_op_attr
}
type LOOKUP3res struct {
	Status  Nfsstat3
	Resok   LOOKUP3resok
	Resfail LOOKUP3resfail
}

const ACCESS3_READ uint32 = 0x0001
const ACCESS3_LOOKUP uint32 = 0x0002
const ACCESS3_MODIFY uint32 = 0x0004
const ACCESS3_EXTEND uint32 = 0x0008
const ACCESS3_DELETE uint32 = 0x0010
const ACCESS3_EXECUTE uint32 = 0x0020

type ACCESS3args struct {
	Object Nfs_fh3
	Access Uint32
}
type ACCESS3resok struct {
	Obj_attributes Post_op_attr
	Access         Uint32
}
type ACCESS3resfail struct {
	Obj_attributes Post_op_attr
}
type ACCESS3res struct {
	Status  Nfsstat3
	Resok   ACCESS3resok
	Resfail ACCESS3resfail
}
type READLINK3args struct {
	Symlink Nfs_fh3
}
type READLINK3resok struct {
	Symlink_attributes Post_op_attr
	Data               Nfspath3
}
type READLINK3resfail struct {
	Symlink_attributes Post_op_attr
}
type READLINK3res struct {
	Status  Nfsstat3
	Resok   READLINK3resok
	Resfail READLINK3resfail
}
type READ3args struct {
	File   Nfs_fh3
	Offset Offset3
	Count  Count3
}
type READ3resok struct {
	File_attributes Post_op_attr
	Count           Count3
	Eof             bool
	Data            []byte
}
type READ3resfail struct {
	File_attributes Post_op_attr
}
type READ3res struct {
	Status  Nfsstat3
	Resok   READ3resok
	Resfail READ3resfail
}
type Stable_how uint32

const UNSTABLE Stable_how = 0
const DATA_SYNC Stable_how = 1
const FILE_SYNC Stable_how = 2

type WRITE3args struct {
	File   Nfs_fh3
	Offset Offset3
	Count  Count3
	Stable Stable_how
	Data   []byte
}
type WRITE3resok struct {
	File_wcc  Wcc_data
	Count     Count3
	Committed Stable_how
	Verf      Writeverf3
}
type WRITE3resfail struct {
	File_wcc Wcc_data
}
type WRITE3res struct {
	Status  Nfsstat3
	Resok   WRITE3resok
	Resfail WRITE3resfail
}
type Createmode3 uint32

const UNCHECKED Createmode3 = 0
const GUARDED Createmode3 = 1
const EXCLUSIVE Createmode3 = 2

type Createhow3 struct {
	Mode           Createmode3
	Obj_attributes Sattr3
	Verf           Createverf3
}
type CREATE3args struct {
	Where Diropargs3
	How   Createhow3
}
type CREATE3resok struct {
	Obj            Post_op_fh3
	Obj_attributes Post_op_attr
	Dir_wcc        Wcc_data
}
type CREATE3resfail struct {
	Dir_wcc Wcc_data
}
type CREATE3res struct {
	Status  Nfsstat3
	Resok   CREATE3resok
	Resfail CREATE3resfail
}
type MKDIR3args struct {
	Where      Diropargs3
	Attributes Sattr3
}
type MKDIR3resok struct {
	Obj            Post_op_fh3
	Obj_attributes Post_op_attr
	Dir_wcc        Wcc_data
}
type MKDIR3resfail struct {
	Dir_wcc Wcc_data
}
type MKDIR3res struct {
	Status  Nfsstat3
	Resok   MKDIR3resok
	Resfail MKDIR3resfail
}
type Symlinkdata3 struct {
	Symlink_attributes Sattr3
	Symlink_data       Nfspath3
}
type SYMLINK3args struct {
	Where   Diropargs3
	Symlink Symlinkdata3
}
type SYMLINK3resok struct {
	Obj            Post_op_fh3
	Obj_attributes Post_op_attr
	Dir_wcc        Wcc_data
}
type SYMLINK3resfail struct {
	Dir_wcc Wcc_data
}
type SYMLINK3res struct {
	Status  Nfsstat3
	Resok   SYMLINK3resok
	Resfail SYMLINK3resfail
}
type Devicedata3 struct {
	Dev_attributes Sattr3
	Spec           Specdata3
}
type Mknoddata3 struct {
	Ftype           Ftype3
	Device          Devicedata3
	Pipe_attributes Sattr3
}
type MKNOD3args struct {
	Where Diropargs3
	What  Mknoddata3
}
type MKNOD3resok struct {
	Obj            Post_op_fh3
	Obj_attributes Post_op_attr
	Dir_wcc        Wcc_data
}
type MKNOD3resfail struct {
	Dir_wcc Wcc_data
}
type MKNOD3res struct {
	Status  Nfsstat3
	Resok   MKNOD3resok
	Resfail MKNOD3resfail
}
type REMOVE3args struct {
	Object Diropargs3
}
type REMOVE3resok struct {
	Dir_wcc Wcc_data
}
type REMOVE3resfail struct {
	Dir_wcc Wcc_data
}
type REMOVE3res struct {
	Status  Nfsstat3
	Resok   REMOVE3resok
	Resfail REMOVE3resfail
}
type RMDIR3args struct {
	Object Diropargs3
}
type RMDIR3resok struct {
	Dir_wcc Wcc_data
}
type RMDIR3resfail struct {
	Dir_wcc Wcc_data
}
type RMDIR3res struct {
	Status  Nfsstat3
	Resok   RMDIR3resok
	Resfail RMDIR3resfail
}
type RENAME3args struct {
	From Diropargs3
	To   Diropargs3
}
type RENAME3resok struct {
	Fromdir_wcc Wcc_data
	Todir_wcc   Wcc_data
}
type RENAME3resfail struct {
	Fromdir_wcc Wcc_data
	Todir_wcc   Wcc_data
}
type RENAME3res struct {
	Status  Nfsstat3
	Resok   RENAME3resok
	Resfail RENAME3resfail
}
type LINK3args struct {
	File Nfs_fh3
	Link Diropargs3
}
type LINK3resok struct {
	File_attributes Post_op_attr
	Linkdir_wcc     Wcc_data
}
type LINK3resfail struct {
	File_attributes Post_op_attr
	Linkdir_wcc     Wcc_data
}
type LINK3res struct {
	Status  Nfsstat3
	Resok   LINK3resok
	Resfail LINK3resfail
}
type READDIR3args struct {
	Dir        Nfs_fh3
	Cookie     Cookie3
	Cookieverf Cookieverf3
	Count      Count3
}
type Entry3 struct {
	Fileid    Fileid3
	Name      Filename3
	Cookie    Cookie3
	Nextentry *Entry3
}
type Dirlist3 struct {
	Entries *Entry3
	Eof     bool
}
type READDIR3resok struct {
	Dir_attributes Post_op_attr
	Cookieverf     Cookieverf3
	Reply          Dirlist3
}
type READDIR3resfail struct {
	Dir_attributes Post_op_attr
}
type READDIR3res struct {
	Status  Nfsstat3
	Resok   READDIR3resok
	Resfail READDIR3resfail
}
type READDIRPLUS3args struct {
	Dir        Nfs_fh3
	Cookie     Cookie3
	Cookieverf Cookieverf3
	Dircount   Count3
	Maxcount   Count3
}
type Entryplus3 struct {
	Fileid          Fileid3
	Name            Filename3
	Cookie          Cookie3
	Name_attributes Post_op_attr
	Name_handle     Post_op_fh3
	Nextentry       *Entryplus3
}
type Dirlistplus3 struct {
	Entries *Entryplus3
	Eof     bool
}
type READDIRPLUS3resok struct {
	Dir_attributes Post_op_attr
	Cookieverf     Cookieverf3
	Reply          Dirlistplus3
}
type READDIRPLUS3resfail struct {
	Dir_attributes Post_op_attr
}
type READDIRPLUS3res struct {
	Status  Nfsstat3
	Resok   READDIRPLUS3resok
	Resfail READDIRPLUS3resfail
}
type FSSTAT3args struct {
	Fsroot Nfs_fh3
}
type FSSTAT3resok struct {
	Obj_attributes Post_op_attr
	Tbytes         Size3
	Fbytes         Size3
	Abytes         Size3
	Tfiles         Size3
	Ffiles         Size3
	Afiles         Size3
	Invarsec       Uint32
}
type FSSTAT3resfail struct {
	Obj_attributes Post_op_attr
}
type FSSTAT3res struct {
	Status  Nfsstat3
	Resok   FSSTAT3resok
	Resfail FSSTAT3resfail
}

const FSF3_LINK uint32 = 0x0001
const FSF3_SYMLINK uint32 = 0x0002
const FSF3_HOMOGENEOUS uint32 = 0x0008
const FSF3_CANSETTIME uint32 = 0x0010

type FSINFO3args struct {
	Fsroot Nfs_fh3
}
type FSINFO3resok struct {
	Obj_attributes Post_op_attr
	Rtmax          Uint32
	Rtpref         Uint32
	Rtmult         Uint32
	Wtmax          Uint32
	Wtpref         Uint32
	Wtmult         Uint32
	Dtpref         Uint32
	Maxfilesize    Size3
	Time_delta     Nfstime3
	Properties     Uint32
}
type FSINFO3resfail struct {
	Obj_attributes Post_op_attr
}
type FSINFO3res struct {
	Status  Nfsstat3
	Resok   FSINFO3resok
	Resfail FSINFO3resfail
}
type PATHCONF3args struct {
	Object Nfs_fh3
}
type PATHCONF3resok struct {
	Obj_attributes   Post_op_attr
	Linkmax          Uint32
	Name_max         Uint32
	No_trunc         bool
	Chown_restricted bool
	Case_insensitive bool
	Case_preserving  bool
}
type PATHCONF3resfail struct {
	Obj_attributes Post_op_attr
}
type PATHCONF3res struct {
	Status  Nfsstat3
	Resok   PATHCONF3resok
	Resfail PATHCONF3resfail
}
type COMMIT3args struct {
	File   Nfs_fh3
	Offset Offset3
	Count  Count3
}
type COMMIT3resok struct {
	File_wcc Wcc_data
	Verf     Writeverf3
}
type COMMIT3resfail struct {
	File_wcc Wcc_data
}
type COMMIT3res struct {
	Status  Nfsstat3
	Resok   COMMIT3resok
	Resfail COMMIT3resfail
}

const MNTPATHLEN3 uint32 = 1024
const MNTNAMLEN3 uint32 = 255
const FHSIZE3 uint32 = 64

type Fhandle3 []byte
type Dirpath3 string
type Name3 string
type Mountstat3 uint32

const MNT3_OK Mountstat3 = 0
const MNT3ERR_PERM Mountstat3 = 1
const MNT3ERR_NOENT Mountstat3 = 2
const MNT3ERR_IO Mountstat3 = 5
const MNT3ERR_ACCES Mountstat3 = 13
const MNT3ERR_NOTDIR Mountstat3 = 20
const MNT3ERR_INVAL Mountstat3 = 22
const MNT3ERR_NAMETOOLONG Mountstat3 = 63
const MNT3ERR_NOTSUPP Mountstat3 = 10004
const MNT3ERR_SERVERFAULT Mountstat3 = 10006
const MOUNT_PROGRAM uint32 = 100005
const MOUNT_V3 uint32 = 3
const MOUNTPROC3_NULL uint32 = 0
const MOUNTPROC3_MNT uint32 = 1
const MOUNTPROC3_DUMP uint32 = 2
const MOUNTPROC3_UMNT uint32 = 3
const MOUNTPROC3_UMNTALL uint32 = 4
const MOUNTPROC3_EXPORT uint32 = 5

type Mountres3_ok struct {
	Fhandle      Fhandle3
	Auth_flavors []uint32
}
type Mountres3 struct {
	Fhs_status Mountstat3
	Mountinfo  Mountres3_ok
}
type Mount3 struct {
	Ml_hostname  Name3
	Ml_directory Dirpath3
	Ml_next      *Mount3
}
type Mountopt3 struct{ P *Mount3 }
type Groups3 struct {
	Gr_name Name3
	Gr_next *Groups3
}
type Exports3 struct {
	Ex_dir    Dirpath3
	Ex_groups *Groups3
	Ex_next   *Exports3
}
type Exportsopt3 struct{ P *Exports3 }
