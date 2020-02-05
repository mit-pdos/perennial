(declare-datatypes ((major_minor 0)) (((Build_major_minor (Build_major_minor_0 (_ BitVec 32)) (Build_major_minor_1 (_ BitVec 32))))))
(declare-datatypes ((inode_type_state 0)) (((Ifile (Ifile_0 String) (Ifile_1 (_ BitVec 64))) (Idir (Idir_0 (Array String option_fh))) (Iblk (Iblk_0 major_minor)) (Ichr (Ichr_0 major_minor)) (Isymlink (Isymlink_0 String)) (Isock) (Ififo))))
(declare-datatypes ((time 0)) (((Build_time (Build_time_0 (_ BitVec 32)) (Build_time_1 (_ BitVec 32))))))
(declare-datatypes ((inode_meta 0)) (((Build_inode_meta (Build_inode_meta_0 (_ BitVec 32)) (Build_inode_meta_1 (_ BitVec 32)) (Build_inode_meta_2 (_ BitVec 32)) (Build_inode_meta_3 (_ BitVec 32)) (Build_inode_meta_4 (_ BitVec 64)) (Build_inode_meta_5 time) (Build_inode_meta_6 time) (Build_inode_meta_7 time)))))
(declare-datatypes ((inode_state 0)) (((Build_inode_state (Build_inode_state_0 inode_meta) (Build_inode_state_1 inode_type_state)))))
(declare-datatypes ((async_inode_state 0)) (((Build_async (Build_async_0 inode_state) (Build_async_1 (Seq inode_state))))))
(declare-datatypes ((option_async 0)) (((Some (Some_0 async_inode_state)) (None))))
(declare-datatypes ((ftype 0)) (((NF3REG) (NF3DIR) (NF3BLK) (NF3CHR) (NF3LNK) (NF3SOCK) (NF3FIFO))))
(declare-datatypes ((fattr 0)) (((Build_fattr (Build_fattr_0 ftype) (Build_fattr_1 (_ BitVec 32)) (Build_fattr_2 (_ BitVec 32)) (Build_fattr_3 (_ BitVec 32)) (Build_fattr_4 (_ BitVec 32)) (Build_fattr_5 (_ BitVec 64)) (Build_fattr_6 (_ BitVec 64)) (Build_fattr_7 major_minor) (Build_fattr_8 (_ BitVec 64)) (Build_fattr_9 (_ BitVec 64)) (Build_fattr_10 time) (Build_fattr_11 time) (Build_fattr_12 time)))))
(declare-datatypes ((option_fh 0)) (((Some (Some_0 String)) (None))))
(declare-datatypes ((unit 0)) (((Tt))))
(declare-datatypes ((err 0)) (((ERR_PERM) (ERR_NOENT) (ERR_IO) (ERR_NXIO) (ERR_ACCES) (ERR_EXIST) (ERR_XDEV) (ERR_NODEV) (ERR_NOTDIR) (ERR_ISDIR) (ERR_INVAL) (ERR_FBIG) (ERR_NOSPC) (ERR_ROFS) (ERR_MLINK) (ERR_NAMETOOLONG) (ERR_NOTEMPTY) (ERR_DQUOT) (ERR_STALE) (ERR_REMOTE) (ERR_BADHANDLE) (ERR_NOT_SYNC) (ERR_BAD_COOKIE) (ERR_NOTSUPP) (ERR_TOOSMALL) (ERR_SERVERFAULT) (ERR_BADTYPE) (ERR_JUKEBOX))))
(declare-datatypes ((res_unit_fattr 0)) (((OK (OK_0 unit) (OK_1 fattr)) (Err (Err_0 unit) (Err_1 err)))))
(declare-datatypes ((state 0)) (((Build_State (Build_State_0 (Array String option_async)) (Build_State_1 (_ BitVec 64)) (Build_State_2 time)))))
(declare-datatypes ((bool 0)) (((True) (False))))
(declare-fun anon9 () bool)
(declare-fun s_init () state)
(declare-fun anon11 () (_ BitVec 64))
(declare-fun anon10 () (_ BitVec 64))
(declare-fun anon12 () (_ BitVec 64))
(assert (let ((a!1 (Build_async_0 (Some_0 (select (Build_State_0 s_init)
                                          "\x01\x00\x01\x00\x00\x00\x00\x00")))))
(let ((a!2 (ite ((_ is (Isymlink (String) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3LNK
                (ite ((_ is (Isock () inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3SOCK
                     NF3FIFO)))
      (a!5 ((_ int2bv 64) (str.len (Ifile_0 (Build_inode_state_1 a!1)))))
      (a!6 (ite ((_ is (Iblk (major_minor) inode_type_state))
                  (Build_inode_state_1 a!1))
                (Iblk_0 (Build_inode_state_1 a!1))
                (ite ((_ is (Ichr (major_minor) inode_type_state))
                       (Build_inode_state_1 a!1))
                     (Ichr_0 (Build_inode_state_1 a!1))
                     (Build_major_minor #x00000000 #x00000000)))))
(let ((a!3 (ite ((_ is (Iblk (major_minor) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3BLK
                (ite ((_ is (Ichr (major_minor) inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3CHR
                     a!2))))
(let ((a!4 (ite ((_ is (Ifile (String (_ BitVec 64)) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3REG
                (ite ((_ is (Idir ((Array String option_fh)) inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3DIR
                     a!3))))
(let ((a!7 (Build_fattr a!4
                        (Build_inode_meta_1 (Build_inode_state_0 a!1))
                        (Build_inode_meta_0 (Build_inode_state_0 a!1))
                        (Build_inode_meta_2 (Build_inode_state_0 a!1))
                        (Build_inode_meta_3 (Build_inode_state_0 a!1))
                        (ite ((_ is
                                 (Ifile (String (_ BitVec 64)) inode_type_state))
                               (Build_inode_state_1 a!1))
                             a!5
                             anon12)
                        anon10
                        a!6
                        anon11
                        (Build_inode_meta_4 (Build_inode_state_0 a!1))
                        (Build_inode_meta_5 (Build_inode_state_0 a!1))
                        (Build_inode_meta_6 (Build_inode_state_0 a!1))
                        (Build_inode_meta_7 (Build_inode_state_0 a!1)))))
(let ((a!8 (ite ((_ is (Some (async_inode_state) option_async))
                  (select (Build_State_0 s_init)
                          "\x01\x00\x01\x00\x00\x00\x00\x00"))
                (OK Tt a!7)
                (ite ((_ is (True () bool)) anon9)
                     (Err Tt ERR_STALE)
                     (Err Tt ERR_BADHANDLE)))))
  (= a!8
     (OK Tt
         (Build_fattr NF3DIR
                      #x000001ed
                      #x0000001b
                      #x00000000
                      #x00000000
                      #x0000000000001000
                      #x0000000000001000
                      (Build_major_minor #x00000000 #x00000000)
                      #x0000000000000000
                      #x0000000000000002
                      (Build_time #x5dee5fab #x1defa4d1)
                      (Build_time #x5dcef8e7 #x04fc66a6)
                      (Build_time #x5dcef8e7 #x04fc66a6)))))))))))
(check-sat)
(declare-fun anon13 () bool)
(declare-fun anon15 () (_ BitVec 64))
(declare-fun anon14 () (_ BitVec 64))
(declare-fun anon16 () (_ BitVec 64))
(assert (let ((a!1 (Build_async_0 (Some_0 (select (Build_State_0 s_init)
                                          "\x01\x00\x01\x01\x00\x00\x00\x00\x01\x00@\x00\xbf\x95\xff\x00")))))
(let ((a!2 (ite ((_ is (Isymlink (String) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3LNK
                (ite ((_ is (Isock () inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3SOCK
                     NF3FIFO)))
      (a!5 ((_ int2bv 64) (str.len (Ifile_0 (Build_inode_state_1 a!1)))))
      (a!6 (ite ((_ is (Iblk (major_minor) inode_type_state))
                  (Build_inode_state_1 a!1))
                (Iblk_0 (Build_inode_state_1 a!1))
                (ite ((_ is (Ichr (major_minor) inode_type_state))
                       (Build_inode_state_1 a!1))
                     (Ichr_0 (Build_inode_state_1 a!1))
                     (Build_major_minor #x00000000 #x00000000)))))
(let ((a!3 (ite ((_ is (Iblk (major_minor) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3BLK
                (ite ((_ is (Ichr (major_minor) inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3CHR
                     a!2))))
(let ((a!4 (ite ((_ is (Ifile (String (_ BitVec 64)) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3REG
                (ite ((_ is (Idir ((Array String option_fh)) inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3DIR
                     a!3))))
(let ((a!7 (Build_fattr a!4
                        (Build_inode_meta_1 (Build_inode_state_0 a!1))
                        (Build_inode_meta_0 (Build_inode_state_0 a!1))
                        (Build_inode_meta_2 (Build_inode_state_0 a!1))
                        (Build_inode_meta_3 (Build_inode_state_0 a!1))
                        (ite ((_ is
                                 (Ifile (String (_ BitVec 64)) inode_type_state))
                               (Build_inode_state_1 a!1))
                             a!5
                             anon16)
                        anon14
                        a!6
                        anon15
                        (Build_inode_meta_4 (Build_inode_state_0 a!1))
                        (Build_inode_meta_5 (Build_inode_state_0 a!1))
                        (Build_inode_meta_6 (Build_inode_state_0 a!1))
                        (Build_inode_meta_7 (Build_inode_state_0 a!1)))))
(let ((a!8 (ite ((_ is (Some (async_inode_state) option_async))
                  (select (Build_State_0 s_init)
                          "\x01\x00\x01\x01\x00\x00\x00\x00\x01\x00@\x00\xbf\x95\xff\x00"))
                (OK Tt a!7)
                (ite ((_ is (True () bool)) anon13)
                     (Err Tt ERR_STALE)
                     (Err Tt ERR_BADHANDLE)))))
  (= a!8
     (OK Tt
         (Build_fattr NF3DIR
                      #x000001ed
                      #x000000a4
                      #x00000000
                      #x00000000
                      #x0000000000003000
                      #x0000000000003000
                      (Build_major_minor #x00000000 #x00000000)
                      #x0000000000000000
                      #x0000000000400001
                      (Build_time #x5ded1068 #x199bc766)
                      (Build_time #x5ded107a #x36b32785)
                      (Build_time #x5ded107a #x36b32785)))))))))))
(check-sat)
(declare-fun anon17 () bool)
(declare-fun anon19 () (_ BitVec 64))
(declare-fun anon18 () (_ BitVec 64))
(declare-fun anon20 () (_ BitVec 64))
(assert (let ((a!1 (Build_async_0 (Some_0 (select (Build_State_0 s_init)
                                          "\x01\x00\x01\x01\x00\x00\x00\x00\xd2\x00@\x00\x82\x97\xff\x00")))))
(let ((a!2 (ite ((_ is (Isymlink (String) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3LNK
                (ite ((_ is (Isock () inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3SOCK
                     NF3FIFO)))
      (a!5 ((_ int2bv 64) (str.len (Ifile_0 (Build_inode_state_1 a!1)))))
      (a!6 (ite ((_ is (Iblk (major_minor) inode_type_state))
                  (Build_inode_state_1 a!1))
                (Iblk_0 (Build_inode_state_1 a!1))
                (ite ((_ is (Ichr (major_minor) inode_type_state))
                       (Build_inode_state_1 a!1))
                     (Ichr_0 (Build_inode_state_1 a!1))
                     (Build_major_minor #x00000000 #x00000000)))))
(let ((a!3 (ite ((_ is (Iblk (major_minor) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3BLK
                (ite ((_ is (Ichr (major_minor) inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3CHR
                     a!2))))
(let ((a!4 (ite ((_ is (Ifile (String (_ BitVec 64)) inode_type_state))
                  (Build_inode_state_1 a!1))
                NF3REG
                (ite ((_ is (Idir ((Array String option_fh)) inode_type_state))
                       (Build_inode_state_1 a!1))
                     NF3DIR
                     a!3))))
(let ((a!7 (Build_fattr a!4
                        (Build_inode_meta_1 (Build_inode_state_0 a!1))
                        (Build_inode_meta_0 (Build_inode_state_0 a!1))
                        (Build_inode_meta_2 (Build_inode_state_0 a!1))
                        (Build_inode_meta_3 (Build_inode_state_0 a!1))
                        (ite ((_ is
                                 (Ifile (String (_ BitVec 64)) inode_type_state))
                               (Build_inode_state_1 a!1))
                             a!5
                             anon20)
                        anon18
                        a!6
                        anon19
                        (Build_inode_meta_4 (Build_inode_state_0 a!1))
                        (Build_inode_meta_5 (Build_inode_state_0 a!1))
                        (Build_inode_meta_6 (Build_inode_state_0 a!1))
                        (Build_inode_meta_7 (Build_inode_state_0 a!1)))))
(let ((a!8 (ite ((_ is (Some (async_inode_state) option_async))
                  (select (Build_State_0 s_init)
                          "\x01\x00\x01\x01\x00\x00\x00\x00\xd2\x00@\x00\x82\x97\xff\x00"))
                (OK Tt a!7)
                (ite ((_ is (True () bool)) anon17)
                     (Err Tt ERR_STALE)
                     (Err Tt ERR_BADHANDLE)))))
  (= a!8
     (OK Tt
         (Build_fattr NF3REG
                      #x000001a4
                      #x00000001
                      #x00000000
                      #x00000000
                      #x0000000000000011
                      #x0000000000001000
                      (Build_major_minor #x00000000 #x00000000)
                      #x0000000000000000
                      #x00000000004000d2
                      (Build_time #x5dae6157 #x0bbc67fc)
                      (Build_time #x5dae6157 #x0bf9712f)
                      (Build_time #x5dae6157 #x0bf9712f)))))))))))
(check-sat)
(check-sat)
(declare-datatypes ((sumbool 0)) (((Left) (Right))))
(declare-datatypes ((option_uint64 0)) (((Some (Some_0 (_ BitVec 64))) (None))))
(declare-datatypes ((option_time 0)) (((Some (Some_0 time)) (None))))
(declare-datatypes ((set_time 0)) (((SET_TO_CLIENT_TIME (SET_TO_CLIENT_TIME_0 time)) (SET_TO_SERVER_TIME))))
(declare-datatypes ((option_set_time 0)) (((Some (Some_0 set_time)) (None))))
(declare-datatypes ((wcc_attr 0)) (((Build_wcc_attr (Build_wcc_attr_0 (_ BitVec 64)) (Build_wcc_attr_1 time) (Build_wcc_attr_2 time)))))
(declare-datatypes ((option_wcc_attr 0)) (((Some (Some_0 wcc_attr)) (None))))
(declare-datatypes ((wcc_data 0)) (((Build_wcc_data (Build_wcc_data_0 option_wcc_attr) (Build_wcc_data_1 option_wcc_attr)))))
(declare-datatypes ((option_uint32 0)) (((Some (Some_0 (_ BitVec 32))) (None))))
(declare-datatypes ((sattr 0)) (((Build_sattr (Build_sattr_0 option_uint32) (Build_sattr_1 option_uint32) (Build_sattr_2 option_uint32) (Build_sattr_3 option_uint64) (Build_sattr_4 option_set_time) (Build_sattr_5 option_set_time)))))
(declare-datatypes ((res_wcc_data_unit 0)) (((OK (OK_0 wcc_data) (OK_1 unit)) (Err (Err_0 wcc_data) (Err_1 err)))))
(declare-fun anon21 () bool)
(declare-fun setattr_fh () String)
(declare-fun anon23 () (_ BitVec 32))
(declare-fun anon22 () (_ BitVec 32))
(declare-fun anon24 () bool)
(declare-fun setattr_sattr () sattr)
(declare-fun anon26 () (_ BitVec 32))
(declare-fun anon25 () (_ BitVec 32))
(declare-fun anon27 () bool)
(declare-fun setattr_ctime_guard () option_time)
(declare-fun the_response () res_wcc_data_unit)
(assert (let ((a!1 (Build_async_0 (Some_0 (select (Build_State_0 s_init) setattr_fh)))))
(let ((a!2 (ite (= (Some_0 setattr_ctime_guard)
                   (Build_inode_meta_7 (Build_inode_state_0 a!1)))
                Left
                Right))
      (a!3 ((_ int2bv 64) (str.len (Ifile_0 (Build_inode_state_1 a!1)))))
      (a!6 (Some (Build_wcc_attr #x0000000000000000
                                 (Build_time anon25 anon26)
                                 (Build_inode_meta_7 (Build_inode_state_0 a!1)))))
      (a!11 (Some (Build_wcc_attr #x0000000000000000
                                  (Build_time anon22 anon23)
                                  (Build_inode_meta_7 (Build_inode_state_0 a!1))))))
(let ((a!4 (ite (bvsle (Some_0 (Build_sattr_3 setattr_sattr)) a!3) False True))
      (a!5 (Build_wcc_attr (ite ((_ is
                                    (Ifile
                                     (String (_ BitVec 64))
                                     inode_type_state))
                                  (Build_inode_state_1 a!1))
                                a!3
                                #x0000000000000000)
                           (Build_inode_meta_6 (Build_inode_state_0 a!1))
                           (Build_inode_meta_7 (Build_inode_state_0 a!1)))))
(let ((a!7 (ite ((_ is (True () bool))
                  (ite ((_ is (True () bool)) a!4) anon27 False))
                (Err (Build_wcc_data (Some a!5) (Some a!5)) ERR_NOSPC)
                (OK (Build_wcc_data (Some a!5) a!6) Tt)))
      (a!12 (ite ((_ is (True () bool))
                   (ite ((_ is (True () bool)) a!4) anon24 False))
                 (Err (Build_wcc_data (Some a!5) (Some a!5)) ERR_NOSPC)
                 (OK (Build_wcc_data (Some a!5) a!11) Tt))))
(let ((a!8 (ite ((_ is (Ifile (String (_ BitVec 64)) inode_type_state))
                  (Build_inode_state_1 a!1))
                a!7
                (Err (Build_wcc_data (Some a!5) (Some a!5)) ERR_INVAL)))
      (a!13 (ite ((_ is (Ifile (String (_ BitVec 64)) inode_type_state))
                   (Build_inode_state_1 a!1))
                 a!12
                 (Err (Build_wcc_data (Some a!5) (Some a!5)) ERR_INVAL))))
(let ((a!9 (ite ((_ is (Some ((_ BitVec 64)) option_uint64))
                  (Build_sattr_3 setattr_sattr))
                a!8
                (OK (Build_wcc_data (Some a!5) (Some a!5)) Tt)))
      (a!14 (ite ((_ is (Some ((_ BitVec 64)) option_uint64))
                   (Build_sattr_3 setattr_sattr))
                 a!13
                 (OK (Build_wcc_data (Some a!5) (Some a!5)) Tt))))
(let ((a!10 (ite ((_ is (Left () sumbool)) a!2)
                 a!9
                 (Err (Build_wcc_data (Some a!5) (Some a!5)) ERR_NOT_SYNC))))
(let ((a!15 (ite ((_ is (Some (async_inode_state) option_async))
                   (select (Build_State_0 s_init) setattr_fh))
                 (ite ((_ is (Some (time) option_time)) setattr_ctime_guard)
                      a!10
                      a!14)
                 (ite ((_ is (True () bool)) anon21)
                      (Err (Build_wcc_data None None) ERR_STALE)
                      (Err (Build_wcc_data None None) ERR_BADHANDLE)))))
  (= the_response a!15))))))))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (Err a!1 ERR_INVAL))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x40000000
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x40000000
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000008
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x40000000
                                                             #x80000000)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000008
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x40000000
                                                             #x80000001)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000008
                                                             #x00000000)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x40000000
                                                             #x80000001)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x40000000
                                                             #x80000001)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x80000001)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x80000001)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x80004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x80000041)
                                                 (Build_time #x00000000
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x80004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x80000041)
                                                 (Build_time #x00000000
                                                             #x00040000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x80004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00040000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x80000041)
                                                 (Build_time #x00000000
                                                             #x00040400)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x80004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00040400))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x80000041)
                                                 (Build_time #x00000000
                                                             #x00040500)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x80004008
                                                             #x00000001)
                                                 (Build_time #x00000000
                                                             #x00040500))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (distinct the_response (Err (Build_wcc_data None None) ERR_BADHANDLE)))
(check-sat)
(assert (distinct the_response (Err (Build_wcc_data None None) ERR_STALE)))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000010
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000010
                                                             #x00000000))))))
  (distinct the_response (Err a!1 ERR_NOT_SYNC))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000010
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00000010
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000010
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000010
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000110
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000110
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000118
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000118
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00000318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00800318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00800318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00010000)
                                                 (Build_time #x00800318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00010000)
                                                 (Build_time #x00800318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00010000)
                                                 (Build_time #x00800308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00010000)
                                                 (Build_time #x00800308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00800308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00020000
                                                             #x00000000)
                                                 (Build_time #x00800308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00000000)
                                                 (Build_time #x00800308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00000000)
                                                 (Build_time #x00800308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00000000)
                                                 (Build_time #x00800318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00000000)
                                                 (Build_time #x00800318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00010000)
                                                 (Build_time #x00800318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00010000)
                                                 (Build_time #x00800318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00010000)
                                                 (Build_time #x00800308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x00010000)
                                                 (Build_time #x00800308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00800308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00800308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00800308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00800308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00800318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00800318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00800318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00800318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00c00308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08010000)
                                                 (Build_time #x00c00308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00308
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00308
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (Err a!1 ERR_INVAL))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000013
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00000000)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000013
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00002000)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000013
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00004000
                                                             #x00002000)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000013
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00004000
                                                             #x00002008)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
(assert (let ((a!1 (Build_wcc_data (Some (Build_wcc_attr #x0000000000000013
                                                 (Build_time #x00120000
                                                             #x08000000)
                                                 (Build_time #x00c00318
                                                             #x00000000)))
                           (Some (Build_wcc_attr #x0000000000000000
                                                 (Build_time #x00000000
                                                             #x00002008)
                                                 (Build_time #x00c00318
                                                             #x00000000))))))
  (distinct the_response (OK a!1 Tt))))
(check-sat)
