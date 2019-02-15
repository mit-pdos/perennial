From Coq Require Import List.

From RecoveryRefinement Require Export Lib.
From RecoveryRefinement Require Import Helpers.MachinePrimitives.
From RecoveryRefinement Require Import Database.Base.
From RecoveryRefinement Require Import Database.Proof.FilesysSpecsForMail.
From RecoveryRefinement Require Export CSL.WeakestPre CSL.Lifting.
From RecoveryRefinement Require Import Database.Proof.BaseMachine.

From iris.algebra Require Import auth frac_auth.


Axiom pid_to_tmpfile : uint64 -> Path.
Axiom rnd_to_msgfile : uint64 -> Path.
Axiom is_tmpfile : Path -> bool.

Section MailServer.

  Context `{!baseG Σ}.
  Context `{!inG Σ (authR (optionUR (exclR boolC)))}.


  Import ProcNotations.
  Local Open Scope proc.


  Definition deliver (pid : uint64) (msg : ByteString) :=
    let tmpfile := pid_to_tmpfile pid in
    fd <- FS.create tmpfile;
    _ <- FS.append fd msg;
    _ <- FS.close fd;
    _ <- Loop
      (fun _ =>
        rnd <- FS.random;
        let msgfile := rnd_to_msgfile rnd in
        ok <- FS.link tmpfile msgfile;
        if ok then
          LoopRet tt
        else
          Continue tt) tt;
    FS.delete tmpfile.

  Definition pickup :=
    fns <- FS.list;
    Loop
      (fun '(fns, msgs) =>
        match fns with
        | nil => LoopRet msgs
        | fn :: fns' =>
          if is_tmpfile fn then Continue (fns', msgs)
          else
            fd <- FS.open fn;
            len <- FS.size fd;
            msg <- FS.readAt fd 0 len;
            _ <- FS.close fd;
            Continue (fns', (fn, msg) :: msgs)
        end) (fns, nil).

  Definition delete (fn : Path) :=
    FS.delete fn.


  Theorem deliver_ok G g pid msg gm :
    {{{ ▷ (dirents G ∗ own g (◯ (Excl' false))) ∗ ⌜G !! (pid_to_tmpfile pid) = Some g⌝ }}}
      deliver pid msg
      {{{ RET (); ∃ msgid, dirents G ∗ own g (◯ (Excl' false)) ∗ own gm (◯ (Excl' true)) ∗ ⌜G !! msgid = Some gm⌝ ∗ msgid ↦ msg }}}.
  Proof.
    iIntros (Φ) "(H&#Hx) Post".
    unfold deliver.

    wp_bind.
    iApply (wp_create with "[H Hx]").
    iFrame. eauto.
    iIntros (fh) "!> (Hd&Ho&Ht&Hfd)".

    wp_bind.
    iApply (wp_append with "[Ht Hfd]").
    iFrame.
    iIntros "!> (Ht&Hfd)".

    wp_bind.
    iApply (wp_close with "Hfd").
    iIntros "!> _".

    wp_bind.

    iLöb as "IHloop".

    wp_loop.
    wp_bind.
    iApply (wp_random).
    eauto.
    iIntros (rnd) "!> _".

    wp_bind.
    iApply (wp_link with "[Hd Ht]").
    iFrame.
    iIntros (ok).
    destruct ok.

    - iIntros "!> (Hd&Ht&Hr&Hot&Hy)".
      wp_ret.
      iNext.
      wp_ret.
      iApply (wp_delete with "[Hd Ho Ht Hx]").
      iFrame. eauto.

      iNext.
      iIntros "(Hd&Ho)".
      iApply "Post".
      iExists _.
      rewrite app_empty.
      iFrame.

    - iIntros "!> (Hd&Ht)".
      wp_ret.
      iNext.
      iApply ("IHloop" with "Post Hd Ho").
      iFrame.
  Qed.


End MailServer.
