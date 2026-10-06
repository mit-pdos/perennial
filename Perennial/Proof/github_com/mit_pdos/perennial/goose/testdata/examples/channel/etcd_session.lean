/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel/etcd_session.v`:
an etcd-style session monitor, using a broadcast channel (`sessionc`) that is
closed (and replaced) whenever the session expires.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.errors
import Perennial.Proof.time
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.github_com.goose_lang.primitive
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Broadcast
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : etcd_session.Assumptions]

local notation "pkg" =>
  pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

/-- The resources protected by `mu`: half of `sessionc` and the current
broadcast channel. -/
abbrev muInv : IProp GF :=
  iprop(∃ (ch : chan.t) (γch : ChanNames),
    "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own (1 : Qp).half) ∗
    "#Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) broadcast.t.Unknown ∗
    "#Hsessionc_is" ∷ isChan ch γch Unit)

abbrev isInv : IProp GF :=
  iprop("#Hmu" ∷ sync.isMutex (globalAddr mu) muInv)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg := define_is_pkg_init isInv
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg := build_get_is_pkg_init_wf

theorem isInv_access :
    isPkgInit (PROP := IProp GF) pkg ⊢ sync.isMutex (globalAddr mu) muInv := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg

omit [AllG GF] in
theorem pointsto_halves {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) :
    typedPointsto (GF := GF) l v (DFrac.own 1) ⊣⊢
      typedPointsto l v (DFrac.own (1 : Qp).half) ∗ typedPointsto l v (DFrac.own (1 : Qp).half) := by
  have h := (typedPointsto_dfractional (GF := GF) l v).dfractional
    (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half)
  rwa [DFrac.op_own, Qp.half_add_half] at h

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗ isPkgInit (PROP := IProp GF) pkg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := sync.Mutex.t) mu sync.Mutex as Hmu
  wp_apply wp_GlobalAlloc (V := chan.t) sessionc
    (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) as Hsc
  wp_apply github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply time.wp_initialize' _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply sync.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply errors.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #H4⟩
  iapply wp_fupd
  wp_apply chan.wp_make1 (V := Unit) as %ch %γ ⟨#Hch, %_, Hoc⟩
  imod alloc_broadcast_chan (E := ⊤) iprop(True) γ ch $$ Hch Hoc with Hbc
  ihave #Hbcu := ownBroadcastChan_Unknown _ _ _ _ $$ Hbc
  icases (pointsto_halves _ _).1 $$ Hsc with ⟨Hsc1, Hsc2⟩
  imod sync.init_Mutex muInv ⊤ (globalAddr mu) $$ Hmu [Hsc1] with #HisMu
  · inext; iexists ch, γ; iframe; iframe #
  imodintro
  iframe Hown
  is_pkg_init_finish

theorem wp_newSession :
    {{ (True : IProp GF) }}
      (App (Val (@! newSession)) (Val #()))
    {{ (err : error.t), RET #err; True }} := by
  wp_start
  wp_apply github_com.goose_lang.primitive.wp_RandomUint64 as %x _
  wp_if_destruct
  · wp_apply errors.wp_New as %_ _
    wp_end
  · wp_end

theorem wp_waitForSessionExpiration :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (@! waitForSessionExpiration)) (Val #()))
    {{ RET #(); True }} := by
  wp_start
  wp_end

/-- The postcondition of the nonblocking `select` in `monitorSession`. -/
abbrev monitorSelectPost (v : val) : IProp GF :=
  iprop(⌜v = executeVal⌝ ∗
    ∃ (ch : chan.t) (γch : ChanNames),
      "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own 1) ∗
      "Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) broadcast.t.Pending ∗
      "#Hsessionc_is" ∷ isChan ch γch Unit)

set_option maxHeartbeats 1600000 in
theorem wp_monitorSession (ch : chan.t) (γch : ChanNames) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗
        "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own (1 : Qp).half) ∗
        "Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) broadcast.t.Pending ∗
        "#Hsessionc_is" ∷ isChan ch γch Unit }}
      (App (Val (@! monitorSession)) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨sessionc, Hsessionc, #Hsessionc_is⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg $$ []
  · iPkgInit
  ihave #Hmu := isInv_access $$ Hpkg
  ihave HH : (∃ (ch : chan.t) (γch : ChanNames) (cst : broadcast.t),
      "sessionc" ∷ typedPointsto (globalAddr sessionc) ch (DFrac.own (1 : Qp).half) ∗
      "Hsessionc" ∷ ownBroadcastChan ch γch iprop(True) cst ∗
      "#Hsessionc_is" ∷ isChan ch γch Unit ∗
      "%Hcst" ∷ ⌜cst ≠ broadcast.t.Unknown⌝ : IProp GF) $$ [sessionc Hsessionc]
  · iexists ch, γch, broadcast.t.Pending
    iframe
    iframe #
    ipureintro; simp
  iclear Hsessionc_is
  wp_for HH
  wp_apply wp_waitForSessionExpiration
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
  icases Hown with ⟨%ch', %γch', sessionc_inv, #Hsessionc_inv, #Hsessionc_is_inv⟩
  icombine sessionc sessionc_inv gives %Heq
  subst Heq
  ihave sessionc := (pointsto_halves _ _).2 $$ [sessionc sessionc_inv]
  · iframe
  wp_bind (App (Val (GoInstruction SelectStmt)) _)
  iapply wp_wand (Φ := monitorSelectPost) $$ [sessionc Hsessionc] [-]
  · iapply chan.wp_select_nonblocking_alt [iprop(⌜cst = broadcast.t.Pending⌝)]
      iprop(typedPointsto (globalAddr sessionc) ch (DFrac.own 1) ∗
        ownBroadcastChan ch γch iprop(True) cst) $$ [] [sessionc Hsessionc] []
    · iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · iintro ⟨sessionc, Hsessionc⟩
        simp only [chan.nonblockingAltClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
        isplit
        · ipureintro; rfl
        isplit
        · iexact Hsessionc_is
        iapply ownBroadcastChan_nonblocking_receive _ _ _ _ _ cst $$ Hsessionc
        cases cst
        · dsimp only
          isplit
          · itrivial
          · iintro Hsessionc
            iframe
            ipureintro; rfl
        · dsimp only
          isplit
          · iintro #Hdone
            wp_auto
            iapply wp_fupd
            wp_apply chan.wp_make1 (V := Unit) as %ch2 %γ2 ⟨#Hch2, %_, Hoc⟩
            imod alloc_broadcast_chan (E := ⊤) iprop(True) γ2 ch2 $$ Hch2 Hoc with Hbc
            imodintro
            isplit
            · ipureintro; rfl
            iexists ch2, γ2
            iframe
            iframe #
          · itrivial
        · exact absurd rfl Hcst
      · iapply BigSepL2.bigSepL2_nil.2
        iempintro
    · iframe
    · iintro ⟨sessionc, Hsessionc⟩ Hnrs
      icases BigSepL.bigSepL_cons.1 $$ Hnrs with ⟨%Hp, -⟩
      subst Hp
      wp_auto
      isplit
      · ipureintro; rfl
      iexists ch, γch
      iframe
      iframe #
  iintro %v ⟨%Hv, %ch2, %γ2, sessionc, Hsessionc, #Hsessionc_is2⟩
  subst Hv
  wp_auto
  icases (pointsto_halves _ _).1 $$ sessionc with ⟨sessionc, sessionc_inv⟩
  -- (Rocq:) subtlety here: because we are deriving a persistent
  -- ownBroadcastChan(ch, broadcast.Pending), the function can retain Hsessionc
  -- asserting that the channel is specifically Pending; this is needed after the
  -- Unlock to safely close.
  ihave #Hunk := ownBroadcastChan_Unknown _ _ _ _ $$ Hsessionc
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked sessionc_inv]
  · inext; iexists ch2, γ2; iframe; iframe #
  wp_apply wp_newSession as %err _
  cases err with
  | nil =>
    wp_auto
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
    icases Hown with ⟨%ch3, %γ3, sessionc_inv, #Hsessionc_inv3, #Hsessionc_is_inv3⟩
    icombine sessionc sessionc_inv gives %Heq
    subst Heq
    wp_apply wp_broadcast_chan_close ch2 γ2 iprop(True) $$ [$Hsessionc] as #Hdone
    · imodintro; itrivial
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked sessionc_inv]
    · inext; iexists ch2, γ3; iframe; iframe #
    wp_for_post
    iframe
    iexists ch2, γ2, broadcast.t.Done
    iframe
    iframe #
    ipureintro; simp
  | ok e =>
    wp_auto
    wp_for_post
    iframe
    iexists ch2, γ2, broadcast.t.Pending
    iframe
    iframe #
    ipureintro; simp

set_option maxHeartbeats 800000 in
/-- Rocq `waitSession` (renamed: the Lean name `waitSession` is the function). -/
theorem wp_waitSession {A' : Type} [ZeroVal A'] [TypedPointsto (GF := GF) A'] [Pos.Countable A']
    {A : go.GoType} [IntoValTyped (GF := GF) A' A]
    (cancel : Loc) (γcancel : ChanNames) (Pcancel : A' → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isChanBag γcancel cancel Pcancel }}
      (App (Val #(functions waitSession [A])) (Val #cancel))
    {{ (err : error.t), RET #err;
        match err with
        | interface.t.nil => iprop(True)
        | _ => iprop(∃ a, Pcancel a) }} := by
  wp_start as #Hcancel
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg $$ []
  · iPkgInit
  ihave #Hmu := isInv_access $$ Hpkg
  wp_pures
  wp_alloc cancel_ptr as Hcancel_ptr
  wp_auto_lc 2
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hown⟩
  icases Hown with ⟨%ch, %γch, sessionc, #Hsessionc, #Hsessionc_is⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked sessionc]
  · inext; iexists ch, γch; iframe; iframe #
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch, γch
    isplit
    · ipureintro; rfl
    isplit
    · iexact Hsessionc_is
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hsessionc
    iintro ⟨_, _⟩
    wp_auto
    wp_end
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists A', inferInstance, inferInstance, inferInstance, inferInstance, cancel, γcancel
    isplit
    · ipureintro; rfl
    isplit
    · iapply is_bag_is_chan $$ Hcancel
    iapply bag_recv_au _ _ _ _ $$ [$Hlc1 $Hlc2] Hcancel
    inext
    iintro %v Hv
    wp_auto
    wp_apply errors.wp_New as %e _
    wp_end
    iexists v
    iexact Hv
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

end Perennial
