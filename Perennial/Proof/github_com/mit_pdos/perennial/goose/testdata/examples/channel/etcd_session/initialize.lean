/-
The proof of `channel/etcd_session`'s `initialize'`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.initialize
public import Perennial.Spec.github_com.goose_lang.primitive.initialize
public import Perennial.Spec.time.initialize
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.errors.initialize

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session

set_option goose.wp.extras true

set_option maxHeartbeats 400000 in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.initialize'.wp_proof
    (wp_primitive_initialize :
      github_com.goose_lang.primitive.initialize'.spec
        (GF := GF) (hG := hG))
    (wp_time_initialize : time.initialize'.spec (GF := GF) (hG := hG))
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_errors_initialize : errors.initialize'.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.channel.etcd_session.initialize'.spec
      (GF := GF) (hG := hG) := fun get_is_pkg_init Hinit => by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := sync.Mutex) mu sync.Mutex.ty as Hmu
  wp_apply wp_GlobalAlloc (V := GoChan) sessionc
    (go.GoType.ChannelType go.ChanDir.sendrecv (go.GoType.StructType [])) as Hsc
  wp_apply wp_primitive_initialize _ Hinit.2.2.2.2.1 $$ Hown as ⟨Hown, #H1⟩
  wp_apply wp_time_initialize _ Hinit.2.2.2.1 $$ Hown as ⟨Hown, #H2⟩
  wp_apply wp_sync_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #H3⟩
  wp_apply wp_errors_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #H4⟩
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

end proof

end Perennial
