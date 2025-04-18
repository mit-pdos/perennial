(* autogenerated from github.com/mit-pdos/tulip/params *)
From Perennial.goose_lang Require Import prelude.

Section code.
Context `{ext_ty: ext_types}.

Definition N_SHARDS : expr := #2.

Definition NS_RECONNECT : expr := #100000000.

Definition NS_RESEND_PREPARE : expr := #500000000.

Definition NS_RESEND_READ : expr := #400000000.

Definition NS_RESEND_COMMIT : expr := #400000000.

Definition NS_RESEND_ABORT : expr := #400000000.

Definition NS_SPAWN_BACKUP_BASE : expr := #5000000000.

Definition NS_SPAWN_BACKUP_DELTA : expr := #1000000000.

Definition NS_SEND_REFRESH : expr := #4000000000.

Definition NS_BACKUP_INTERVAL : expr := #5000000000.

Definition NS_BATCH_INTERVAL : expr := #300000000.

Definition NS_HEARTBEAT_INTERVAL : expr := #1000000000.

Definition NS_ELECTION_TIMEOUT_BASE : expr := #2000000000.

Definition NS_ELECTION_TIMEOUT_DELTA : expr := #1000000000.

Definition N_RETRY_REPLICATED : expr := #500.

Definition NS_REPLICATED_INTERVAL : expr := #10000.

Definition N_TXN_SITES : expr := #1024.

End code.
