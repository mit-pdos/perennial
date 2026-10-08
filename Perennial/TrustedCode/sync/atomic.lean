/-
Trusted code for the Go `sync/atomic` package (namespace `sync.atomic`, as the
generated package).
-/
module

public import Perennial.Golang.Defn.Pre

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync.atomic
section code
variable [FfiSyntax] [GoGlobalContext]

def LoadUint64.impl : val :=
  λ: "addr", Load "addr"
def StoreUint64.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapUint64.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def AddUint64.impl : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def CompareAndSwapUint64.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def LoadInt64.impl : val :=
  λ: "addr", Load "addr"
def StoreInt64.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapInt64.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def AddInt64.impl : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def CompareAndSwapInt64.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def LoadUint32.impl : val :=
  λ: "addr", Load "addr"
def StoreUint32.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapUint32.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def AddUint32.impl : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def CompareAndSwapUint32.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def LoadInt32.impl : val :=
  λ: "addr", Load "addr"
def StoreInt32.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapInt32.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def AddInt32.impl : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def CompareAndSwapInt32.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def LoadPointer.impl : val :=
  λ: "addr", Load "addr"
def StorePointer.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def SwapPointer.impl : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def CompareAndSwapPointer.impl : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

end code
end sync.atomic

end Perennial
