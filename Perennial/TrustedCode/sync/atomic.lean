/-
Port of `new/trusted_code/sync/atomic.v` (namespace `sync.atomic`, as the
generated package).
-/
import Perennial.Golang.Defn.Pre

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace sync.atomic
section code
variable [FfiSyntax] [GoGlobalContext]

def «LoadUint64ⁱᵐᵖˡ» : val :=
  λ: "addr", Load "addr"
def «StoreUint64ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def «SwapUint64ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def «AddUint64ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def «CompareAndSwapUint64ⁱᵐᵖˡ» : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def «LoadInt64ⁱᵐᵖˡ» : val :=
  λ: "addr", Load "addr"
def «StoreInt64ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def «SwapInt64ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def «AddInt64ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def «CompareAndSwapInt64ⁱᵐᵖˡ» : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def «LoadUint32ⁱᵐᵖˡ» : val :=
  λ: "addr", Load "addr"
def «StoreUint32ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def «SwapUint32ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def «AddUint32ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def «CompareAndSwapUint32ⁱᵐᵖˡ» : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def «LoadInt32ⁱᵐᵖˡ» : val :=
  λ: "addr", Load "addr"
def «StoreInt32ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def «SwapInt32ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def «AddInt32ⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicAdd "addr" "val"
def «CompareAndSwapInt32ⁱᵐᵖˡ» : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

def «LoadPointerⁱᵐᵖˡ» : val :=
  λ: "addr", Load "addr"
def «StorePointerⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val" ;; #()
def «SwapPointerⁱᵐᵖˡ» : val :=
  λ: "addr" "val", AtomicSwap "addr" "val"
def «CompareAndSwapPointerⁱᵐᵖˡ» : val :=
  λ: "addr" "old" "new",
    Snd (CmpXchg "addr" "old" "new")

end code
end sync.atomic

end Perennial
