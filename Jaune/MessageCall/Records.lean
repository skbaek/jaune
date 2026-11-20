import Jaune.Execution
import Jaune.MessageCall

/-!
# Shared records of the frame vocabulary (goal `jaune-shape-and-names-v1`, G2b N4-0)

The defaults of the static records a frame reads, the substate and trail operations, the
`Pending` a spawn hands the driver, the status word a calling opcode pushes, and `SELFDESTRUCT`'s
fault. They were extracted unchanged from the `Devm`-era message-call modules so that the checked
interpreter no longer imports those modules.
-/

section
namespace Jaune
/-- `SELFDESTRUCT`'s fault: the donor's balance could not be debited by itself. -/
def insufficientBalanceFault : Fault :=
  .internal (.invariant (.text "InsufficientBalanceError"))
end Jaune
end

section
open Jaune
namespace Jaune.Staging
/-- What the caller waits with while its child runs, besides the saved caller itself. -/
structure Pending : Type where
  /-- Where the child's result goes. -/
  target : ReturnTarget
  /-- Whether the spawn charged a new account's state gas, which a failed child refunds. -/
  newAccountCharged : Bool
end Jaune.Staging
end

section
namespace Jaune
/-- The word the calling opcode pushes: the new address after a successful creation, 1 after a
successful call, 0 after a failure. -/
def ReturnTarget.status : ReturnTarget → Frame.Result → U256
  | .create address, .success .. => address.toU256
  | .call .., .success .. => 1
  | _, _ => 0
end Jaune
end

section
namespace Jaune
instance : Inhabited BlockContext := ⟨
  { fork := .prague, chainId := 0, gasLimit := 0, blockHashes := [], coinbase := 0, number := 0
    baseFeePerGas := 0, timestamp := 0, prevRandao := 0, excessBlobGas := 0
    parentBeaconBlockRoot := 0 }⟩
end Jaune
end

section
namespace Jaune
instance : Inhabited TransactionContext := ⟨
  { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := .empty }⟩
end Jaune
end

section
namespace Jaune
instance : Inhabited CallContext := ⟨
  { caller := 0, recipient := 0, value := 0, calldata := [], code := .empty, depthLeft := 1024
    isStatic := false, tx := default, block := default }⟩
end Jaune
end

section
namespace Jaune
/-- Append a log. -/
def Substate.addLog (u : Substate) (log : Log) : Substate := { u with logs := u.logs ++ [log] }
end Jaune
end

section
namespace Jaune
/-- Warm an address (EIP-2929). -/
def Substate.addAccessedAddress (u : Substate) (a : Address) : Substate :=
  { u with accessedAddresses := u.accessedAddresses.insert a }
end Jaune
end

section
namespace Jaune
/-- Warm a storage key (EIP-2929). -/
def Substate.addAccessedStorageKey (u : Substate) (a : Address) (k : U256) : Substate :=
  { u with accessedStorageKeys := u.accessedStorageKeys.insert (a, k) }
end Jaune
end

section
namespace Jaune
/-- Record an account read (EIP-7928), whatever the rules. -/
def Trail.readAccount (t : Trail) (a : Address) : Trail :=
  { t with accountReads := t.accountReads.insert a }
end Jaune
end

section
namespace Jaune
/-- Record a storage read (EIP-7928), whatever the rules. -/
def Trail.readStorage (t : Trail) (a : Address) (k : U256) : Trail :=
  { t with storageReads := t.storageReads.insert (a, k) }
end Jaune
end
