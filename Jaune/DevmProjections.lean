import Jaune.Machine

/-!
# Update-projection laws for `Devm`

Each `Devm` updater (`addLog`, `addAccessedAddress`, `addAccessedStorageKey`,
`setTransVal`, `setStorVal`, `withRefundCounter`, `memWrite`, `memExtends`,
`setCode`, `withGasLeft`, ...) against each accessor it leaves alone, or moves
in a stated way. Named update-first, `<updater>_<accessor>`, as the
`Devm.setMach_*` block of `Jaune.Machine` and the `gasLeft`/`stateGas` sets of
`Jaune.Sufficiency`; an updater defined outside `Devm` (`addAccessedAddress`,
`addAccessedStorageKey`) gives a root name, as there.

The matrix is the one downstream proofs restate, not every pair: a pair
appears here when a consumer needed it. All but the storage read-after-write
laws hold by `rfl`. None is `@[simp]`: consumers that work by `simp only`
name them, and adding them to the default set would change existing `simp`
calls.
-/

namespace Jaune

/-! #### `Devm.addLog` -/

theorem Devm.addLog_accessedAddresses (devm : Devm) (log : Log) :
    (devm.addLog log).accessedAddresses = devm.accessedAddresses := rfl

theorem Devm.addLog_accessedStorageKeys (devm : Devm) (log : Log) :
    (devm.addLog log).accessedStorageKeys = devm.accessedStorageKeys := rfl

theorem Devm.addLog_accountsToDelete (devm : Devm) (log : Log) :
    (devm.addLog log).accountsToDelete = devm.accountsToDelete := rfl

theorem Devm.addLog_createdAccounts (devm : Devm) (log : Log) :
    (devm.addLog log).createdAccounts = devm.createdAccounts := rfl

theorem Devm.addLog_output (devm : Devm) (log : Log) :
    (devm.addLog log).output = devm.output := rfl

theorem Devm.addLog_refundCounter (devm : Devm) (log : Log) :
    (devm.addLog log).refundCounter = devm.refundCounter := rfl

theorem Devm.addLog_returnData (devm : Devm) (log : Log) :
    (devm.addLog log).returnData = devm.returnData := rfl

theorem Devm.addLog_state (devm : Devm) (log : Log) :
    (devm.addLog log).state = devm.state := rfl

theorem Devm.addLog_transientStorage (devm : Devm) (log : Log) :
    (devm.addLog log).transientStorage = devm.transientStorage := rfl

theorem Devm.addLog_getAcct (devm : Devm) (log : Log) (x : Address) :
    (devm.addLog log).getAcct x = devm.getAcct x := rfl

theorem Devm.addLog_getCode (devm : Devm) (log : Log) (x : Address) :
    (devm.addLog log).getCode x = devm.getCode x := rfl

theorem Devm.addLog_getStorVal (devm : Devm) (log : Log) (x : Address) (key' : U256) :
    (devm.addLog log).getStorVal x key' = devm.getStorVal x key' := rfl

/-! #### `addAccessedAddress` -/

theorem addAccessedAddress_createdAccounts (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).createdAccounts = devm.createdAccounts := rfl

theorem addAccessedAddress_error (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).error = devm.error := rfl

theorem addAccessedAddress_logs (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).logs = devm.logs := rfl

theorem addAccessedAddress_output (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).output = devm.output := rfl

theorem addAccessedAddress_returnData (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).returnData = devm.returnData := rfl

theorem addAccessedAddress_state (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).state = devm.state := rfl

theorem addAccessedAddress_getCode (devm : Devm) (a : Address) (x : Address) :
    (addAccessedAddress devm a).getCode x = devm.getCode x := rfl

theorem addAccessedAddress_getStorVal (devm : Devm) (a : Address) (x : Address) (key' : U256) :
    (addAccessedAddress devm a).getStorVal x key' = devm.getStorVal x key' := rfl

/-! #### `addAccessedStorageKey` -/

theorem addAccessedStorageKey_accessedAddresses (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).accessedAddresses = devm.accessedAddresses := rfl

theorem addAccessedStorageKey_accountsToDelete (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).accountsToDelete = devm.accountsToDelete := rfl

theorem addAccessedStorageKey_createdAccounts (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).createdAccounts = devm.createdAccounts := rfl

theorem addAccessedStorageKey_error (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).error = devm.error := rfl

theorem addAccessedStorageKey_logs (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).logs = devm.logs := rfl

theorem addAccessedStorageKey_output (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).output = devm.output := rfl

theorem addAccessedStorageKey_refundCounter (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).refundCounter = devm.refundCounter := rfl

theorem addAccessedStorageKey_returnData (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).returnData = devm.returnData := rfl

theorem addAccessedStorageKey_state (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).state = devm.state := rfl

theorem addAccessedStorageKey_transientStorage (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).transientStorage = devm.transientStorage := rfl

theorem addAccessedStorageKey_getBal (devm : Devm) (a : Address) (k : U256) (x : Address) :
    (addAccessedStorageKey devm a k).getBal x = devm.getBal x := rfl

theorem addAccessedStorageKey_getCode (devm : Devm) (a : Address) (k : U256) (x : Address) :
    (addAccessedStorageKey devm a k).getCode x = devm.getCode x := rfl

theorem addAccessedStorageKey_getStorVal (devm : Devm) (a : Address) (k : U256) (x : Address) (key' : U256) :
    (addAccessedStorageKey devm a k).getStorVal x key' = devm.getStorVal x key' := rfl

/-! #### `Devm.setTransVal` -/

theorem Devm.setTransVal_createdAccounts (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).createdAccounts = devm.createdAccounts := rfl

theorem Devm.setTransVal_error (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).error = devm.error := rfl

theorem Devm.setTransVal_logs (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).logs = devm.logs := rfl

theorem Devm.setTransVal_output (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).output = devm.output := rfl

theorem Devm.setTransVal_getStorVal (devm : Devm) (adr : Address) (key val : U256) (x : Address) (key' : U256) :
    (devm.setTransVal adr key val).getStorVal x key' = devm.getStorVal x key' := rfl

/-! #### `Devm.setStorVal` -/

theorem Devm.setStorVal_createdAccounts (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).createdAccounts = devm.createdAccounts := rfl

theorem Devm.setStorVal_error (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).error = devm.error := rfl

theorem Devm.setStorVal_logs (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).logs = devm.logs := rfl

theorem Devm.setStorVal_output (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).output = devm.output := rfl

theorem Devm.setStorVal_returnData (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).returnData = devm.returnData := rfl

/-! #### `Devm.withRefundCounter` -/

theorem Devm.withRefundCounter_createdAccounts (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).createdAccounts = devm.createdAccounts := rfl

theorem Devm.withRefundCounter_output (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).output = devm.output := rfl

theorem Devm.withRefundCounter_returnData (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).returnData = devm.returnData := rfl

theorem Devm.withRefundCounter_getBal (devm : Devm) (rc : Int) (x : Address) :
    (devm.withRefundCounter rc).getBal x = devm.getBal x := rfl

theorem Devm.withRefundCounter_getCode (devm : Devm) (rc : Int) (x : Address) :
    (devm.withRefundCounter rc).getCode x = devm.getCode x := rfl

theorem Devm.withRefundCounter_getStorVal (devm : Devm) (rc : Int) (x : Address) (key' : U256) :
    (devm.withRefundCounter rc).getStorVal x key' = devm.getStorVal x key' := rfl

/-! #### `Devm.memWrite` -/

theorem Devm.memWrite_logs (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).logs = devm.logs := rfl

theorem Devm.memWrite_output (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).output = devm.output := rfl

theorem Devm.memWrite_returnData (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).returnData = devm.returnData := rfl

theorem Devm.memWrite_stack (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).stack = devm.stack := rfl

/-! #### `Devm.memExtends` -/

theorem Devm.memExtends_logs (devm : Devm) (pairs : List (Nat × Nat)) :
    (devm.memExtends pairs).logs = devm.logs := rfl

theorem Devm.memExtends_output (devm : Devm) (pairs : List (Nat × Nat)) :
    (devm.memExtends pairs).output = devm.output := rfl

theorem Devm.memExtends_returnData (devm : Devm) (pairs : List (Nat × Nat)) :
    (devm.memExtends pairs).returnData = devm.returnData := rfl

theorem Devm.memExtends_getCode (devm : Devm) (pairs : List (Nat × Nat)) (x : Address) :
    (devm.memExtends pairs).getCode x = devm.getCode x := rfl

/-! #### `Devm.setCode` -/

theorem Devm.setCode_accountsToDelete (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).accountsToDelete = devm.accountsToDelete := rfl

theorem Devm.setCode_error (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).error = devm.error := rfl

theorem Devm.setCode_logs (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).logs = devm.logs := rfl

theorem Devm.setCode_output (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).output = devm.output := rfl

theorem Devm.setCode_refundCounter (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).refundCounter = devm.refundCounter := rfl

/-! #### `Devm.withGasLeft` -/

theorem Devm.withGasLeft_accessedAddresses (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).accessedAddresses = devm.accessedAddresses := rfl

theorem Devm.withGasLeft_logs (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).logs = devm.logs := rfl

theorem Devm.withGasLeft_returnData (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).returnData = devm.returnData := rfl

theorem Devm.withGasLeft_state (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).state = devm.state := rfl

/-! #### `Devm.withStack` -/

theorem Devm.withStack_logs (devm : Devm) (stack : List U256) :
    (devm.withStack stack).logs = devm.logs := rfl

/-! #### `Devm.withReturnData` -/

theorem Devm.withReturnData_logs (devm : Devm) (returnData : Bytes) :
    (devm.withReturnData returnData).logs = devm.logs := rfl

theorem Devm.withReturnData_getCode (devm : Devm) (returnData : Bytes) (x : Address) :
    (devm.withReturnData returnData).getCode x = devm.getCode x := rfl

/-! #### `Devm.withOutput` -/

theorem Devm.withOutput_getStorVal (devm : Devm) (out : Bytes) (x : Address) (key' : U256) :
    (devm.withOutput out).getStorVal x key' = devm.getStorVal x key' := rfl

/-! #### `Devm.incrNonce` -/

theorem Devm.incrNonce_output (devm : Devm) (adr : Address) :
    (devm.incrNonce adr).output = devm.output := rfl

theorem Devm.incrNonce_returnData (devm : Devm) (adr : Address) :
    (devm.incrNonce adr).returnData = devm.returnData := rfl

/-! #### `Devm.setBal` -/

theorem Devm.setBal_output (devm : Devm) (adr : Address) (val : U256) :
    (devm.setBal adr val).output = devm.output := rfl

/-! #### `Devm.setMach` -/

theorem Devm.setMach_getBal (devm : Devm) (mach : Mach) (x : Address) :
    (devm.setMach mach).getBal x = devm.getBal x := rfl

/-! #### Accessors an updater moves -/

theorem Devm.addLog_logs (devm : Devm) (log : Log) :
    (devm.addLog log).logs = devm.logs ++ [log] := rfl

theorem addAccessedAddress_accessedAddresses (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).accessedAddresses = devm.accessedAddresses.insert a := rfl

theorem addAccessedStorageKey_accessedStorageKeys (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).accessedStorageKeys =
      devm.accessedStorageKeys.insert (a, k) := rfl

theorem Devm.memWrite_memory (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).memory = devm.memory.write idx val := rfl

theorem Devm.setCode_state (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).state = devm.state.setCode adr code := rfl

/-! #### Storage read-after-write -/

/-- A persistent storage write leaves every balance alone. -/
theorem Devm.setStorVal_getBal (devm : Devm) (adr : Address) (key val : U256) (x : Address) :
    (devm.setStorVal adr key val).getBal x = devm.getBal x := by
  show ((devm.state.setStorVal adr key val).get x).balance = (devm.state.get x).balance
  by_cases h : adr = x
  · subst h
    rw [State.setStorVal_get_self]
  · rw [State.setStorVal_get_ne _ h]

/-- Persistent storage read-after-write at the written address and key. -/
theorem Devm.setStorVal_getStorVal_self (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).getStorVal adr key = val := by
  show ((devm.state.setStorVal adr key val).get adr).storage.get key = val
  rw [State.setStorVal_get_self, Storage.get_set_self]

/-- Persistent storage read-after-write at the written address and another key. -/
theorem Devm.setStorVal_getStorVal_of_ne (devm : Devm) (adr : Address) {key key' : U256}
    (h : key ≠ key') (val : U256) :
    (devm.setStorVal adr key val).getStorVal adr key' = devm.getStorVal adr key' := by
  show ((devm.state.setStorVal adr key val).get adr).storage.get key' =
    (devm.state.get adr).storage.get key'
  rw [State.setStorVal_get_self, Storage.get_set_ne _ h]

end Jaune
