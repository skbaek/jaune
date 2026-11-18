import Jaune.MessageCall.State
import Jaune.MessageCall.Settle

/-!
# Bridge: the state vocabulary against `Devm`, `Evm` and `Execution` (G2b, unit W3-1)

The maps from today's running state to the lifetime-grouped one, their round trips, and one
commuting lemma per operation of `Jaune.MessageCall.State` against its `Devm` counterpart under
`Frame.State.ofDevm`. The instruction-body bridges of W3's later units compose these.

* `Frame.State.ofDevm` forgets `output` and `error` and sets the trail's RIPEMD-160 flag to
  `false`; `Frame.State.toDevm` puts back no output and no error. The round trips hold exactly
  under those two conditions (`toDevm_ofDevm_of_clean`, `ofDevm_toDevm`).
* `Frame.Running.ofEvm` forgets the five `Sevm` fields that stay on the `Message` (`target`,
  `gas`, `codeAddress`, the value-transfer flag, `disablePrecompiles`); `Frame.Running.toEvm`
  takes them back from a message.
* `Frame.Exit.ofExecution` sends a fault to the fault channel and forgets a halted frame's
  output, which `settle` never reads.
* An operation that can fail is compared through `Except.ofHalt`, which embeds the halt-only
  error type in `EvmError`; its states through `Except.mapState` and `Except.mapResultState`.

Everything here is a bridge artifact: it goes with `Devm` after G2b's tag.
-/

namespace Jaune

/-! ### Outcome maps -/

/-- Map the state carried on both channels of an outcome with a value. -/
def Except.mapState {ε σ τ α : Type} (f : σ → τ) :
    Except (ε × σ) (α × σ) → Except (ε × τ) (α × τ)
  | .error (e, s) => .error (e, f s)
  | .ok (a, s) => .ok (a, f s)

/-- Map the state carried on both channels of an outcome without a value. -/
def Except.mapResultState {ε σ τ : Type} (f : σ → τ) : Except (ε × σ) σ → Except (ε × τ) τ
  | .error (e, s) => .error (e, f s)
  | .ok s => .ok (f s)

/-- A halt-only outcome as an `EvmError` outcome. -/
def Except.ofHalt {σ β : Type} : Except (ExceptionalHalt × σ) β → Except (EvmError × σ) β
  | .error (h, s) => .error (.halt h, s)
  | .ok b => .ok b

/-- `Frame.State.ofDevm` on both channels of an outcome with a value. -/
abbrev Frame.State.ofOutcome {ε α : Type} : Except (ε × Devm) (α × Devm) →
    Except (ε × Frame.State) (α × Frame.State) :=
  Except.mapState Frame.State.ofDevm

/-- `Frame.State.ofDevm` on both channels of an `Execution`. -/
abbrev Frame.State.ofExecution : Execution → Except (EvmError × Frame.State) Frame.State :=
  Except.mapResultState Frame.State.ofDevm

/-! ### `Mach` against `Machine` -/

/-- The `Mach` part of a machine. -/
def Machine.toMach (m : Machine) : Mach :=
  { stack := m.stack, memory := m.memory, gasLeft := m.gasLeft, stateGas := m.stateGas }

/-- A `Mach` and the return data as a machine. -/
def Machine.ofMach (mach : Mach) (returnData : Bytes) : Machine :=
  { stack := mach.stack, memory := mach.memory, gasLeft := mach.gasLeft
    stateGas := mach.stateGas, returnData }

/-- Replace a machine's `Mach` part, keeping its return data. -/
abbrev Machine.withMach (m : Machine) (mach : Mach) : Machine := Machine.ofMach mach m.returnData

@[simp] theorem Machine.withMach_toMach (m : Machine) : m.withMach m.toMach = m := rfl
@[simp] theorem Machine.toMach_ofMach (mach : Mach) (r : Bytes) :
    (Machine.ofMach mach r).toMach = mach := rfl

/-- A `Mach` operation with a value, on a machine. -/
def Machine.liftMach {α : Type} (core : Mach → Footprint.Outcome Mach α) (m : Machine) :
    Except (EvmError × Machine) (α × Machine) :=
  Except.mapState m.withMach (core m.toMach)

/-- A `Mach` operation without a value, on a machine. -/
def Machine.liftMachUnit (core : Mach → Footprint.Outcome Mach Unit) (m : Machine) :
    Except (EvmError × Machine) Machine :=
  match core m.toMach with
  | .error (e, mach) => .error (e, m.withMach mach)
  | .ok (_, mach) => .ok (m.withMach mach)

/-! ### `Devm` against `Frame.State`: the round trips -/

namespace Frame.State

@[simp] theorem ofDevm_machine_toMach (d : Devm) : (ofDevm d).machine.toMach = d.mach := rfl

theorem ofDevm_machine (d : Devm) : (ofDevm d).machine = Machine.ofMach d.mach d.returnData := rfl

/-- Back and forth from a `Devm` loses exactly its output and its stored error. -/
theorem toDevm_ofDevm (d : Devm) :
    (ofDevm d).toDevm = { d with «meta» := { d.meta with output := [], error := none } } := by
  rcases d with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩; rfl

/-- A `Devm` with no output and no stored error survives the round trip. -/
theorem toDevm_ofDevm_of_clean {d : Devm} (ho : d.output = []) (he : d.error = none) :
    (ofDevm d).toDevm = d := by
  rcases d with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  simp only [Devm.output, Devm.error] at ho he
  subst ho he; rfl

/-- A state whose RIPEMD-160 flag is down (every running frame's) survives the round trip. -/
theorem ofDevm_toDevm {s : Frame.State} (h : s.trail.touchedRIPEMD160 = false) :
    ofDevm s.toDevm = s := by
  rcases s with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨_, _, _, flag⟩⟩
  simp only at h; subst h; rfl

@[simp] theorem ofDevm_touchedRIPEMD160 (d : Devm) :
    (ofDevm d).trail.touchedRIPEMD160 = false := rfl

/-! ### Readers -/

@[simp] theorem ofDevm_world (d : Devm) : (ofDevm d).world = d.world := rfl
@[simp] theorem ofDevm_stack (d : Devm) : (ofDevm d).stack = d.stack := rfl
@[simp] theorem ofDevm_memory (d : Devm) : (ofDevm d).memory = d.memory := rfl
@[simp] theorem ofDevm_gasLeft (d : Devm) : (ofDevm d).gasLeft = d.gasLeft := rfl
@[simp] theorem ofDevm_stateGas (d : Devm) : (ofDevm d).stateGas = d.stateGas := rfl
@[simp] theorem ofDevm_returnData (d : Devm) : (ofDevm d).returnData = d.returnData := rfl
@[simp] theorem ofDevm_logs (d : Devm) : (ofDevm d).logs = d.logs := rfl
@[simp] theorem ofDevm_refund (d : Devm) : (ofDevm d).refund = d.refundCounter := rfl
@[simp] theorem ofDevm_selfDestructs (d : Devm) :
    (ofDevm d).selfDestructs = d.accountsToDelete := rfl
@[simp] theorem ofDevm_accessedAddresses (d : Devm) :
    (ofDevm d).accessedAddresses = d.accessedAddresses := rfl
@[simp] theorem ofDevm_accessedStorageKeys (d : Devm) :
    (ofDevm d).accessedStorageKeys = d.accessedStorageKeys := rfl
@[simp] theorem ofDevm_touchedAccounts (d : Devm) :
    (ofDevm d).touchedAccounts = d.meta.touchedAccounts := rfl
@[simp] theorem ofDevm_createdAccounts (d : Devm) :
    (ofDevm d).createdAccounts = d.createdAccounts := rfl
@[simp] theorem ofDevm_accountReads (d : Devm) :
    (ofDevm d).accountReads = d.meta.accountReads := rfl
@[simp] theorem ofDevm_storageReads (d : Devm) :
    (ofDevm d).storageReads = d.meta.storageReads := rfl
@[simp] theorem ofDevm_state (d : Devm) : (ofDevm d).state = d.state := rfl
@[simp] theorem ofDevm_transientStorage (d : Devm) :
    (ofDevm d).transientStorage = d.transientStorage := rfl
@[simp] theorem ofDevm_storageWrites (d : Devm) :
    (ofDevm d).storageWrites = d.world.storageWrites := rfl
@[simp] theorem ofDevm_account (d : Devm) (a : Address) : (ofDevm d).account a = d.getAcct a := rfl
@[simp] theorem ofDevm_balance (d : Devm) (a : Address) : (ofDevm d).balance a = d.getBal a := rfl
@[simp] theorem ofDevm_code (d : Devm) (a : Address) : (ofDevm d).code a = d.getCode a := rfl
@[simp] theorem ofDevm_storage (d : Devm) (a : Address) : (ofDevm d).storage a = d.getStor a := rfl
@[simp] theorem ofDevm_storageValue (d : Devm) (a : Address) (k : U256) :
    (ofDevm d).storageValue a k = d.getStorVal a k := rfl
@[simp] theorem ofDevm_transientValue (d : Devm) (a : Address) (k : U256) :
    (ofDevm d).transientValue a k = d.getTransVal a k := rfl
/-- `SSTORE`'s original value, with the transaction's start state named explicitly. -/
@[simp] theorem ofDevm_originalStorageValue (d : Devm) (sevm : Sevm) (a : Address) (k : U256) :
    (ofDevm d).originalStorageValue sevm.benvStat.origState a k = d.getOrigStorVal sevm a k := rfl
@[simp] theorem ofDevm_extCost (d : Devm) (pairs : List (Nat × Nat)) :
    (ofDevm d).extCost pairs = d.extCost pairs := rfl

/-! ### Setters -/

theorem ofDevm_setMach (d : Devm) (mach : Mach) :
    ofDevm (d.setMach mach) = (ofDevm d).withMachine ((ofDevm d).machine.withMach mach) := rfl
theorem ofDevm_setWorld (d : Devm) (w : World) :
    ofDevm (d.setWorld w) = (ofDevm d).withWorld w := rfl
theorem ofDevm_withStack (d : Devm) (x : List U256) :
    ofDevm (d.withStack x) = (ofDevm d).withStack x := rfl
theorem ofDevm_withMemory (d : Devm) (x : Mem) :
    ofDevm (d.withMemory x) = (ofDevm d).withMemory x := rfl
theorem ofDevm_withGasLeft (d : Devm) (x : Nat) :
    ofDevm (d.withGasLeft x) = (ofDevm d).withGasLeft x := rfl
theorem ofDevm_withReturnData (d : Devm) (x : Bytes) :
    ofDevm (d.withReturnData x) = (ofDevm d).withReturnData x := rfl
theorem ofDevm_withLogs (d : Devm) (x : List Log) :
    ofDevm (d.withLogs x) = (ofDevm d).withLogs x := rfl
theorem ofDevm_withRefundCounter (d : Devm) (x : Int) :
    ofDevm (d.withRefundCounter x) = (ofDevm d).withRefund x := rfl
theorem ofDevm_withAccountsToDelete (d : Devm) (x : AdrSet) :
    ofDevm (d.withAccountsToDelete x) = (ofDevm d).withSelfDestructs x := rfl
theorem ofDevm_withCreatedAccounts (d : Devm) (x : AdrSet) :
    ofDevm (d.withCreatedAccounts x) = (ofDevm d).withCreatedAccounts x := rfl
theorem ofDevm_withState (d : Devm) (x : Jaune.State) :
    ofDevm (d.withState x) = (ofDevm d).withState x := rfl
theorem ofDevm_withStorageWrites (d : Devm) (x : KeySet) :
    ofDevm (d.withStorageWrites x) = (ofDevm d).withStorageWrites x := rfl
theorem ofDevm_withTransientStorage (d : Devm) (x : TransientStorage) :
    ofDevm (d.withTransientStorage x) = (ofDevm d).withTransientStorage x := rfl
/-- The output is not part of the grouped state. -/
@[simp] theorem ofDevm_withOutput (d : Devm) (x : Bytes) : ofDevm (d.withOutput x) = ofDevm d := rfl
/-- The stored error is not part of the grouped state. -/
@[simp] theorem ofDevm_withError (d : Devm) (x : Option SettledHalt) :
    ofDevm (d.withError x) = ofDevm d := rfl

/-! ### Substate, trail and world modifiers -/

theorem ofDevm_addLog (d : Devm) (l : Log) : ofDevm (d.addLog l) = (ofDevm d).addLog l := rfl
theorem ofDevm_emitTransferLog (d : Devm) (a b : Address) (v : U256) :
    ofDevm (d.emitTransferLog a b v) = (ofDevm d).emitTransferLog a b v := by
  unfold Devm.emitTransferLog emitTransferLog; split <;> rfl
theorem ofDevm_addAccessedAddress (d : Devm) (a : Address) :
    ofDevm (Jaune.addAccessedAddress d a) = (ofDevm d).addAccessedAddress a := rfl
theorem ofDevm_addAccessedStorageKey (d : Devm) (a : Address) (k : U256) :
    ofDevm (Jaune.addAccessedStorageKey d a k) = (ofDevm d).addAccessedStorageKey a k := rfl
theorem ofDevm_balReadAccount (rules : ForkRules) (a : Address) (d : Devm) :
    ofDevm (d.balReadAccount rules a) = (ofDevm d).recordAccountRead rules a := by
  unfold Devm.balReadAccount recordAccountRead; split <;> rfl
theorem ofDevm_balReadStorage (rules : ForkRules) (a : Address) (k : U256) (d : Devm) :
    ofDevm (d.balReadStorage rules a k) = (ofDevm d).recordStorageRead rules a k := by
  unfold Devm.balReadStorage recordStorageRead; split <;> rfl
theorem ofDevm_recordTouch (rules : ForkRules) (cond : Bool) (a : Address) (d : Devm) :
    ofDevm (d.recordTouch rules cond a) = (ofDevm d).recordTouch rules cond a := rfl
theorem ofDevm_clearStorageWritesIfEmpty (d : Devm) (a : Address) :
    ofDevm (d.clearStorageWritesIfEmpty a) = (ofDevm d).clearStorageWritesIfEmpty a := rfl
theorem ofDevm_setStorVal (d : Devm) (a : Address) (k v : U256) :
    ofDevm (d.setStorVal a k v) = (ofDevm d).setStorageValue a k v := rfl
theorem ofDevm_setTransVal (d : Devm) (a : Address) (k v : U256) :
    ofDevm (d.setTransVal a k v) = (ofDevm d).setTransientValue a k v := rfl
theorem ofDevm_setBal (d : Devm) (a : Address) (v : U256) :
    ofDevm (d.setBal a v) = (ofDevm d).setBalance a v := rfl
theorem ofDevm_subBal (d : Devm) (a : Address) (v : U256) :
    (d.subBal a v).map ofDevm = (ofDevm d).subtractBalance a v := by
  simp only [Devm.subBal, subtractBalance, World.subtractBalance, ofDevm_world, Devm.state]
  cases Jaune.State.subBal d.world.state a v <;> rfl
theorem ofDevm_addBal (d : Devm) (a : Address) (v : U256) :
    ofDevm (d.addBal a v) = (ofDevm d).addBalance a v := rfl
theorem ofDevm_incrNonce (d : Devm) (a : Address) :
    ofDevm (d.incrNonce a) = (ofDevm d).incrNonce a := rfl
theorem ofDevm_setCode (d : Devm) (a : Address) (c : ByteArray) :
    ofDevm (d.setCode a c) = (ofDevm d).setCode a c := rfl
theorem ofDevm_creditBeneficiary (rules : ForkRules) (a : Address) (v : U256) (d : Devm) :
    ofDevm (d.creditBeneficiary rules a v) = (ofDevm d).creditBeneficiary rules a v := by
  unfold Devm.creditBeneficiary creditBeneficiary; split <;> rfl

/-! ### Machine modifiers -/

theorem ofDevm_memWrite (d : Devm) (i : Nat) (v : Bytes) :
    ofDevm (d.memWrite i v) = (ofDevm d).memWrite i v := rfl
theorem ofDevm_memExtends (d : Devm) (p : List (Nat × Nat)) :
    ofDevm (d.memExtends p) = (ofDevm d).memExtends p := rfl
theorem ofDevm_memRead (d : Devm) (i n : Nat) :
    Prod.map id ofDevm (d.memRead i n) = (ofDevm d).memRead i n := by
  have hm : (ofDevm d).machine.memory = d.memory := rfl
  simp only [Devm.memRead, memRead, Machine.memRead, hm]
  cases d.memory.read i n; rfl
theorem ofDevm_creditStateGasRefund (n : Nat) (d : Devm) :
    ofDevm (d.creditStateGasRefund n) = (ofDevm d).creditStateGasRefund n := rfl
theorem ofDevm_commitStateGas (d : Devm) :
    ofDevm d.commitStateGas = (ofDevm d).commitStateGas := rfl
theorem ofDevm_restoreStateGas (d : Devm) :
    ofDevm d.restoreStateGas = (ofDevm d).restoreStateGas := rfl
theorem ofDevm_restoreStateGasToEntry (g : Nat) (d : Devm) :
    ofDevm (d.restoreStateGasToEntry g) = (ofDevm d).restoreStateGasToEntry g := rfl
theorem ofDevm_forfeitRemainingGas (d : Devm) :
    ofDevm d.forfeitRemainingGas = (ofDevm d).forfeitRemainingGas := rfl
theorem ofDevm_restoreChildGas (g r : Nat) (d : Devm) :
    ofDevm (d.restoreChildGas g r) = (ofDevm d).restoreChildGas g r := rfl
theorem ofDevm_withholdCreateGas (d : Devm) :
    Prod.map id ofDevm d.withholdCreateGas = (ofDevm d).withholdCreateGas := rfl
theorem ofDevm_drainStateGasReservoir (d : Devm) :
    Prod.map id ofDevm d.drainStateGasReservoir = (ofDevm d).drainStateGasReservoir := rfl

end Frame.State

/-! ### `Mach` operations against `Machine` operations -/

namespace Machine

theorem liftMachUnit_push (x : U256) (m : Machine) :
    liftMachUnit (Mach.push x) m = Except.ofHalt (m.push x) := by
  simp only [liftMachUnit, Mach.push, push, toMach]
  by_cases h : m.stack.length < 1024 <;> simp only [h, ↓reduceIte] <;> rfl

theorem liftMach_pop (m : Machine) : liftMach Mach.pop m = Except.ofHalt m.pop := by
  rcases m with ⟨_ | ⟨x, xs⟩, _, _, _, _⟩ <;> rfl

theorem liftMach_popToNat (m : Machine) :
    liftMach Mach.popToNat m = Except.ofHalt m.popToNat := by
  rcases m with ⟨_ | ⟨x, xs⟩, _, _, _, _⟩ <;> rfl

theorem liftMach_popToAdr (m : Machine) :
    liftMach Mach.popToAdr m = Except.ofHalt m.popToAddress := by
  rcases m with ⟨_ | ⟨x, xs⟩, _, _, _, _⟩ <;> rfl

theorem popN_ofMach (r : Bytes) (n : Nat) : ∀ mach : Mach,
    Except.mapState (fun x => Machine.ofMach x r) (Mach.popN mach n) =
      Except.ofHalt (Machine.popN (Machine.ofMach mach r) n) := by
  induction n with
  | zero => intro mach; rfl
  | succ n ih =>
    intro ⟨stack, mem, g, sg⟩
    cases stack with
    | nil => rfl
    | cons x xs =>
      have h := ih ⟨xs, mem, g, sg⟩
      simp only [Mach.popN, Mach.pop, Machine.popN, Machine.pop, Machine.ofMach] at h ⊢
      revert h
      generalize Mach.popN _ n = A
      generalize Machine.popN _ n = B
      rcases A with ⟨e, mm⟩ | ⟨vs, mm⟩ <;> rcases B with ⟨e', mm'⟩ | ⟨vs', mm'⟩ <;>
        intro h <;> simp_all [Except.mapState, Except.ofHalt]

theorem liftMach_popN (n : Nat) (m : Machine) :
    liftMach (Mach.popN · n) m = Except.ofHalt (m.popN n) :=
  popN_ofMach m.returnData n m.toMach

theorem liftMachUnit_chargeGas (c : Nat) (m : Machine) :
    liftMachUnit (Mach.chargeGas c) m = Except.ofHalt (m.chargeGas c) := by
  simp only [liftMachUnit, Mach.chargeGas, chargeGas, toMach]
  cases safeSub m.gasLeft c <;> rfl

theorem liftMachUnit_pushItem (x : U256) (c : Nat) (m : Machine) :
    liftMachUnit (Mach.pushItem x c) m = Except.ofHalt (m.pushItem x c) := by
  simp only [liftMachUnit, Mach.pushItem, pushItem, Mach.chargeGas, chargeGas, Mach.push, push,
    toMach]
  cases safeSub m.gasLeft c with
  | none => rfl
  | some g =>
    simp only
    by_cases h : m.stack.length < 1024 <;> simp only [h, ↓reduceIte] <;> rfl

theorem liftMachUnit_applyUnary (f : U256 → U256) (c : Nat) (m : Machine) :
    liftMachUnit (Mach.applyUnary f c) m = Except.ofHalt (m.applyUnary f c) := by
  rcases m with ⟨_ | ⟨x, xs⟩, mem, g, sg, r⟩
  · rfl
  · exact liftMachUnit_pushItem (f x) c ⟨xs, mem, g, sg, r⟩

theorem liftMachUnit_applyBinary (f : U256 → U256 → U256) (c : Nat) (m : Machine) :
    liftMachUnit (Mach.applyBinary f c) m = Except.ofHalt (m.applyBinary f c) := by
  rcases m with ⟨_ | ⟨x, _ | ⟨y, ys⟩⟩, mem, g, sg, r⟩
  · rfl
  · rfl
  · exact liftMachUnit_pushItem (f x y) c ⟨ys, mem, g, sg, r⟩

theorem liftMachUnit_applyTernary (f : U256 → U256 → U256 → U256) (c : Nat) (m : Machine) :
    liftMachUnit (Mach.applyTernary f c) m = Except.ofHalt (m.applyTernary f c) := by
  rcases m with ⟨_ | ⟨x, _ | ⟨y, _ | ⟨z, zs⟩⟩⟩, mem, g, sg, r⟩
  · rfl
  · rfl
  · rfl
  · exact liftMachUnit_pushItem (f x y z) c ⟨zs, mem, g, sg, r⟩

theorem liftMachUnit_chargeStateGas (n : Nat) (m : Machine) :
    liftMachUnit (Mach.chargeStateGas n) m = Except.ofHalt (m.chargeStateGas n) := by
  simp only [liftMachUnit, Mach.chargeStateGas, chargeStateGas, toMach]
  by_cases h1 : n ≤ m.stateGas.left <;> by_cases h2 : n - m.stateGas.left ≤ m.gasLeft <;>
    simp only [h1, h2, ↓reduceIte] <;> rfl

theorem withMach_creditStateGasRefund (n : Nat) (m : Machine) :
    m.withMach (m.toMach.creditStateGasRefund n) = m.creditStateGasRefund n := rfl
theorem withMach_repayStateGasSpill (m : Machine) :
    m.withMach m.toMach.repayStateGasSpill = m.repayStateGasSpill := rfl
theorem withMach_commitStateGas (m : Machine) :
    m.withMach m.toMach.commitStateGas = m.commitStateGas := rfl
theorem withMach_restoreStateGas (m : Machine) :
    m.withMach m.toMach.restoreStateGas = m.restoreStateGas := rfl
theorem withMach_restoreStateGasToEntry (g : Nat) (m : Machine) :
    m.withMach (m.toMach.restoreStateGasToEntry g) = m.restoreStateGasToEntry g := rfl
theorem withMach_forfeitRemainingGas (m : Machine) :
    m.withMach m.toMach.forfeitRemainingGas = m.forfeitRemainingGas := rfl
theorem withMach_restoreChildGas (g r : Nat) (m : Machine) :
    m.withMach (m.toMach.restoreChildGas g r) = m.restoreChildGas g r := rfl
theorem withMach_withholdCreateGas (m : Machine) :
    Prod.map id m.withMach m.toMach.withholdCreateGas = m.withholdCreateGas := rfl
theorem withMach_drainStateGasReservoir (m : Machine) :
    Prod.map id m.withMach m.toMach.drainStateGasReservoir = m.drainStateGasReservoir := rfl
theorem withMach_memWrite (i : Nat) (v : Bytes) (m : Machine) :
    m.withMach (m.toMach.memWrite i v) = m.memWrite i v := rfl
theorem withMach_memExtends (p : List (Nat × Nat)) (m : Machine) :
    m.withMach (m.toMach.memExtends p) = m.memExtends p := rfl
theorem toMach_gasMeasure (m : Machine) : m.toMach.gasMeasure = m.gasMeasure := rfl

end Machine

/-! ### The lifts against `liftMach*` -/

namespace Frame.State

theorem liftMachine_ofHalt (core : Machine → Except (ExceptionalHalt × Machine) Machine)
    (s : Frame.State) :
    s.liftMachine (fun m => Except.ofHalt (core m)) = Except.ofHalt (s.liftMachine core) := by
  unfold liftMachine; dsimp only
  rcases core s.machine with ⟨e, m⟩ | m <;> rfl

theorem liftMachineValue_ofHalt {α : Type}
    (core : Machine → Except (ExceptionalHalt × Machine) (α × Machine)) (s : Frame.State) :
    s.liftMachineValue (fun m => Except.ofHalt (core m)) =
      Except.ofHalt (s.liftMachineValue core) := by
  unfold liftMachineValue; dsimp only
  rcases core s.machine with ⟨e, m⟩ | ⟨a, m⟩ <;> rfl

/-- `liftMach` under `ofDevm`. -/
theorem ofOutcome_liftMach {α : Type} (core : Mach → Footprint.Outcome Mach α) (d : Devm) :
    ofOutcome (liftMach core d) = (ofDevm d).liftMachineValue (Machine.liftMach core) := by
  simp only [liftMach, Footprint.liftOutcome, liftMachineValue, Machine.liftMach,
    ofDevm_machine_toMach]
  rcases core d.mach with ⟨e, mach⟩ | ⟨a, mach⟩ <;> rfl

/-- `liftMachExecution` under `ofDevm`. -/
theorem ofExecution_liftMachExecution (core : Mach → Footprint.Outcome Mach Unit) (d : Devm) :
    ofExecution (liftMachExecution core d) =
      (ofDevm d).liftMachine (Machine.liftMachUnit core) := by
  simp only [liftMachExecution, liftMach, Footprint.toExecution, Footprint.liftOutcome,
    liftMachine, Machine.liftMachUnit, ofDevm_machine_toMach]
  rcases core d.mach with ⟨e, mach⟩ | ⟨a, mach⟩ <;> rfl

/-- `liftMachPure` under `ofDevm`. -/
theorem ofDevm_liftMachPure (core : Mach → Mach) (d : Devm) :
    ofDevm (liftMachPure core d) =
      (ofDevm d).liftMachinePure (fun m => m.withMach (core m.toMach)) := rfl

/-- A `Mach`+`Meta` operation on a grouped state: the operation sees no output and no stored
error, and the trail's RIPEMD-160 flag is kept. -/
def liftMachMeta {α : Type} (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α)
    (s : Frame.State) : Except (EvmError × Frame.State) (α × Frame.State) :=
  Except.mapState
    (fun p => let t := ofDevm ⟨p.1, p.2, s.world⟩
      t.withTrail { t.trail with touchedRIPEMD160 := s.trail.touchedRIPEMD160 })
    (core s.machine.toMach s.toDevm.meta)

/-- A `Mach`+`Meta` operation that cannot tell the output and the stored error apart, up to
what `ofDevm` keeps. Every such operation in the interpreter only carries both through. -/
def MetaCoreExitBlind {α : Type} (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α) :
    Prop :=
  ∀ mach v w, Except.mapState (fun p => ofDevm ⟨p.1, p.2, w⟩) (core mach v) =
    Except.mapState (fun p => ofDevm ⟨p.1, p.2, w⟩)
      (core mach { v with output := [], error := none })

/-- `liftMachMeta` under `ofDevm`, for an operation blind to the output and the stored error. -/
theorem ofOutcome_liftMachMeta {α : Type} {core : Mach → Meta → Footprint.Outcome (Mach × Meta) α}
    (h : MetaCoreExitBlind core) (d : Devm) :
    ofOutcome (Jaune.liftMachMeta core d) = (ofDevm d).liftMachMeta core := by
  have hm : (ofDevm d).toDevm.meta = { d.meta with output := [], error := none } := by
    rw [toDevm_ofDevm]
  have key : ofOutcome (Jaune.liftMachMeta core d) =
      Except.mapState (fun p => ofDevm ⟨p.1, p.2, d.world⟩) (core d.mach d.meta) := by
    unfold Jaune.liftMachMeta Footprint.liftOutcome; dsimp only
    rcases core d.mach d.meta with ⟨e, mach, v⟩ | ⟨a, mach, v⟩ <;> rfl
  rw [key, h, ← hm]
  unfold liftMachMeta
  rw [ofDevm_machine_toMach]
  rcases core d.mach (ofDevm d).toDevm.meta with ⟨e, mach, v⟩ | ⟨a, mach, v⟩ <;> rfl

/-! ### The machine operations at the state, against the `Devm` ones -/

theorem ofExecution_push (x : U256) (d : Devm) :
    ofExecution (d.push x) = Except.ofHalt ((ofDevm d).push x) := by
  rw [Devm.push, ofExecution_liftMachExecution, push, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_push x m

theorem ofOutcome_pop (d : Devm) : ofOutcome d.pop = Except.ofHalt (ofDevm d).pop := by
  rw [Devm.pop, ofOutcome_liftMach, pop, ← liftMachineValue_ofHalt]
  congr 1; funext m; exact Machine.liftMach_pop m

theorem ofOutcome_popToNat (d : Devm) :
    ofOutcome d.popToNat = Except.ofHalt (ofDevm d).popToNat := by
  rw [Devm.popToNat, ofOutcome_liftMach, popToNat, ← liftMachineValue_ofHalt]
  congr 1; funext m; exact Machine.liftMach_popToNat m

theorem ofOutcome_popToAdr (d : Devm) :
    ofOutcome d.popToAdr = Except.ofHalt (ofDevm d).popToAddress := by
  rw [Devm.popToAdr, ofOutcome_liftMach, popToAddress, ← liftMachineValue_ofHalt]
  congr 1; funext m; exact Machine.liftMach_popToAdr m

theorem ofOutcome_popN (d : Devm) (n : Nat) :
    ofOutcome (d.popN n) = Except.ofHalt ((ofDevm d).popN n) := by
  rw [Devm.popN, ofOutcome_liftMach, popN, ← liftMachineValue_ofHalt]
  congr 1; funext m; exact Machine.liftMach_popN n m

theorem ofExecution_chargeGas (c : Nat) (d : Devm) :
    ofExecution (Jaune.chargeGas c d) = Except.ofHalt ((ofDevm d).chargeGas c) := by
  rw [Jaune.chargeGas, ofExecution_liftMachExecution, chargeGas, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_chargeGas c m

theorem ofExecution_pushItem (x : U256) (c : Nat) (d : Devm) :
    ofExecution (Jaune.pushItem x c d) = Except.ofHalt ((ofDevm d).pushItem x c) := by
  rw [Jaune.pushItem, ofExecution_liftMachExecution, pushItem, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_pushItem x c m

theorem ofExecution_applyUnary (f : U256 → U256) (c : Nat) (d : Devm) :
    ofExecution (Jaune.applyUnary f c d) = Except.ofHalt ((ofDevm d).applyUnary f c) := by
  rw [Jaune.applyUnary, ofExecution_liftMachExecution, applyUnary, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_applyUnary f c m

theorem ofExecution_applyBinary (f : U256 → U256 → U256) (c : Nat) (d : Devm) :
    ofExecution (Jaune.applyBinary f c d) = Except.ofHalt ((ofDevm d).applyBinary f c) := by
  rw [Jaune.applyBinary, ofExecution_liftMachExecution, applyBinary, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_applyBinary f c m

theorem ofExecution_applyTernary (f : U256 → U256 → U256 → U256) (c : Nat) (d : Devm) :
    ofExecution (Jaune.applyTernary f c d) = Except.ofHalt ((ofDevm d).applyTernary f c) := by
  rw [Jaune.applyTernary, ofExecution_liftMachExecution, applyTernary, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_applyTernary f c m

theorem ofExecution_chargeStateGas (n : Nat) (d : Devm) :
    ofExecution (Jaune.chargeStateGas n d) = Except.ofHalt ((ofDevm d).chargeStateGas n) := by
  rw [Jaune.chargeStateGas, ofExecution_liftMachExecution, chargeStateGas, ← liftMachine_ofHalt]
  congr 1; funext m; exact Machine.liftMachUnit_chargeStateGas n m

/-- The halt-only charge `settle`'s deposit uses. -/
theorem mapResultState_devmChargeGas (c : Nat) (d : Devm) :
    Except.mapResultState ofDevm (Devm.chargeGas c d) = (ofDevm d).chargeGas c := by
  simp only [Devm.chargeGas, chargeGas, liftMachine, Machine.chargeGas, ofDevm_machine,
    Machine.ofMach, Devm.gasLeft]
  cases safeSub d.mach.gasLeft c <;> rfl

/-- The halt-only state-gas charge `settle`'s deposit uses. -/
theorem mapResultState_devmChargeStateGas (n : Nat) (d : Devm) :
    Except.mapResultState ofDevm (Devm.chargeStateGas n d) = (ofDevm d).chargeStateGas n := by
  simp only [Devm.chargeStateGas, chargeStateGas, liftMachine, Machine.chargeStateGas,
    ofDevm_machine, Machine.ofMach]
  by_cases h1 : n ≤ d.mach.stateGas.left <;>
    by_cases h2 : n - d.mach.stateGas.left ≤ d.mach.gasLeft <;>
    simp only [h1, h2, ↓reduceIte] <;> rfl

end Frame.State

/-! ### `Sevm` and `Evm` against `CallContext` and `Frame.Running` -/

/-- What `step` reads of a static machine. -/
def CallContext.ofSevm (s : Sevm) : CallContext :=
  { caller := s.caller, recipient := s.currentTarget, value := s.value, calldata := s.data
    code := s.code, depthLeft := s.depth, isStatic := s.isStatic, tx := s.tenvStat
    block := s.benvStat }

/-- A static machine as a message, with the two things it does not carry. -/
def Message.ofSevm (s : Sevm) (kind : Message.Kind) (stateGasGrant : Nat) : Message :=
  { context := .ofSevm s, kind, codeAddress := s.codeAddress, target := s.target, gas := s.gas
    stateGasGrant, transfersValue := s.shouldTransferValue
    disablePrecompiles := s.disablePrecompiles }

theorem CallContext.ofSevm_sevm (m : Message) : CallContext.ofSevm m.sevm = m.context := rfl

theorem Message.sevm_ofSevm (s : Sevm) (k : Message.Kind) (g : Nat) :
    (Message.ofSevm s k g).sevm = s := rfl

theorem Message.ofSevm_sevm (m : Message) : Message.ofSevm m.sevm m.kind m.stateGasGrant = m := rfl

/-- The defaults agree. -/
theorem CallContext.ofSevm_default : CallContext.ofSevm default = default := rfl

/-- `assertDynamic` under `ofDevm`. -/
theorem Frame.State.assertDynamic_ofDevm (sevm : Sevm) (d : Devm) :
    Frame.State.ofExecution ((Jaune.assertDynamic sevm d).map (fun _ => d)) =
      Except.ofHalt (((Frame.State.ofDevm d).assertDynamic (CallContext.ofSevm sevm)).map
        (fun _ => Frame.State.ofDevm d)) := by
  simp only [Jaune.assertDynamic, Frame.State.assertDynamic, Except.assert, CallContext.ofSevm]
  by_cases h : sevm.isStatic = true <;>
    simp [h, Except.map, Except.ofHalt, Except.mapResultState]

/-- A running machine as a running frame: it forgets what stays on the message, the output and
the stored error. -/
def Frame.Running.ofEvm (evm : Evm) : Frame.Running :=
  ⟨evm.pc, .ofSevm evm.sta, .ofDevm evm.dyna⟩

/-- A running frame as a running machine, with the rest of its static record from a message. -/
def Frame.Running.toEvm (x : Frame.Running) (m : Message) : Evm :=
  ⟨x.pc, { m with context := x.context }.sevm, x.state.toDevm⟩

/-- The machine `enter` builds, as a running frame. -/
theorem Frame.Running.ofEvm_mk (pc : Nat) (m : Message) (d : Devm) :
    Frame.Running.ofEvm ⟨pc, m.sevm, d⟩ = ⟨pc, m.context, .ofDevm d⟩ := rfl

theorem Frame.Running.ofEvm_toEvm {x : Frame.Running} (m : Message)
    (h : x.state.trail.touchedRIPEMD160 = false) : Frame.Running.ofEvm (x.toEvm m) = x := by
  rcases x with ⟨pc, ctx, s⟩
  simp only [ofEvm, toEvm, Frame.State.ofDevm_toDevm h]
  rfl

theorem Frame.Running.toEvm_ofEvm {evm : Evm} (k : Message.Kind) (g : Nat)
    (ho : evm.dyna.output = []) (he : evm.dyna.error = none) :
    (Frame.Running.ofEvm evm).toEvm (Message.ofSevm evm.sta k g) = evm := by
  rcases evm with ⟨pc, sta, d⟩
  simp only [ofEvm, toEvm, Frame.State.toDevm_ofDevm_of_clean ho he]
  rfl

/-! ### `Execution` against `Frame.Exit` -/

/-- A raw result as an exit, or the fault it carries. A halted frame's output is forgotten. -/
def Frame.Exit.ofExecution : Execution → Except Fault Frame.Exit
  | .ok d => .ok (.finished d.output (.ofDevm d))
  | .error (.revert, d) => .ok (.reverted d.output (.ofDevm d))
  | .error (.halt reason, d) => .ok (.halted reason (.ofDevm d))
  | .error (.crypto reason, _) => .error (.crypto reason)
  | .error (.internal reason, _) => .error (.internal reason)

/-- An exit as a raw result, with no stored error. -/
def Frame.Exit.toExecution : Frame.Exit → Execution
  | .finished output s => .ok (s.toDevm.withOutput output)
  | .reverted output s => .error (.revert, s.toDevm.withOutput output)
  | .halted reason s => .error (.halt reason, s.toDevm)

theorem Frame.Exit.ofExecution_toExecution {e : Frame.Exit}
    (h : e.state.trail.touchedRIPEMD160 = false) : ofExecution e.toExecution = .ok e := by
  cases e with
  | finished o s =>
    simp only [state] at h
    simp only [toExecution, ofExecution, Frame.State.ofDevm_withOutput,
      Frame.State.ofDevm_toDevm h]; rfl
  | reverted o s =>
    simp only [state] at h
    simp only [toExecution, ofExecution, Frame.State.ofDevm_withOutput,
      Frame.State.ofDevm_toDevm h]; rfl
  | halted r s =>
    simp only [state] at h
    simp only [toExecution, ofExecution, Frame.State.ofDevm_toDevm h]

theorem Frame.Exit.toExecution_ofExecution_ok {d : Devm} (he : d.error = none) :
    (ofExecution (.ok d)).map toExecution = .ok (.ok d) := by
  rcases d with ⟨mach, ⟨⟩, world⟩
  simp only [Devm.error] at he; subst he; rfl

theorem Frame.Exit.toExecution_ofExecution_revert {d : Devm} (he : d.error = none) :
    (ofExecution (.error (.revert, d))).map toExecution = .ok (.error (.revert, d)) := by
  rcases d with ⟨mach, ⟨⟩, world⟩
  simp only [Devm.error] at he; subst he; rfl

theorem Frame.Exit.toExecution_ofExecution_halt {d : Devm} (r : ExceptionalHalt)
    (ho : d.output = []) (he : d.error = none) :
    (ofExecution (.error (.halt r, d))).map toExecution = .ok (.error (.halt r, d)) := by
  simp only [ofExecution, Except.map, toExecution, Frame.State.toDevm_ofDevm_of_clean ho he]

theorem Frame.Exit.ofExecution_failed {raw : Execution} {e : Frame.Exit}
    (h : ofExecution raw = .ok e) : e.failed = raw.isOk.not := by
  rcases raw with ⟨_ | _ | _ | _, d⟩ | d <;> simp only [ofExecution] at h <;>
    (try cases h) <;> rfl

/-! ### The group laws reach the field setters and modifiers

`simp` sees through the reducible field setters and modifiers to the group setters, so the
group laws decide which groups a step leaves alone. -/

theorem Frame.State.withStack_world (s : Frame.State) (x : List U256) :
    (s.withStack x).world = s.world := by simp
theorem Frame.State.addLog_machine (s : Frame.State) (l : Log) :
    (s.addLog l).machine = s.machine := by simp
theorem Frame.State.setStorageValue_substate (s : Frame.State) (a : Address) (k v : U256) :
    (s.setStorageValue a k v).substate = s.substate := by simp
theorem Frame.State.recordAccountRead_world (rules : ForkRules) (a : Address) (s : Frame.State) :
    (s.recordAccountRead rules a).world = s.world := by simp
theorem Frame.State.memWrite_trail (s : Frame.State) (i : Nat) (v : Bytes) :
    (s.memWrite i v).trail = s.trail := by simp
theorem Frame.State.push_world {s s' : Frame.State} {x : U256} (h : s.push x = .ok s') :
    s'.world = s.world := by
  unfold Frame.State.push Frame.State.liftMachine at h
  split at h <;> cases h; simp

end Jaune
