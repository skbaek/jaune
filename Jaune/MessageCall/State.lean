import Jaune.MessageCall.Resume
import Jaune.MessageCall.Records

/-!
# The running frame and its state vocabulary (goal `jaune-shape-and-names-v1`, W3 unit W3-1)

The final forms of the running frame and of what a halted frame hands to `settle`, and the
vocabulary the instruction bodies are written in once they run over `Frame.State` instead of
`Devm`:

* `Frame.Running` is what `Evm` becomes: a program counter, the `CallContext` that `step` reads,
  and the lifetime-grouped state.
* `Frame.Exit` is what replaces a frame's raw `Execution`: finished, reverted or halted, each
  with the state the frame stopped in. A fault is not an exit; it travels on its own channel.
* Group setters (`withMachine`, `withWorld`, `withSubstate`, `withTrail`), with one `@[simp]`
  law per group pair. Every field setter and every modifier below is a reducible abbreviation
  over them, so the group laws are the only simp lemmas a body needs to see which groups a step
  leaves alone.
* The machine operations (`Machine.push`, `pop`, `chargeGas`, the state-gas operations, the
  memory operations), with a halt-only error type, and their lifts to the state
  (`Frame.State.liftMachine`, `liftMachineValue`, `liftMachinePure`), which replace `liftMach*`.
* The world, substate and trail operations a body performs (`setStorageValue`, `addLog`,
  `recordAccountRead`, `recordTouch`, ...), which replace the `Devm` setters.

This module is staged beside the `Devm` interpreter: nothing in the interpreter uses it yet. The
maps from `Devm`, `Evm` and `Execution`, and one commuting lemma per operation against its `Devm`
counterpart, are in `Jaune.Bridge.G2b.State`.
-/

namespace Jaune

/-! ### Defaults for the static records

The defaults agree with `default : BenvStat`, `default : TenvStat` and `default : Sevm`. -/




/-! ### The running frame and its exit -/

/-- A running frame: where it is in its code, what it reads of its message, and its state. -/
structure Frame.Running : Type where
  /-- The program counter. -/
  pc : Nat
  /-- What `step` reads of the message the frame runs. -/
  context : CallContext
  /-- The frame's dynamic state. -/
  state : Frame.State

/-- How a frame stopped, with the state it stopped in. `settle` turns it into a
`Frame.Result`. -/
inductive Frame.Exit : Type
  /-- `STOP`, `RETURN`, `SELFDESTRUCT`, or a precompile that succeeded: the frame's output (for
  a creation, the code to deposit). -/
  | finished (output : Bytes) (state : Frame.State)
  /-- `REVERT`: the frame's output. -/
  | reverted (output : Bytes) (state : Frame.State)
  /-- An exceptional halt. -/
  | halted (reason : ExceptionalHalt) (state : Frame.State)

namespace Frame.Exit

/-- The state the frame stopped in. -/
def state : Frame.Exit → Frame.State
  | .finished _ s => s
  | .reverted _ s => s
  | .halted _ s => s

/-- The bytes the frame hands back; a halt hands back none. -/
def output : Frame.Exit → Bytes
  | .finished output _ => output
  | .reverted output _ => output
  | .halted .. => []

/-- Whether the frame failed (reverted or halted). -/
def failed : Frame.Exit → Bool
  | .finished .. => false
  | .reverted .. => true
  | .halted .. => true

end Frame.Exit

/-! ### Group setters

One setter per lifetime group, and the sixteen laws that say what each leaves alone. -/

namespace Frame.State

/-- Replace the machine. -/
def withMachine (s : Frame.State) (machine : Machine) : Frame.State := { s with machine }
/-- Replace the world. -/
def withWorld (s : Frame.State) (world : World) : Frame.State := { s with world }
/-- Replace the substate. -/
def withSubstate (s : Frame.State) (substate : Substate) : Frame.State := { s with substate }
/-- Replace the trail. -/
def withTrail (s : Frame.State) (trail : Trail) : Frame.State := { s with trail }

@[simp] theorem withMachine_machine (s : Frame.State) (m : Machine) :
    (s.withMachine m).machine = m := rfl
@[simp] theorem withMachine_world (s : Frame.State) (m : Machine) :
    (s.withMachine m).world = s.world := rfl
@[simp] theorem withMachine_substate (s : Frame.State) (m : Machine) :
    (s.withMachine m).substate = s.substate := rfl
@[simp] theorem withMachine_trail (s : Frame.State) (m : Machine) :
    (s.withMachine m).trail = s.trail := rfl

@[simp] theorem withWorld_machine (s : Frame.State) (w : World) :
    (s.withWorld w).machine = s.machine := rfl
@[simp] theorem withWorld_world (s : Frame.State) (w : World) :
    (s.withWorld w).world = w := rfl
@[simp] theorem withWorld_substate (s : Frame.State) (w : World) :
    (s.withWorld w).substate = s.substate := rfl
@[simp] theorem withWorld_trail (s : Frame.State) (w : World) :
    (s.withWorld w).trail = s.trail := rfl

@[simp] theorem withSubstate_machine (s : Frame.State) (u : Substate) :
    (s.withSubstate u).machine = s.machine := rfl
@[simp] theorem withSubstate_world (s : Frame.State) (u : Substate) :
    (s.withSubstate u).world = s.world := rfl
@[simp] theorem withSubstate_substate (s : Frame.State) (u : Substate) :
    (s.withSubstate u).substate = u := rfl
@[simp] theorem withSubstate_trail (s : Frame.State) (u : Substate) :
    (s.withSubstate u).trail = s.trail := rfl

@[simp] theorem withTrail_machine (s : Frame.State) (t : Trail) :
    (s.withTrail t).machine = s.machine := rfl
@[simp] theorem withTrail_world (s : Frame.State) (t : Trail) :
    (s.withTrail t).world = s.world := rfl
@[simp] theorem withTrail_substate (s : Frame.State) (t : Trail) :
    (s.withTrail t).substate = s.substate := rfl
@[simp] theorem withTrail_trail (s : Frame.State) (t : Trail) :
    (s.withTrail t).trail = t := rfl

/-! ### Field readers

Each reads one field of one group, as the `Devm` accessor of the same name does. -/

/-- The operand stack. -/
abbrev stack (s : Frame.State) : List U256 := s.machine.stack
/-- The memory. -/
abbrev memory (s : Frame.State) : Mem := s.machine.memory
/-- Execution gas left. -/
abbrev gasLeft (s : Frame.State) : Nat := s.machine.gasLeft
/-- The state-gas meter. -/
abbrev stateGas (s : Frame.State) : StateGasMeter := s.machine.stateGas
/-- The output of the last child frame. -/
abbrev returnData (s : Frame.State) : Bytes := s.machine.returnData
/-- The logs emitted so far. -/
abbrev logs (s : Frame.State) : List Log := s.substate.logs
/-- The refund counter. -/
abbrev refund (s : Frame.State) : Int := s.substate.refund
/-- The accounts scheduled for deletion. -/
abbrev selfDestructs (s : Frame.State) : AdrSet := s.substate.selfDestructs
/-- EIP-2929's accessed addresses. -/
abbrev accessedAddresses (s : Frame.State) : AdrSet := s.substate.accessedAddresses
/-- EIP-2929's accessed storage keys. -/
abbrev accessedStorageKeys (s : Frame.State) : KeySet := s.substate.accessedStorageKeys
/-- EIP-161's touched accounts. -/
abbrev touchedAccounts (s : Frame.State) : AdrSet := s.substate.touchedAccounts
/-- The accounts created in this transaction so far. -/
abbrev createdAccounts (s : Frame.State) : AdrSet := s.trail.createdAccounts
/-- EIP-7928's account reads. -/
abbrev accountReads (s : Frame.State) : AdrSet := s.trail.accountReads
/-- EIP-7928's storage reads. -/
abbrev storageReads (s : Frame.State) : KeySet := s.trail.storageReads
/-- The account state. -/
abbrev state (s : Frame.State) : Jaune.State := s.world.state
/-- The transient storage. -/
abbrev transientStorage (s : Frame.State) : TransientStorage := s.world.transientStorage
/-- The explicit storage writes. -/
abbrev storageWrites (s : Frame.State) : KeySet := s.world.storageWrites

/-- An account in the current state. -/
abbrev account (s : Frame.State) (a : Address) : Account := Jaune.State.get s.state a
/-- An account's balance. -/
abbrev balance (s : Frame.State) (a : Address) : U256 := (s.account a).balance
/-- An account's code. -/
abbrev code (s : Frame.State) (a : Address) : ByteArray := (s.account a).code
/-- An account's storage. -/
abbrev storage (s : Frame.State) (a : Address) : Storage := (s.account a).storage
/-- One storage slot. -/
abbrev storageValue (s : Frame.State) (a : Address) (k : U256) : U256 := (s.account a).storage.get k
/-- One transient storage slot. -/
abbrev transientValue (s : Frame.State) (a : Address) (k : U256) : U256 :=
  (s.transientStorage.getD a .empty).get k
/-- The value a slot had when the transaction started (`SSTORE`'s original value): zero for an
account created in this transaction, otherwise read from `original`, the transaction's start
state. -/
abbrev originalStorageValue (s : Frame.State) (original : Jaune.State) (a : Address) (k : U256) :
    U256 :=
  if a ∈ s.createdAccounts then 0 else (Jaune.State.get original a).storage.get k

/-! ### Field setters -/

/-- Replace the stack. -/
abbrev withStack (s : Frame.State) (stack : List U256) : Frame.State :=
  s.withMachine { s.machine with stack }
/-- Replace the memory. -/
abbrev withMemory (s : Frame.State) (memory : Mem) : Frame.State :=
  s.withMachine { s.machine with memory }
/-- Replace the execution gas left. -/
abbrev withGasLeft (s : Frame.State) (gasLeft : Nat) : Frame.State :=
  s.withMachine { s.machine with gasLeft }
/-- Replace the state-gas meter. -/
abbrev withStateGas (s : Frame.State) (stateGas : StateGasMeter) : Frame.State :=
  s.withMachine { s.machine with stateGas }
/-- Replace the return data. -/
abbrev withReturnData (s : Frame.State) (returnData : Bytes) : Frame.State :=
  s.withMachine { s.machine with returnData }
/-- Replace the logs. -/
abbrev withLogs (s : Frame.State) (logs : List Log) : Frame.State :=
  s.withSubstate { s.substate with logs }
/-- Replace the refund counter. -/
abbrev withRefund (s : Frame.State) (refund : Int) : Frame.State :=
  s.withSubstate { s.substate with refund }
/-- Replace the accounts scheduled for deletion. -/
abbrev withSelfDestructs (s : Frame.State) (selfDestructs : AdrSet) : Frame.State :=
  s.withSubstate { s.substate with selfDestructs }
/-- Replace the created accounts. -/
abbrev withCreatedAccounts (s : Frame.State) (createdAccounts : AdrSet) : Frame.State :=
  s.withTrail { s.trail with createdAccounts }
/-- Replace the account state. -/
abbrev withState (s : Frame.State) (state : Jaune.State) : Frame.State :=
  s.withWorld { s.world with state }
/-- Replace the explicit storage writes. -/
abbrev withStorageWrites (s : Frame.State) (storageWrites : KeySet) : Frame.State :=
  s.withWorld { s.world with storageWrites }
/-- Replace the transient storage. -/
abbrev withTransientStorage (s : Frame.State) (transientStorage : TransientStorage) :
    Frame.State :=
  s.withWorld { s.world with transientStorage }

end Frame.State

/-! ### Machine operations

Each is the `Mach` operation of the same name on the lifetime-grouped machine, which also holds
the return data. Those that can fail raise only an exceptional halt. -/

namespace Machine

/-- Push a word, halting on a full stack (1024 words). -/
def push (x : U256) (m : Machine) : Except (ExceptionalHalt × Machine) Machine :=
  if m.stack.length < 1024 then .ok { m with stack := x :: m.stack }
  else .error (.stackOverflow .none, m)

/-- Pop a word, halting on an empty stack. -/
def pop (m : Machine) : Except (ExceptionalHalt × Machine) (U256 × Machine) :=
  match m.stack with
  | [] => .error (.stackUnderflow .none, m)
  | x :: xs => .ok (x, { m with stack := xs })

/-- Pop a word as a number. -/
def popToNat (m : Machine) : Except (ExceptionalHalt × Machine) (Nat × Machine) :=
  match m.pop with
  | .error err => .error err
  | .ok (x, m') => .ok (x.toNat, m')

/-- Pop a word as an address. -/
def popToAddress (m : Machine) : Except (ExceptionalHalt × Machine) (Address × Machine) :=
  match m.pop with
  | .error err => .error err
  | .ok (x, m') => .ok (x.toAddress, m')

/-- Pop `n` words, top first. -/
def popN (m : Machine) : Nat → Except (ExceptionalHalt × Machine) (List U256 × Machine)
  | 0 => .ok ([], m)
  | n + 1 =>
    match m.pop with
    | .error err => .error err
    | .ok (x, m') =>
      match m'.popN n with
      | .error err => .error err
      | .ok (xs, m'') => .ok (x :: xs, m'')

/-- Charge execution gas, halting when too little is left. -/
def chargeGas (cost : Nat) (m : Machine) : Except (ExceptionalHalt × Machine) Machine :=
  match safeSub m.gasLeft cost with
  | none => .error (.outOfGas .none, m)
  | some gas => .ok { m with gasLeft := gas }

/-- Charge, then push. -/
def pushItem (x : U256) (cost : Nat) (m : Machine) : Except (ExceptionalHalt × Machine) Machine :=
  match chargeGas cost m with
  | .error err => .error err
  | .ok m' => push x m'

/-- Pop one word, charge, push `f` of it. -/
def applyUnary (f : U256 → U256) (cost : Nat) (m : Machine) :
    Except (ExceptionalHalt × Machine) Machine :=
  match m.pop with
  | .error err => .error err
  | .ok (x, m') => pushItem (f x) cost m'

/-- Pop two words, charge, push `f` of them. -/
def applyBinary (f : U256 → U256 → U256) (cost : Nat) (m : Machine) :
    Except (ExceptionalHalt × Machine) Machine :=
  match m.pop with
  | .error err => .error err
  | .ok (x, m') =>
    match m'.pop with
    | .error err => .error err
    | .ok (y, m'') => pushItem (f x y) cost m''

/-- Pop three words, charge, push `f` of them. -/
def applyTernary (f : U256 → U256 → U256 → U256) (cost : Nat) (m : Machine) :
    Except (ExceptionalHalt × Machine) Machine :=
  match m.pop with
  | .error err => .error err
  | .ok (x, m') =>
    match m'.pop with
    | .error err => .error err
    | .ok (y, m'') =>
      match m''.pop with
      | .error err => .error err
      | .ok (z, m''') => pushItem (f x y z) cost m'''

/-- `charge_state_gas_from_meter`: the reservoir first, then spill into execution gas. -/
def chargeStateGas (amount : Nat) (m : Machine) : Except (ExceptionalHalt × Machine) Machine :=
  if amount ≤ m.stateGas.left then
    .ok { m with stateGas := { m.stateGas with left := m.stateGas.left - amount } }
  else if amount - m.stateGas.left ≤ m.gasLeft then
    .ok { m with
      gasLeft := m.gasLeft - (amount - m.stateGas.left)
      stateGas := { m.stateGas with
        left := 0
        spilled := m.stateGas.spilled + (amount - m.stateGas.left) } }
  else
    .error (.outOfGas .none, m)

/-- `commit_state_gas`: the baseline drops to the reservoir and the spill is committed. -/
def commitStateGas (m : Machine) : Machine :=
  let g := m.stateGas
  { m with stateGas :=
      { g with left := g.left, baseline := g.left, spilled := 0
               committedSpill := g.committedSpill + g.spilled } }

/-- `restore_state_gas` on the machine: the spill returns to execution gas, the reservoir to the
baseline. The refund discard is `Frame.State.restoreStateGas`'s other half. -/
def restoreStateGas (m : Machine) : Machine :=
  let g := m.stateGas
  { m with
    gasLeft := m.gasLeft + g.spilled
    stateGas := { g with left := g.baseline, spilled := 0 } }

/-- `restore_state_gas_to_entry`: every spill returns and both levels reset to the grant. -/
def restoreStateGasToEntry (grant : Nat) (m : Machine) : Machine :=
  let g := m.stateGas
  { m with
    gasLeft := m.gasLeft + g.spilled + g.committedSpill
    stateGas := { left := grant, baseline := grant, spilled := 0, committedSpill := 0 } }

/-- `forfeit_remaining_gas`. -/
def forfeitRemainingGas (m : Machine) : Machine := { m with gasLeft := 0 }

/-- `withhold_create_gas`: all but one sixty-fourth goes to the child. -/
def withholdCreateGas (m : Machine) : Nat × Machine :=
  let child := except64th m.gasLeft
  (child, { m with gasLeft := m.gasLeft - child })

/-- `drain_state_gas_reservoir`: the child receives the whole reservoir. -/
def drainStateGasReservoir (m : Machine) : Nat × Machine :=
  (m.stateGas.left, { m with stateGas := { m.stateGas with left := 0 } })

/-- `restore_child_gas`: a refused spawn's grants come back. -/
def restoreChildGas (gas reservoir : Nat) (m : Machine) : Machine :=
  { m with
    gasLeft := m.gasLeft + gas
    stateGas := { m.stateGas with left := m.stateGas.left + reservoir } }

/-- The termination measure: execution gas plus the spill a refund or a rollback can return. -/
def gasMeasure (m : Machine) : Nat :=
  m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill

/-- Write bytes to memory. -/
def memWrite (m : Machine) (index : Nat) (value : Bytes) : Machine :=
  { m with memory := m.memory.write index value }

/-- Extend memory to cover the given ranges. -/
def memExtends (m : Machine) (pairs : List (Nat × Nat)) : Machine :=
  { m with memory := m.memory.extends pairs }

/-- Read bytes from memory, extending it to cover them. -/
def memRead (m : Machine) (index size : Nat) : Bytes × Machine :=
  let (value, memory) := m.memory.read index size
  (value, { m with memory })

/-- The gas cost of extending memory to cover the given ranges. -/
def extCost (m : Machine) (pairs : List (Nat × Nat)) : Nat :=
  calculateMemoryGasCost (memExtsSize m.memory.size pairs) - calculateMemoryGasCost m.memory.size

end Machine

/-! ### Substate and trail operations -/






/-! ### State operations and lifts -/

namespace Frame.State

/-- Run a machine operation on the state's machine; the world, substate and trail are kept, on
both channels. -/
def liftMachine {ε : Type} (core : Machine → Except (ε × Machine) Machine) (s : Frame.State) :
    Except (ε × Frame.State) Frame.State :=
  match core s.machine with
  | .error (e, m) => .error (e, s.withMachine m)
  | .ok m => .ok (s.withMachine m)

/-- `liftMachine` for an operation that also returns a value. -/
def liftMachineValue {ε α : Type} (core : Machine → Except (ε × Machine) (α × Machine))
    (s : Frame.State) : Except (ε × Frame.State) (α × Frame.State) :=
  match core s.machine with
  | .error (e, m) => .error (e, s.withMachine m)
  | .ok (a, m) => .ok (a, s.withMachine m)

/-- `liftMachine` for an operation that cannot fail. -/
abbrev liftMachinePure (core : Machine → Machine) (s : Frame.State) : Frame.State :=
  s.withMachine (core s.machine)

/-- Push a word. -/
def push (x : U256) (s : Frame.State) : Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.push x)
/-- Pop a word. -/
def pop (s : Frame.State) : Except (ExceptionalHalt × Frame.State) (U256 × Frame.State) :=
  s.liftMachineValue Machine.pop
/-- Pop a word as a number. -/
def popToNat (s : Frame.State) : Except (ExceptionalHalt × Frame.State) (Nat × Frame.State) :=
  s.liftMachineValue Machine.popToNat
/-- Pop a word as an address. -/
def popToAddress (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) (Address × Frame.State) :=
  s.liftMachineValue Machine.popToAddress
/-- Pop `n` words. -/
def popN (s : Frame.State) (n : Nat) :
    Except (ExceptionalHalt × Frame.State) (List U256 × Frame.State) :=
  s.liftMachineValue (Machine.popN · n)
/-- Charge execution gas. -/
def chargeGas (cost : Nat) (s : Frame.State) : Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.chargeGas cost)
/-- Charge, then push. -/
def pushItem (x : U256) (cost : Nat) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.pushItem x cost)
/-- A unary word operation. -/
def applyUnary (f : U256 → U256) (cost : Nat) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.applyUnary f cost)
/-- A binary word operation. -/
def applyBinary (f : U256 → U256 → U256) (cost : Nat) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.applyBinary f cost)
/-- A ternary word operation. -/
def applyTernary (f : U256 → U256 → U256 → U256) (cost : Nat) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.applyTernary f cost)
/-- Charge state gas. -/
def chargeStateGas (amount : Nat) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  s.liftMachine (Machine.chargeStateGas amount)

/-- Halt with `writeInStaticContext` when the frame is static. -/
def assertDynamic (ctx : CallContext) (s : Frame.State) :
    Except (ExceptionalHalt × Frame.State) Unit :=
  Except.assert (!ctx.isStatic) (.writeInStaticContext .none, s)

/-- `credit_state_gas_refund`. -/
abbrev creditStateGasRefund (amount : Nat) (s : Frame.State) : Frame.State :=
  s.liftMachinePure (Machine.creditStateGasRefund amount)
/-- `commit_state_gas`. -/
abbrev commitStateGas (s : Frame.State) : Frame.State := s.liftMachinePure Machine.commitStateGas
/-- `restore_state_gas`: the machine's half, and the refund counter is zeroed. -/
abbrev restoreStateGas (s : Frame.State) : Frame.State :=
  (s.liftMachinePure Machine.restoreStateGas).withRefund 0
/-- `restore_state_gas_to_entry`. -/
abbrev restoreStateGasToEntry (grant : Nat) (s : Frame.State) : Frame.State :=
  s.liftMachinePure (Machine.restoreStateGasToEntry grant)
/-- `forfeit_remaining_gas`. -/
abbrev forfeitRemainingGas (s : Frame.State) : Frame.State :=
  s.liftMachinePure Machine.forfeitRemainingGas
/-- `restore_child_gas`. -/
abbrev restoreChildGas (gas reservoir : Nat) (s : Frame.State) : Frame.State :=
  s.liftMachinePure (Machine.restoreChildGas gas reservoir)
/-- `repay_state_gas_spill`. -/
abbrev repayStateGasSpill (s : Frame.State) : Frame.State :=
  s.liftMachinePure Machine.repayStateGasSpill
/-- `withhold_create_gas`. -/
abbrev withholdCreateGas (s : Frame.State) : Nat × Frame.State :=
  let (child, m) := s.machine.withholdCreateGas
  (child, s.withMachine m)
/-- `drain_state_gas_reservoir`. -/
abbrev drainStateGasReservoir (s : Frame.State) : Nat × Frame.State :=
  let (reservoir, m) := s.machine.drainStateGasReservoir
  (reservoir, s.withMachine m)

/-- Write bytes to memory. -/
abbrev memWrite (s : Frame.State) (index : Nat) (value : Bytes) : Frame.State :=
  s.liftMachinePure (·.memWrite index value)
/-- Extend memory to cover the given ranges. -/
abbrev memExtends (s : Frame.State) (pairs : List (Nat × Nat)) : Frame.State :=
  s.liftMachinePure (·.memExtends pairs)
/-- Read bytes from memory, extending it. -/
abbrev memRead (s : Frame.State) (index size : Nat) : Bytes × Frame.State :=
  let (value, m) := s.machine.memRead index size
  (value, s.withMachine m)
/-- The gas cost of extending memory. -/
abbrev extCost (s : Frame.State) (pairs : List (Nat × Nat)) : Nat := s.machine.extCost pairs

/-- Append a log. -/
abbrev addLog (s : Frame.State) (log : Log) : Frame.State := s.withSubstate (s.substate.addLog log)
/-- EIP-7708's transfer log, with upstream's guards: a self transfer and a zero transfer emit
nothing. -/
abbrev emitTransferLog (s : Frame.State) (sender recipient : Address) (amount : U256) :
    Frame.State :=
  if sender = recipient ∨ amount = 0 then s else s.addLog (transferLog sender recipient amount)
/-- Warm an address. -/
abbrev addAccessedAddress (s : Frame.State) (a : Address) : Frame.State :=
  s.withSubstate (s.substate.addAccessedAddress a)
/-- Warm a storage key. -/
abbrev addAccessedStorageKey (s : Frame.State) (a : Address) (k : U256) : Frame.State :=
  s.withSubstate (s.substate.addAccessedStorageKey a k)

/-- Record an account read for the block-level access list, under rules that carry one; the
identity otherwise. -/
abbrev recordAccountRead (rules : ForkRules) (a : Address) (s : Frame.State) : Frame.State :=
  s.withTrail (if rules.blockAccessListRules.isSome then s.trail.readAccount a else s.trail)
/-- The storage-read twin of `recordAccountRead`. -/
abbrev recordStorageRead (rules : ForkRules) (a : Address) (k : U256) (s : Frame.State) :
    Frame.State :=
  s.withTrail (if rules.blockAccessListRules.isSome then s.trail.readStorage a k else s.trail)

/-- Record `a` as touched when the rules sweep, `cond` holds, and `a` exists and is empty in the
current state. -/
abbrev recordTouch (rules : ForkRules) (cond : Bool) (a : Address) (s : Frame.State) :
    Frame.State :=
  s.withSubstate { s.substate with
    touchedAccounts :=
      if rules.settlement.touchedSweep && cond && decide (accountExistsAndIsEmpty s.world.state a)
      then s.substate.touchedAccounts.insert a
      else s.substate.touchedAccounts }

/-- Forget an empty account's storage writes. -/
abbrev clearStorageWritesIfEmpty (s : Frame.State) (a : Address) : Frame.State :=
  s.withWorld (s.world.clearStorageWritesIfEmpty a)
/-- Write a storage slot, recording the write. -/
abbrev setStorageValue (s : Frame.State) (a : Address) (k v : U256) : Frame.State :=
  s.withWorld { s.world with
    state := s.world.state.setStorVal a k v
    storageWrites := s.world.storageWrites.insert (a, k) }
/-- Write a transient storage slot. -/
abbrev setTransientValue (s : Frame.State) (a : Address) (k v : U256) : Frame.State :=
  s.withTransientStorage (s.transientStorage.setStorageValue a k v)
/-- Set a balance. -/
abbrev setBalance (s : Frame.State) (a : Address) (v : U256) : Frame.State :=
  (s.withState (Jaune.State.setBal s.world.state a v)).clearStorageWritesIfEmpty a
/-- Debit a balance, or nothing if it is too small. -/
abbrev subtractBalance (s : Frame.State) (a : Address) (v : U256) : Option Frame.State :=
  (s.world.subtractBalance a v).map s.withWorld
/-- Credit a balance. -/
abbrev addBalance (s : Frame.State) (a : Address) (v : U256) : Frame.State :=
  s.withWorld (s.world.addBalance a v)
/-- Increment a nonce. -/
abbrev incrNonce (s : Frame.State) (a : Address) : Frame.State :=
  (s.withState (Jaune.State.incrNonce s.world.state a)).clearStorageWritesIfEmpty a
/-- Set an account's code. -/
abbrev setCode (s : Frame.State) (a : Address) (code : ByteArray) : Frame.State :=
  (s.withState (Jaune.State.setCode s.world.state a code)).clearStorageWritesIfEmpty a

/-- `SELFDESTRUCT`'s beneficiary credit (`Devm.creditBeneficiary`): from Paris an erasing credit;
before, a credit that keeps the account, followed by a touch. -/
abbrev creditBeneficiary (rules : ForkRules) (donee : Address) (v : U256) (s : Frame.State) :
    Frame.State :=
  if rules.settlement.eraseEmptyOnModify then s.addBalance donee v
  else
    (s.withState (Jaune.State.setPresent s.world.state donee
      ((Jaune.State.get s.world.state donee).withBalance
        (Jaune.State.bal s.world.state donee + v)))).recordTouch rules true donee

end Frame.State

end Jaune
