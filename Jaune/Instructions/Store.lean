import Jaune.MessageCall.CheckedState

/-! Restricted-effect table rows for `SSTORE` and `TSTORE`.

`SSTORE` spans three fork shapes in `Checked.PlainOp` (`sstoreBerlin`, `sstoreLegacy`,
`sstoreAmsterdam`), differing in static-check ordering, EIP-2929 warming, the sentry `gasLeft`
bound, and second-dimension state gas. `SstoreRow` packages all `ForkRules` regimes via pure
flags and cost/refund arithmetic over `(cold, newVal, origVal, currVal, oldRefund)`, while routing
all non-machine side effects through `StoreTouch` and `Frame.State.liftStore`. `TstoreRow` covers
`TSTORE` in the same style. -/

namespace Jaune.Checked

open Jaune

/-- The sole persistent or transient slot write a store row can emit on `ctx.recipient`. -/
inductive StoreWrite where
  /-- Persistent storage write `(key, value)` on `ctx.recipient`. -/
  | storage (key value : U256)
  /-- Transient storage write `(key, value)` on `ctx.recipient`. -/
  | transient (key value : U256)
deriving DecidableEq

/-- Restricted non-machine effects emitted by a store instruction row on the calling frame's
`recipient`: optional EIP-7928 trail read marks, optional EIP-2929 slot warming, optional refund
counter overwrite, and at most one persistent or transient slot write at `recipient`.

No balance, nonce, code, log, self-destruct, or other-account mutation is representable. -/
structure StoreTouch where
  /-- Record an EIP-7928 storage read on `(recipient, key)` in `trail`. -/
  readStorage : Option U256 := none
  /-- Warm `(recipient, key)` in `substate.accessedStorageKeys`. -/
  warmKey : Option U256 := none
  /-- Replace `substate.refund` when `some`. -/
  newRefund : Option Int := none
  /-- Record an EIP-7928 account read on `recipient` in `trail` (only after `assertDynamic`). -/
  readAccount : Bool := false
  /-- Write at most one storage or transient slot at `recipient`. -/
  write : Option StoreWrite := none
deriving DecidableEq

/-- Read-only view of one target storage slot `(cold, original, current, refund)`. -/
structure SlotView where
  /-- Whether `(recipient, key)` is absent from `substate.accessedStorageKeys`. -/
  cold : Bool
  /-- Transaction-start value from `originalStorageValue`. -/
  original : U256
  /-- Current world storage value from `storageValue`. -/
  current : U256
  /-- Current frame gas refund counter `substate.refund`. -/
  refund : Int
deriving DecidableEq

/-- Read a slot at the recipient in the transaction-start and current states. -/
def Frame.State.slotView (s : Frame.State) (recipient : Address) (originalState : Jaune.State)
    (key : U256) : SlotView where
  cold := decide ((recipient, key) ∉ s.accessedStorageKeys)
  original := s.originalStorageValue originalState recipient key
  current := s.storageValue recipient key
  refund := s.refund

/-- Apply a restricted `StoreTouch` at `recipient` under `rules` to `s`. -/
def Frame.State.applyStoreTouch (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) : Frame.State :=
  let s := match touch.readStorage with
    | none => s
    | some k => s.recordStorageRead rules recipient k
  let s := match touch.warmKey with
    | none => s
    | some k => s.addAccessedStorageKey recipient k
  let s := match touch.newRefund with
    | none => s
    | some r => s.withRefund r
  let s := if touch.readAccount then s.recordAccountRead rules recipient else s
  match touch.write with
  | none => s
  | some (.storage k v) => s.setStorageValue recipient k v
  | some (.transient k v) => s.setTransientValue recipient k v

/-- Lift a machine-plus-`StoreTouch` store kernel onto `Frame.State`. Even an exceptional halt
applies whatever `StoreTouch` prefix the kernel emitted before halting. -/
def Frame.State.liftStore (rules : ForkRules) (recipient : Address)
    (core : Machine → Except (ExceptionalHalt × Machine × StoreTouch) (Machine × StoreTouch))
    (s : Frame.State) : Except (ExceptionalHalt × Frame.State) Frame.State :=
  match core s.machine with
  | .error (e, m, touch) => .error (e, (s.withMachine m).applyStoreTouch rules recipient touch)
  | .ok (m, touch) => .ok ((s.withMachine m).applyStoreTouch rules recipient touch)

/-- Restricted-effect table row for `SSTORE` across every `ForkRules` regime (`Frontier` through
`Amsterdam`). Contains only rule flags and pure gas/refund arithmetic over `(cold, newVal,
origVal, currVal, oldRefund)` — no state-transforming `Frame.State` or `Machine` function. -/
structure SstoreRow where
  /-- Check `isStatic` before stack pops (`Amsterdam`) rather than after `chargeGas` (legacy). -/
  staticFirst : Bool
  /-- Warm `(recipient, key)` and pass coldness into `gasCost` and `sentry` (`EIP-2929` / `Amsterdam`). -/
  tracksWarmth : Bool
  /-- Minimum `gasLeft` required before slot reads and warming (`sentry cold ≤ gasLeft`). -/
  sentry : Bool → Nat
  /-- Execution gas cost `(cold, newVal, origVal, currVal) → Nat`. -/
  gasCost : Bool → U256 → U256 → U256 → Nat
  /-- Refund counter function `(newVal, origVal, currVal, oldRefund) → Int`. -/
  refundCounter : U256 → U256 → U256 → Int → Int
  /-- Second-dimension state gas cost `(newVal, origVal, currVal) → Nat` (0 pre-Amsterdam). -/
  stateGasCost : U256 → U256 → U256 → Nat := fun _ _ _ => 0
  /-- Second-dimension state gas refund `(newVal, origVal, currVal) → Nat` (0 pre-Amsterdam). -/
  stateGasRefund : U256 → U256 → U256 → Nat := fun _ _ _ => 0

/-- Instantiate `SstoreRow` for any `rules : ForkRules`. -/
def SstoreRow.ofRules (rules : ForkRules) : SstoreRow :=
  match rules.stateGas with
  | none =>
    { staticFirst := false
      tracksWarmth := match rules.access with | .eip2929 => true | .flat _ => false
      sentry := fun _ => if rules.sstore.stipendSentry then Gas.callStipend + 1 else 0
      gasCost := fun isCold newVal origVal currVal =>
        sstoreRegimeGasCost rules.sstore rules.access (if isCold then Gas.coldSloadCost else 0)
          newVal origVal currVal
      refundCounter := fun newVal origVal currVal rc =>
        match rules.sstore.netMetering, rules.access with
        | false, _ => sstoreLegacyRefundCounter rules.gas newVal origVal currVal rc
        | true, .flat g => sstoreFlatRefundCounter rules.gas g.sload newVal origVal currVal rc
        | true, .eip2929 => sstoreNewRefundCounter rules.gas newVal origVal currVal rc }
  | some state =>
    { staticFirst := true
      tracksWarmth := true
      sentry := fun isCold =>
        max (if isCold then Gas.coldSloadCost else Gas.warmStorageReadCost) (Gas.callStipend + 1)
      gasCost := fun isCold newVal origVal currVal =>
        sstoreAmsterdamGasCost state newVal origVal currVal isCold
      refundCounter := sstoreAmsterdamRefundCounter rules.gas state
      stateGasCost := sstoreAmsterdamStateGas state
      stateGasRefund := sstoreAmsterdamStateRefund state }

/-- Execute an `SstoreRow` against `isStatic` and a read-only `SlotView` lookup `slot`, updating
only `Machine` and producing a restricted `StoreTouch`. -/
def SstoreRow.step (row : SstoreRow) (isStatic : Bool) (slot : U256 → SlotView) (m : Machine) :
    Except (ExceptionalHalt × Machine × StoreTouch) (Machine × StoreTouch) :=
  if row.staticFirst && isStatic then
    .error (.writeInStaticContext .none, m, {})
  else
    match m.pop with
    | .error (e, m') => .error (e, m', {})
    | .ok (key, m₁) =>
      match m₁.pop with
      | .error (e, m') => .error (e, m', {})
      | .ok (newVal, m₂) =>
        let sv := slot key
        let isCold := row.tracksWarmth && sv.cold
        if m₂.gasLeft < row.sentry isCold then
          .error (.outOfGas .none, m₂, {})
        else
          let touch : StoreTouch :=
            { readStorage := some key
              warmKey := if isCold then some key else none
              newRefund := some (row.refundCounter newVal sv.original sv.current sv.refund) }
          let m₃ := m₂.creditStateGasRefund (row.stateGasRefund newVal sv.original sv.current)
          match m₃.chargeGas (row.gasCost isCold newVal sv.original sv.current) with
          | .error (e, m') => .error (e, m', touch)
          | .ok m₄ =>
            match m₄.chargeStateGas (row.stateGasCost newVal sv.original sv.current) with
            | .error (e, m') => .error (e, m', touch)
            | .ok m₅ =>
              if !row.staticFirst && isStatic then
                .error (.writeInStaticContext .none, m₅, touch)
              else
                .ok (m₅, { touch with readAccount := true, write := some (.storage key newVal) })

/-- Restricted-effect table row for `TSTORE` across every `ForkRules` regime. -/
structure TstoreRow where
  /-- Fork opcode availability predicate. -/
  available : OpcodeRules → Bool
  /-- Check `isStatic` before stack pops (`Amsterdam`) rather than after `chargeGas` (legacy). -/
  staticFirst : Bool
  /-- Execution gas cost. -/
  gasCost : Nat

/-- Instantiate `TstoreRow` for any `rules : ForkRules`. -/
def TstoreRow.ofRules (rules : ForkRules) : TstoreRow where
  available := OpcodeRules.transient
  staticFirst := rules.stateGas.isSome
  gasCost := Gas.warmStorageReadCost

/-- Execute a `TstoreRow` against `opcodes` and `isStatic`, updating `Machine` and returning a
restricted `StoreTouch` (writing at most one transient slot). -/
def TstoreRow.step (row : TstoreRow) (opcodes : OpcodeRules) (isStatic : Bool) (m : Machine) :
    Except (ExceptionalHalt × Machine × StoreTouch) (Machine × StoreTouch) :=
  if !row.available opcodes then
    .error (.invalidOpcode .none, m, {})
  else if row.staticFirst && isStatic then
    .error (.writeInStaticContext .none, m, {})
  else
    match m.pop with
    | .error (e, m') => .error (e, m', {})
    | .ok (key, m₁) =>
      match m₁.pop with
      | .error (e, m') => .error (e, m', {})
      | .ok (newVal, m₂) =>
        match m₂.chargeGas row.gasCost with
        | .error (e, m') => .error (e, m', {})
        | .ok m₃ =>
          if !row.staticFirst && isStatic then
            .error (.writeInStaticContext .none, m₃, {})
          else
            .ok (m₃, { write := some (.transient key newVal) })

end Jaune.Checked
