import Jaune.MessageCall.CheckedMessageOps
import Jaune.Bridge.G2b.CheckedWalk

namespace Jaune.Checked

def MessageOp.Outcome.toLegacy : MessageOp.Outcome → Staging.MessageOp.Outcome
  | .done (.error (reason, s)) => .done (.error (reason, s.toLegacy))
  | .done (.ok s) => .done (.ok s.toLegacy)
  | .spawn f p => .spawn f.toLegacy p

end Jaune.Checked

namespace Jaune.MemorySimulation

instance eraseOutcome : Erases Checked.MessageOp.Outcome Staging.MessageOp.Outcome :=
  ⟨Checked.MessageOp.Outcome.toLegacy⟩

theorem MessageOp.Outcome.ofExcept {x : Except (ExceptionalHalt × Checked.Frame.State) Checked.MessageOp.Outcome}
    {y : Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome} (h : Square x y) :
    Square (Checked.MessageOp.Outcome.ofExcept x) (Staging.MessageOp.Outcome.ofExcept y) := by
  change erase x = y at h
  subst y
  cases x with
  | error p => cases p; rfl
  | ok o => rfl

theorem GasSchedule.accessDelegation (gas : GasSchedule) (s : Checked.Frame.State) (a : Address) :
    Square (Checked.GasSchedule.accessDelegation gas s a) (Staging.GasSchedule.accessDelegation gas s.toLegacy a) := by
  unfold Checked.GasSchedule.accessDelegation Staging.GasSchedule.accessDelegation
  simp only [show s.toLegacy.code a = s.code a from rfl]
  cases getDelegatedCodeAddress (s.code a) <;> rfl

theorem ForkRules.accessDelegation (rules : ForkRules) (s : Checked.Frame.State) (a : Address) :
    Square (Checked.ForkRules.accessDelegation rules s a) (Staging.ForkRules.accessDelegation rules s.toLegacy a) := by
  unfold Checked.ForkRules.accessDelegation Staging.ForkRules.accessDelegation
  cases rules.delegationEnabled <;> first | rfl | apply GasSchedule.accessDelegation

theorem completeDelegationAccess (s : Checked.Frame.State) (b : Bool) (a : Address) :
    Square (Checked.completeDelegationAccess s b a) (Staging.completeDelegationAccess s.toLegacy b a) := by
  cases b <;> rfl


private theorem accessDelegation_legacy (r : ForkRules) (s : Checked.Frame.State) (a : Address) :
    Staging.ForkRules.accessDelegation r s.toLegacy a = erase (Checked.ForkRules.accessDelegation r s a) :=
  (ForkRules.accessDelegation r s a).legacy_eq

private theorem completeDelegation_legacy (s : Checked.Frame.State) (b : Bool) (a : Address) :
    Staging.completeDelegationAccess s.toLegacy b a = erase (Checked.completeDelegationAccess s b a) :=
  (completeDelegationAccess s b a).legacy_eq

private theorem delegationCost_legacy (r : ForkRules) (s : Checked.Frame.State) (a : Address) :
    Staging.ForkRules.delegationCost r s.toLegacy a = Checked.ForkRules.delegationCost r s a := rfl

private theorem addAccessedAddress_legacy (s : Checked.Frame.State) (a : Address) :
    s.toLegacy.addAccessedAddress a = (s.addAccessedAddress a).toLegacy := rfl

private theorem memExtends_legacy (s : Checked.Frame.State) (p : List (Nat × Nat)) :
    s.toLegacy.memExtends p = (s.memExtends p).toLegacy := rfl

local macro "message_align" : tactic => `(tactic| simp only [accessDelegation_legacy, completeDelegation_legacy,
  delegationCost_legacy, addAccessedAddress_legacy, memExtends_legacy, erase_pair, erase_state, erase_same])

theorem genericCall.step (ctx : CallContext) (s : Checked.Frame.State) (g : Nat) (v : U256)
    (c t a : Address) (transfer static : Bool) (i n o k : Nat) (code : ByteArray) (disable : Bool) :
    Square (Checked.genericCall.step ctx s g v c t a transfer static i n o k code disable)
      (Staging.genericCall.step ctx s.toLegacy g v c t a transfer static i n o k code disable) := by
  unfold Checked.genericCall.step Staging.genericCall.step
  split <;> first | rfl | (apply MessageOp.Outcome.ofExcept; checked_sq_walk)

theorem genericCallAmsterdam.step (ctx : CallContext) (rules : StateGasRules) (s : Checked.Frame.State)
    (g res : Nat) (v : U256) (c t a : Address) (transfer static : Bool) (i n o k : Nat)
    (code : ByteArray) (disable charged insuff : Bool) :
    Square (Checked.genericCallAmsterdam.step ctx rules s g res v c t a transfer static i n o k code disable charged insuff)
      (Staging.genericCallAmsterdam.step ctx rules s.toLegacy g res v c t a transfer static i n o k code disable charged insuff) := by
  unfold Checked.genericCallAmsterdam.step Staging.genericCallAmsterdam.step
  split <;> first | rfl | (apply MessageOp.Outcome.ofExcept; cases charged <;> checked_sq_walk)

theorem genericCreate.step (ctx : CallContext) (s : Checked.Frame.State) (v : U256) (a : Address) (i n : Nat) :
    Square (Checked.genericCreate.step ctx s v a i n) (Staging.genericCreate.step ctx s.toLegacy v a i n) := by
  unfold Checked.genericCreate.step Staging.genericCreate.step
  apply MessageOp.Outcome.ofExcept
  checked_sq_walk

theorem genericCreateAmsterdam.step (ctx : CallContext) (rules : StateGasRules) (s : Checked.Frame.State)
    (v : U256) (a : Address) (i n : Nat) :
    Square (Checked.genericCreateAmsterdam.step ctx rules s v a i n)
      (Staging.genericCreateAmsterdam.step ctx rules s.toLegacy v a i n) := by
  unfold Checked.genericCreateAmsterdam.step Staging.genericCreateAmsterdam.step
  apply MessageOp.Outcome.ofExcept
  checked_sq_walk

private theorem recordedAccess_legacy (schedule : AccessSchedule) (s : Checked.Frame.State)
    (address : Address) :
    (match schedule with
     | .eip2929 => s.toLegacy.addAccessedAddress address
     | .flat _ => s.toLegacy) =
    (match schedule with
     | .eip2929 => s.addAccessedAddress address
     | .flat _ => s).toLegacy := by cases schedule <;> rfl

private theorem erased_first [Erases α γ] [Erases β δ] (p : α × β) :
    (@erase _ _ (eraseProd (α := α) (β := β) (γ := γ) (δ := δ)) p).1 = erase p.1 := rfl

private theorem erased_second [Erases α γ] [Erases β δ] (p : α × β) :
    (@erase _ _ (eraseProd (α := α) (β := β) (γ := γ) (δ := δ)) p).2 = erase p.2 := rfl

private theorem drained_legacy (s : Checked.Frame.State) :
    s.toLegacy.drainStateGasReservoir = ((s.drainStateGasReservoir).1, (s.drainStateGasReservoir).2.toLegacy) := rfl

private theorem memoryData_legacy (s : Checked.Frame.State) : s.toLegacy.memory.data = s.memory.data := rfl

local macro "message_state" : tactic => `(tactic| simp only [recordedAccess_legacy,
  accessDelegation_legacy, completeDelegation_legacy, delegationCost_legacy, drained_legacy,
  erased_first, erased_second, erase_same, erase_pair, erase_state, legacy_recordAccountRead,
  legacy_addAccessedAddress, legacy_memExtends, legacy_account, legacy_accessedAddresses,
  legacy_gasLeft, legacy_extCost, memoryData_legacy, legacy_withGasLeft, legacy_withReturnData])

local macro "message_walk" : tactic => `(tactic| repeat' first
  | (solve | checked_sq_leaf)
  | message_state
  | (with_reducible apply MessageOp.Outcome.ofExcept)
  | checked_sq_one)

private theorem message_call_legacy (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.MessageOp.step ctx s .call) (Staging.MessageOp.step ctx s.toLegacy .call) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_call_state (ctx : CallContext) (s : Checked.Frame.State) (rules : StateGasRules)
    (hr : ctx.block.rules.stateGas = some rules) :
    Square (Checked.MessageOp.step ctx s .call) (Staging.MessageOp.step ctx s.toLegacy .call) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_call (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.MessageOp.step ctx s .call) (Staging.MessageOp.step ctx s.toLegacy .call) := by
  cases hr : ctx.block.rules.stateGas with
  | none => exact message_call_legacy ctx s hr
  | some rules => exact message_call_state ctx s rules hr

private theorem message_callcode_legacy (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.MessageOp.step ctx s .callcode) (Staging.MessageOp.step ctx s.toLegacy .callcode) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_callcode_state (ctx : CallContext) (s : Checked.Frame.State) (rules : StateGasRules)
    (hr : ctx.block.rules.stateGas = some rules) :
    Square (Checked.MessageOp.step ctx s .callcode) (Staging.MessageOp.step ctx s.toLegacy .callcode) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_callcode (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.MessageOp.step ctx s .callcode) (Staging.MessageOp.step ctx s.toLegacy .callcode) := by
  cases hr : ctx.block.rules.stateGas with
  | none => exact message_callcode_legacy ctx s hr
  | some rules => exact message_callcode_state ctx s rules hr

private theorem message_delegatecall_legacy (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.MessageOp.step ctx s .delegatecall) (Staging.MessageOp.step ctx s.toLegacy .delegatecall) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_delegatecall_state (ctx : CallContext) (s : Checked.Frame.State) (rules : StateGasRules)
    (hr : ctx.block.rules.stateGas = some rules) :
    Square (Checked.MessageOp.step ctx s .delegatecall) (Staging.MessageOp.step ctx s.toLegacy .delegatecall) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_delegatecall (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.MessageOp.step ctx s .delegatecall) (Staging.MessageOp.step ctx s.toLegacy .delegatecall) := by
  cases hr : ctx.block.rules.stateGas with
  | none => exact message_delegatecall_legacy ctx s hr
  | some rules => exact message_delegatecall_state ctx s rules hr

private theorem message_staticcall_legacy (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.MessageOp.step ctx s .staticcall) (Staging.MessageOp.step ctx s.toLegacy .staticcall) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_staticcall_state (ctx : CallContext) (s : Checked.Frame.State) (rules : StateGasRules)
    (hr : ctx.block.rules.stateGas = some rules) :
    Square (Checked.MessageOp.step ctx s .staticcall) (Staging.MessageOp.step ctx s.toLegacy .staticcall) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_staticcall (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.MessageOp.step ctx s .staticcall) (Staging.MessageOp.step ctx s.toLegacy .staticcall) := by
  cases hr : ctx.block.rules.stateGas with
  | none => exact message_staticcall_legacy ctx s hr
  | some rules => exact message_staticcall_state ctx s rules hr

private theorem message_create_legacy (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.MessageOp.step ctx s .create) (Staging.MessageOp.step ctx s.toLegacy .create) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_create_state (ctx : CallContext) (s : Checked.Frame.State) (rules : StateGasRules)
    (hr : ctx.block.rules.stateGas = some rules) :
    Square (Checked.MessageOp.step ctx s .create) (Staging.MessageOp.step ctx s.toLegacy .create) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_create (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.MessageOp.step ctx s .create) (Staging.MessageOp.step ctx s.toLegacy .create) := by
  cases hr : ctx.block.rules.stateGas with
  | none => exact message_create_legacy ctx s hr
  | some rules => exact message_create_state ctx s rules hr

private theorem message_create2_legacy (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.MessageOp.step ctx s .create2) (Staging.MessageOp.step ctx s.toLegacy .create2) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_create2_state (ctx : CallContext) (s : Checked.Frame.State) (rules : StateGasRules)
    (hr : ctx.block.rules.stateGas = some rules) :
    Square (Checked.MessageOp.step ctx s .create2) (Staging.MessageOp.step ctx s.toLegacy .create2) := by
  simp only [Checked.MessageOp.step, Staging.MessageOp.step, hr]
  message_walk

private theorem message_create2 (ctx : CallContext) (s : Checked.Frame.State) :
    Square (Checked.MessageOp.step ctx s .create2) (Staging.MessageOp.step ctx s.toLegacy .create2) := by
  cases hr : ctx.block.rules.stateGas with
  | none => exact message_create2_legacy ctx s hr
  | some rules => exact message_create2_state ctx s rules hr

theorem MessageOp.step (ctx : CallContext) (s : Checked.Frame.State) (op : Jaune.MessageOp) :
    Square (Checked.MessageOp.step ctx s op) (Staging.MessageOp.step ctx s.toLegacy op) := by
  cases op with
  | call => exact message_call ctx s
  | callcode => exact message_callcode ctx s
  | delegatecall => exact message_delegatecall ctx s
  | staticcall => exact message_staticcall ctx s
  | create => exact message_create ctx s
  | create2 => exact message_create2 ctx s

end Jaune.MemorySimulation
