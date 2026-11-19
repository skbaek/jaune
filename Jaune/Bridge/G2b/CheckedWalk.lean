import Jaune.Bridge.G2b.CheckedSimulation

namespace Jaune.MemorySimulation


@[simp] theorem legacy_stack (m : Checked.Machine) : m.toLegacy.stack = m.stack := rfl
@[simp] theorem legacy_stateMachine (s : Checked.Frame.State) : s.toLegacy.machine = s.machine.toLegacy := rfl
@[simp] theorem legacy_stateStack (s : Checked.Frame.State) : s.toLegacy.stack = s.stack := rfl
@[simp] theorem legacy_accessedAddresses (s : Checked.Frame.State) : s.toLegacy.accessedAddresses = s.accessedAddresses := rfl
@[simp] theorem legacy_accessedStorageKeys (s : Checked.Frame.State) : s.toLegacy.accessedStorageKeys = s.accessedStorageKeys := rfl
@[simp] theorem legacy_account (s : Checked.Frame.State) (a : Address) : s.toLegacy.account a = s.account a := rfl
@[simp] theorem legacy_balance (s : Checked.Frame.State) (a : Address) : s.toLegacy.balance a = s.balance a := rfl
@[simp] theorem legacy_gasLeft (s : Checked.Frame.State) : s.toLegacy.gasLeft = s.gasLeft := rfl
@[simp] theorem legacy_extCost (s : Checked.Frame.State) (pairs : List (Nat × Nat)) :
    s.toLegacy.extCost pairs = s.extCost pairs := rfl

theorem legacy_recordAccountRead (s : Checked.Frame.State) (r : ForkRules) (a : Address) :
    s.toLegacy.recordAccountRead r a = (s.recordAccountRead r a).toLegacy := rfl
theorem legacy_recordStorageRead (s : Checked.Frame.State) (r : ForkRules) (a : Address) (k : U256) :
    s.toLegacy.recordStorageRead r a k = (s.recordStorageRead r a k).toLegacy := rfl
theorem legacy_addAccessedAddress (s : Checked.Frame.State) (a : Address) :
    s.toLegacy.addAccessedAddress a = (s.addAccessedAddress a).toLegacy := rfl
theorem legacy_addAccessedStorageKey (s : Checked.Frame.State) (a : Address) (k : U256) :
    s.toLegacy.addAccessedStorageKey a k = (s.addAccessedStorageKey a k).toLegacy := rfl
theorem legacy_memExtends (s : Checked.Frame.State) (p : List (Nat × Nat)) :
    s.toLegacy.memExtends p = (s.memExtends p).toLegacy := rfl
theorem legacy_withReturnData (s : Checked.Frame.State) (b : Bytes) :
    s.toLegacy.withReturnData b = (s.withReturnData b).toLegacy := rfl
theorem legacy_withGasLeft (s : Checked.Frame.State) (n : Nat) :
    s.toLegacy.withGasLeft n = (s.withGasLeft n).toLegacy := rfl
theorem legacy_withRefund (s : Checked.Frame.State) (n : Int) :
    s.toLegacy.withRefund n = (s.withRefund n).toLegacy := rfl
theorem legacy_creditStateGasRefund (s : Checked.Frame.State) (n : Nat) :
    s.toLegacy.creditStateGasRefund n = (s.creditStateGasRefund n).toLegacy := rfl
theorem legacy_setStorageValue (s : Checked.Frame.State) (a : Address) (k v : U256) :
    s.toLegacy.setStorageValue a k v = (s.setStorageValue a k v).toLegacy := rfl
theorem legacy_setTransientValue (s : Checked.Frame.State) (a : Address) (k v : U256) :
    s.toLegacy.setTransientValue a k v = (s.setTransientValue a k v).toLegacy := rfl
theorem legacy_returnData (s : Checked.Frame.State)  :
    s.toLegacy.returnData = s.returnData := rfl
theorem legacy_transientValue (s : Checked.Frame.State) (a : Address) (k : U256) :
    s.toLegacy.transientValue a k = s.transientValue a k := rfl
theorem legacy_storageValue (s : Checked.Frame.State) (a : Address) (k : U256) :
    s.toLegacy.storageValue a k = s.storageValue a k := rfl
theorem legacy_memorySize (s : Checked.Frame.State)  :
    s.toLegacy.memory.size = s.memory.size := rfl
theorem legacy_refund (s : Checked.Frame.State)  :
    s.toLegacy.refund = s.refund := rfl
theorem legacy_readValue (m : Checked.Machine) (i n : Nat) : (m.toLegacy.memRead i n).1 = (m.memRead i n).1 := rfl
theorem legacy_readMachine (m : Checked.Machine) (i n : Nat) : (m.toLegacy.memRead i n).2 = (m.memRead i n).2.toLegacy := rfl
theorem legacy_machineReturnData (m : Checked.Machine) : m.toLegacy.returnData = m.returnData := rfl

macro "checked_sq_normal" : tactic => `(tactic| simp only [erase_pair, erase_machine, erase_state, erase_same, legacy_recordAccountRead, legacy_recordStorageRead, legacy_addAccessedAddress, legacy_addAccessedStorageKey, legacy_memExtends, legacy_withReturnData, legacy_withGasLeft, legacy_withRefund, legacy_creditStateGasRefund, legacy_setStorageValue, legacy_setTransientValue, legacy_returnData, legacy_transientValue, legacy_storageValue, legacy_memorySize, legacy_refund, legacy_readValue, legacy_readMachine, legacy_machineReturnData])

macro "checked_sq_align" : tactic => `(tactic| simp_all only [erase_pair, erase_machine, erase_state,
  erase_same, legacy_stack, legacy_stateStack, legacy_stateMachine, legacy_accessedAddresses,
  legacy_accessedStorageKeys, legacy_account, legacy_balance, legacy_gasLeft, legacy_extCost,
  ↓reduceIte, ↓reduceDIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq])

macro "checked_sq_intro" : tactic => `(tactic| (intro a; try (guard_hyp a : _ × _; rcases a with ⟨_, _⟩); try dsimp only))

/- Select a primitive square by the head of its checked expression, before tactic
unification can unfold an unrelated instruction body. -/
open Lean Elab Tactic Meta in
elab "checked_sq_leaf" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let args := target.getAppArgs
  unless target.getAppFn.isConstOf ``Square && args.size ≥ 2 do
    throwError "expected an erasure square"
  let some checkedArg := args[args.size - 2]? | throwError "expected an erasure square"
  let .const head _ := checkedArg.headBeta.getAppFn | throwError "no operation head"
  let squareName := head.replacePrefix `Jaune.Checked `Jaune.MemorySimulation
  unless squareName != head && (← getEnv).contains squareName do
    throwError "no primitive square for {head}"
  evalTactic (← `(tactic| apply $(mkIdent squareName)))

macro "checked_sq_one" : tactic => `(tactic| first
  | (solve | checked_sq_leaf)
  | (with_reducible rfl)
  | (refine Square.bind (by first | checked_sq_leaf | apply Square.assert | rfl) ?_; checked_sq_intro)
  | (with_reducible refine Square.bind ?_ ?_; rotate_left; checked_sq_intro)
  | (with_reducible apply Frame.State.liftMachine; intro _)
  | (with_reducible apply Frame.State.liftMachineValue; intro _)
  | (refine Square.ite rfl ?_ ?_ <;> intro _)
  | apply Square.ok | apply Square.error | apply Square.pair
  | checked_sq_normal
  | (solve | rfl)
  | (split <;> try checked_sq_align))

macro "checked_sq_walk" : tactic => `(tactic| repeat' checked_sq_one)

end Jaune.MemorySimulation
