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

macro "checked_sq_align" : tactic => `(tactic| simp_all only [erase_pair, erase_machine, erase_state,
  erase_same, legacy_stack, legacy_stateStack, legacy_stateMachine, legacy_accessedAddresses,
  legacy_accessedStorageKeys, legacy_account, legacy_balance, legacy_gasLeft, legacy_extCost,
  ↓reduceIte, ↓reduceDIte, reduceCtorEq, Option.some.injEq, Prod.mk.injEq])

macro "checked_sq_intro" : tactic => `(tactic| (intro a; try (guard_hyp a : _ × _; rcases a with ⟨_, _⟩); try dsimp only))

macro "checked_sq_leaf" : tactic => `(tactic| first
  | assumption
  | apply Frame.State.pushItem
  | apply Frame.State.applyUnary | apply Frame.State.applyBinary | apply Frame.State.applyTernary
  | apply Frame.State.push | apply Frame.State.pop | apply Frame.State.popToNat | apply Frame.State.popToAddress
  | apply Frame.State.popN | apply Frame.State.chargeGas | apply Frame.State.chargeStateGas
  | apply Frame.State.assertDynamic | apply Frame.State.memRead | apply Frame.State.memExtends | apply Frame.State.memWrite
  | apply Machine.pushItem | apply Machine.applyUnary | apply Machine.applyBinary | apply Machine.applyTernary
  | apply Machine.push | apply Machine.pop | apply Machine.popToNat | apply Machine.popToAddress
  | apply Machine.popN | apply Machine.chargeGas | apply Machine.chargeStateGas
  | apply Machine.memRead | apply Machine.memExtends | apply Machine.memWrite
  | apply Square.assert | rfl)

macro "checked_sq_one" : tactic => `(tactic| first
  | (with_reducible solve | checked_sq_leaf)
  | (solve | rfl)
  | (refine Square.bind (by solve | checked_sq_leaf) ?_; checked_sq_intro)
  | (with_reducible refine Square.bind ?_ ?_; rotate_left; checked_sq_intro)
  | (apply Frame.State.liftMachine; intro _)
  | (apply Frame.State.liftMachineValue; intro _)
  | (refine Square.ite rfl ?_ ?_ <;> intro _)
  | apply Square.ok | apply Square.error | apply Square.pair
  | simp only [erase_pair, erase_machine, erase_state, erase_same]
  | (split <;> try checked_sq_align))

macro "checked_sq_walk" : tactic => `(tactic| repeat' checked_sq_one)

end Jaune.MemorySimulation
