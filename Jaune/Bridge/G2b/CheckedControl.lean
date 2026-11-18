import Jaune.Bridge.G2b.CheckedWalk
import Jaune.MessageCall.CheckedControl

namespace Jaune.MemorySimulation

theorem Frame.Exit.catchHalt {x : Except (ExceptionalHalt × Checked.Frame.State) (Except Fault Checked.Frame.Exit)}
    {y : Except (ExceptionalHalt × Frame.State) (Except Fault Frame.Exit)} (h : Square x y) :
    Square (Checked.Frame.Exit.catchHalt x) (Jaune.Frame.Exit.catchHalt y) := by
  change erase x = y at h
  subst y
  cases x with
  | error p => cases p; rfl
  | ok o => cases o <;> rfl

theorem JumpOp.runCore (pc : Nat) (ctx : CallContext) (s : Checked.Frame.State) (j : Jaune.JumpOp) :
    Square (Checked.JumpOp.runCore pc ctx s j) (Staging.JumpOp.runCore pc ctx s.toLegacy j) := by
  cases j <;> simp only [Checked.JumpOp.runCore, Staging.JumpOp.runCore] <;> checked_sq_walk

theorem JumpOp.run (r : Checked.Frame.Running) (j : Jaune.JumpOp) :
    Square (Checked.JumpOp.run r j) (Staging.JumpOp.run r.toLegacy j) := by
  unfold Checked.JumpOp.run Staging.JumpOp.run
  rw [show r.toLegacy.state = r.state.toLegacy from rfl, show r.toLegacy.pc = r.pc from rfl,
    show r.toLegacy.context = r.context from rfl, (JumpOp.runCore r.pc r.context r.state j).legacy_eq]
  rcases Checked.JumpOp.runCore r.pc r.context r.state j with ⟨e, s⟩ | ⟨pc, s⟩ <;> rfl

private theorem subtractBalance_toLegacy (s : Checked.Frame.State) (a : Address) (v : U256) :
    s.toLegacy.subtractBalance a v = (s.subtractBalance a v).map Checked.Frame.State.toLegacy := by
  unfold Jaune.Frame.State.subtractBalance Checked.Frame.State.subtractBalance
  change (s.world.subtractBalance a v).map _ = _
  cases s.world.subtractBalance a v <;> rfl

private theorem creditBeneficiary_legacy (rules : ForkRules) (a : Address) (v : U256) (s : Checked.Frame.State) :
    s.toLegacy.creditBeneficiary rules a v = (s.creditBeneficiary rules a v).toLegacy := by
  unfold Jaune.Frame.State.creditBeneficiary Checked.Frame.State.creditBeneficiary
  cases rules.settlement.eraseEmptyOnModify <;> rfl

private theorem emitTransferLog_legacy (a b : Address) (v : U256) (s : Checked.Frame.State) :
    s.toLegacy.emitTransferLog a b v = (s.emitTransferLog a b v).toLegacy := by
  unfold Jaune.Frame.State.emitTransferLog Checked.Frame.State.emitTransferLog
  by_cases h : a = b ∨ v = 0 <;> simp only [h, ↓reduceIte] <;> rfl

private theorem creditRefund_legacy (rules : ForkRules) (scheduled : Prop) [Decidable scheduled]
    (s : Checked.Frame.State) :
    s.toLegacy.creditSelfdestructRefund rules scheduled = (s.creditSelfdestructRefund rules scheduled).toLegacy := by
  unfold Jaune.Frame.State.creditSelfdestructRefund Checked.Frame.State.creditSelfdestructRefund
  by_cases h : scheduled <;> simp only [h, ↓reduceIte] <;> rfl

private theorem legacy_createdAccounts (s : Checked.Frame.State) : s.toLegacy.createdAccounts = s.createdAccounts := rfl
private theorem legacy_selfDestructs (s : Checked.Frame.State) : s.toLegacy.selfDestructs = s.selfDestructs := rfl
private theorem legacy_setBalance (s : Checked.Frame.State) (a : Address) (v : U256) :
    s.toLegacy.setBalance a v = (s.setBalance a v).toLegacy := rfl
private theorem legacy_addSelfDestruct (s : Checked.Frame.State) (a : Address) :
    s.toLegacy.addSelfDestruct a = (s.addSelfDestruct a).toLegacy := rfl
private theorem legacy_addBalance (s : Checked.Frame.State) (a : Address) (v : U256) :
    s.toLegacy.addBalance a v = (s.addBalance a v).toLegacy := rfl

private theorem recordAccountRead_accessedAddresses (s : Checked.Frame.State) (r : ForkRules) (a : Address) :
    (s.recordAccountRead r a).accessedAddresses = s.accessedAddresses := rfl
private theorem legacy_recordAccountRead_accessedAddresses (s : Frame.State) (r : ForkRules) (a : Address) :
    (s.recordAccountRead r a).accessedAddresses = s.accessedAddresses := rfl

local macro "selfdestruct_align" : tactic => `(tactic| simp only [subtractBalance_toLegacy,
  creditBeneficiary_legacy, emitTransferLog_legacy, creditRefund_legacy, legacy_recordAccountRead,
  legacy_addAccessedAddress, legacy_account, legacy_balance, legacy_accessedAddresses,
  legacy_createdAccounts, legacy_selfDestructs, legacy_setBalance, legacy_addSelfDestruct,
  legacy_addBalance, legacy_gasLeft, erase_pair, erase_state, erase_same])

private theorem selfdestruct_before (ctx : CallContext) (s : Checked.Frame.State)
    (hr : ctx.block.rules.stateGas = none) :
    Square (Checked.HaltOp.run ctx s .selfdestruct) (Staging.HaltOp.run ctx s.toLegacy .selfdestruct) := by
  simp only [Checked.HaltOp.run, Staging.HaltOp.run, hr]
  apply Frame.Exit.catchHalt
  refine Square.bind (Frame.State.popToAddress s) ?_
  rintro ⟨donee, s1⟩
  dsimp only
  simp only [erase_pair, erase_state, erase_same]
  cases ha : ctx.block.rules.access <;>
    try (by_cases hcold : donee ∈ s1.accessedAddresses <;>
      simp only [recordAccountRead_accessedAddresses, legacy_recordAccountRead_accessedAddresses,
        legacy_accessedAddresses, hcold, not_true_eq_false, not_false_eq_true, ↓reduceIte])
  all_goals
    selfdestruct_align
    refine Square.bind (Frame.State.chargeGas _ _) ?_
    intro s2
    refine Square.bind (Frame.State.assertDynamic _ _) ?_
    intro _
    selfdestruct_align
    cases hsub : s2.subtractBalance ctx.recipient _ <;> simp only [Option.map_none, Option.map_some]
    · rfl
    · selfdestruct_align
      split <;> rfl

private theorem selfdestruct_amsterdam (ctx : CallContext) (s : Checked.Frame.State) (sg : StateGasRules)
    (hr : ctx.block.rules.stateGas = some sg) :
    Square (Checked.HaltOp.run ctx s .selfdestruct) (Staging.HaltOp.run ctx s.toLegacy .selfdestruct) := by
  simp only [Checked.HaltOp.run, Staging.HaltOp.run, hr]
  apply Frame.Exit.catchHalt
  refine Square.bind (Frame.State.assertDynamic s ctx) ?_
  intro _
  refine Square.bind (Frame.State.popToAddress s) ?_
  rintro ⟨donee, s1⟩
  dsimp only
  simp only [erase_pair, erase_state, erase_same, legacy_gasLeft]
  by_cases hcold : donee ∈ s1.accessedAddresses <;>
    simp only [legacy_accessedAddresses, hcold, not_true_eq_false, not_false_eq_true, ↓reduceIte]
  all_goals
    selfdestruct_align
    refine Square.bind (Square.assert _ _) ?_
    intro _
    refine Square.bind (Frame.State.chargeGas _ _) ?_
    intro s2
    refine Square.bind (Frame.State.chargeStateGas _ _) ?_
    intro s3
    selfdestruct_align
    cases hsub : s3.subtractBalance ctx.recipient _ <;> simp only [Option.map_none, Option.map_some]
    · rfl
    · selfdestruct_align
      split <;> rfl

theorem HaltOp.run (ctx : CallContext) (s : Checked.Frame.State) (h : Jaune.HaltOp) :
    Square (Checked.HaltOp.run ctx s h) (Staging.HaltOp.run ctx s.toLegacy h) := by
  cases h with
  | stop => rfl
  | return_ | revert =>
    simp only [Checked.HaltOp.run, Staging.HaltOp.run]
    apply Frame.Exit.catchHalt
    checked_sq_walk
  | selfdestruct =>
    cases hr : ctx.block.rules.stateGas with
    | none => exact selfdestruct_before ctx s hr
    | some sg => exact selfdestruct_amsterdam ctx s sg hr

end Jaune.MemorySimulation
