import Jaune.Instructions.Shuffle
import Jaune.Instructions.MachineSteps
import Jaune.Instructions.WordFacts
import Jaune.MessageCall.Step

/-! The Shuffle family's effect law, proved once, its per-row table lemmas, and the lemmas that the
checked interpreter reads its rows: `Checked.PlainOp.run` for `DUP`/`SWAP` and
`Checked.NextOp.step` for `DUPN`/`SWAPN`/`EXCHANGE`, for every input and every `Fork`. The rows'
agreement with the per-opcode arms is in `Jaune.Bridge.G2b.CheckedRowAgreement`. -/

namespace Jaune

open Jaune

/-- A shuffle on a machine is its list shuffle, with the overflow check for `DUP`. -/
theorem Shuffle.run_eq (sh : Shuffle) (m : Machine) :
    sh.run m = match sh.apply m.stack with
      | none => .error (.stackUnderflow .none, m)
      | some stack =>
        if sh.grows ∧ ¬ m.stack.length < 1024 then .error (.stackOverflow .none, m)
        else .ok { m with stack := stack } := by
  cases sh with
  | dup index =>
    simp only [Shuffle.run, Shuffle.apply, Shuffle.grows, true_and]
    cases m.stack[index]? with
    | none => rfl
    | some word =>
      simp only [Option.map_some, Machine.push]
      by_cases hl : m.stack.length < 1024 <;> simp [hl]
  | swap index =>
    simp only [Shuffle.run, Shuffle.apply, Shuffle.grows]
    cases List.swap m.stack index <;> simp
  | exchange i j =>
    simp only [Shuffle.run, Shuffle.apply, Shuffle.grows]
    cases List.exchange m.stack i j <;> simp

/-- **Family effect law (success).** A shuffle row is available, charges exactly its cost, and
replaces the stack by its shuffle; memory, state gas and return data are kept. -/
theorem ShuffleRow.step_ok {row : ShuffleRow} {opcodes : OpcodeRules} {m out : Machine}
    (h : row.step opcodes m = .ok out) :
    row.available opcodes = true ∧ row.cost ≤ m.gasLeft ∧
      ∃ sh stack, row.shuffle = some sh ∧ sh.apply m.stack = some stack ∧
        (sh.grows = true → m.stack.length < 1024) ∧
        out = { m with gasLeft := m.gasLeft - row.cost, stack := stack } := by
  cases ha : row.available opcodes with
  | false => simp [ShuffleRow.step, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | true =>
    refine ⟨rfl, ?_⟩
    simp only [ShuffleRow.step, ha, ↓reduceIte, bind, Except.bind] at h
    cases hc : m.chargeGas row.cost with
    | error e => simp [hc] at h
    | ok charged =>
      obtain ⟨enough, rfl⟩ := InstructionStep.chargeGas_eq_ok hc
      simp only [hc] at h
      refine ⟨enough, ?_⟩
      cases hs : row.shuffle with
      | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
      | some sh =>
        simp only [hs] at h
        rw [Shuffle.run_eq] at h
        dsimp only at h
        cases hap : sh.apply m.stack with
        | none => simp [hap] at h
        | some stack =>
          simp only [hap] at h
          split at h
          · contradiction
          · rename_i hno
            cases h
            refine ⟨sh, stack, rfl, hap, fun hg => ?_, rfl⟩
            by_contra hl
            exact hno ⟨hg, hl⟩

/-- **Family effect law (halting).** A shuffle row halts in exactly this order: `invalidOpcode`
(unavailable, state unchanged), `outOfGas` (state unchanged), `invalidOpcode` (an immediate that
does not decode, charge kept), `stackUnderflow` (charge kept), `stackOverflow` (`DUP` only,
charge kept). -/
theorem ShuffleRow.step_error {row : ShuffleRow} {opcodes : OpcodeRules} {m out : Machine}
    {e : ExceptionalHalt} (h : row.step opcodes m = .error (e, out)) :
    (row.available opcodes = false ∧ e = .invalidOpcode .none ∧ out = m) ∨
    (row.available opcodes = true ∧ m.gasLeft < row.cost ∧ e = .outOfGas .none ∧ out = m) ∨
    (row.available opcodes = true ∧ row.cost ≤ m.gasLeft ∧ row.shuffle = none ∧
      e = .invalidOpcode .none ∧ out = { m with gasLeft := m.gasLeft - row.cost }) ∨
    (∃ sh, row.available opcodes = true ∧ row.cost ≤ m.gasLeft ∧ row.shuffle = some sh ∧
      sh.apply m.stack = none ∧
      e = .stackUnderflow .none ∧ out = { m with gasLeft := m.gasLeft - row.cost }) ∨
    (∃ sh stack, row.available opcodes = true ∧ row.cost ≤ m.gasLeft ∧ row.shuffle = some sh ∧
      sh.apply m.stack = some stack ∧ sh.grows = true ∧ 1024 ≤ m.stack.length ∧
      e = .stackOverflow .none ∧ out = { m with gasLeft := m.gasLeft - row.cost }) := by
  cases ha : row.available opcodes with
  | false =>
    simp [ShuffleRow.step, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    rcases h with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [ShuffleRow.step, ha, ↓reduceIte, bind, Except.bind] at h
    cases hc : m.chargeGas row.cost with
    | error err =>
      simp only [hc] at h
      cases h
      obtain ⟨rfl, hlt, rfl⟩ := InstructionStep.chargeGas_eq_error hc
      exact Or.inr (Or.inl ⟨rfl, hlt, rfl, rfl⟩)
    | ok charged =>
      obtain ⟨enough, rfl⟩ := InstructionStep.chargeGas_eq_ok hc
      simp only [hc] at h
      cases hs : row.shuffle with
      | none =>
        simp only [hs, throw, throwThe, MonadExceptOf.throw, Except.error.injEq,
          Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, enough, rfl, rfl, rfl⟩))
      | some sh =>
        simp only [hs] at h
        rw [Shuffle.run_eq] at h
        dsimp only at h
        cases hap : sh.apply m.stack with
        | none =>
          simp only [hap, Except.error.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨sh, rfl, enough, rfl, hap, rfl, rfl⟩)))
        | some stack =>
          simp only [hap] at h
          split at h
          · rename_i hyes
            simp only [Except.error.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨sh, stack, rfl, enough, rfl, hap, hyes.1, Nat.le_of_not_lt hyes.2, rfl, rfl⟩)))
          · contradiction

/-- On both channels a shuffle row changes only the stack and the gas left, and never adds gas:
memory, state gas and return data are kept. -/
theorem ShuffleRow.step_frame (row : ShuffleRow) (opcodes : OpcodeRules) (m : Machine) :
    (match row.step opcodes m with
      | .ok out | .error (_, out) =>
        ∃ (stack : List U256) (gasLeft : Nat), gasLeft ≤ m.gasLeft ∧
          out = { m with stack := stack, gasLeft := gasLeft }) := by
  cases h : row.step opcodes m with
  | ok out =>
    obtain ⟨_, _, sh, stack, _, _, _, rfl⟩ := ShuffleRow.step_ok h
    exact ⟨stack, _, Nat.sub_le _ _, rfl⟩
  | error e =>
    rcases e with ⟨reason, out⟩
    rcases ShuffleRow.step_error h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    all_goals first
      | exact ⟨_, _, Nat.le_refl _, rfl⟩
      | exact ⟨_, _, Nat.sub_le _ _, rfl⟩

theorem ShuffleRow.step_gasMeasure_lt_of_ok {row : ShuffleRow} {opcodes : OpcodeRules}
    {m out : Machine} (hpos : 0 < row.cost) (h : row.step opcodes m = .ok out) :
    out.gasMeasure < m.gasMeasure := by
  obtain ⟨_, enough, _, _, _, _, _, rfl⟩ := ShuffleRow.step_ok h
  simp only [Machine.gasMeasure]
  omega

/-! ### Table lemmas -/

theorem PlainOp.shuffleRow?_isSome_iff (op : Jaune.PlainOp) :
    (PlainOp.shuffleRow? op).isSome = true ↔ (∃ n, op = .dup n) ∨ (∃ n, op = .swap n) := by
  cases op <;> simp [PlainOp.shuffleRow?, PlainOp.family]

theorem NextOp.shuffleRow?_isSome_iff (n : Jaune.NextOp) :
    (NextOp.shuffleRow? n).isSome = true ↔
      (∃ i, n = .dupn i) ∨ (∃ i, n = .swapn i) ∨ (∃ i, n = .exchange i) := by
  cases n <;> simp [NextOp.shuffleRow?, NextOp.dupnRow, NextOp.swapnRow, NextOp.exchangeRow]

theorem PlainOp.shuffleRow?_cost {op : Jaune.PlainOp} {row : ShuffleRow}
    (h : PlainOp.shuffleRow? op = some row) : row.cost = Gas.veryLow ∧ 0 < row.cost := by
  cases op <;> simp only [PlainOp.shuffleRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact ⟨rfl, by simp [Gas.veryLow]⟩

theorem NextOp.shuffleRow?_cost {n : Jaune.NextOp} {row : ShuffleRow}
    (h : NextOp.shuffleRow? n = some row) : row.cost = Gas.veryLow ∧ 0 < row.cost := by
  cases n <;> simp only [NextOp.shuffleRow?, NextOp.dupnRow, NextOp.swapnRow, NextOp.exchangeRow, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> exact ⟨rfl, by simp [Gas.veryLow]⟩

/-- `DUP` and `SWAP` read no rule field. -/
theorem PlainOp.shuffleRow?_available {op : Jaune.PlainOp} {row : ShuffleRow}
    (h : PlainOp.shuffleRow? op = some row) (opcodes : OpcodeRules) :
    row.available opcodes = true := by
  cases op <;> simp only [PlainOp.shuffleRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-- The only rule field EIP-8024's rows read: `opcodes.stackAccess`. -/
theorem NextOp.shuffleRow?_available {n : Jaune.NextOp} {row : ShuffleRow}
    (h : NextOp.shuffleRow? n = some row) (opcodes : OpcodeRules) :
    row.available opcodes = opcodes.stackAccess := by
  cases n <;> simp only [NextOp.shuffleRow?, NextOp.dupnRow, NextOp.swapnRow, NextOp.exchangeRow, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-! ### Table lemmas: the dispatch reads the rows -/

theorem PlainOp.shuffleRow?_eq_some {op : Jaune.PlainOp} {row : ShuffleRow} :
    PlainOp.shuffleRow? op = some row ↔ PlainOp.family op = .shuffle row := by
  unfold PlainOp.shuffleRow?
  cases PlainOp.family op <;> simp

theorem PlainOp.shuffleRow?_run_eq {op : Jaune.PlainOp} {row : ShuffleRow}
    (hrow : PlainOp.shuffleRow? op = some row) (r : Frame.Running) :
    r.state.liftMachine (row.step r.context.block.rules.opcodes) = PlainOp.run r op := by
  simp only [PlainOp.run, PlainOp.runCore, PlainOp.shuffleRow?_eq_some.1 hrow, Family.run]

/-- `DUPN`, `SWAPN` and `EXCHANGE` are their rows, lifted by `liftMachine` and turned into a step
at the next program counter, by the definition of `NextOp.step`. -/
theorem NextOp.shuffleRow?_step_eq {n : Jaune.NextOp} {row : ShuffleRow}
    (hrow : NextOp.shuffleRow? n = some row) (r : Frame.Running) :
    Step.ofHalt (r.pc + n.size) (r.state.liftMachine (row.step r.context.block.rules.opcodes)) =
      NextOp.step r n := by
  cases n <;> simp only [NextOp.shuffleRow?, NextOp.dupnRow, NextOp.swapnRow, NextOp.exchangeRow, Option.some.injEq, reduceCtorEq] at hrow <;>
    subst hrow <;> rfl

/-! ### What the lift keeps, and fork uniformity -/

/-- `DUP` and `SWAP` keep the world, the substate and the trail, on both channels. -/
theorem PlainOp.shuffle_run_keeps {op : Jaune.PlainOp}
    (hrow : (PlainOp.shuffleRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with
      | .ok s' | .error (_, s') =>
        s'.world = r.state.world ∧ s'.substate = r.state.substate ∧ s'.trail = r.state.trail) := by
  cases h : PlainOp.shuffleRow? op with
  | none => simp [h] at hrow
  | some row =>
    rw [← PlainOp.shuffleRow?_run_eq h]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes r.state.machine <;> exact ⟨rfl, rfl, rfl⟩

theorem PlainOp.shuffle_run_gasMeasure_lt {op : Jaune.PlainOp}
    (hrow : (PlainOp.shuffleRow? op).isSome) (r : Frame.Running) {s' : Frame.State}
    (hok : PlainOp.run r op = .ok s') : s'.machine.gasMeasure < r.state.machine.gasMeasure := by
  cases h : PlainOp.shuffleRow? op with
  | none => simp [h] at hrow
  | some row =>
    rw [← PlainOp.shuffleRow?_run_eq h] at hok
    unfold Frame.State.liftMachine at hok
    cases hs : row.step r.context.block.rules.opcodes r.state.machine with
    | error e => simp [hs] at hok
    | ok m' =>
      simp only [hs, Except.ok.injEq] at hok
      subst hok
      exact ShuffleRow.step_gasMeasure_lt_of_ok (PlainOp.shuffleRow?_cost h).2 hs

/-- `DUP` and `SWAP` do not depend on the fork at all. -/
theorem PlainOp.shuffle_run_congr_fork {op : Jaune.PlainOp}
    (hrow : (PlainOp.shuffleRow? op).isSome) (r : Frame.Running) (f' : Fork) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } } op =
      PlainOp.run r op := by
  cases h : PlainOp.shuffleRow? op with
  | none => simp [h] at hrow
  | some row =>
    rw [← PlainOp.shuffleRow?_run_eq h, ← PlainOp.shuffleRow?_run_eq h]
    refine Frame.State.liftMachine_congr r.state ?_
    simp only [ShuffleRow.step, PlainOp.shuffleRow?_available h]

/-- EIP-8024's operations depend on the fork only through `opcodes.stackAccess`. -/
theorem NextOp.shuffle_step_congr_fork {n : Jaune.NextOp}
    (hrow : (NextOp.shuffleRow? n).isSome) (r : Frame.Running) (f' : Fork)
    (h : (Fork.ruleSet r.context.block.fork).opcodes.stackAccess =
      (Fork.ruleSet f').opcodes.stackAccess) :
    NextOp.step { r with context := { r.context with block := { r.context.block with fork := f' } } } n =
      NextOp.step r n := by
  cases hr : NextOp.shuffleRow? n with
  | none => simp [hr] at hrow
  | some row =>
    rw [← NextOp.shuffleRow?_step_eq hr, ← NextOp.shuffleRow?_step_eq hr]
    congr 2
    funext m
    simp only [ShuffleRow.step, NextOp.shuffleRow?_available hr, BlockContext.rules] at h ⊢
    rw [h]

end Jaune
