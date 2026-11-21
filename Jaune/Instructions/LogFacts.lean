import Jaune.Instructions.Log
import Jaune.Instructions.MachineSteps
import Jaune.MessageCall.Plain

/-! The Log family's effect law, proved once, its table lemmas, and the lemma that
`Checked.PlainOp.run` reads its rows for `LOG0`–`LOG4`, for every input and every `Fork`. The rows'
agreement with the per-opcode arms is in `Jaune.Bridge.G2b.CheckedRowAgreement`. -/

namespace Jaune

open Jaune

/-- **Family effect law (success).** A log row pops the offset, the size and exactly
`row.topics` topics, charges `row.cost`, needs a non-static frame, and returns the log
`⟨recipient, topics, memory slice⟩`. The machine changes only in its stack, gas left and memory
(the read's extension); state gas and return data are kept. -/
theorem LogRow.step_ok {row : LogRow} {ctx : CallContext} {m out : Machine} {log : Log}
    (h : row.step ctx m = .ok (out, log)) :
    ctx.isStatic = false ∧ ∃ offset size topics rest,
      m.stack = offset :: size :: topics ++ rest ∧ topics.length = row.topics.val ∧
      row.cost m offset.toNat size.toNat ≤ m.gasLeft ∧
      log = ⟨ctx.recipient, topics, (m.memory.read offset.toNat size.toNat).1⟩ ∧
      out = { m with stack := rest, gasLeft := m.gasLeft - row.cost m offset.toNat size.toNat,
                     memory := (m.memory.read offset.toNat size.toNat).2 } := by
  simp only [LogRow.step, bind, Except.bind] at h
  cases h1 : m.popToNat with
  | error e => simp [h1] at h
  | ok p1 =>
    obtain ⟨offset, m1⟩ := p1
    obtain ⟨w1, t1, hs1, rfl, rfl⟩ := InstructionStep.popToNat_eq_ok h1
    simp only [h1] at h
    cases h2 : ({ m with stack := t1 } : Machine).popToNat with
    | error e => simp [h2] at h
    | ok p2 =>
      obtain ⟨size, m2⟩ := p2
      obtain ⟨w2, t2, hs2, rfl, rfl⟩ := InstructionStep.popToNat_eq_ok h2
      simp only [h2] at h
      cases h3 : ({ m with stack := t2 } : Machine).popList row.topics with
      | error e => simp [h3] at h
      | ok p3 =>
        obtain ⟨topics, m3⟩ := p3
        obtain ⟨rest, hs3, hlen, rfl⟩ := InstructionStep.popList_eq_ok h3
        simp only [h3] at h
        cases h4 : ({ m with stack := rest } : Machine).chargeGas
            (row.cost { m with stack := rest } w1.toNat w2.toNat) with
        | error e => simp [h4] at h
        | ok m4 =>
          obtain ⟨enough, rfl⟩ := InstructionStep.chargeGas_eq_ok h4
          simp only [h4] at h
          by_cases hst : ctx.isStatic
          · simp [hst, Except.assert] at h
          · simp only [hst, Except.assert, Bool.not_false, ↓reduceIte, Machine.readMemory,
              Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨by simpa using hst, w1, w2, topics, rest, ?_, hlen, enough, rfl, rfl⟩
            simp only at hs2 hs3
            simp [hs1, hs2, hs3]

/-- **Family effect law (halting).** A log row halts in exactly this order: `stackUnderflow`
(stack emptied), `outOfGas` (operands popped), `writeInStaticContext` (operands popped, charge
kept). -/
theorem LogRow.step_error {row : LogRow} {ctx : CallContext} {m out : Machine}
    {e : ExceptionalHalt} (h : row.step ctx m = .error (e, out)) :
    (e = .stackUnderflow .none ∧ m.stack.length < 2 + row.topics.val ∧
      out = { m with stack := [] }) ∨
    (∃ offset size topics rest,
      m.stack = offset :: size :: topics ++ rest ∧ topics.length = row.topics.val ∧
      m.gasLeft < row.cost m offset.toNat size.toNat ∧
      e = .outOfGas .none ∧ out = { m with stack := rest }) ∨
    (∃ offset size topics rest,
      m.stack = offset :: size :: topics ++ rest ∧ topics.length = row.topics.val ∧
      row.cost m offset.toNat size.toNat ≤ m.gasLeft ∧ ctx.isStatic = true ∧
      e = .writeInStaticContext .none ∧
      out = { m with stack := rest, gasLeft := m.gasLeft - row.cost m offset.toNat size.toNat }) := by
  simp only [LogRow.step, bind, Except.bind] at h
  cases h1 : m.popToNat with
  | error err =>
    simp only [h1] at h
    cases h
    obtain ⟨rfl, hs, rfl⟩ := InstructionStep.popToNat_eq_error h1
    exact Or.inl ⟨rfl, by simp [hs], rfl⟩
  | ok p1 =>
    obtain ⟨offset, m1⟩ := p1
    obtain ⟨w1, t1, hs1, rfl, rfl⟩ := InstructionStep.popToNat_eq_ok h1
    simp only [h1] at h
    cases h2 : ({ m with stack := t1 } : Machine).popToNat with
    | error err =>
      simp only [h2] at h
      cases h
      obtain ⟨rfl, hs, rfl⟩ := InstructionStep.popToNat_eq_error h2
      simp only at hs
      exact Or.inl ⟨rfl, by simp [hs1, hs]; omega, rfl⟩
    | ok p2 =>
      obtain ⟨size, m2⟩ := p2
      obtain ⟨w2, t2, hs2, rfl, rfl⟩ := InstructionStep.popToNat_eq_ok h2
      simp only [h2] at h
      simp only at hs2
      cases h3 : ({ m with stack := t2 } : Machine).popList row.topics with
      | error err =>
        simp only [h3] at h
        cases h
        obtain ⟨rfl, hlen, rfl⟩ := InstructionStep.popList_eq_error h3
        simp only at hlen
        exact Or.inl ⟨rfl, by simp [hs1, hs2]; omega, rfl⟩
      | ok p3 =>
        obtain ⟨topics, m3⟩ := p3
        obtain ⟨rest, hs3, hlen, rfl⟩ := InstructionStep.popList_eq_ok h3
        simp only [h3] at h
        simp only at hs3
        have hstack : m.stack = w1 :: w2 :: topics ++ rest := by simp [hs1, hs2, hs3]
        cases h4 : ({ m with stack := rest } : Machine).chargeGas
            (row.cost { m with stack := rest } w1.toNat w2.toNat) with
        | error err =>
          simp only [h4] at h
          cases h
          obtain ⟨rfl, hlt, rfl⟩ := InstructionStep.chargeGas_eq_error h4
          exact Or.inr (Or.inl ⟨w1, w2, topics, rest, hstack, hlen, hlt, rfl, rfl⟩)
        | ok m4 =>
          obtain ⟨enough, rfl⟩ := InstructionStep.chargeGas_eq_ok h4
          simp only [h4] at h
          by_cases hst : ctx.isStatic
          · simp only [hst, Except.assert, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
              Except.error.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact Or.inr (Or.inr ⟨w1, w2, topics, rest, hstack, hlen, enough, hst, rfl, rfl⟩)
          · simp [hst, Except.assert, Machine.readMemory] at h

/-- On the success channel a log step adds no gas and keeps state gas and return data; on the
error channel it also keeps memory. -/
theorem LogRow.step_frame (row : LogRow) (ctx : CallContext) (m : Machine) :
    (match row.step ctx m with
      | .ok (out, _) => out.gasLeft ≤ m.gasLeft ∧ out.stateGas = m.stateGas ∧
          out.returnData = m.returnData
      | .error (_, out) => out.gasLeft ≤ m.gasLeft ∧ out.stateGas = m.stateGas ∧
          out.returnData = m.returnData ∧ out.memory = m.memory) := by
  cases h : row.step ctx m with
  | ok p =>
    obtain ⟨out, log⟩ := p
    obtain ⟨_, _, _, _, _, _, _, _, _, rfl⟩ := LogRow.step_ok h
    exact ⟨Nat.sub_le _ _, rfl, rfl⟩
  | error p =>
    obtain ⟨e, out⟩ := p
    rcases LogRow.step_error h with ⟨_, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
    · exact ⟨Nat.le_refl _, rfl, rfl, rfl⟩
    · exact ⟨Nat.sub_le _ _, rfl, rfl, rfl⟩

theorem LogRow.step_gasMeasure_lt_of_ok {row : LogRow} {ctx : CallContext} {m out : Machine}
    {log : Log} (hpos : 0 < row.base) (h : row.step ctx m = .ok (out, log)) :
    out.gasMeasure < m.gasMeasure := by
  obtain ⟨_, offset, size, _, _, _, _, enough, _, rfl⟩ := LogRow.step_ok h
  have : 0 < row.cost m offset.toNat size.toNat := by simp only [LogRow.cost]; omega
  simp only [Machine.gasMeasure]
  omega

/-! ### The lift -/

/-- `liftLog` changes, outside the machine, only the log list, and only by appending the step's
log on success. -/
theorem Frame.State.liftLog_eq (s : Frame.State)
    (r : Except (ExceptionalHalt × Machine) (Machine × Log)) :
    s.liftLog r = match r with
      | .error (e, m) => .error (e, { s with machine := m })
      | .ok (m, log) =>
        .ok { s with machine := m, substate := { s.substate with logs := s.substate.logs ++ [log] } } := by
  cases r with
  | error p => obtain ⟨e, m⟩ := p; rfl
  | ok p => obtain ⟨m, log⟩ := p; rfl

theorem Frame.State.liftLog_keeps (s : Frame.State)
    (r : Except (ExceptionalHalt × Machine) (Machine × Log)) :
    (match s.liftLog r with
      | .ok s' | .error (_, s') =>
        s'.world = s.world ∧ s'.trail = s.trail ∧
          s'.substate = { s.substate with logs := s'.substate.logs }) := by
  rw [Frame.State.liftLog_eq]
  cases r with
  | error p => obtain ⟨e, m⟩ := p; exact ⟨rfl, rfl, rfl⟩
  | ok p => obtain ⟨m, log⟩ := p; exact ⟨rfl, rfl, rfl⟩

/-! ### Table lemmas -/

theorem PlainOp.logRow?_isSome_iff (op : Jaune.PlainOp) :
    (PlainOp.logRow? op).isSome = true ↔ ∃ n, op = .log n := by
  cases op <;> simp [PlainOp.logRow?, PlainOp.family]

theorem PlainOp.logRow?_prices {op : Jaune.PlainOp} {row : LogRow}
    (h : PlainOp.logRow? op = some row) :
    row.base = Gas.log ∧ row.perByte = Gas.logData ∧ row.perTopic = Gas.logTopic ∧
      0 < row.base := by
  cases op <;> simp only [PlainOp.logRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h
  subst h
  exact ⟨rfl, rfl, rfl, by simp [Gas.log]⟩

/-! ### The dispatch reads the rows -/

theorem PlainOp.logRow?_eq_some {op : Jaune.PlainOp} {row : LogRow} :
    PlainOp.logRow? op = some row ↔ PlainOp.family op = .log row := by
  unfold PlainOp.logRow?
  cases PlainOp.family op <;> simp

/-- **Table lemma (`LOG0`–`LOG4`):** the row, lifted by `Frame.State.liftLog`, is `PlainOp.run`. -/
theorem PlainOp.logRow?_run_eq {op : Jaune.PlainOp} {row : LogRow}
    (hrow : PlainOp.logRow? op = some row) (r : Frame.Running) :
    r.state.liftLog (row.step r.context r.state.machine) = PlainOp.run r op := by
  simp only [PlainOp.run, PlainOp.runCore, PlainOp.logRow?_eq_some.1 hrow, Family.run]

/-- `LOG0`–`LOG4` keep the world and the trail, and of the substate change only the logs. -/
theorem PlainOp.log_run_keeps {op : Jaune.PlainOp} (hrow : (PlainOp.logRow? op).isSome)
    (r : Frame.Running) :
    (match PlainOp.run r op with
      | .ok s' | .error (_, s') =>
        s'.world = r.state.world ∧ s'.trail = r.state.trail ∧
          s'.substate = { r.state.substate with logs := s'.substate.logs }) := by
  cases h : PlainOp.logRow? op with
  | none => simp [h] at hrow
  | some row =>
    rw [← PlainOp.logRow?_run_eq h]
    exact Frame.State.liftLog_keeps _ _

theorem PlainOp.log_run_gasMeasure_lt {op : Jaune.PlainOp} (hrow : (PlainOp.logRow? op).isSome)
    (r : Frame.Running) {s' : Frame.State} (hok : PlainOp.run r op = .ok s') :
    s'.machine.gasMeasure < r.state.machine.gasMeasure := by
  cases h : PlainOp.logRow? op with
  | none => simp [h] at hrow
  | some row =>
    rw [← PlainOp.logRow?_run_eq h, Frame.State.liftLog_eq] at hok
    cases hs : row.step r.context r.state.machine with
    | error p => simp [hs] at hok
    | ok p =>
      obtain ⟨m', log⟩ := p
      simp only [hs, Except.ok.injEq] at hok
      subst hok
      exact LogRow.step_gasMeasure_lt_of_ok (PlainOp.logRow?_prices h).2.2.2 hs

/-- `LOG0`–`LOG4` do not depend on the fork at all. -/
theorem PlainOp.log_run_congr_fork {op : Jaune.PlainOp} (hrow : (PlainOp.logRow? op).isSome)
    (r : Frame.Running) (f' : Fork) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } } op =
      PlainOp.run r op := by
  cases h : PlainOp.logRow? op with
  | none => simp [h] at hrow
  | some row =>
    rw [← PlainOp.logRow?_run_eq h, ← PlainOp.logRow?_run_eq h]
    rfl

end Jaune
