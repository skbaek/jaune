import Jaune.Instructions.Read
import Jaune.Instructions.MemoryFacts

/-! Laws and bridges of the Read family. -/

namespace Jaune

open Jaune

/-! ### What a read's result does -/

/-- What a successful result does to the machine after the key's pop: a push of the read word
after the price, or `EXTCODECOPY`'s three pops, its price (access, per word, extension) and the
write of the code slice. -/
def ReadResult.Done : {t : ReadTarget} → ReadResult t → CallContext → World → t.Key → Nat →
    Machine → Machine → Prop
  | _, .push f, ctx, w, key, price, m, out =>
    price ≤ m.gasLeft ∧ m.stack.length < 1024 ∧
      out = { m with gasLeft := m.gasLeft - price, stack := f ctx w key :: m.stack }
  | _, .copyCode perWord, _, w, (a : Address), price, m, out =>
    ∃ d o n rest, m.stack = d :: o :: n :: rest ∧
      price + perWord * ceilDiv n.toNat 32 + m.memoryExpansionCost [(d.toNat, n.toNat)] ≤ m.gasLeft ∧
      out = { m with
        stack := rest
        gasLeft := m.gasLeft - (price + perWord * ceilDiv n.toNat 32 + m.memoryExpansionCost [(d.toNat, n.toNat)])
        memory := m.memory.write d.toNat
          ((Jaune.State.get w.state a).code.sliceD o.toNat n.toNat (HaltOp.toUInt8 .stop)) }

private theorem popToNat_ok {m out : Machine} {x : Nat} (h : m.popToNat = .ok (x, out)) :
    ∃ w rest, m.stack = w :: rest ∧ x = w.toNat ∧ out = { m with stack := rest } := by
  unfold Machine.popToNat at h
  split at h
  · cases h
  · rename_i w m' hp
    cases h
    obtain ⟨rest, hs, rfl⟩ := MemoryReadFacts.pop_ok_inversion hp
    exact ⟨w, rest, hs, rfl, rfl⟩

private theorem popToNat_error {m out : Machine} {e : ExceptionalHalt}
    (h : m.popToNat = .error (e, out)) : e = .stackUnderflow .none ∧ out = { m with stack := [] } := by
  unfold Machine.popToNat at h
  split at h
  · rename_i err hp
    cases h
    obtain ⟨rfl, -, rfl⟩ := MemoryReadFacts.pop_error_inversion hp
    exact ⟨rfl, rfl⟩
  · cases h

theorem ReadResult.finish_ok {t : ReadTarget} {r : ReadResult t} {ctx : CallContext} {w : World}
    {key : t.Key} {price : Nat} {warmed read : Option ReadAccessKey} {m out : Machine}
    {touch : ReadTouch} (h : r.finish ctx w key price warmed read m = .ok (out, touch)) :
    touch = { warmed := warmed, read := read } ∧ out.stateGas = m.stateGas ∧ out.returnData = m.returnData ∧
      r.Done ctx w key price m out := by
  cases r with
  | push f =>
    simp only [ReadResult.finish] at h
    split at h
    · cases h
    · rename_i m₁ hc
      obtain ⟨enough, rfl⟩ := MemoryReadFacts.chargeGas_ok_inversion hc
      split at h
      · cases h
      · rename_i m₂ hq
        obtain ⟨hlen, rfl⟩ := MemoryReadFacts.push_ok_inversion hq
        cases h
        exact ⟨rfl, rfl, rfl, enough, hlen, rfl⟩
  | copyCode perWord =>
    simp only [ReadResult.finish] at h
    split at h
    · cases h
    · rename_i d m₁ h1
      obtain ⟨wd, r1, hs1, rfl, rfl⟩ := popToNat_ok h1
      split at h
      · cases h
      · rename_i o m₂ h2
        obtain ⟨wo, r2, hs2, rfl, rfl⟩ := popToNat_ok h2
        split at h
        · cases h
        · rename_i n m₃ h3
          obtain ⟨wn, r3, hs3, rfl, rfl⟩ := popToNat_ok h3
          split at h
          · cases h
          · rename_i m₄ hc
            obtain ⟨enough, rfl⟩ := MemoryReadFacts.chargeGas_ok_inversion hc
            cases h
            simp only at hs2 hs3
            subst hs2 hs3
            exact ⟨rfl, rfl, rfl, wd, wo, wn, r3, hs1, enough, rfl⟩

theorem ReadResult.finish_error {t : ReadTarget} {r : ReadResult t} {ctx : CallContext}
    {w : World} {key : t.Key} {price : Nat} {warmed read : Option ReadAccessKey} {m out : Machine}
    {e : ExceptionalHalt} {touch : ReadTouch}
    (h : r.finish ctx w key price warmed read m = .error (e, out, touch)) :
    out.stateGas = m.stateGas ∧ out.returnData = m.returnData ∧
      ((e = .stackUnderflow .none ∧ touch = {}) ∨
       (e = .outOfGas .none ∧ touch = { warmed := warmed }) ∨
       (e = .stackOverflow .none ∧ touch = { warmed := warmed, read := read })) := by
  cases r with
  | push f =>
    simp only [ReadResult.finish] at h
    split at h
    · rename_i e' m' hc
      cases h
      obtain ⟨rfl, -, rfl⟩ := MemoryReadFacts.chargeGas_error_inversion hc
      exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · rename_i m₁ hc
      obtain ⟨-, rfl⟩ := MemoryReadFacts.chargeGas_ok_inversion hc
      split at h
      · rename_i e' m' hq
        cases h
        obtain ⟨rfl, -, rfl⟩ := MemoryReadFacts.push_error_inversion hq
        exact ⟨rfl, rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩
      · cases h
  | copyCode perWord =>
    simp only [ReadResult.finish] at h
    split at h
    · rename_i e' m' h1
      cases h
      obtain ⟨rfl, rfl⟩ := popToNat_error h1
      exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · rename_i d m₁ h1
      obtain ⟨_, _, _, rfl, rfl⟩ := popToNat_ok h1
      split at h
      · rename_i e' m' h2
        cases h
        obtain ⟨rfl, rfl⟩ := popToNat_error h2
        exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
      · rename_i o m₂ h2
        obtain ⟨_, _, _, rfl, rfl⟩ := popToNat_ok h2
        split at h
        · rename_i e' m' h3
          cases h
          obtain ⟨rfl, rfl⟩ := popToNat_error h3
          exact ⟨rfl, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · rename_i n m₃ h3
          obtain ⟨_, _, _, rfl, rfl⟩ := popToNat_ok h3
          split at h
          · rename_i e' m' hc
            cases h
            obtain ⟨rfl, -, rfl⟩ := MemoryReadFacts.chargeGas_error_inversion hc
            exact ⟨rfl, rfl, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
          · cases h

theorem ReadTarget.pop_ok {t : ReadTarget} {m out : Machine} {key : t.Key}
    (h : t.pop m = .ok (key, out)) :
    out = { m with stack := out.stack } := by
  cases t with
  | recipient => cases h; rfl
  | slot | transient =>
    obtain ⟨rest, hs, rfl⟩ := MemoryReadFacts.pop_ok_inversion h
    rfl
  | account =>
    simp only [ReadTarget.pop, Machine.popToAddress] at h
    split at h
    · cases h
    · rename_i x m' hp
      cases h
      obtain ⟨rest, hs, rfl⟩ := MemoryReadFacts.pop_ok_inversion hp
      rfl

theorem ReadTarget.pop_error {t : ReadTarget} {m out : Machine} {e : ExceptionalHalt}
    (h : t.pop m = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack = [] ∧ out = { m with stack := [] } := by
  cases t with
  | recipient => cases h
  | slot | transient => exact MemoryReadFacts.pop_error_inversion h
  | account =>
    simp only [ReadTarget.pop, Machine.popToAddress] at h
    split at h
    · rename_i err hp
      cases h
      exact MemoryReadFacts.pop_error_inversion hp
    · cases h

/-! ### The Read family's effect law -/

/-- **Family effect law (success).** A Read row checks availability, pops its key, warms at
most the key the quote names (a cold key under EIP-2929 access), records exactly the read the
target names, and then does what its result says (`ReadResult.Done`) at the quoted price. The
state gas and the return data are kept. -/
theorem ReadRow.step_ok {row : ReadRow} {rules : ForkRules} {ctx : CallContext} {v : ReadView}
    {m out : Machine} {t : ReadTouch} (h : row.step rules ctx v m = .ok (out, t)) :
    row.available rules.opcodes = true ∧ ∃ key m₁, row.target.pop m = .ok (key, m₁) ∧
      t = { warmed := (row.price.quote rules ctx v key).2, read := row.target.readKey ctx key } ∧
      out.stateGas = m.stateGas ∧ out.returnData = m.returnData ∧
      row.result.Done ctx v.world key (row.price.quote rules ctx v key).1 m₁ out := by
  unfold ReadRow.step at h
  split at h
  · cases h
  · rename_i hav
    refine ⟨by simpa using hav, ?_⟩
    split at h
    · cases h
    · rename_i key m₁ hp
      obtain ⟨ht, hsg, hrd, hdone⟩ := ReadResult.finish_ok h
      have hm₁ := ReadTarget.pop_ok hp
      refine ⟨key, m₁, hp, ht, ?_, ?_, hdone⟩
      · rw [hsg, hm₁]
      · rw [hrd, hm₁]

/-- **Family effect law (halting).** A Read row halts in exactly one of five ways, in source
order, each with the touch it has made by then: `invalidOpcode` (nothing), `stackUnderflow`
(nothing), `outOfGas` (the warmed key only), `stackOverflow` (the warmed key and the read). The
state gas and the return data are kept. -/
theorem ReadRow.step_error {row : ReadRow} {rules : ForkRules} {ctx : CallContext}
    {v : ReadView} {m out : Machine} {e : ExceptionalHalt} {t : ReadTouch}
    (h : row.step rules ctx v m = .error (e, out, t)) :
    out.stateGas = m.stateGas ∧ out.returnData = m.returnData ∧
    ((row.available rules.opcodes = false ∧ e = .invalidOpcode .none ∧ out = m ∧ t = {}) ∨
     (row.available rules.opcodes = true ∧ e = .stackUnderflow .none ∧ t = {}) ∨
     (∃ key m₁, row.available rules.opcodes = true ∧ row.target.pop m = .ok (key, m₁) ∧
        ((e = .outOfGas .none ∧ t = { warmed := (row.price.quote rules ctx v key).2 }) ∨
         (e = .stackOverflow .none ∧
           t = { warmed := (row.price.quote rules ctx v key).2,
                 read := row.target.readKey ctx key })))) := by
  unfold ReadRow.step at h
  split at h
  · rename_i hav
    cases h
    exact ⟨rfl, rfl, Or.inl ⟨by simpa using hav, rfl, rfl, rfl⟩⟩
  · rename_i hav
    have hav' : row.available rules.opcodes = true := by simpa using hav
    split at h
    · rename_i e' m' hp
      cases h
      obtain ⟨rfl, -, rfl⟩ := ReadTarget.pop_error hp
      exact ⟨rfl, rfl, Or.inr (Or.inl ⟨hav', rfl, rfl⟩)⟩
    · rename_i key m₁ hp
      obtain ⟨hsg, hrd, hcases⟩ := ReadResult.finish_error h
      have hm₁ := ReadTarget.pop_ok hp
      refine ⟨by rw [hsg, hm₁], by rw [hrd, hm₁], ?_⟩
      rcases hcases with ⟨rfl, rfl⟩ | hrest
      · exact Or.inr (Or.inl ⟨hav', rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨key, m₁, hav', hp, hrest⟩)

/-! ### What the lift fixes by type -/

/-- A read's touch keeps the world, the logs, the refund, the self-destructs, the touched
accounts and the created accounts. -/
theorem Frame.State.applyReadTouch_keeps (rules : ForkRules) (t : ReadTouch) (s : Frame.State) :
    let s' := s.applyReadTouch rules t
    s'.machine = s.machine ∧ s'.world = s.world ∧ s'.substate.logs = s.substate.logs ∧
      s'.substate.refund = s.substate.refund ∧
      s'.substate.selfDestructs = s.substate.selfDestructs ∧
      s'.substate.touchedAccounts = s.substate.touchedAccounts ∧
      s'.trail.createdAccounts = s.trail.createdAccounts := by
  rcases t with ⟨warmed, read⟩
  rcases warmed with _ | ⟨a⟩ | ⟨a, k⟩ <;> rcases read with _ | ⟨b⟩ | ⟨b, j⟩ <;>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩ <;>
    dsimp only [Frame.State.applyReadTouch, Frame.State.recordAccountRead,
      Frame.State.recordStorageRead, Frame.State.withTrail] <;>
    (try split) <;> rfl

/-- **By type:** a Read lift keeps the world, the logs, the refund, the self-destructs, the
touched accounts and the created accounts, on both channels. -/
theorem Frame.State.liftRead_keeps (rules : ForkRules)
    (core : Machine → Except (ExceptionalHalt × Machine × ReadTouch) (Machine × ReadTouch))
    (s : Frame.State) :
    let s' := match s.liftRead rules core with | .ok s' | .error (_, s') => s'
    s'.world = s.world ∧ s'.substate.logs = s.substate.logs ∧
      s'.substate.refund = s.substate.refund ∧
      s'.substate.selfDestructs = s.substate.selfDestructs ∧
      s'.substate.touchedAccounts = s.substate.touchedAccounts ∧
      s'.trail.createdAccounts = s.trail.createdAccounts := by
  unfold Frame.State.liftRead
  cases core s.machine with
  | error x =>
    obtain ⟨e, m, t⟩ := x
    obtain ⟨-, h⟩ := Frame.State.applyReadTouch_keeps rules t (s.withMachine m)
    exact h
  | ok x =>
    obtain ⟨m, t⟩ := x
    obtain ⟨-, h⟩ := Frame.State.applyReadTouch_keeps rules t (s.withMachine m)
    exact h

/-! ### The table -/

/-- The seven Read opcodes. -/
def PlainOp.readList : List Jaune.PlainOp :=
  [.balance, .extcodesize, .extcodecopy, .extcodehash, .selfbalance, .sload, .tload]

theorem PlainOp.readList_length : PlainOp.readList.length = 7 := rfl

theorem PlainOp.readList_nodup : PlainOp.readList.Nodup := by decide

theorem PlainOp.readRow?_isSome_iff (op : Jaune.PlainOp) :
    (PlainOp.readRow? op).isSome = true ↔ op ∈ PlainOp.readList := by
  cases op <;> simp [PlainOp.readRow?, PlainOp.family, PlainOp.readList]

/-- Only `TLOAD` reads transient storage, and it neither warms nor records. -/
theorem PlainOp.readRow?_transient {op : Jaune.PlainOp} {row : ReadRow}
    (h : PlainOp.readRow? op = some row) (ht : row.target = .transient) : op = .tload := by
  cases op <;> simp only [PlainOp.readRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    first | rfl | cases ht

/-- The rule fields a Read row reads: its availability flag, the access schedule, the gas
schedule (for cold and surcharge prices) and whether the rules keep a block-level access list. -/
def PlainOp.readRuleReads (op : Jaune.PlainOp) (rules : ForkRules) :
    Bool × AccessSchedule × GasSchedule × Bool :=
  match PlainOp.readRow? op with
  | none => (false, rules.access, rules.gas, rules.blockAccessListRules.isSome)
  | some row =>
    (row.available rules.opcodes, rules.access, rules.gas, rules.blockAccessListRules.isSome)

theorem PlainOp.readRow?_eq_some {op : Jaune.PlainOp} {row : ReadRow} :
    PlainOp.readRow? op = some row ↔ PlainOp.family op = .read row := by
  unfold PlainOp.readRow?
  cases PlainOp.family op <;> simp

/-- **Table lemma (Read):** every Read row, lifted through `Frame.State.liftRead` over the frame's
read view, is `PlainOp.run`, on both channels with their touches. -/
theorem PlainOp.readRow?_run_eq {op : Jaune.PlainOp} {row : ReadRow}
    (hrow : PlainOp.readRow? op = some row) (r : Frame.Running) :
    r.state.liftRead r.context.block.rules
        (row.step r.context.block.rules r.context r.state.readView) = PlainOp.run r op := by
  simp only [PlainOp.run, PlainOp.runCore, PlainOp.readRow?_eq_some.1 hrow, Family.run]

theorem PlainOp.readRow?_run_fork_eq (f : Fork) {op : Jaune.PlainOp} {row : ReadRow}
    (hrow : PlainOp.readRow? op = some row) (r : Frame.Running)
    (hf : r.context.block.fork = f) :
    r.state.liftRead (Fork.ruleSet f)
        (row.step (Fork.ruleSet f) r.context r.state.readView) = PlainOp.run r op := by
  have hr : r.context.block.rules = Fork.ruleSet f := by simp only [BlockContext.rules, hf]
  rw [← hr]
  exact PlainOp.readRow?_run_eq hrow r

/-- By type, lifted to the instruction: a Read opcode keeps the world, the logs, the refund,
the self-destructs, the touched accounts and the created accounts, on both channels. -/
theorem PlainOp.read_run_keeps {op : Jaune.PlainOp} (hread : (PlainOp.readRow? op).isSome)
    (r : Frame.Running) :
    let s' := match PlainOp.run r op with | .ok s' | .error (_, s') => s'
    s'.world = r.state.world ∧ s'.substate.logs = r.state.substate.logs ∧
      s'.substate.refund = r.state.substate.refund ∧
      s'.substate.selfDestructs = r.state.substate.selfDestructs ∧
      s'.substate.touchedAccounts = r.state.substate.touchedAccounts ∧
      s'.trail.createdAccounts = r.state.trail.createdAccounts := by
  cases hrow : PlainOp.readRow? op with
  | none => simp [hrow] at hread
  | some row =>
    rw [← PlainOp.readRow?_run_eq hrow]
    exact Frame.State.liftRead_keeps _ _ _

/-- Fork congruence: changing the fork alone, with the same `readRuleReads`, keeps every Read
opcode's run. -/
theorem PlainOp.read_run_congr_fork {op : Jaune.PlainOp} (hread : (PlainOp.readRow? op).isSome)
    (r : Frame.Running) (f' : Fork)
    (h : PlainOp.readRuleReads op (Fork.ruleSet r.context.block.fork) =
      PlainOp.readRuleReads op (Fork.ruleSet f')) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } } op =
      PlainOp.run r op := by
  cases hrow : PlainOp.readRow? op with
  | none => simp [hrow] at hread
  | some row =>
    rw [← PlainOp.readRow?_run_eq hrow, ← PlainOp.readRow?_run_eq hrow]
    simp only [PlainOp.readRuleReads, hrow, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    cases op <;> simp only [PlainOp.readRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;>
      subst hrow
    all_goals
      simp only [Frame.State.liftRead, ReadRow.step, ReadPrice.quote, BlockContext.rules,
        Frame.State.applyReadTouch, Frame.State.recordAccountRead,
        Frame.State.recordStorageRead] at h1 h2 h3 h4 ⊢
      simp only [h1, h2, h3, h4]
      rfl

end Jaune
