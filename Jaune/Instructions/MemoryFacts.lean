import Jaune.Instructions.Memory
import Jaune.Instructions.WordFacts

/-! Laws and bridges of the Memory family. -/

open private keccakReadRun from Jaune.Machine

namespace Jaune.Checked

open Jaune

private theorem liftMachine_congr {ε : Type} {f g : Machine → Except (ε × Machine) Machine}
    (s : Frame.State) (h : f s.machine = g s.machine) : s.liftMachine f = s.liftMachine g := by
  unfold Frame.State.liftMachine
  rw [h]

/-! ### Machine inversions shared by the Memory and Read laws -/

theorem MemoryReadFacts.chargeGas_ok_inv {m out : Machine} {cost : Nat} (h : m.chargeGas cost = .ok out) :
    cost ≤ m.gasLeft ∧ out = { m with gasLeft := m.gasLeft - cost } := by
  by_cases enough : cost ≤ m.gasLeft
  · exact ⟨enough, by simpa [Machine.chargeGas, safeSub, enough, eq_comm] using h⟩
  · simp [Machine.chargeGas, safeSub, enough] at h

theorem MemoryReadFacts.chargeGas_error_inv {m out : Machine} {cost : Nat} {e : ExceptionalHalt}
    (h : m.chargeGas cost = .error (e, out)) :
    e = .outOfGas .none ∧ m.gasLeft < cost ∧ out = m := by
  by_cases enough : cost ≤ m.gasLeft
  · simp [Machine.chargeGas, safeSub, enough] at h
  · simp [Machine.chargeGas, safeSub, enough] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, Nat.lt_of_not_le enough, rfl⟩

theorem MemoryReadFacts.push_ok_inv {m out : Machine} {x : U256} (h : m.push x = .ok out) :
    m.stack.length < 1024 ∧ out = { m with stack := x :: m.stack } := by
  unfold Machine.push at h
  split at h
  · cases h
    exact ⟨‹_›, rfl⟩
  · contradiction

theorem MemoryReadFacts.push_error_inv {m out : Machine} {x : U256} {e : ExceptionalHalt}
    (h : m.push x = .error (e, out)) :
    e = .stackOverflow .none ∧ 1024 ≤ m.stack.length ∧ out = m := by
  unfold Machine.push at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, Nat.le_of_not_lt ‹_›, rfl⟩

theorem MemoryReadFacts.pop_ok_inv {m out : Machine} {x : U256} (h : m.pop = .ok (x, out)) :
    ∃ rest, m.stack = x :: rest ∧ out = { m with stack := rest } := by
  unfold Machine.pop at h
  split at h
  · contradiction
  · rename_i first rest hs
    cases h
    exact ⟨rest, hs, rfl⟩

theorem MemoryReadFacts.pop_error_inv {m out : Machine} {e : ExceptionalHalt}
    (h : m.pop = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack = [] ∧ out = { m with stack := [] } := by
  rcases m with ⟨stk, mem, gl, sg, rd⟩
  cases stk with
  | nil =>
    simp only [Machine.pop, Except.error.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  | cons _ _ => simp [Machine.pop] at h

/-! ### The Memory family's effect law -/

/-- The word an effect pushes, as the new stack. -/
def MemoryEffect.stackAfter (pushed : Option U256) (rest : List U256) : List U256 :=
  match pushed with
  | none => rest
  | some x => x :: rest

/-- **Family effect law (success).** A Memory row checks availability, pops `row.arity` words,
pays `row.base args` plus the extension of `row.effect.ranges args`, and the new memory and the
pushed word are exactly what `row.effect.apply` gives. The state gas and the return data are
kept. -/
theorem MemoryRow.step_ok {row : MemoryRow} {opcodes : OpcodeRules} {ctx : CallContext}
    {m out : Machine} (h : row.step opcodes ctx m = .ok out) :
    row.available opcodes = true ∧ ∃ args rest pushed,
      m.stack = Words.toList row.arity args ++ rest ∧
      out.gasLeft + (row.base args + m.extCost (row.effect.ranges args)) = m.gasLeft ∧
      row.effect.apply ctx.calldata ctx.code m.returnData args m.memory = some (out.memory, pushed) ∧
      out.stack = MemoryEffect.stackAfter pushed rest ∧
      out.stateGas = m.stateGas ∧ out.returnData = m.returnData := by
  cases ha : row.available opcodes with
  | false => simp [MemoryRow.step, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | true =>
    refine ⟨rfl, ?_⟩
    simp only [MemoryRow.step, ha, ↓reduceIte, pure, Except.pure, bind, Except.bind] at h
    cases hp : m.popWords row.arity with
    | error e => simp [hp] at h
    | ok pair =>
      obtain ⟨args, popped⟩ := pair
      obtain ⟨rest, stack, rfl⟩ := Machine.popWords_ok hp
      rw [hp] at h
      dsimp only at h
      cases hc : ({ m with stack := rest } : Machine).chargeGas
          (row.base args + ({ m with stack := rest } : Machine).extCost (row.effect.ranges args)) with
      | error e => rw [hc] at h; cases h
      | ok charged =>
        rw [hc] at h
        dsimp only at h
        obtain ⟨enough, rfl⟩ := MemoryReadFacts.chargeGas_ok_inv hc
        dsimp only at h enough
        cases happ : row.effect.apply ctx.calldata ctx.code m.returnData args m.memory with
        | none => rw [happ] at h; cases h
        | some r =>
          obtain ⟨memory, pushed⟩ := r
          rw [happ] at h
          refine ⟨args, rest, pushed, stack, ?_⟩
          cases pushed with
          | none =>
            cases h
            exact ⟨by simp only [Machine.extCost] at enough ⊢; omega, happ, rfl, rfl, rfl⟩
          | some x =>
            obtain ⟨_, rfl⟩ := MemoryReadFacts.push_ok_inv h
            exact ⟨by simp only [Machine.extCost] at enough ⊢; omega, happ, rfl, rfl, rfl⟩

/-- **Family effect law (halting).** A Memory row halts in exactly one of five ways, in source
order: `invalidOpcode` (state kept), `stackUnderflow` (stack emptied), `outOfGas` (stack
popped), `outOfBoundsRead` (the charge kept), `stackOverflow` (the charge and the memory kept). -/
theorem MemoryRow.step_error {row : MemoryRow} {opcodes : OpcodeRules} {ctx : CallContext}
    {m out : Machine} {h : ExceptionalHalt}
    (herr : row.step opcodes ctx m = .error (h, out)) :
    (row.available opcodes = false ∧ h = .invalidOpcode .none ∧ out = m) ∨
    (row.available opcodes = true ∧ m.stack.length < row.arity.val ∧
      h = .stackUnderflow .none ∧ out = { m with stack := [] }) ∨
    (∃ args rest, row.available opcodes = true ∧ m.stack = Words.toList row.arity args ++ rest ∧
      m.gasLeft < row.base args + m.extCost (row.effect.ranges args) ∧ h = .outOfGas .none ∧
      out = { m with stack := rest }) ∨
    (∃ args rest, row.available opcodes = true ∧ m.stack = Words.toList row.arity args ++ rest ∧
      row.base args + m.extCost (row.effect.ranges args) ≤ m.gasLeft ∧
      row.effect.apply ctx.calldata ctx.code m.returnData args m.memory = none ∧ h = .outOfBoundsRead .none ∧
      out = { m with stack := rest,
                     gasLeft := m.gasLeft - (row.base args + m.extCost (row.effect.ranges args)) }) ∨
    (∃ args rest memory x, row.available opcodes = true ∧
      m.stack = Words.toList row.arity args ++ rest ∧
      row.base args + m.extCost (row.effect.ranges args) ≤ m.gasLeft ∧
      row.effect.apply ctx.calldata ctx.code m.returnData args m.memory = some (memory, some x) ∧
      1024 ≤ rest.length ∧ h = .stackOverflow .none ∧
      out = { m with stack := rest, memory,
                     gasLeft := m.gasLeft - (row.base args + m.extCost (row.effect.ranges args)) }) := by
  cases ha : row.available opcodes with
  | false =>
    simp [MemoryRow.step, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at herr
    rcases herr with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [MemoryRow.step, ha, ↓reduceIte, bind, Except.bind, pure, Except.pure] at herr
    cases hp : m.popWords row.arity with
    | error err =>
      rw [hp] at herr
      cases herr
      obtain ⟨rfl, hlen, rfl⟩ := Machine.popWords_error hp
      exact Or.inr (Or.inl ⟨rfl, hlen, rfl, rfl⟩)
    | ok pair =>
      obtain ⟨args, popped⟩ := pair
      obtain ⟨rest, stack, rfl⟩ := Machine.popWords_ok hp
      rw [hp] at herr
      dsimp only at herr
      cases hc : ({ m with stack := rest } : Machine).chargeGas
          (row.base args + ({ m with stack := rest } : Machine).extCost (row.effect.ranges args)) with
      | error err =>
        rw [hc] at herr
        cases herr
        obtain ⟨rfl, hlt, rfl⟩ := MemoryReadFacts.chargeGas_error_inv hc
        exact Or.inr (Or.inr (Or.inl ⟨args, rest, rfl, stack, hlt, rfl, rfl⟩))
      | ok charged =>
        rw [hc] at herr
        dsimp only at herr
        obtain ⟨enough, rfl⟩ := MemoryReadFacts.chargeGas_ok_inv hc
        dsimp only at herr enough
        cases happ : row.effect.apply ctx.calldata ctx.code m.returnData args m.memory with
        | none =>
          rw [happ] at herr
          simp only [throw, throwThe, MonadExceptOf.throw, Except.error.injEq, Prod.mk.injEq]
            at herr
          rcases herr with ⟨rfl, rfl⟩
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨args, rest, rfl, stack, enough, happ, rfl, rfl⟩)))
        | some r =>
          obtain ⟨memory, pushed⟩ := r
          rw [happ] at herr
          cases pushed with
          | none => cases herr
          | some x =>
            obtain ⟨rfl, hlen, rfl⟩ := MemoryReadFacts.push_error_inv herr
            exact Or.inr (Or.inr (Or.inr (Or.inr
              ⟨args, rest, memory, x, rfl, stack, enough, happ, hlen, rfl, rfl⟩)))


/-! ### Memory size under the word-aligned invariant -/

theorem MemoryEffect.memExtSize_dvd {c : Nat} (i n : Nat) (h : 32 ∣ c) : 32 ∣ memExtSize c i n := by
  unfold memExtSize
  split
  · exact h
  · exact Nat.dvd_mul_right 32 _

theorem MemoryEffect.memExtsSize_dvd {c : Nat} (pairs : List (Nat × Nat)) (h : 32 ∣ c) :
    32 ∣ memExtsSize c pairs := by
  induction pairs generalizing c with
  | nil => exact h
  | cons pair pairs ih => exact ih (MemoryEffect.memExtSize_dvd pair.1 pair.2 h)

private theorem aligned_write_arith {size i n : Nat} (h : 32 ∣ size) (hn : 0 < n) :
    (if i + n ≤ size then size else ceil32 (i + n)) =
      32 * max (ceilDiv size 32) (ceilDiv (i + n) 32) := by
  obtain ⟨k, rfl⟩ := h
  simp only [ceilDiv, ceil32, Nat.max_def]
  repeat' split
  all_goals omega

/-- On a word-aligned memory, a write grows the size exactly as the extension rule says. -/
theorem MemoryEffect.write_size {mem : Memory} (h : 32 ∣ mem.size) (i : Nat) (bytes : Bytes) :
    (mem.write i bytes).size = memExtSize mem.size i bytes.length := by
  cases bytes with
  | nil => simp [Memory.write, memExtSize]
  | cons b bs =>
    have arith := aligned_write_arith (i := i) h (Nat.succ_pos bs.length)
    simp only [memExtSize, List.length_cons, Nat.succ_eq_add_one, Nat.add_one_ne_zero,
      ↓reduceIte] at arith ⊢
    rw [← arith]
    simp only [Memory.write]
    split
    · rename_i fits
      simp only [List.length_cons] at fits
      simp only [fits, ↓reduceIte]
      split <;> rfl
    · rename_i fits
      simp only [List.length_cons] at fits
      simp only [fits, ↓reduceIte, List.length_cons]

private theorem sliceD_aux_length {ξ : Type} (xs : Array ξ) (acc : List ξ) (m n : Nat) (d : ξ) :
    (Array.sliceD.aux xs acc m n d).length = acc.length + n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp only [Array.sliceD.aux, ih, List.length_cons]; omega

theorem MemoryEffect.extend_size (mem : Memory) (i n : Nat) :
    (mem.extend i n).size = memExtSize mem.size i n := rfl

theorem MemoryEffect.read_size (mem : Memory) (i n : Nat) :
    (mem.read i n).2.size = memExtSize mem.size i n := rfl

/-- **Size law.** On a word-aligned memory, the memory an effect leaves has exactly the size its
ranges' extension gives, and stays word-aligned. -/
theorem MemoryEffect.apply_size {a : Fin 4} (e : MemoryEffect a) {calldata : Bytes} {code : ByteArray}
    {returnData : Bytes} {args : Words a} {mem mem' : Memory} {pushed : Option U256}
    (h32 : 32 ∣ mem.size) (h : e.apply calldata code returnData args mem = some (mem', pushed)) :
    mem'.size = memExtsSize mem.size (e.ranges args) ∧ 32 ∣ mem'.size := by
  have aligned : ∀ {x : Memory}, x.size = memExtsSize mem.size (e.ranges args) →
      x.size = memExtsSize mem.size (e.ranges args) ∧ 32 ∣ x.size := fun hx =>
    ⟨hx, hx ▸ MemoryEffect.memExtsSize_dvd _ h32⟩
  refine aligned ?_
  cases e with
  | copy source =>
    obtain ⟨d, o, n⟩ := args
    cases source <;> simp only [MemoryEffect.apply, Option.some.injEq, Prod.mk.injEq] at h
    · obtain ⟨rfl, -⟩ := h
      simp [MemoryEffect.ranges, memExtsSize, MemoryEffect.write_size h32, List.sliceD]
    · obtain ⟨rfl, -⟩ := h
      simp [MemoryEffect.ranges, memExtsSize, MemoryEffect.write_size h32, ByteArray.length_sliceD]
    · split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp [MemoryEffect.ranges, memExtsSize, MemoryEffect.write_size h32, List.sliceD]
  | move =>
    obtain ⟨d, src, n⟩ := args
    simp only [MemoryEffect.apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hr : 32 ∣ (mem.read src.toNat n.toNat).2.size := MemoryEffect.memExtSize_dvd _ _ h32
    rw [MemoryEffect.write_size hr]
    simp [MemoryEffect.ranges, memExtsSize, Memory.read, Memory.extend, Array.sliceD,
      sliceD_aux_length]
  | storeWord =>
    obtain ⟨i, x⟩ := args
    simp only [MemoryEffect.apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [MemoryEffect.ranges, memExtsSize, MemoryEffect.write_size h32, U256.length_toBytes]
  | storeByte =>
    obtain ⟨i, x⟩ := args
    simp only [MemoryEffect.apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp [MemoryEffect.ranges, memExtsSize, MemoryEffect.write_size h32]
  | load =>
    simp only [MemoryEffect.apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | digest =>
    obtain ⟨i, n⟩ := args
    simp only [MemoryEffect.apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl


/-- **Size law, at the step.** On a word-aligned memory, a successful Memory row leaves a
word-aligned memory of exactly the size the extension of its ranges gives: the size it paid for. -/
theorem MemoryRow.step_size {row : MemoryRow} {opcodes : OpcodeRules} {ctx : CallContext}
    {m out : Machine} (h32 : 32 ∣ m.memory.size) (h : row.step opcodes ctx m = .ok out) :
    ∃ args, out.memory.size = memExtsSize m.memory.size (row.effect.ranges args) ∧
      32 ∣ out.memory.size := by
  obtain ⟨_, args, _, _, _, _, happ, _⟩ := MemoryRow.step_ok h
  exact ⟨args, MemoryEffect.apply_size row.effect h32 happ⟩

/-! ### The table -/

/-- The eight Memory opcodes. -/
def PlainOp.memoryList : List Jaune.PlainOp :=
  [.mload, .mstore, .mstore8, .calldatacopy, .codecopy, .returndatacopy, .mcopy, .keccak256]

theorem PlainOp.memoryList_length : PlainOp.memoryList.length = 8 := rfl

theorem PlainOp.memoryList_nodup : PlainOp.memoryList.Nodup := by decide

theorem PlainOp.memoryRow?_isSome_iff (op : Jaune.PlainOp) :
    (PlainOp.memoryRow? op).isSome = true ↔ op ∈ PlainOp.memoryList := by
  cases op <;> simp [PlainOp.memoryRow?, PlainOp.memoryList]

/-- Every Memory row's base price is positive, so every successful step lowers the gas left. -/
theorem PlainOp.memoryRow?_base_pos {op : Jaune.PlainOp} {row : MemoryRow}
    (h : PlainOp.memoryRow? op = some row) (args : Words row.arity) : 0 < row.base args := by
  cases op <;> simp only [PlainOp.memoryRow?, Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals
    obtain ⟨_, _, _⟩ := args
    dsimp only
    simp only [Gas.veryLow, Gas.keccak256]
    omega

/-- Only `RETURNDATACOPY`'s effect can fail (EIP-211's strict bound). -/
theorem PlainOp.memoryRow?_apply_isSome {op : Jaune.PlainOp} {row : MemoryRow}
    (h : PlainOp.memoryRow? op = some row) (hne : op ≠ .returndatacopy) (calldata : Bytes)
    (code : ByteArray) (returnData : Bytes) (args : Words row.arity) (mem : Memory) :
    (row.effect.apply calldata code returnData args mem).isSome = true := by
  cases op <;> simp only [PlainOp.memoryRow?, Option.some.injEq, reduceCtorEq] at h
  case returndatacopy => exact absurd rfl hne
  all_goals
    subst h
    obtain ⟨_, _, _⟩ := args
    rfl

/-- The rule fields a Memory row reads: its availability flag (only `MCOPY`'s varies). -/
def PlainOp.memoryRuleReads (op : Jaune.PlainOp) (rules : ForkRules) : Bool :=
  match PlainOp.memoryRow? op with
  | none => false
  | some row => row.available rules.opcodes

/-- The Memory table's bridge: every Memory row, lifted through `Frame.State.liftMachine`,
equals `Checked.PlainOp.runCore`, for every `pc`, call context and frame state (hence every
`Fork`). -/
theorem PlainOp.memoryRow?_runCore_eq {op : Jaune.PlainOp} {row : MemoryRow}
    (hrow : PlainOp.memoryRow? op = some row) (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    s.liftMachine (row.step ctx.block.rules.opcodes ctx) = PlainOp.runCore pc ctx s op := by
  cases op <;> simp only [PlainOp.memoryRow?, Option.some.injEq, reduceCtorEq] at hrow <;>
    subst hrow <;> dsimp only [PlainOp.runCore] <;> refine liftMachine_congr s ?_
  case mload =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
      cases hc : m₁.chargeGas (Gas.veryLow + m₁.extCost [(x.toNat, 32)]) with
      | error e => rfl
      | ok m₂ => rfl
  case mstore =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only
      cases hq : m₁.pop with
      | error e => rfl
      | ok q =>
        obtain ⟨y, m₂⟩ := q
        dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
        cases hc : m₂.chargeGas (Gas.veryLow + m₂.extCost [(x.toNat, 32)]) with
        | error e => rfl
        | ok m₃ => rfl
  case mstore8 =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only
      cases hq : m₁.pop with
      | error e => rfl
      | ok q =>
        obtain ⟨y, m₂⟩ := q
        dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
        cases hc : m₂.chargeGas (Gas.veryLow + m₂.extCost [(x.toNat, 1)]) with
        | error e => rfl
        | ok m₃ => rfl
  case keccak256 =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only
      cases hq : m₁.pop with
      | error e => rfl
      | ok q =>
        obtain ⟨y, m₂⟩ := q
        dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
  case calldatacopy =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only
      cases hq : m₁.pop with
      | error e => rfl
      | ok q =>
        obtain ⟨y, m₂⟩ := q
        dsimp only
        cases hr : m₂.pop with
        | error e => rfl
        | ok r =>
          obtain ⟨z, m₃⟩ := r
          dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
          cases hc : m₃.chargeGas (Gas.veryLow + Gas.copy * ceilDiv z.toNat 32 + m₃.extCost [(x.toNat, z.toNat)]) with
          | error e => rfl
          | ok m₄ => rfl
  case codecopy =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only
      cases hq : m₁.pop with
      | error e => rfl
      | ok q =>
        obtain ⟨y, m₂⟩ := q
        dsimp only
        cases hr : m₂.pop with
        | error e => rfl
        | ok r =>
          obtain ⟨z, m₃⟩ := r
          dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
          cases hc : m₃.chargeGas (Gas.veryLow + Gas.copy * ceilDiv z.toNat 32 + m₃.extCost [(x.toNat, z.toNat)]) with
          | error e => rfl
          | ok m₄ => rfl
  case returndatacopy =>
    simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
      Except.pure, ↓reduceIte]
    cases hp : s.machine.pop with
    | error e => rfl
    | ok p =>
      obtain ⟨x, m₁⟩ := p
      dsimp only
      cases hq : m₁.pop with
      | error e => rfl
      | ok q =>
        obtain ⟨y, m₂⟩ := q
        dsimp only
        cases hr : m₂.pop with
        | error e => rfl
        | ok r =>
          obtain ⟨z, m₃⟩ := r
          dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
          cases hc : m₃.chargeGas (Gas.veryLow + Gas.returnDataCopy * ceilDiv z.toNat 32 + m₃.extCost [(x.toNat, z.toNat)]) with
          | error e => rfl
          | ok m₄ => by_cases hb : m₄.returnData.length < y.toNat + z.toNat <;> simp [hb, throw, throwThe, MonadExceptOf.throw, Machine.memWrite]
  case mcopy =>
    by_cases ha : ctx.block.rules.opcodes.mcopy
    · simp only [ha, MemoryRow.step, Machine.popWords, Machine.popToNat, bind, Except.bind, pure,
        Except.pure, ↓reduceIte]
      cases hp : s.machine.pop with
      | error e => rfl
      | ok p =>
        obtain ⟨x, m₁⟩ := p
        dsimp only
        cases hq : m₁.pop with
        | error e => rfl
        | ok q =>
          obtain ⟨y, m₂⟩ := q
          dsimp only
          cases hr : m₂.pop with
          | error e => rfl
          | ok r =>
            obtain ⟨z, m₃⟩ := r
            dsimp only [MemoryEffect.ranges, MemoryEffect.apply]
            cases hc : m₃.chargeGas (Gas.veryLow + Gas.copy * ceilDiv z.toNat 32 + m₃.extCost [(y.toNat, z.toNat), (x.toNat, z.toNat)]) with
            | error e => rfl
            | ok m₄ => rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte, MemoryRow.step, PlainOp.unavailable]
      simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem PlainOp.memoryRow?_run_eq {op : Jaune.PlainOp} {row : MemoryRow}
    (hrow : PlainOp.memoryRow? op = some row) (r : Frame.Running) :
    r.state.liftMachine (row.step r.context.block.rules.opcodes r.context) = PlainOp.run r op :=
  PlainOp.memoryRow?_runCore_eq hrow r.pc r.context r.state

theorem PlainOp.memoryRow?_run_fork_eq (f : Fork) {op : Jaune.PlainOp} {row : MemoryRow}
    (hrow : PlainOp.memoryRow? op = some row) (r : Frame.Running)
    (hf : r.context.block.fork = f) :
    r.state.liftMachine (row.step (Fork.ruleSet f).opcodes r.context) = PlainOp.run r op := by
  have hr : r.context.block.rules = Fork.ruleSet f := by simp only [BenvStat.rules, hf]
  rw [← hr]
  exact PlainOp.memoryRow?_run_eq hrow r

/-- Fork congruence: changing the fork alone, with the same availability, keeps every Memory
opcode's run. -/
theorem PlainOp.memory_run_congr_fork {op : Jaune.PlainOp}
    (hmem : (PlainOp.memoryRow? op).isSome) (r : Frame.Running) (f' : Fork)
    (h : PlainOp.memoryRuleReads op (Fork.ruleSet r.context.block.fork) =
      PlainOp.memoryRuleReads op (Fork.ruleSet f')) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } } op =
      PlainOp.run r op := by
  cases hrow : PlainOp.memoryRow? op with
  | none => simp [hrow] at hmem
  | some row =>
    rw [← PlainOp.memoryRow?_run_eq hrow, ← PlainOp.memoryRow?_run_eq hrow]
    simp only [PlainOp.memoryRuleReads, hrow] at h
    refine liftMachine_congr r.state ?_
    simp only [MemoryRow.step, BenvStat.rules] at h ⊢
    simp only [h]
    rfl

/-- By type: a Memory opcode keeps the world, on both channels. -/
theorem PlainOp.memory_run_world {op : Jaune.PlainOp}
    (hmem : (PlainOp.memoryRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.world) = r.state.world := by
  cases hrow : PlainOp.memoryRow? op with
  | none => simp [hrow] at hmem
  | some row =>
    rw [← PlainOp.memoryRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes r.context r.state.machine <;> rfl

/-- By type: a Memory opcode keeps the substate, on both channels. -/
theorem PlainOp.memory_run_substate {op : Jaune.PlainOp}
    (hmem : (PlainOp.memoryRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.substate) = r.state.substate := by
  cases hrow : PlainOp.memoryRow? op with
  | none => simp [hrow] at hmem
  | some row =>
    rw [← PlainOp.memoryRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes r.context r.state.machine <;> rfl

/-- By type: a Memory opcode keeps the trail, on both channels. -/
theorem PlainOp.memory_run_trail {op : Jaune.PlainOp}
    (hmem : (PlainOp.memoryRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.trail) = r.state.trail := by
  cases hrow : PlainOp.memoryRow? op with
  | none => simp [hrow] at hmem
  | some row =>
    rw [← PlainOp.memoryRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes r.context r.state.machine <;> rfl

/-- A successful Memory opcode lowers the termination measure. -/
theorem PlainOp.memory_run_gasMeasure_lt {op : Jaune.PlainOp}
    (hmem : (PlainOp.memoryRow? op).isSome) (r : Frame.Running) {s' : Frame.State}
    (hok : PlainOp.run r op = .ok s') :
    s'.machine.gasMeasure < r.state.machine.gasMeasure := by
  cases hrow : PlainOp.memoryRow? op with
  | none => simp [hrow] at hmem
  | some row =>
    rw [← PlainOp.memoryRow?_run_eq hrow] at hok
    unfold Frame.State.liftMachine at hok
    cases hs : row.step r.context.block.rules.opcodes r.context r.state.machine with
    | error e => simp [hs] at hok
    | ok m' =>
      simp only [hs, Except.ok.injEq] at hok
      subst hok
      obtain ⟨_, args, _, _, _, hgas, _, _, hsg, _⟩ := MemoryRow.step_ok hs
      have hpos := PlainOp.memoryRow?_base_pos hrow args
      simp only [Machine.gasMeasure, Frame.State.withMachine_machine, hsg]
      omega

end Jaune.Checked
