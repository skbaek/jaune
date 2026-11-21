import Jaune.Instructions.Word
import Jaune.MessageCall.Plain

namespace Jaune

open Jaune

def Words.toList : (n : Fin 4) → Words n → List U256
  | 0, _ => []
  | 1, x => [x]
  | 2, (x, y) => [x, y]
  | 3, (x, y, z) => [x, y, z]

private theorem pop_ok {m out : Machine} {x : U256} (h : m.pop = .ok (x, out)) :
    ∃ rest, m.stack = x :: rest ∧ out = { m with stack := rest } := by
  unfold Machine.pop at h
  split at h
  · contradiction
  · rename_i first rest hs
    cases h
    exact ⟨rest, hs, rfl⟩

private theorem pop_error {m out : Machine} {e : ExceptionalHalt}
    (h : m.pop = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack = [] ∧ out = { m with stack := [] } := by
  rcases m with ⟨stk, mem, gl, sg, rd⟩
  cases stk with
  | nil =>
    simp only [Machine.pop, Except.error.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  | cons _ _ => simp [Machine.pop] at h

theorem Machine.popWords_ok {n : Fin 4} {m out : Machine} {args : Words n}
    (h : m.popWords n = .ok (args, out)) :
    ∃ rest, m.stack = Words.toList n args ++ rest ∧ out = { m with stack := rest } := by
  have options : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases options with rfl | rfl | rfl | rfl
  · cases h
    exact ⟨m.stack, rfl, rfl⟩
  · exact pop_ok h
  · change (do let (x, m₁) ← m.pop; let (y, m₂) ← m₁.pop; pure ((x, y), m₂)) = _ at h
    obtain ⟨⟨x, m₁⟩, hx, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨y, m₂⟩, hy, h⟩ := Except.bind_eq_ok h
    cases h
    obtain ⟨tail, first, rfl⟩ := pop_ok hx
    obtain ⟨rest, second, rfl⟩ := pop_ok hy
    exact ⟨rest, first.trans (congrArg (List.cons x) second), rfl⟩
  · change (do let (x, m₁) ← m.pop; let (y, m₂) ← m₁.pop; let (z, m₃) ← m₂.pop;
               pure ((x, y, z), m₃)) = _ at h
    obtain ⟨⟨x, m₁⟩, hx, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨y, m₂⟩, hy, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨z, m₃⟩, hz, h⟩ := Except.bind_eq_ok h
    cases h
    obtain ⟨tail, first, rfl⟩ := pop_ok hx
    obtain ⟨tail', second, rfl⟩ := pop_ok hy
    obtain ⟨rest, third, rfl⟩ := pop_ok hz
    exact ⟨rest, first.trans (congrArg (List.cons x) (second.trans (congrArg (List.cons y) third))), rfl⟩

theorem Machine.popWords_error {n : Fin 4} {m out : Machine} {e : ExceptionalHalt}
    (h : m.popWords n = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack.length < n.val ∧ out = { m with stack := [] } := by
  have options : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases options with rfl | rfl | rfl | rfl
  · cases h
  · obtain ⟨rfl, hs, heq⟩ := pop_error h
    exact ⟨rfl, by simp [hs], heq⟩
  · simp only [Machine.popWords, bind, Except.bind, pure, Except.pure] at h
    cases hx : m.pop with
    | error err =>
      rw [hx] at h
      cases h
      obtain ⟨rfl, hs, heq⟩ := pop_error hx
      exact ⟨rfl, by simp [hs], heq⟩
    | ok p1 =>
      rw [hx] at h
      obtain ⟨x, m₁⟩ := p1
      obtain ⟨tail, hs1, rfl⟩ := pop_ok hx
      dsimp only at h
      cases hy : ({ m with stack := tail } : Machine).pop with
      | error err =>
        rw [hy] at h
        cases h
        obtain ⟨rfl, hs2, heq⟩ := pop_error hy
        dsimp only at hs2
        subst hs2
        exact ⟨rfl, by simp [hs1], heq⟩
      | ok p2 =>
        rw [hy] at h
        cases h
  · simp only [Machine.popWords, bind, Except.bind, pure, Except.pure] at h
    cases hx : m.pop with
    | error err =>
      rw [hx] at h
      cases h
      obtain ⟨rfl, hs, heq⟩ := pop_error hx
      exact ⟨rfl, by simp [hs], heq⟩
    | ok p1 =>
      rw [hx] at h
      obtain ⟨x, m₁⟩ := p1
      obtain ⟨t1, hs1, rfl⟩ := pop_ok hx
      dsimp only at h
      cases hy : ({ m with stack := t1 } : Machine).pop with
      | error err =>
        rw [hy] at h
        cases h
        obtain ⟨rfl, hs2, heq⟩ := pop_error hy
        dsimp only at hs2
        subst hs2
        exact ⟨rfl, by simp [hs1], heq⟩
      | ok p2 =>
        rw [hy] at h
        obtain ⟨y, m₂⟩ := p2
        obtain ⟨t2, hs2, rfl⟩ := pop_ok hy
        dsimp only at h
        cases hz : ({ m with stack := t2 } : Machine).pop with
        | error err =>
          rw [hz] at h
          cases h
          obtain ⟨rfl, hs3, heq⟩ := pop_error hz
          dsimp only at hs3
          subst hs3
          dsimp only at hs2
          subst hs2
          exact ⟨rfl, by simp [hs1], heq⟩
        | ok p3 =>
          rw [hz] at h
          cases h

private theorem charged_ok {m out : Machine} {cost : Nat} (h : m.chargeGas cost = .ok out) :
    cost ≤ m.gasLeft ∧ out = { m with gasLeft := m.gasLeft - cost } := by
  by_cases enough : cost ≤ m.gasLeft
  · exact ⟨enough, by simpa [Machine.chargeGas, safeSub, enough, eq_comm] using h⟩
  · simp [Machine.chargeGas, safeSub, enough] at h

private theorem charged_error {m out : Machine} {cost : Nat} {e : ExceptionalHalt}
    (h : m.chargeGas cost = .error (e, out)) :
    e = .outOfGas .none ∧ m.gasLeft < cost ∧ out = m := by
  by_cases enough : cost ≤ m.gasLeft
  · simp [Machine.chargeGas, safeSub, enough] at h
  · simp [Machine.chargeGas, safeSub, enough] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, Nat.lt_of_not_le enough, rfl⟩

private theorem push_error {m out : Machine} {x : U256} {e : ExceptionalHalt}
    (h : m.push x = .error (e, out)) :
    e = .stackOverflow .none ∧ 1024 ≤ m.stack.length ∧ out = m := by
  unfold Machine.push at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, Nat.le_of_not_lt ‹_›, rfl⟩

/-- **Family effect law (success):** any `WordRow` checks availability, pops `row.arity` words,
deducts `row.cost args`, pushes `row.result` (or drops it for `POP`), and leaves `memory`,
`stateGas`, and `returnData` untouched. -/
theorem WordRow.step_ok {row : WordRow} {opcodes : OpcodeRules} {env : Word.Env} {m out : Machine}
    (h : row.step opcodes env m = .ok out) :
    row.available opcodes = true ∧ ∃ args rest,
      m.stack = Words.toList row.arity args ++ rest ∧
      out.gasLeft + row.cost args = m.gasLeft ∧
      out.stack = (match row.result with
        | none => rest
        | some f => f args ⟨env, m.memory.size, m.returnData, out.gasLeft⟩ :: rest) ∧
      out.memory = m.memory ∧ out.stateGas = m.stateGas ∧ out.returnData = m.returnData := by
  cases ha : row.available opcodes with
  | false => simp [WordRow.step, ha, bind, Except.bind] at h
  | true =>
    refine ⟨rfl, ?_⟩
    simp only [WordRow.step, ha, ↓reduceIte, pure, Except.pure, bind, Except.bind] at h
    cases hp : m.popWords row.arity with
    | error e => simp [hp] at h
    | ok pair =>
      obtain ⟨args, popped⟩ := pair
      obtain ⟨rest, stack, rfl⟩ := Machine.popWords_ok hp
      simp only [hp] at h
      split at h
      · contradiction
      · rename_i charged hc
        obtain ⟨enough, rfl⟩ := charged_ok hc
        refine ⟨args, rest, stack, ?_⟩
        cases hr : row.result with
        | none =>
          simp only [hr] at h
          cases h
          exact ⟨Nat.sub_add_cancel enough, rfl, rfl, rfl, rfl⟩
        | some f =>
          simp only [hr, Machine.push] at h
          split at h
          · cases h
            exact ⟨Nat.sub_add_cancel enough, rfl, rfl, rfl, rfl⟩
          · contradiction

/-- **Family effect law (halting):** any `WordRow` error is one of the four halts in exact
order: `invalidOpcode`, `stackUnderflow` (stack emptied), `outOfGas` (stack popped), or
`stackOverflow` (stack popped and gas charged). -/
theorem WordRow.step_error {row : WordRow} {opcodes : OpcodeRules} {env : Word.Env}
    {m out : Machine} {h : ExceptionalHalt}
    (herr : row.step opcodes env m = .error (h, out)) :
    (row.available opcodes = false ∧ h = .invalidOpcode .none ∧ out = m) ∨
    (row.available opcodes = true ∧ m.stack.length < row.arity.val ∧
      h = .stackUnderflow .none ∧ out = { m with stack := [] }) ∨
    (∃ args rest, row.available opcodes = true ∧ m.stack = Words.toList row.arity args ++ rest ∧
      m.gasLeft < row.cost args ∧ h = .outOfGas .none ∧ out = { m with stack := rest }) ∨
    (∃ args rest f, row.available opcodes = true ∧ m.stack = Words.toList row.arity args ++ rest ∧
      row.cost args ≤ m.gasLeft ∧ row.result = some f ∧ 1024 ≤ rest.length ∧
      h = .stackOverflow .none ∧
      out = { m with stack := rest, gasLeft := m.gasLeft - row.cost args }) := by
  cases ha : row.available opcodes with
  | false =>
    simp [WordRow.step, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at herr
    rcases herr with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | true =>
    simp only [WordRow.step, ha, ↓reduceIte, bind, Except.bind, pure, Except.pure] at herr
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
      cases hc : ({ m with stack := rest } : Machine).chargeGas (row.cost args) with
      | error err =>
        rw [hc] at herr
        cases herr
        obtain ⟨rfl, hlt, rfl⟩ := charged_error hc
        exact Or.inr (Or.inr (Or.inl ⟨args, rest, rfl, stack, hlt, rfl, rfl⟩))
      | ok charged =>
        rw [hc] at herr
        dsimp only at herr
        obtain ⟨enough, rfl⟩ := charged_ok hc
        cases hr : row.result with
        | none =>
          rw [hr] at herr
          cases herr
        | some f =>
          rw [hr] at herr
          dsimp only at herr
          obtain ⟨rfl, hlen, rfl⟩ := push_error herr
          exact Or.inr (Or.inr (Or.inr ⟨args, rest, f, rfl, stack, enough, rfl, hlen, rfl, rfl⟩))

theorem WordRow.step_unavailable {row : WordRow} {opcodes : OpcodeRules} {env : Word.Env}
    {m : Machine} (h : row.available opcodes = false) :
    row.step opcodes env m = .error (.invalidOpcode .none, m) := by
  simp [WordRow.step, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

theorem WordRow.step_memory (row : WordRow) (opcodes : OpcodeRules) (env : Word.Env) (m : Machine) :
    (match row.step opcodes env m with | .ok out | .error (_, out) => out.memory) = m.memory := by
  cases h : row.step opcodes env m with
  | ok out => exact (WordRow.step_ok h).2.choose_spec.choose_spec.2.2.2.1
  | error e =>
    rcases e with ⟨reason, out⟩
    rcases WordRow.step_error h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩ <;> rfl

theorem WordRow.step_stateGas (row : WordRow) (opcodes : OpcodeRules) (env : Word.Env) (m : Machine) :
    (match row.step opcodes env m with | .ok out | .error (_, out) => out.stateGas) = m.stateGas := by
  cases h : row.step opcodes env m with
  | ok out => exact (WordRow.step_ok h).2.choose_spec.choose_spec.2.2.2.2.1
  | error e =>
    rcases e with ⟨reason, out⟩
    rcases WordRow.step_error h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩ <;> rfl

theorem WordRow.step_returnData (row : WordRow) (opcodes : OpcodeRules) (env : Word.Env)
    (m : Machine) :
    (match row.step opcodes env m with | .ok out | .error (_, out) => out.returnData) =
      m.returnData := by
  cases h : row.step opcodes env m with
  | ok out => exact (WordRow.step_ok h).2.choose_spec.choose_spec.2.2.2.2.2
  | error e =>
    rcases e with ⟨reason, out⟩
    rcases WordRow.step_error h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩ <;> rfl

theorem WordRow.step_gasMeasure_le (row : WordRow) (opcodes : OpcodeRules) (env : Word.Env)
    (m : Machine) :
    (match row.step opcodes env m with | .ok out | .error (_, out) => out.gasMeasure) ≤
      m.gasMeasure := by
  cases h : row.step opcodes env m with
  | ok out =>
    obtain ⟨_, args, rest, _, hgas, _, _, hsg, _⟩ := WordRow.step_ok h
    simp only [Machine.gasMeasure, hsg]
    omega
  | error e =>
    rcases e with ⟨reason, out⟩
    rcases WordRow.step_error h with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, rfl⟩ <;>
      simp only [Machine.gasMeasure] <;> omega

theorem WordRow.step_gasMeasure_lt_of_ok {row : WordRow} {opcodes : OpcodeRules} {env : Word.Env}
    {m out : Machine} (hpos : ∀ args, 0 < row.cost args) (h : row.step opcodes env m = .ok out) :
    out.gasMeasure < m.gasMeasure := by
  obtain ⟨_, args, rest, _, hgas, _, _, hsg, _⟩ := WordRow.step_ok h
  have hc := hpos args
  simp only [Machine.gasMeasure, hsg]
  omega

theorem Frame.State.liftMachine_world {ε : Type} (core : Machine → Except (ε × Machine) Machine)
    (s : Frame.State) :
    (match s.liftMachine core with | .ok s' | .error (_, s') => s'.world) = s.world := by
  unfold Frame.State.liftMachine
  cases core s.machine <;> rfl

theorem Frame.State.liftMachine_substate {ε : Type} (core : Machine → Except (ε × Machine) Machine)
    (s : Frame.State) :
    (match s.liftMachine core with | .ok s' | .error (_, s') => s'.substate) = s.substate := by
  unfold Frame.State.liftMachine
  cases core s.machine <;> rfl

theorem Frame.State.liftMachine_trail {ε : Type} (core : Machine → Except (ε × Machine) Machine)
    (s : Frame.State) :
    (match s.liftMachine core with | .ok s' | .error (_, s') => s'.trail) = s.trail := by
  unfold Frame.State.liftMachine
  cases core s.machine <;> rfl

theorem WordRow.binary_step (f : U256 → U256 → U256) (cost : Nat) (o : OpcodeRules)
    (e : Word.Env) (m : Machine) :
    (WordRow.binary f cost).step o e m = m.applyBinary f cost := by
  simp only [WordRow.step, WordRow.binary, Machine.popWords, Machine.applyBinary,
    Machine.pushItem, bind, Except.bind, pure, Except.pure]
  cases hx : m.pop with
  | error err => rfl
  | ok pair =>
    obtain ⟨x, next⟩ := pair
    dsimp only
    cases hy : next.pop with
    | error err => rfl
    | ok pair =>
      obtain ⟨y, last⟩ := pair
      dsimp only
      cases hg : last.chargeGas cost <;> rfl

theorem WordRow.unary_step (f : U256 → U256) (cost : Nat) (o : OpcodeRules)
    (e : Word.Env) (m : Machine) :
    (WordRow.unary f cost).step o e m = m.applyUnary f cost := by
  simp only [WordRow.step, WordRow.unary, Machine.popWords, Machine.applyUnary,
    Machine.pushItem, bind, Except.bind]
  cases hx : m.pop with
  | error err => rfl
  | ok pair =>
    obtain ⟨x, next⟩ := pair
    dsimp only
    cases hg : next.chargeGas cost <;> rfl

theorem WordRow.ternary_step (f : U256 → U256 → U256 → U256) (cost : Nat) (o : OpcodeRules)
    (e : Word.Env) (m : Machine) :
    (WordRow.ternary f cost).step o e m = m.applyTernary f cost := by
  simp only [WordRow.step, WordRow.ternary, Machine.popWords, Machine.applyTernary,
    Machine.pushItem, bind, Except.bind, pure, Except.pure]
  cases hx : m.pop with
  | error err => rfl
  | ok pair =>
    obtain ⟨x, first⟩ := pair
    dsimp only
    cases hy : first.pop with
    | error err => rfl
    | ok pair =>
      obtain ⟨y, second⟩ := pair
      dsimp only
      cases hz : second.pop with
      | error err => rfl
      | ok pair =>
        obtain ⟨z, last⟩ := pair
        dsimp only
        cases hg : last.chargeGas cost <;> rfl

theorem WordRow.context_step (read : Word.View → U256) (cost : Nat) (o : OpcodeRules)
    (e : Word.Env) (m : Machine) (value : U256)
    (stable : ∀ remaining, read ⟨e, m.memory.size, m.returnData, remaining⟩ = value) :
    (WordRow.context cost read).step o e m = m.pushItem value cost := by
  simp only [WordRow.step, WordRow.context, Machine.popWords, Machine.pushItem,
    bind, Except.bind, ↓reduceIte]
  cases hg : m.chargeGas cost with
  | error err => rfl
  | ok charged =>
    obtain ⟨_, rfl⟩ := charged_ok hg
    dsimp only
    rw [stable]

/-- All 50 plain word opcodes covered by `PlainOp.wordRow?`. -/
def PlainOp.wordList : List Jaune.PlainOp :=
  [ .address, .origin, .caller, .callvalue, .calldatasize, .codesize, .gasprice, .returndatasize,
    .number, .timestamp, .gaslimit, .prevrandao, .coinbase, .msize, .pc, .basefee, .blobbasefee,
    .chainid, .slotnum, .gas, .blobhash, .calldataload, .blockhash,
    .eq, .lt, .gt, .slt, .sgt, .iszero, .not, .and, .or, .xor, .signextend, .byte,
    .add, .sub, .mul, .div, .sdiv, .mod, .smod, .addmod, .mulmod,
    .shl, .shr, .sar, .clz, .exp, .pop ]

theorem PlainOp.wordList_length : PlainOp.wordList.length = 50 := rfl

theorem PlainOp.wordList_nodup : PlainOp.wordList.Nodup := by decide

theorem PlainOp.wordRow?_isSome_iff (op : Jaune.PlainOp) :
    (PlainOp.wordRow? op).isSome = true ↔ op ∈ PlainOp.wordList := by
  cases op <;> simp [PlainOp.wordRow?, PlainOp.family, PlainOp.wordList]

theorem PlainOp.wordRow?_cost_pos {op : Jaune.PlainOp} {row : WordRow}
    (h : PlainOp.wordRow? op = some row) (args : Words row.arity) :
    0 < row.cost args := by
  cases op <;> simp only [PlainOp.wordRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h <;> subst h
  case exp =>
    rcases args with ⟨_, exponent⟩
    dsimp only
    simp only [Gas.exp, Gas.expByte]
    omega
  all_goals
    dsimp only [WordRow.context, WordRow.unary, WordRow.binary, WordRow.ternary]
    simp only [Gas.base, Gas.veryLow, Gas.low, Gas.mid, Gas.hashOpcodeGas, Gas.blockhash]
    omega

theorem PlainOp.wordRow?_gasFree {op : Jaune.PlainOp} {row : WordRow}
    (h : PlainOp.wordRow? op = some row) (hne : op ≠ .gas)
    (args : Words row.arity) (env : Word.Env) (mem : Nat) (rd : Bytes) (g₁ g₂ : Nat) :
    row.result.map (· args ⟨env, mem, rd, g₁⟩) = row.result.map (· args ⟨env, mem, rd, g₂⟩) := by
  cases op <;> simp only [PlainOp.wordRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h
  all_goals first | exact absurd rfl hne | (subst h; rfl)

theorem PlainOp.wordRow?_pcFree {op : Jaune.PlainOp} {row : WordRow}
    (h : PlainOp.wordRow? op = some row) (hne : op ≠ .pc)
    (args : Words row.arity) (pc₁ pc₂ : Nat) (ctx : CallContext) (mem : Nat) (rd : Bytes) (g : Nat) :
    row.result.map (· args ⟨⟨pc₁, ctx⟩, mem, rd, g⟩) =
      row.result.map (· args ⟨⟨pc₂, ctx⟩, mem, rd, g⟩) := by
  cases op <;> simp only [PlainOp.wordRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at h
  all_goals first | exact absurd rfl hne | (subst h; rfl)

/-- The exact rule fields a word row reads from `ForkRules`: its availability flag in `opcodes`,
plus `rules.blob` for `BLOBBASEFEE` only. -/
def PlainOp.wordRuleReads (op : Jaune.PlainOp) (rules : ForkRules) : Bool × Option BlobSchedule :=
  match PlainOp.wordRow? op with
  | none => (false, none)
  | some row =>
    (row.available rules.opcodes, match op with | .blobbasefee => some rules.blob | _ => none)

theorem Frame.State.liftMachine_congr {ε : Type} {f g : Machine → Except (ε × Machine) Machine}
    (s : Frame.State) (h : f s.machine = g s.machine) : s.liftMachine f = s.liftMachine g := by
  unfold Frame.State.liftMachine
  rw [h]

/-- A Word row is the table's row of a Word family member. -/
theorem PlainOp.wordRow?_eq_some {op : Jaune.PlainOp} {row : WordRow} :
    PlainOp.wordRow? op = some row ↔ PlainOp.family op = .word row := by
  unfold PlainOp.wordRow?
  cases PlainOp.family op <;> simp

/-- **Table lemma (50 plain word opcodes):** every row in `PlainOp.wordRow?`, lifted via
`Frame.State.liftMachine`, is `PlainOp.run`, by the definition of the dispatch. -/
theorem PlainOp.wordRow?_run_eq {op : Jaune.PlainOp} {row : WordRow}
    (hrow : PlainOp.wordRow? op = some row) (r : Frame.Running) :
    r.state.liftMachine (row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩) =
      PlainOp.run r op := by
  simp only [PlainOp.run, PlainOp.runCore, PlainOp.wordRow?_eq_some.1 hrow, Family.run]

theorem PlainOp.wordRow?_run_fork_eq (f : Fork) {op : Jaune.PlainOp} {row : WordRow}
    (hrow : PlainOp.wordRow? op = some row) (r : Frame.Running)
    (hf : r.context.block.fork = f) :
    r.state.liftMachine (row.step (Fork.ruleSet f).opcodes ⟨r.pc, r.context⟩) =
      PlainOp.run r op := by
  have hr : r.context.block.rules = Fork.ruleSet f := by
    simp only [BlockContext.rules, hf]
  rw [← hr]
  exact PlainOp.wordRow?_run_eq hrow r

/-- Fork congruence for every plain word opcode: replacing the fork while keeping
`PlainOp.wordRuleReads` fixed preserves `PlainOp.run`. -/
theorem PlainOp.word_run_congr_fork {op : Jaune.PlainOp} (hword : (PlainOp.wordRow? op).isSome)
    (r : Frame.Running) (f' : Fork)
    (h : PlainOp.wordRuleReads op (Fork.ruleSet r.context.block.fork) =
      PlainOp.wordRuleReads op (Fork.ruleSet f')) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } } op =
      PlainOp.run r op := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow, ← PlainOp.wordRow?_run_eq hrow]
    refine Frame.State.liftMachine_congr r.state ?_
    simp only [PlainOp.wordRuleReads, hrow, Prod.mk.injEq] at h
    cases op <;> simp only [PlainOp.wordRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;> subst hrow
    case some.blobbasefee =>
      simp only [WordRow.step, WordRow.context, BlockContext.rules, Option.some.injEq] at h ⊢
      simp only [h.1, h.2]
      rfl
    all_goals
      simp only [WordRow.step, WordRow.context, WordRow.unary, WordRow.binary, WordRow.ternary,
        PlainOp.blockHashAt, BlockContext.rules] at h ⊢
      try simp only [h.1]
    all_goals rfl

theorem PlainOp.word_run_gasMeasure_lt {op : Jaune.PlainOp}
    (hword : (PlainOp.wordRow? op).isSome) (r : Frame.Running) {s' : Frame.State}
    (hok : PlainOp.run r op = .ok s') :
    s'.machine.gasMeasure < r.state.machine.gasMeasure := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow] at hok
    unfold Frame.State.liftMachine at hok
    cases hs : row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine with
    | error e => simp [hs] at hok
    | ok m' =>
      simp only [hs, Except.ok.injEq] at hok
      subst hok
      exact WordRow.step_gasMeasure_lt_of_ok (PlainOp.wordRow?_cost_pos hrow) hs

theorem PlainOp.word_run_memory {op : Jaune.PlainOp}
    (hword : (PlainOp.wordRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.machine.memory) =
      r.state.machine.memory := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    have hm := WordRow.step_memory row r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine
    cases hs : row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine <;>
      simpa [hs] using hm

theorem PlainOp.word_run_stateGas {op : Jaune.PlainOp}
    (hword : (PlainOp.wordRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.machine.stateGas) =
      r.state.machine.stateGas := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    have hm := WordRow.step_stateGas row r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine
    cases hs : row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine <;>
      simpa [hs] using hm

theorem PlainOp.word_run_world {op : Jaune.PlainOp}
    (hword : (PlainOp.wordRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.world) = r.state.world := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine <;> rfl

theorem PlainOp.word_run_substate {op : Jaune.PlainOp}
    (hword : (PlainOp.wordRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.substate) = r.state.substate := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine <;> rfl

theorem PlainOp.word_run_trail {op : Jaune.PlainOp}
    (hword : (PlainOp.wordRow? op).isSome) (r : Frame.Running) :
    (match PlainOp.run r op with | .ok s' | .error (_, s') => s'.trail) = r.state.trail := by
  cases hrow : PlainOp.wordRow? op with
  | none => simp [hrow] at hword
  | some row =>
    rw [← PlainOp.wordRow?_run_eq hrow]
    unfold Frame.State.liftMachine
    cases row.step r.context.block.rules.opcodes ⟨r.pc, r.context⟩ r.state.machine <;> rfl

end Jaune
