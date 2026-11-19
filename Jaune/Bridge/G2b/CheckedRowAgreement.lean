import Jaune.Bridge.G2b.CheckedPlainArms
import Jaune.Bridge.G2b.CheckedContext
import Jaune.Instructions.WordFacts
import Jaune.Instructions.ShuffleFacts
import Jaune.Instructions.PushFacts
import Jaune.Instructions.LogFacts
import Jaune.Instructions.MemoryFacts
import Jaune.Instructions.ReadFacts

/-!
# Bridge: the rows of the Word, Shuffle, push, Log, Memory and Read families against the arms

The agreement lemmas of W4's family units (u4x, u67, u68), moved here unchanged from
`Jaune/Instructions/{Word,Shuffle,Push,Log,Memory,Read}Facts.lean` at `9ce48608` into the
namespace `Jaune.Checked.Arms`, where `PlainOp.runCore`, `PlainOp.run` and `NextOp.step` name the
old side (`Jaune.Bridge.G2b.CheckedPlainArms`). Each says that a row, stepped by its family's
step and lifted, is the per-opcode arm, for every program counter, call context and frame state,
hence every `Fork`, on both channels. They are the inputs of the cut's bridge
(`Jaune.Bridge.G2b.CheckedDispatch`) and go with it after G2b's tag.
-/

namespace Jaune.Checked.Arms

open Jaune

private theorem liftMachine_congr {ε : Type} {f g : Machine → Except (ε × Machine) Machine}
    (s : Frame.State) (h : f s.machine = g s.machine) : s.liftMachine f = s.liftMachine g := by
  unfold Frame.State.liftMachine
  rw [h]

/-! ### Word -/

/-- **Bridge (50 plain word opcodes):** every row in `PlainOp.wordRow?`, lifted via
`Frame.State.liftMachine`, equals `Checked.PlainOp.runCore` for every `pc`, `CallContext`,
and `Frame.State` (hence every `Fork`). -/
theorem PlainOp.wordRow?_runCore_eq {op : Jaune.PlainOp} {row : WordRow}
    (hrow : PlainOp.wordRow? op = some row) (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftMachine (row.step ctx.block.rules.opcodes ⟨pc, ctx.toChecked⟩) = PlainOp.runCore pc ctx s op := by
  cases op <;> simp only [PlainOp.wordRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;> subst hrow <;>
    dsimp only [PlainOp.runCore, Frame.State.pushItem, Frame.State.applyUnary,
      Frame.State.applyBinary, Frame.State.applyTernary]
  case address | origin | caller | callvalue | calldatasize | codesize | gasprice |
      returndatasize | number | timestamp | gaslimit | prevrandao | coinbase | msize | pc =>
    exact liftMachine_congr s (WordRow.context_step _ _ _ _ s.machine _ (fun _ => rfl))
  case iszero | not =>
    exact liftMachine_congr s (WordRow.unary_step ..)
  case eq | lt | gt | slt | sgt | and | or | xor | signextend | byte | add | sub | mul |
      div | sdiv | mod | smod =>
    exact liftMachine_congr s (WordRow.binary_step ..)
  case addmod | mulmod =>
    exact liftMachine_congr s (WordRow.ternary_step ..)
  case basefee =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.baseFee
    · simp only [ha, ↓reduceIte, WordRow.step, WordRow.context, Machine.popWords,
        Machine.pushItem, bind, Except.bind]
      cases hg : s.machine.chargeGas Gas.base <;> rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case blobbasefee =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.blobBaseFee
    · simp only [ha, ↓reduceIte, WordRow.step, WordRow.context, Machine.popWords,
        Machine.pushItem, bind, Except.bind]
      cases hg : s.machine.chargeGas Gas.base <;> rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case chainid =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.chainId
    · simp only [ha, ↓reduceIte, WordRow.step, WordRow.context, Machine.popWords,
        Machine.pushItem, bind, Except.bind]
      cases hg : s.machine.chargeGas Gas.base <;> rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case slotnum =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.slotnum
    · simp only [ha, ↓reduceIte, WordRow.step, WordRow.context, Machine.popWords,
        Machine.pushItem, bind, Except.bind]
      cases hg : s.machine.chargeGas Gas.base <;> rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case gas =>
    refine liftMachine_congr s ?_
    simp only [WordRow.step, WordRow.context, Machine.popWords, ↓reduceIte, bind, Except.bind]
  case blobhash =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.blobHash
    · simp only [ha, ↓reduceIte, WordRow.step, Machine.popWords, bind, Except.bind]
      cases hp : s.machine.pop with
      | error err => rfl
      | ok pair =>
        obtain ⟨x, m'⟩ := pair
        simp only [Jaune.CallContext.toChecked_blobVersionedHashes]
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case calldataload =>
    refine liftMachine_congr s ?_
    simp only [WordRow.step, Machine.popWords, ↓reduceIte, bind, Except.bind]
    cases hp : s.machine.pop with
    | error err => rfl
    | ok pair =>
      obtain ⟨x, m'⟩ := pair
      simp only [Jaune.CallContext.toChecked_calldata]
  case blockhash =>
    refine liftMachine_congr s ?_
    simp only [WordRow.step, Machine.popWords, ↓reduceIte, bind, Except.bind]
    cases hp : s.machine.pop with
    | error err => rfl
    | ok pair =>
      obtain ⟨x, m'⟩ := pair
      dsimp only
  case shl | shr | sar =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.shifts
    · simp only [ha, ↓reduceIte, WordRow.step, WordRow.binary, Machine.popWords,
        Machine.applyBinary, Machine.pushItem, bind, Except.bind, pure, Except.pure]
      cases hx : s.machine.pop with
      | error err => rfl
      | ok p1 =>
        obtain ⟨x, next⟩ := p1
        dsimp only
        cases hy : next.pop with
        | error err => rfl
        | ok p2 =>
          obtain ⟨y, last⟩ := p2
          dsimp only
          cases hg : last.chargeGas Gas.veryLow <;> rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case clz =>
    refine liftMachine_congr s ?_
    by_cases ha : ctx.block.rules.opcodes.clz
    · simp only [ha, ↓reduceIte, WordRow.step, WordRow.unary, Machine.popWords,
        Machine.applyUnary, Machine.pushItem, bind, Except.bind]
      cases hx : s.machine.pop with
      | error err => rfl
      | ok pair =>
        obtain ⟨x, next⟩ := pair
        dsimp only
        cases hg : next.chargeGas Gas.low <;> rfl
    · simp only [ha, Bool.false_eq_true, ↓reduceIte]
      exact WordRow.step_unavailable (by simp [ha])
  case exp =>
    refine liftMachine_congr s ?_
    simp only [WordRow.step, Machine.popWords, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    cases hx : s.machine.pop with
    | error err => rfl
    | ok p1 =>
      obtain ⟨base, m₁⟩ := p1
      dsimp only
      cases hy : m₁.pop with
      | error err => rfl
      | ok p2 =>
        obtain ⟨exponent, m₂⟩ := p2
        dsimp only
  case pop =>
    refine liftMachine_congr s ?_
    simp only [WordRow.step, Machine.popWords, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    cases hx : s.machine.pop with
    | error err => rfl
    | ok pair =>
      dsimp only
      cases hg : pair.2.chargeGas Gas.base <;> rfl

/-! ### Shuffle -/

/-- **Bridge (`DUP1`–`DUP16`, `SWAP1`–`SWAP16`):** the row, lifted by `liftMachine`, equals
`Checked.PlainOp.runCore` for every `pc`, `CallContext` and `Frame.State` (hence every `Fork`). -/
theorem PlainOp.shuffleRow?_runCore_eq {op : Jaune.PlainOp} {row : ShuffleRow}
    (hrow : PlainOp.shuffleRow? op = some row) (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftMachine (row.step ctx.block.rules.opcodes) = PlainOp.runCore pc ctx s op := by
  cases op <;> simp only [PlainOp.shuffleRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;>
    subst hrow <;> dsimp only [PlainOp.runCore] <;> refine liftMachine_congr s ?_ <;>
    simp only [ShuffleRow.step, Shuffle.run, ↓reduceIte, bind, Except.bind] <;>
    cases s.machine.chargeGas Gas.veryLow <;> rfl

/-- **Bridge (`DUPN`, `SWAPN`, `EXCHANGE`):** the row, lifted by `liftMachine` and turned into a
step at the next program counter, equals `Checked.NextOp.step` for every running frame (hence
every `Fork`). -/
theorem NextOp.shuffleRow?_step_eq {n : Jaune.NextOp} {row : ShuffleRow}
    (hrow : NextOp.shuffleRow? n = some row) (r : Frame.Running) :
    Step.ofHalt (r.pc + n.size) (r.state.liftMachine (row.step r.context.block.rules.opcodes)) =
      NextOp.step r n := by
  cases n <;> simp only [NextOp.shuffleRow?, NextOp.dupnRow, NextOp.swapnRow, NextOp.exchangeRow, Option.some.injEq, reduceCtorEq] at hrow <;>
    subst hrow <;> simp only [NextOp.step] <;> congr 1
  all_goals
    by_cases ha : r.context.block.rules.opcodes.stackAccess
    case neg =>
      simp [ShuffleRow.step, ha, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
        Frame.State.liftMachine, Frame.State.withMachine]
    simp only [ShuffleRow.step, ha, ↓reduceIte, bind, Except.bind,
      Frame.State.chargeGas, Frame.State.liftMachine]
    cases hc : r.state.machine.chargeGas Gas.veryLow with
    | error err => rfl
    | ok m => ?_
    simp only
  next imm =>
    cases hd : decodeSingle imm with
    | none => rfl
    | some n =>
      simp only [Option.map_some, Shuffle.run, Frame.State.push, Frame.State.liftMachine,
        Frame.State.withMachine, Frame.State.stack]
      cases m.stack[n - 1]? with
      | none => rfl
      | some w => cases Machine.push w m <;> rfl
  next imm =>
    cases hd : decodeSingle imm with
    | none => rfl
    | some n =>
      simp only [Option.map_some, Shuffle.run, Frame.State.withStack, Frame.State.withMachine,
        Frame.State.stack]
      cases List.swap m.stack (n - 1) <;> rfl
  next imm =>
    cases hd : decodePair imm with
    | none => rfl
    | some p =>
      simp only [Option.map_some, Shuffle.run, Frame.State.withStack, Frame.State.withMachine,
        Frame.State.stack]
      cases List.exchange m.stack p.1 p.2 <;> rfl

/-! ### Push -/

/-- **Bridge (`PUSH0`–`PUSH32`):** the push row, stepped by `WordRow.step`, lifted by
`liftMachine` and turned into a step at the next program counter, equals `Checked.NextOp.step`
for every running frame (hence every `Fork`). -/
theorem NextOp.pushRow_step_eq (xs : Bytes) (hxs : xs.length ≤ 32) (r : Frame.Running) :
    Step.ofHalt (r.pc + (NextOp.push xs hxs).size)
        (r.state.liftMachine ((NextOp.pushRow xs).step r.context.block.rules.opcodes
          ⟨r.pc, r.context.toChecked⟩)) =
      NextOp.step r (.push xs hxs) := by
  simp only [NextOp.step]
  by_cases hnil : xs = []
  · subst hnil
    by_cases h0 : r.context.block.rules.opcodes.push0
    · simp only [h0, NextOp.pushRow, WordRow.step, List.isEmpty_nil, Bool.not_true,
        Bool.false_or, ↓reduceIte, Machine.popWords, bind, Except.bind, decide_true,
        Bool.not_true, Bool.and_false, Bool.false_eq_true, Frame.State.chargeGas,
        Frame.State.push, Frame.State.liftMachine]
      cases r.state.machine.chargeGas Gas.base <;> rfl
    · simp [h0, NextOp.pushRow, WordRow.step, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind, Frame.State.liftMachine, Frame.State.withMachine]
  · have he : xs.isEmpty = false := by simpa using hnil
    simp only [hnil, he, NextOp.pushRow, WordRow.step, Bool.not_false, Bool.true_or,
      ↓reduceIte, Machine.popWords, bind, Except.bind, decide_false, Bool.false_and,
      Bool.false_eq_true, Bool.false_eq_true, Frame.State.chargeGas, Frame.State.push,
      Frame.State.liftMachine]
    cases r.state.machine.chargeGas Gas.veryLow <;> rfl

theorem NextOp.pushRow?_step_eq {n : Jaune.NextOp} {row : WordRow}
    (hrow : NextOp.pushRow? n = some row) (r : Frame.Running) :
    Step.ofHalt (r.pc + n.size)
        (r.state.liftMachine (row.step r.context.block.rules.opcodes ⟨r.pc, r.context.toChecked⟩)) =
      NextOp.step r n := by
  cases n <;> simp only [NextOp.pushRow?, Option.some.injEq, reduceCtorEq] at hrow
  subst hrow
  exact NextOp.pushRow_step_eq _ _ r

/-! ### Log -/

theorem PlainOp.logRow_step_eq (n : Fin 5) :
    (fun ctx : Jaune.CallContext => LogRow.step { topics := n } ctx.toChecked) = PlainOp.logStep n := rfl

/-- **Bridge (`LOG0`–`LOG4`):** the row, lifted by `Frame.State.liftLog`, equals
`Checked.PlainOp.runCore` for every `pc`, `CallContext` and `Frame.State` (hence every `Fork`). -/
theorem PlainOp.logRow?_runCore_eq {op : Jaune.PlainOp} {row : LogRow}
    (hrow : PlainOp.logRow? op = some row) (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftLog (row.step ctx.toChecked s.machine) = PlainOp.runCore pc ctx s op := by
  cases op <;> simp only [PlainOp.logRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow
  subst hrow
  rfl

/-! ### Memory -/

/-- The Memory table's bridge: every Memory row, lifted through `Frame.State.liftMachine`,
equals `Checked.PlainOp.runCore`, for every `pc`, call context and frame state (hence every
`Fork`). -/
theorem PlainOp.memoryRow?_runCore_eq {op : Jaune.PlainOp} {row : MemoryRow}
    (hrow : PlainOp.memoryRow? op = some row) (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftMachine (row.step ctx.block.rules.opcodes ctx.toChecked) = PlainOp.runCore pc ctx s op := by
  cases op <;> simp only [PlainOp.memoryRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;>
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

/-! ### Read -/

/-- Unfold the frame-state helpers into structure literals, so both sides of a bridge meet on
the machine. -/
local macro "read_norm" : tactic => `(tactic| try dsimp only [Frame.State.chargeGas, Frame.State.push, Frame.State.pushItem, Frame.State.liftMachine,
    Frame.State.withMachine, Frame.State.withSubstate, Frame.State.withTrail,
    Frame.State.accessedAddresses, Frame.State.accessedStorageKeys, Frame.State.addAccessedAddress,
    Frame.State.addAccessedStorageKey, Frame.State.recordAccountRead, Frame.State.recordStorageRead,
    Frame.State.balance, Frame.State.account, Frame.State.state, Frame.State.code,
    Frame.State.storageValue, Frame.State.transientValue, Frame.State.transientStorage,
    Frame.State.memWrite, Frame.State.liftMachinePure, Frame.State.extCost, Frame.State.popToNat,
    Frame.State.pop, Frame.State.liftMachineValue, Machine.pushItem] at *)

/-- The charge and the push of a Read row against its `runCore` arm. -/
local macro "read_tail " m:term:max cost:term:max : tactic => `(tactic| (
  cases hc : Machine.chargeGas $cost $m with
  | error e => rcases e with ⟨e, m'⟩; rfl
  | ok m₂ =>
    read_norm
    by_cases hlen : m₂.stack.length < 1024 <;>
      simp only [Machine.push, hlen, ↓reduceIte, bind, Except.bind] <;> rfl))

/-- The charge and the write of `EXTCODECOPY` against its `runCore` arm. -/
local macro "copy_tail " m:term:max cost:term:max : tactic => `(tactic| (
  cases hc : Machine.chargeGas $cost $m with
  | error e => rcases e with ⟨e, m'⟩; rfl
  | ok m₂ => rfl))

/-- The Read table's bridge: every Read row, lifted through `Frame.State.liftRead` over the
frame's read view, equals `Checked.PlainOp.runCore`, for every `pc`, call context and frame state
(hence every `Fork`), on both channels with their touches. -/
theorem PlainOp.readRow?_runCore_eq {op : Jaune.PlainOp} {row : ReadRow}
    (hrow : PlainOp.readRow? op = some row) (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftRead ctx.block.rules (row.step ctx.block.rules ctx.toChecked s.readView) =
      PlainOp.runCore pc ctx s op := by
  cases op <;> simp only [PlainOp.readRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;>
    subst hrow <;> dsimp only [PlainOp.runCore]
  case balance =>
    simp only [Frame.State.liftRead, ReadRow.step, ReadTarget.pop, Frame.State.popToAddress,
      Frame.State.liftMachineValue, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    cases hp : s.machine.popToAddress with
    | error e => rcases e with ⟨e, m'⟩; rfl
    | ok p =>
      obtain ⟨a, m₁⟩ := p
      try dsimp only [ReadPrice.quote, ReadResult.finish, Frame.State.readView]
      read_norm
      cases hacc : ctx.block.rules.access with
      | flat g =>
        read_norm
        read_tail m₁ g.balance
      | eip2929 =>
        read_norm
        by_cases hw : a ∈ s.substate.accessedAddresses
        · simp only [hw, ↓reduceIte]
          read_tail m₁ Gas.warmStorageReadCost
        · simp only [hw, ↓reduceIte]
          read_tail m₁ ctx.block.rules.gas.coldAccountAccess
  case extcodesize =>
    simp only [Frame.State.liftRead, ReadRow.step, ReadTarget.pop, Frame.State.popToAddress,
      Frame.State.liftMachineValue, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    cases hp : s.machine.popToAddress with
    | error e => rcases e with ⟨e, m'⟩; rfl
    | ok p =>
      obtain ⟨a, m₁⟩ := p
      try dsimp only [ReadPrice.quote, ReadResult.finish, Frame.State.readView]
      read_norm
      cases hacc : ctx.block.rules.access with
      | flat g =>
        read_norm
        read_tail m₁ (g.extCode + ctx.block.rules.gas.codeReadSurcharge)
      | eip2929 =>
        read_norm
        by_cases hw : a ∈ s.substate.accessedAddresses
        · simp only [hw, ↓reduceIte]
          read_tail m₁ (Gas.warmStorageReadCost + ctx.block.rules.gas.codeReadSurcharge)
        · simp only [hw, ↓reduceIte]
          read_tail m₁ (ctx.block.rules.gas.coldAccountAccess + ctx.block.rules.gas.codeReadSurcharge)
  case extcodehash =>
    by_cases hav : ctx.block.rules.opcodes.extCodeHash
    · simp only [Frame.State.liftRead, ReadRow.step, hav, ↓reduceIte, Bool.not_true,
        Bool.false_eq_true]
      try simp only [ReadTarget.pop, Frame.State.popToAddress, Frame.State.liftMachineValue, bind,
        Except.bind]
      cases hp : s.machine.popToAddress with
      | error e => rcases e with ⟨e, m'⟩; rfl
      | ok p =>
        obtain ⟨a, m₁⟩ := p
        try dsimp only [ReadPrice.quote, ReadResult.finish, Frame.State.readView]
        read_norm
        cases hacc : ctx.block.rules.access with
        | flat g =>
          read_norm
          read_tail m₁ (g.extCodeHash)
        | eip2929 =>
          read_norm
          by_cases hw : a ∈ s.substate.accessedAddresses
          · simp only [hw, ↓reduceIte]
            read_tail m₁ (Gas.warmStorageReadCost)
          · simp only [hw, ↓reduceIte]
            read_tail m₁ (ctx.block.rules.gas.coldAccountAccess)
    · simp only [hav, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Frame.State.liftRead,
        ReadRow.step]
      try rfl
  case selfbalance =>
    by_cases hav : ctx.block.rules.opcodes.selfBalance
    · simp only [Frame.State.liftRead, ReadRow.step, hav, ↓reduceIte, Bool.not_true,
        Bool.false_eq_true, ReadTarget.pop, ReadPrice.quote, ReadResult.finish, Frame.State.readView]
      read_norm
      read_tail s.machine Gas.low
    · simp only [hav, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Frame.State.liftRead,
        ReadRow.step]
      try rfl
  case sload =>
    simp only [Frame.State.liftRead, ReadRow.step, ReadTarget.pop, bind, Except.bind,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    read_norm
    cases hp : s.machine.pop with
    | error e => rcases e with ⟨e, m'⟩; rfl
    | ok p =>
      obtain ⟨k, m₁⟩ := p
      try dsimp only [ReadPrice.quote, ReadResult.finish, Frame.State.readView]
      read_norm
      cases hacc : ctx.block.rules.access with
      | flat g =>
        read_norm
        read_tail m₁ g.sload
      | eip2929 =>
        read_norm
        simp only [Jaune.CallContext.toChecked_recipient]
        by_cases hw : ((ctx.recipient, k) : Address × U256) ∈ s.substate.accessedStorageKeys
        · simp only [hw, ↓reduceIte]
          read_tail m₁ Gas.warmStorageReadCost
        · simp only [hw, ↓reduceIte]
          read_tail m₁ Gas.coldSloadCost
  case tload =>
    by_cases hav : ctx.block.rules.opcodes.transient
    · simp only [Frame.State.liftRead, ReadRow.step, hav, ↓reduceIte, Bool.not_true,
        Bool.false_eq_true, ReadTarget.pop, bind, Except.bind]
      read_norm
      cases hp : s.machine.pop with
      | error e => rcases e with ⟨e, m'⟩; rfl
      | ok p =>
        obtain ⟨k, m₁⟩ := p
        simp only [ReadPrice.quote, ReadResult.finish, Frame.State.readView]
        read_tail m₁ Gas.warmStorageReadCost
    · simp only [hav, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Frame.State.liftRead,
        ReadRow.step]
      try rfl
  case extcodecopy =>
    simp only [Frame.State.liftRead, ReadRow.step, ReadTarget.pop, Frame.State.popToAddress,
      Frame.State.liftMachineValue, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte]
    cases hp : s.machine.popToAddress with
    | error e => rcases e with ⟨e, m'⟩; rfl
    | ok p =>
      obtain ⟨a, m₁⟩ := p
      try dsimp only [ReadPrice.quote, ReadResult.finish, Frame.State.readView]
      read_norm
      cases h1 : m₁.popToNat with
      | error e => rcases e with ⟨e, m'⟩; rfl
      | ok p =>
        obtain ⟨d, m₂⟩ := p
        read_norm
        cases h2 : m₂.popToNat with
        | error e => rcases e with ⟨e, m'⟩; rfl
        | ok p =>
          obtain ⟨o, m₃⟩ := p
          read_norm
          cases h3 : m₃.popToNat with
          | error e => rcases e with ⟨e, m'⟩; rfl
          | ok p =>
            obtain ⟨n, m₄⟩ := p
            read_norm
            cases hacc : ctx.block.rules.access with
            | flat g =>
              read_norm
              copy_tail m₄ (g.extCode + ctx.block.rules.gas.codeReadSurcharge + Gas.copy * ceilDiv n 32 +
                m₄.extCost [(d, n)])
            | eip2929 =>
              read_norm
              by_cases hw : a ∈ s.substate.accessedAddresses
              · simp only [hw, ↓reduceIte]
                copy_tail m₄ (Gas.warmStorageReadCost + ctx.block.rules.gas.codeReadSurcharge +
                  Gas.copy * ceilDiv n 32 + m₄.extCost [(d, n)])
              · simp only [hw, ↓reduceIte]
                copy_tail m₄ (ctx.block.rules.gas.coldAccountAccess +
                  ctx.block.rules.gas.codeReadSurcharge + Gas.copy * ceilDiv n 32 + m₄.extCost [(d, n)])

end Jaune.Checked.Arms
