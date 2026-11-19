import Jaune.CheckedSymbolicArith
import Jaune.FrameRun.CheckedAdequacy

/-!
Composition by inversion on the checked interpreter: `PUSH1 a; PUSH1 b; ADD; STOP`. The audited
rows of `Examples.Arithmetic` restated over `Checked.Frame.Run` and `Checked.exec`.

The operand bytes, the call context, the incoming stack `s`, the gas `g`, memory, world, substate
and trail are all variables. The run ends at `STOP` with a finished exit; it says nothing about
settlement. Its premises are `9 ≤ g` (three static charges of 3) and `s.length < 1023` (room for
two pushes). `concrete` exhibits them at `g = 9`, `s = []`.
-/
namespace Examples.Checked.Arithmetic

open Jaune

abbrev code (a b : UInt8) : ByteArray := ⟨#[0x60, a, 0x60, b, 0x01, 0x00]⟩

theorem first (a b : UInt8) :
    Jaune.NextOp.At (code a b) 0 (.push [a] (by simp)) := by
  simp [Jaune.NextOp.At, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, ByteArray.sliceD, UInt8.toHaltOp]
  rfl

theorem second (a b : UInt8) :
    Jaune.NextOp.At (code a b) 2 (.push [b] (by simp)) := by
  simp [Jaune.NextOp.At, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, ByteArray.sliceD, UInt8.toHaltOp]
  rfl

theorem third (a b : UInt8) :
    Jaune.PlainOp.At (code a b) 4 (Checked.SymbolicArith.Op.add.rinst) := by
  simp [Jaune.PlainOp.At, Checked.SymbolicArith.Op.rinst, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, UInt8.toHaltOp]
  rfl

theorem last (a b : UInt8) : Jaune.HaltOp.At (code a b) 5 .stop := by
  simp [Jaune.HaltOp.At, code, ByteArray.getOp,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toOpClass, UInt8.highs, UInt8.lows, UInt8.toHaltOp]
  rfl

/-- Start with gas `g` and incoming stack `s`; everything else comes from `base`. -/
def initial (base : Checked.Frame.State) (g : Nat) (s : List U256) : Checked.Frame.State :=
  { base with machine := { base.machine with stack := s, gasLeft := g } }

def afterFirst (base : Checked.Frame.State) (a : UInt8) (g : Nat) (s : List U256) : Checked.Frame.State :=
  Checked.SymbolicPush.post [a] (initial base g s)

def afterSecond (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256) : Checked.Frame.State :=
  Checked.SymbolicPush.post [b] (afterFirst base a g s)

def finalState (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256) : Checked.Frame.State :=
  Checked.SymbolicArith.post .add (Bytes.toU256 [b]) (Bytes.toU256 [a]) s (afterSecond base a b g s)

/-- The call context running this code. -/
abbrev context (ctx : Checked.CallContext) (a b : UInt8) : Checked.CallContext := { ctx with code := code a b }

theorem final_stack (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256) :
    (finalState base a b g s).machine.stack = (Bytes.toU256 [b] + Bytes.toU256 [a]) :: s := rfl

theorem toNat_single (x : UInt8) : (Bytes.toU256 [x]).toNat = x.toNat := by
  simp [Bytes.toU256, Bytes.toU256.go, U256.toNat, U128.toNat]

/-- The pushed word is the sum of the two bytes; `ADD` wraps modulo `2 ^ 256`, and two bytes never
reach that bound. -/
theorem final_sum (a b : UInt8) :
    (Bytes.toU256 [b] + Bytes.toU256 [a]).toNat = a.toNat + b.toNat := by
  have ha := UInt8.toNat_lt a
  have hb := UInt8.toNat_lt b
  rw [U256.toNat_add, toNat_single, toNat_single, Nat.lo_eq_of_lt (by omega)]
  omega

/-- The exact gas figure: three static charges of 3. -/
theorem final_gas (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256) :
    (finalState base a b g s).machine.gasLeft = g - 9 := by
  simp [finalState, afterSecond, afterFirst, initial, Checked.SymbolicArith.post,
    Checked.SymbolicPush.post, Checked.SymbolicArith.Op.cost, Checked.SymbolicPush.cost, Gas.veryLow]
  omega

theorem final_world (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256) :
    (finalState base a b g s).world = base.world := rfl

/-- Proposed replacement of `Examples.Arithmetic.final_meta` (row 79): the substate and trail are
unchanged. -/
theorem final_substate_trail (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256) :
    (finalState base a b g s).substate = base.substate ∧ (finalState base a b g s).trail = base.trail :=
  ⟨rfl, rfl⟩

section Steps

variable (ctx : Checked.CallContext) (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256)

theorem step0 (gas : 9 ≤ g) (room : s.length < 1023) :
    Checked.step ⟨0, context ctx a b, initial base g s⟩ = .ok (.next 2 (afterFirst base a g s)) :=
  (Checked.step_of_next (r := ⟨0, context ctx a b, initial base g s⟩) (first a b)).trans <|
    congrArg Except.ok <| Checked.SymbolicPush.step_success _ [a] (by simp)
      (by simp [Checked.SymbolicPush.cost, initial, Gas.veryLow]; omega)
      (by simp [initial]; omega)
      (Or.inl (by simp))

theorem step2 (gas : 9 ≤ g) (room : s.length < 1023) :
    Checked.step ⟨2, context ctx a b, afterFirst base a g s⟩ = .ok (.next 4 (afterSecond base a b g s)) :=
  (Checked.step_of_next (r := ⟨2, context ctx a b, afterFirst base a g s⟩) (second a b)).trans <|
    congrArg Except.ok <| Checked.SymbolicPush.step_success _ [b] (by simp)
      (by simp [Checked.SymbolicPush.cost, Checked.SymbolicPush.post, afterFirst, initial, Gas.veryLow]; omega)
      (by simp [Checked.SymbolicPush.post, afterFirst, initial]; omega)
      (Or.inl (by simp))

theorem step4 (gas : 9 ≤ g) (room : s.length < 1023) :
    Checked.step ⟨4, context ctx a b, afterSecond base a b g s⟩ = .ok (.next 5 (finalState base a b g s)) :=
  (Checked.step_of_next (r := ⟨4, context ctx a b, afterSecond base a b g s⟩)
    (n := .plain Checked.SymbolicArith.Op.add.rinst) (third a b)).trans <|
    congrArg Except.ok <| Checked.SymbolicArith.step_success _ .add _ _ s rfl
      (by simp [Checked.SymbolicArith.Op.cost, Checked.SymbolicPush.cost, Checked.SymbolicPush.post,
            afterSecond, afterFirst, initial, Gas.veryLow]; omega)
      (by omega)

theorem step5 :
    Checked.step ⟨5, context ctx a b, finalState base a b g s⟩ =
      .ok (.exit (.finished [] (finalState base a b g s))) :=
  Checked.step_of_halt (r := ⟨5, context ctx a b, finalState base a b g s⟩) (l := .stop) (last a b)

end Steps

/-- One run on the checked interpreter. -/
def execution (ctx : Checked.CallContext) (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256)
    (gas : 9 ≤ g) (room : s.length < 1023) :
    Checked.Frame.Run ⟨0, context ctx a b, initial base g s⟩
      (.exit (.ok (.finished [] (finalState base a b g s)))) :=
  .next (step0 ctx base a b g s gas room) <|
  .next (step2 ctx base a b g s gas room) <|
  .next (step4 ctx base a b g s gas room) <|
  .halt (step5 ctx base a b g s)

/-- Inversion at a continuing step. -/
def next {r : Checked.Frame.Running} {pc' : Nat} {s' : Checked.Frame.State} {out}
    (d : Checked.Frame.Run r (.exit out)) (h : Checked.step r = .ok (.next pc' s')) :
    Checked.Frame.Run ⟨pc', r.context, s'⟩ (.exit out) := by
  cases d with
  | halt h' => rw [h] at h'; cases out <;> cases h'
  | next h' d' => cases h.symm.trans h'; exact d'
  | callDone h' _ _ _ => cases h.symm.trans h'
  | callRan h' _ _ _ _ => cases h.symm.trans h'
  | callDoneEnd h' _ _ => cases h.symm.trans h'
  | callRanEnd h' _ _ _ => cases h.symm.trans h'

private theorem halt_inv {r : Checked.Frame.Running} {x out}
    (d : Checked.Frame.Run r (.exit out)) (h : Checked.step r = .ok (.exit x)) : out = .ok x := by
  cases d with
  | halt h' =>
    rw [h] at h'
    cases out with
    | error => cases h'
    | ok y => cases h'; rfl
  | next h' _ | callDone h' _ _ _ | callRan h' _ _ _ _ | callDoneEnd h' _ _ | callRanEnd h' _ _ _ =>
    cases h.symm.trans h'

/-- Every run from this start state ends in `finalState`. -/
theorem result (ctx : Checked.CallContext) (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256)
    (gas : 9 ≤ g) (room : s.length < 1023) {out}
    (d : Checked.Frame.Run ⟨0, context ctx a b, initial base g s⟩ (.exit out)) :
    out = .ok (.finished [] (finalState base a b g s)) :=
  let d2 := next d (step0 ctx base a b g s gas room)
  let d4 := next d2 (step2 ctx base a b g s gas room)
  let d5 := next d4 (step4 ctx base a b g s gas room)
  halt_inv d5 (step5 ctx base a b g s)

/-- Adequacy connects the run to the checked total interpreter. -/
theorem interpreter (ctx : Checked.CallContext) (base : Checked.Frame.State) (a b : UInt8) (g : Nat) (s : List U256)
    (gas : 9 ≤ g) (room : s.length < 1023) :
    Checked.exec ⟨0, context ctx a b, initial base g s⟩ = .ok (.finished [] (finalState base a b g s)) :=
  (Checked.Frame.Run.exec_iff _ _).mp ⟨execution ctx base a b g s gas room⟩

/-- The premises are satisfiable: exactly nine gas and an empty stack. -/
theorem concrete (ctx : Checked.CallContext) (base : Checked.Frame.State) (a b : UInt8) :
    Checked.exec ⟨0, context ctx a b, initial base 9 []⟩ = .ok (.finished [] (finalState base a b 9 [])) ∧
      (finalState base a b 9 []).machine.gasLeft = 0 :=
  ⟨interpreter ctx base a b 9 [] (by decide) (by decide), final_gas base a b 9 []⟩

/-! ### Negative checks

Each block below must fail to elaborate. `#guard_msgs` turns the expected error into a pass and any
other outcome, including success, into a build error. -/

-- `DIV` is not a member of the arithmetic family, so the `ADD` rule cannot describe its step.
/--
error: Type mismatch
  Checked.SymbolicArith.step_success r Checked.SymbolicArith.Op.add x y rest stack gas room
has type
  Checked.NextOp.step r (NextOp.plain Checked.SymbolicArith.Op.add.rinst) =
    Checked.Step.next (r.pc + 1) (Checked.SymbolicArith.post Checked.SymbolicArith.Op.add x y rest r.state)
but is expected to have type
  Checked.NextOp.step r (NextOp.plain PlainOp.div) =
    Checked.Step.next (r.pc + 1) (Checked.SymbolicArith.post Checked.SymbolicArith.Op.add x y rest r.state)
-/
#guard_msgs in
example (r : Checked.Frame.Running) (x y : U256) (rest : List U256)
    (stack : r.state.machine.stack = x :: y :: rest)
    (gas : Checked.SymbolicArith.Op.cost .add ≤ r.state.machine.gasLeft) (room : rest.length < 1024) :
    Checked.NextOp.step r (.plain .div) =
      .next (r.pc + 1) (Checked.SymbolicArith.post .add x y rest r.state) :=
  Checked.SymbolicArith.step_success r .add x y rest stack gas room

-- Eight gas is one short of the three static charges: the gas premise is rejected.
/--
error: Tactic `decide` proved that the proposition
  9 ≤ 8
is false
-/
#guard_msgs in
example (ctx : Checked.CallContext) (base : Checked.Frame.State) (a b : UInt8) :
    Checked.exec ⟨0, context ctx a b, initial base 8 []⟩ = .ok (.finished [] (finalState base a b 8 [])) :=
  interpreter ctx base a b 8 [] (by decide) (by decide)

end Examples.Checked.Arithmetic
