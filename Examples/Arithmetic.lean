import Jaune.SymbolicPush
import Jaune.SymbolicArith

/-!
Composition by inversion: `PUSH1 a; PUSH1 b; ADD; STOP`.

The operand bytes, the environment, the incoming stack `s`, the gas `g`,
memory, metadata and world are all variables. The derivation is a completed
raw frame: it ends at `STOP` with an `.ok` machine state, and it says nothing
about message settlement or transaction validation. Its premises are
`9 ≤ g` (three static charges of 3) and `s.length < 1023` (room for two pushes).
`concrete` exhibits them at `g = 9`, `s = []`.

`execution` builds one derivation. `result` inverts an arbitrary derivation
step by step, so every derivation from this start state (not only the one we
built) ends in the same state; `interpreter` then reads the total interpreter's
answer through adequacy. The negative checks at the end fail the build if a
wrong premise or an unsupported opcode ever starts elaborating.
-/
namespace Examples.Arithmetic

open Jaune

abbrev code (a b : UInt8) : ByteArray := ⟨#[0x60, a, 0x60, b, 0x01, 0x00]⟩

theorem first (a b : UInt8) :
    Jaune.Ninst.At (code a b) 0 (.push [a] (by simp)) := by
  simp [Jaune.Ninst.At, code, ByteArray.getInst,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toInstType, UInt8.highs, UInt8.lows, ByteArray.sliceD, UInt8.toLinst]
  rfl

theorem second (a b : UInt8) :
    Jaune.Ninst.At (code a b) 2 (.push [b] (by simp)) := by
  simp [Jaune.Ninst.At, code, ByteArray.getInst,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toInstType, UInt8.highs, UInt8.lows, ByteArray.sliceD, UInt8.toLinst]
  rfl

theorem third (a b : UInt8) :
    Jaune.Rinst.At (code a b) 4 (SymbolicArith.Op.add.rinst) := by
  simp [Jaune.Rinst.At, SymbolicArith.Op.rinst, code, ByteArray.getInst,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toInstType, UInt8.highs, UInt8.lows, UInt8.toLinst]
  rfl

theorem last (a b : UInt8) : Jaune.Linst.At (code a b) 5 .stop := by
  simp [Jaune.Linst.At, code, ByteArray.getInst,
    ← ByteArray.size_data, ByteArray.getElem_eq_getElem_data,
    UInt8.toInstType, UInt8.highs, UInt8.lows, UInt8.toLinst]
  rfl

/-- Start with gas `g` and incoming stack `s`; everything else comes from `base`. -/
def initial (base : Devm) (g : Nat) (s : List B256) : Devm :=
  base.setMach { base.mach with stack := s, gasLeft := g }

def afterFirst (base : Devm) (a : UInt8) (g : Nat) (s : List B256) : Devm :=
  SymbolicPush.post [a] (initial base g s)

def afterSecond (base : Devm) (a b : UInt8) (g : Nat) (s : List B256) : Devm :=
  SymbolicPush.post [b] (afterFirst base a g s)

def finalState (base : Devm) (a b : UInt8) (g : Nat) (s : List B256) : Devm :=
  SymbolicArith.post .add (Bytes.toB256 [b]) (Bytes.toB256 [a]) s
    (afterSecond base a b g s)

section Steps

variable (env : Sevm) (base : Devm) (a b : UInt8) (g : Nat) (s : List B256)

/-- The environment running this code. -/
abbrev sevm : Sevm := { env with code := code a b }

theorem step0 (gas : 9 ≤ g) (room : s.length < 1023) :
    Evm.step ⟨0, sevm env a b, initial base g s⟩ = .cont 2 (afterFirst base a g s) :=
  (Evm.step_next (first a b)).trans <|
    SymbolicPush.step_success _ [a] (by simp)
      (by simp [SymbolicPush.cost, initial, Devm.gasLeft, Devm.setMach, gVerylow]; omega)
      (by simp [initial, Devm.stack, Devm.setMach]; omega)

theorem step2 (gas : 9 ≤ g) (room : s.length < 1023) :
    Evm.step ⟨2, sevm env a b, afterFirst base a g s⟩ =
      .cont 4 (afterSecond base a b g s) :=
  (Evm.step_next (second a b)).trans <|
    SymbolicPush.step_success _ [b] (by simp)
      (by simp [SymbolicPush.cost, SymbolicPush.post, afterFirst, initial, Devm.gasLeft,
            Devm.setMach, gVerylow]; omega)
      (by simp [SymbolicPush.post, afterFirst, initial, Devm.stack, Devm.setMach]; omega)

theorem step4 (gas : 9 ≤ g) (room : s.length < 1023) :
    Evm.step ⟨4, sevm env a b, afterSecond base a b g s⟩ =
      .cont 5 (finalState base a b g s) :=
  (Evm.step_next (pc := 4) (sevm := sevm env a b)
    (n := .reg SymbolicArith.Op.add.rinst) (third a b)).trans <|
    SymbolicArith.step_success _ .add _ _ s rfl
      (by simp [SymbolicArith.Op.cost, SymbolicPush.cost, SymbolicPush.post, afterSecond,
            afterFirst, initial, Devm.gasLeft, Devm.setMach, gVerylow]; omega)
      (by omega)

theorem step5 :
    Evm.step ⟨5, sevm env a b, finalState base a b g s⟩ =
      .halt (.ok (finalState base a b g s)) :=
  Evm.step_last (l := .stop) (last a b)

end Steps

/-- One derivation, from the canonical constructors. -/
def execution (env : Sevm) (base : Devm) (a b : UInt8) (g : Nat) (s : List B256)
    (gas : 9 ≤ g) (room : s.length < 1023) :
    Exec 0 (sevm env a b) (initial base g s) (.ok (finalState base a b g s)) :=
  .cont (step0 env base a b g s gas room) <|
  .cont (step2 env base a b g s gas room) <|
  .cont (step4 env base a b g s gas room) <|
  .halt (step5 env base a b g s)

/-- Inversion at a continuing step: a derivation whose root step continues
contains a derivation of the same outcome from the successor state. -/
def next {pc pc' : Nat} {sevm : Sevm} {devm devm' : Devm} {out : Execution}
    (d : Exec pc sevm devm out) (h : Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm') :
    Exec pc' sevm devm' out := by
  cases d with
  | halt h' => cases h.symm.trans h'
  | cont h' d' => cases h.symm.trans h'; exact d'
  | doneErr h' _ _ => cases h.symm.trans h'
  | doneOk h' _ _ _ => cases h.symm.trans h'
  | runErr h' _ _ _ => cases h.symm.trans h'
  | runOk h' _ _ _ _ => cases h.symm.trans h'

/-- Every derivation from this start state ends in `finalState`: the outcome is
forced by inverting the three continuing steps and the final `STOP`. -/
theorem result (env : Sevm) (base : Devm) (a b : UInt8) (g : Nat) (s : List B256)
    (gas : 9 ≤ g) (room : s.length < 1023) {out : Execution}
    (d : Exec 0 (sevm env a b) (initial base g s) out) :
    out = .ok (finalState base a b g s) :=
  let d2 := next d (step0 env base a b g s gas room)
  let d4 := next d2 (step2 env base a b g s gas room)
  let d5 := next d4 (step4 env base a b g s gas room)
  d5.halt_inv (step5 env base a b g s)

/-- Adequacy connects the derivation to the total interpreter. -/
theorem interpreter (env : Sevm) (base : Devm) (a b : UInt8) (g : Nat) (s : List B256)
    (gas : 9 ≤ g) (room : s.length < 1023) :
    exec ⟨0, sevm env a b, initial base g s⟩ = .ok (finalState base a b g s) :=
  (exec_iff_exec_eq _ _ _ _).mp ⟨execution env base a b g s gas room⟩

theorem final_stack (base : Devm) (a b : UInt8) (g : Nat) (s : List B256) :
    (finalState base a b g s).stack = (Bytes.toB256 [b] + Bytes.toB256 [a]) :: s := rfl

theorem toNat_single (x : UInt8) : (Bytes.toB256 [x]).toNat = x.toNat := by
  simp [Bytes.toB256, Bytes.toB256.go, B256.toNat, B128.toNat]

/-- The pushed word is the sum of the two bytes; `ADD` wraps modulo `2 ^ 256`,
and two bytes never reach that bound. -/
theorem final_sum (a b : UInt8) :
    (Bytes.toB256 [b] + Bytes.toB256 [a]).toNat = a.toNat + b.toNat := by
  have ha := UInt8.toNat_lt a
  have hb := UInt8.toNat_lt b
  rw [B256.toNat_add, toNat_single, toNat_single, Nat.lo_eq_of_lt (by omega)]
  omega

/-- The exact gas figure: three static charges of 3. -/
theorem final_gas (base : Devm) (a b : UInt8) (g : Nat) (s : List B256) :
    (finalState base a b g s).gasLeft = g - 9 := by
  simp [finalState, afterSecond, afterFirst, initial, SymbolicArith.post, SymbolicPush.post,
    SymbolicArith.Op.cost, SymbolicPush.cost, Devm.gasLeft, Devm.setMach, gVerylow]
  omega

theorem final_world (base : Devm) (a b : UInt8) (g : Nat) (s : List B256) :
    (finalState base a b g s).world = base.world := rfl

theorem final_meta (base : Devm) (a b : UInt8) (g : Nat) (s : List B256) :
    (finalState base a b g s).meta = base.meta := rfl

/-- The premises are satisfiable: exactly nine gas and an empty stack. -/
theorem concrete (env : Sevm) (base : Devm) (a b : UInt8) :
    exec ⟨0, sevm env a b, initial base 9 []⟩ = .ok (finalState base a b 9 []) ∧
      (finalState base a b 9 []).gasLeft = 0 :=
  ⟨interpreter env base a b 9 [] (by decide) (by decide), final_gas base a b 9 []⟩

/-! ### Negative checks

Each block below must fail to elaborate. `#guard_msgs` turns the expected
error into a pass and any other outcome, including success, into a build error. -/

-- Eight gas is one short of the three static charges: the gas premise is rejected.
/--
error: Tactic `decide` proved that the proposition
  9 ≤ 8
is false
-/
#guard_msgs in
example (env : Sevm) (base : Devm) (a b : UInt8) :
    exec ⟨0, sevm env a b, initial base 8 []⟩ = .ok (finalState base a b 8 []) :=
  interpreter env base a b 8 [] (by decide) (by decide)

-- `DIV` is not a member of the arithmetic family, so the `ADD` rule cannot
-- describe its step.
/--
error: Type mismatch
  SymbolicArith.step_success evm SymbolicArith.Op.add x y rest stack gas room
has type
  Ninst.step evm (Ninst.reg SymbolicArith.Op.add.rinst) =
    Step.cont (evm.pc + 1) (SymbolicArith.post SymbolicArith.Op.add x y rest evm.dyna)
but is expected to have type
  Ninst.step evm (Ninst.reg Rinst.div) =
    Step.cont (evm.pc + 1) (SymbolicArith.post SymbolicArith.Op.add x y rest evm.dyna)
-/
#guard_msgs in
example (evm : Evm) (x y : B256) (rest : List B256)
    (stack : evm.dyna.stack = x :: y :: rest)
    (gas : SymbolicArith.Op.cost .add ≤ evm.dyna.gasLeft) (room : rest.length < 1024) :
    Ninst.step evm (.reg .div) =
      .cont (evm.pc + 1) (SymbolicArith.post .add x y rest evm.dyna) :=
  SymbolicArith.step_success evm .add x y rest stack gas room

end Examples.Arithmetic
