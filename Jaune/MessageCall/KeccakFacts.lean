import Batteries.Tactic.OpenPrivate
import Jaune.MessageCall.Plain

/-! The KECCAK256 row computes the reference digest (goal `jaune-shape-and-names-v1`, G2b, unit
jsn-u97).

The Memory row's `digest` effect absorbs the memory backing array in place
(`keccakReadRun`). These facts tie it to `Bytes.keccak` of the slice `Memory.read` returns,
with no fork, stack, gas, well-formedness or success premise: the checked counterpart of the
original-run `Jaune.PlainOp.runCore_keccak256_eq_reference`. -/

open private keccakReadRun keccakReadRun_data_eq from Jaune.Machine

namespace Jaune

open Jaune

/-- The in-place absorber over a memory's backing array is `Bytes.keccak` of the bytes
`Memory.read` returns, for every start and length (out-of-range bytes read as zero). -/
theorem Memory.keccakReadRun_eq_keccak_read (memory : Memory) (index size : Nat) :
    keccakReadRun (fun j => memory.data.getD j 0) index size 0 (.replicate 25 0) =
      (memory.read index size).1.keccak := by
  unfold Bytes.keccak Memory.read
  exact keccakReadRun_data_eq memory.data index size 0 (.replicate 25 0)

/-- The `digest` effect extends memory over the range and pushes `Bytes.keccak` of the bytes
read. -/
theorem MemoryEffect.apply_digest (calldata : Bytes) (code : ByteArray) (returnData : Bytes)
    (index size : U256) (memory : Memory) :
    MemoryEffect.digest.apply calldata code returnData (index, size) memory =
      some ((memory.read index.toNat size.toNat).2,
        some (memory.read index.toNat size.toNat).1.keccak) := by
  simp only [MemoryEffect.apply, Memory.keccakReadRun_eq_keccak_read]
  rfl

/-- Unconditional KECCAK256 compatibility over the checked frame: the instruction table's
KECCAK256 row computes the whole reference bind chain (both pops, word and extension gas, the
charge, the memory read with its extension, the digest and the push), with no fork, stack, gas,
well-formedness or success premise. The checked counterpart of the original-run
`Jaune.PlainOp.runCore_keccak256_eq_reference`; kept out of the simp set. -/
theorem PlainOp.runCore_keccak256_eq_reference (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    PlainOp.runCore pc ctx s .keccak256 = s.liftMachine (fun m => do
      let ⟨memoryStartIndex, m⟩ ← m.popToNat
      let ⟨size, m⟩ ← m.popToNat
      let words := ceilDiv size 32
      let wordGasCost := Gas.keccak256Word * words
      let extendMemoryCost := m.memoryExpansionCost [⟨memoryStartIndex, size⟩]
      let m ← m.chargeGas (Gas.keccak256 + wordGasCost + extendMemoryCost)
      let ⟨arg, m⟩ := m.readMemory memoryStartIndex size
      m.push arg.keccak) := by
  show s.liftMachine (MemoryRow.step _ ctx.block.rules.opcodes ctx) = _
  congr 1
  funext m
  simp only [MemoryRow.step, Machine.popWords, Machine.popToNat, MemoryEffect.ranges]
  cases h1 : m.pop with
  | error e => rfl
  | ok p1 =>
    obtain ⟨x, m1⟩ := p1
    cases h2 : m1.pop with
    | error e => simp [bind, Except.bind, h2]
    | ok p2 =>
      obtain ⟨y, m2⟩ := p2
      simp only [bind, Except.bind, h2, pure, Except.pure, ↓reduceIte]
      split
      · rfl
      · simp only [MemoryEffect.apply_digest, Machine.readMemory]

end Jaune
