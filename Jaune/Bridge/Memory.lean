import Jaune.Memory

/-! Conversion and operation equations for well-formed legacy EVM memory. -/

namespace Jaune

def Mem.Wf (m : Mem) : Prop := m.data.size ≤ m.size

def Memory.ofMem (m : Mem) (h : m.Wf) : Memory := ⟨m.data, m.size, h⟩

def Memory.toMem (m : Memory) : Mem := ⟨m.data, m.size⟩

theorem Memory.wf_toMem (m : Memory) : m.toMem.Wf := m.wf

theorem Memory.toMem_ofMem (m : Mem) (h : m.Wf) : (Memory.ofMem m h).toMem = m := rfl

theorem Memory.ofMem_toMem (m : Memory) : Memory.ofMem m.toMem m.wf_toMem = m := rfl

theorem Memory.empty_toMem : Memory.empty.toMem = Mem.empty := rfl

theorem Memory.extend_toMem (m : Memory) (index size : Nat) :
    (m.extend index size).toMem = m.toMem.extend index size := rfl

theorem Memory.extends_toMem (m : Memory) (pairs : List (Nat × Nat)) :
    (m.extends pairs).toMem = m.toMem.extends pairs := rfl

theorem Memory.read_toMem (m : Memory) (index size : Nat) :
    Prod.map id Memory.toMem (m.read index size) = m.toMem.read index size := rfl

theorem Memory.write_toMem (m : Memory) (index : Nat) (bytes : Bytes) :
    (m.write index bytes).toMem = m.toMem.write index bytes := by
  cases bytes with
  | nil => rfl
  | cons b bs =>
    by_cases logical : index + (b :: bs).length ≤ m.size
    · by_cases backed : index + (b :: bs).length ≤ m.data.size <;>
        simp only [Memory.write, Memory.toMem, Mem.write, logical, backed,
          ite_true, ite_false, dite_true]
    · simp only [Memory.write, Memory.toMem, Mem.write, logical, ite_false, dite_false]

theorem Mem.wf_empty : Mem.empty.Wf := Memory.empty.wf_toMem

theorem Mem.Wf.write {m : Mem} (h : m.Wf) (index : Nat) (bytes : Bytes) :
    (m.write index bytes).Wf := by
  change ((Memory.ofMem m h).toMem.write index bytes).Wf
  rw [← Memory.write_toMem]
  exact Memory.wf_toMem _

theorem Mem.Wf.extend {m : Mem} (h : m.Wf) (index size : Nat) :
    (m.extend index size).Wf :=
  ((Memory.ofMem m h).extend index size).wf_toMem

theorem Mem.Wf.extends {m : Mem} (h : m.Wf) (pairs : List (Nat × Nat)) :
    (m.extends pairs).Wf :=
  ((Memory.ofMem m h).extends pairs).wf_toMem

theorem Mem.Wf.read {m : Mem} (h : m.Wf) (index size : Nat) :
    (m.read index size).2.Wf := h.extend index size

end Jaune
