import Jaune.Machine

namespace Jaune

private theorem le_ceilDiv32_mul (n : Nat) : n ≤ 32 * ceilDiv n 32 := by
  simp only [ceilDiv]
  split <;> omega

theorem memExtSize_ge (current index size : Nat) :
    current ≤ memExtSize current index size := by
  simp only [memExtSize]
  split
  · exact Nat.le_refl _
  · have h := le_ceilDiv32_mul current
    have hm := Nat.le_max_left (ceilDiv current 32) (ceilDiv (index + size) 32)
    omega

theorem memExtsSize_ge (current : Nat) (pairs : List (Nat × Nat)) :
    current ≤ memExtsSize current pairs := by
  induction pairs generalizing current with
  | nil => exact Nat.le_refl _
  | cons pair pairs ih =>
    exact Nat.le_trans (memExtSize_ge current pair.1 pair.2) (ih _)

/-- A nonempty access is covered by the actual rounded expansion. -/
theorem memExtSize_access_le (current index size : Nat) (hsize : size ≠ 0) :
    index + size ≤ memExtSize current index size := by
  simp only [memExtSize, ite_eq_right hsize]
  have h := le_ceilDiv32_mul (index + size)
  have hm := Nat.le_max_right (ceilDiv current 32) (ceilDiv (index + size) 32)
  omega

/-- The number of bytes backed by the array fits in the logical memory size.
Extending memory can reserve zero-filled space without materialising them. -/
structure Memory where
  data : Array UInt8
  size : Nat
  wf : data.size ≤ size

def Memory.empty : Memory := ⟨#[], 0, Nat.le_refl 0⟩

theorem Array.size_writeD {α : Type u} (xs : Array α) (index : Nat) (values : List α) :
    (Array.writeD xs index values).size = xs.size := by
  induction values generalizing xs index with
  | nil => rfl
  | cons x xs' ih =>
    rw [Array.writeD]
    split
    · rw [ih, Array.size_set]
    · rfl

def Memory.extend (m : Memory) (index size : Nat) : Memory :=
  ⟨m.data, memExtSize m.size index size, m.wf.trans (memExtSize_ge ..)⟩

def Memory.extends (m : Memory) (pairs : List (Nat × Nat)) : Memory :=
  ⟨m.data, memExtsSize m.size pairs, m.wf.trans (memExtsSize_ge ..)⟩

def Memory.read (m : Memory) (index size : Nat) : Bytes × Memory :=
  (Array.sliceD m.data index size 0, m.extend index size)

def Memory.write (m : Memory) (index : Nat) : Bytes → Memory
  | [] => m
  | bytes@(_ :: _) =>
    if fits : index + bytes.length ≤ m.size then
      if index + bytes.length ≤ m.data.size then
        ⟨Array.writeD m.data index bytes, m.size, by rw [Array.size_writeD]; exact m.wf⟩
      else
        let blank : Array UInt8 := Array.replicate (index + bytes.length) 0
        ⟨Array.writeD (Array.copyD m.data blank) index bytes, m.size, by
          simpa only [Array.size_writeD, Array.size_copyD, blank, Array.size_replicate] using fits⟩
    else
      let newSize := ceil32 (index + bytes.length)
      let blank : Array UInt8 := Array.replicate newSize 0
      ⟨Array.writeD (Array.copyD m.data blank) index bytes, newSize, by
        simp only [Array.size_writeD, Array.size_copyD, blank, Array.size_replicate, Nat.le_refl]⟩

end Jaune
