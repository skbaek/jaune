import Lean

/-! Fidelity controls for attributes per declaration, elaboration attributes
outside the first tracked set, instance order and quoted spellings. -/

namespace FidelityElab

inductive Shape where
  | box (n : Nat)
  | dot

mutual
@[match_pattern] def boxed (n : Nat) : Shape := .box n
@[deprecated "control" (since := "2026-11-16")] def plain (n : Nat) : Shape := .box n
def other (n : Nat) : Shape := .box n
end

class Tag (α : Type) where
  tag : Nat

instance : Tag Nat := ⟨1⟩
instance : Tag Nat := ⟨2⟩

class Pick (α : Type) where
  pick : α

@[default_instance] instance : Pick Nat := ⟨1⟩
@[deprecated "control" (since := "2026-11-16")] instance : Pick Int := ⟨2⟩
instance : Pick Bool := ⟨true⟩

open Lean in
def quoted : MacroM Term := `(Shape.dot)

end FidelityElab
