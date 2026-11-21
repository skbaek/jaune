import Jaune.Precompiles

/-!
# Gas schedule facts (goal `jaune-shape-and-names-v1`, G2b N4-0)

Monotonicity of the memory cost, the message-call gas bounds, the 63/64 rule and the modexp
cost bounds. Extracted from `Jaune.MemoryAccounting` and `Jaune.Sufficiency`; the
message-call lemmas take the `calculateMessageCallGas_*` names.
-/

section
namespace Jaune
theorem MessageCall.gasCostAndChildGas_child_at_most_requested_of_zero_value (gas gasLeft memoryCost extraGas cs : Nat) :
    (MessageCall.gasCostAndChildGas 0 gas gasLeft memoryCost extraGas cs).2 ≤ gas := by
  simp only [MessageCall.gasCostAndChildGas]
  split
  · exact Nat.le_refl gas
  · exact Nat.min_le_left _ _
end Jaune
end

section
namespace Jaune
/-- The CALL stipend adds at most its fixed amount to a word-sized requested
grant, including the underfunded branch of the gas calculator. -/
theorem MessageCall.gasCostAndChildGas_child_below_word_limit_plus_stipend (value gas : U256)
    (gasLeft memoryCost extraGas : Nat) :
    (MessageCall.gasCostAndChildGas value.toNat gas.toNat gasLeft memoryCost extraGas
      Gas.callStipend).2 < 2 ^ 256 + Gas.callStipend := by
  have hg := U256.toNat_lt gas
  unfold MessageCall.gasCostAndChildGas
  by_cases hv : value.toNat = 0
  · simp only [hv, ite_true, Nat.add_zero]
    split
    · omega
    · have hm := Nat.min_le_left gas.toNat
        (except64th (gasLeft - memoryCost - extraGas))
      omega
  · simp only [hv, ite_false]
    split
    · omega
    · have hm := Nat.min_le_left gas.toNat
        (except64th (gasLeft - memoryCost - extraGas))
      omega
end Jaune
end

section
namespace Jaune
private theorem ceilDiv32_le {a b : Nat} (h : a ≤ b) :
    ceilDiv a 32 ≤ ceilDiv b 32 := by
  simp only [ceilDiv]
  split <;> split <;> omega
end Jaune
end

section
namespace Jaune
theorem calculateMemoryGasCost_mono {a b : Nat} (h : a ≤ b) :
    calculateMemoryGasCost a ≤ calculateMemoryGasCost b := by
  have hw := ceilDiv32_le h
  have hq := Nat.div_le_div_right (c := 512) (Nat.pow_le_pow_left hw 2)
  simp only [calculateMemoryGasCost, Gas.memory]
  omega
end Jaune
end

section
namespace Jaune
theorem MessageCall.gasCostAndChildGas_cost_of_zero_value (gas gasLeft memoryCost extraGas cs : Nat) :
    (MessageCall.gasCostAndChildGas 0 gas gasLeft memoryCost extraGas cs).1 =
      (MessageCall.gasCostAndChildGas 0 gas gasLeft memoryCost extraGas cs).2 + extraGas := by
  simp only [MessageCall.gasCostAndChildGas]
  split <;> rfl
end Jaune
end

section
namespace Jaune
private theorem ceilDiv8_ge_pow157_of_ge_pow160 {n : Nat}
    (hn : 2 ^ 160 ≤ n) : 2 ^ 157 ≤ ceilDiv n 8 := by
  have hceil : n ≤ 8 * ceilDiv n 8 := by
    simp only [ceilDiv]
    split <;> omega
  have hp : (2 : Nat) ^ 160 = 8 * 2 ^ 157 := by decide
  omega
end Jaune
end

section
namespace Jaune
/-- The Prague MODEXP schedule alone rejects a modulus header this large
within any 256-bit gas grant. -/
theorem pragueModexpGasCost_large_modulus
    {baseLength modulusLength expLength expHead : Nat}
    (hmod : 2 ^ 160 ≤ modulusLength) :
    2 ^ 256 + Gas.callStipend ≤ modexpGasCost .eip2565 pragueModexpRules
      baseLength modulusLength expLength expHead := by
  let words := ceilDiv (max baseLength modulusLength) 8
  have hw : 2 ^ 157 ≤ words :=
    ceilDiv8_ge_pow157_of_ge_pow160
      (Nat.le_trans hmod (Nat.le_max_right baseLength modulusLength))
  have hsq : (2 ^ 157) ^ 2 ≤ words ^ 2 := Nat.pow_le_pow_left hw 2
  have hiter : 1 ≤ modexpIterations pragueModexpRules expLength expHead := by
    unfold modexpIterations
    exact Nat.le_max_right _ _
  have hmul : words ^ 2 ≤ words ^ 2 *
      modexpIterations pragueModexpRules expLength expHead := by
    simpa only [mul_one] using Nat.mul_le_mul_left (words ^ 2) hiter
  have hbig : 3 * (2 ^ 256 + Gas.callStipend) ≤ (2 ^ 157) ^ 2 := by decide
  have hcost : 2 ^ 256 + Gas.callStipend ≤
      (words ^ 2 * modexpIterations pragueModexpRules expLength expHead) / 3 := by
    omega
  simp only [modexpGasCost, modexpComplexity, pragueModexpRules, Nat.one_mul]
  exact Nat.le_trans hcost (Nat.le_max_right _ _)
end Jaune
end

section
namespace Jaune
/-- Above 1024 bytes EIP-198 charges its third branch. -/
private theorem eip198Complexity_third
    {baseLength modulusLength : Nat}
    (h : 1024 < max baseLength modulusLength) :
    eip198Complexity baseLength modulusLength =
      (max baseLength modulusLength) ^ 2 / 16 +
        480 * (max baseLength modulusLength) - 199680 := by
  have h64 : ¬ max baseLength modulusLength ≤ 64 := by omega
  have h1024 : ¬ max baseLength modulusLength ≤ 1024 := by omega
  simp only [eip198Complexity, h64, h1024, ite_false]
end Jaune
end

section
namespace Jaune
/-- EIP-198's third branch alone prices a 2^160-byte modulus past any 256-bit
gas grant at divisor 20: `x ^ 2 / 16` at `x = 2 ^ 160` is already `2 ^ 316`. -/
private theorem eip198Complexity_third_large
    {baseLength modulusLength : Nat}
    (hmod : 2 ^ 160 ≤ modulusLength) :
    20 * (2 ^ 256 + Gas.callStipend) ≤
      eip198Complexity baseLength modulusLength := by
  have hX : 2 ^ 160 ≤ max baseLength modulusLength :=
    Nat.le_trans hmod (Nat.le_max_right baseLength modulusLength)
  have h1024 : 1024 < max baseLength modulusLength := by
    calc (1024 : Nat) < 2 ^ 160 := by decide
    _ ≤ max baseLength modulusLength := hX
  rw [eip198Complexity_third h1024]
  have h157 : (2 ^ 157) ^ 2 ≤ (2 ^ 160) ^ 2 := by decide
  have hsq : (2 ^ 157) ^ 2 ≤ (max baseLength modulusLength) ^ 2 :=
    Nat.le_trans h157 (Nat.pow_le_pow_left hX 2)
  have hdiv : (2 ^ 157) ^ 2 / 16 ≤ (max baseLength modulusLength) ^ 2 / 16 :=
    Nat.div_le_div_right hsq
  have hmul : 480 * 2 ^ 160 ≤ 480 * max baseLength modulusLength :=
    Nat.mul_le_mul_left 480 hX
  have hbig : 20 * (2 ^ 256 + Gas.callStipend) ≤
      (2 ^ 157) ^ 2 / 16 + 480 * 2 ^ 160 - 199680 := by decide
  have hle : (2 ^ 157) ^ 2 / 16 + 480 * 2 ^ 160 - 199680 ≤
      (max baseLength modulusLength) ^ 2 / 16 +
        480 * (max baseLength modulusLength) - 199680 :=
    Nat.sub_le_sub_right (Nat.add_le_add hdiv hmul) 199680
  exact Nat.le_trans hbig hle
end Jaune
end

section
namespace Jaune
/-- The EIP-198 MODEXP schedule alone rejects a modulus header this large
within any 256-bit gas grant: the divisor is 20 rather than 3, but a
2^160-byte modulus still costs far past it. -/
theorem eip198ModexpGasCost_large_modulus
    {baseLength modulusLength expLength expHead : Nat}
    (hmod : 2 ^ 160 ≤ modulusLength) :
    2 ^ 256 + Gas.callStipend ≤ modexpGasCost .eip198 eip198ModexpRules
      baseLength modulusLength expLength expHead := by
  have hiter : 1 ≤ modexpIterations eip198ModexpRules expLength expHead := by
    unfold modexpIterations
    exact Nat.le_max_right _ _
  have hbig := eip198Complexity_third_large (baseLength := baseLength) hmod
  have hmul : eip198Complexity baseLength modulusLength ≤
      eip198Complexity baseLength modulusLength *
        modexpIterations eip198ModexpRules expLength expHead := by
    simpa only [mul_one] using Nat.mul_le_mul_left _ hiter
  have hcost : 2 ^ 256 + Gas.callStipend ≤
      (eip198Complexity baseLength modulusLength *
        modexpIterations eip198ModexpRules expLength expHead) / 20 := by
    omega
  simp only [modexpGasCost, modexpComplexity, eip198ModexpRules]
  exact Nat.le_trans hcost (Nat.le_max_right _ _)
end Jaune
end

section
open Jaune
namespace Jaune
theorem access_cost_pos (x : Address) (a : AddressSet) : 0 < accessCost x a := by
  unfold accessCost Gas.warmStorageReadCost Gas.coldAccountAccessCost
  split <;> omega
end Jaune
end

section
open Jaune
namespace Jaune
theorem Gas.warmStorageReadCost_at_most_access_cost (x : Address) (a : AddressSet) :
    Gas.warmStorageReadCost ≤ accessCost x a := by
  unfold accessCost Gas.warmStorageReadCost Gas.coldAccountAccessCost
  split <;> omega
end Jaune
end

section
open Jaune
namespace Jaune
/-- Under the flat (pre-EIP-2929) schedule every family's price is positive:
the termination argument's one need of that shape, from `ForkRules.Valid`. -/
theorem ForkRules.Valid.flatAccess {r : ForkRules} (hv : r.Valid)
    {g : FlatAccessGas} (h : r.access = .flat g) : g.Valid := by
  have ha := hv.access
  rw [h] at ha
  exact ha
end Jaune
end

section
open Jaune
namespace Jaune
theorem MessageCall.gasCostAndChildGas_child_below_cost_plus_memory_of_stipend_bound
    {value gas gasLeft memoryCost extraGas cs : Nat}
    (hstip : (if value = 0 then 0 else cs) < extraGas + memoryCost) :
    (MessageCall.gasCostAndChildGas value gas gasLeft memoryCost extraGas cs).2 <
      (MessageCall.gasCostAndChildGas value gas gasLeft memoryCost extraGas cs).1 + memoryCost := by
  unfold MessageCall.gasCostAndChildGas
  split <;> split <;> simp_all <;> omega
end Jaune
end

section
open Jaune
namespace Jaune
theorem MessageCall.gasCostAndChildGas_child_of_zero_memory_and_extra_cost
    (value gas gasLeft cs : Nat) :
    (MessageCall.gasCostAndChildGas value gas gasLeft 0 0 cs).2 =
      (MessageCall.gasCostAndChildGas value gas gasLeft 0 0 cs).1 +
        (if value = 0 then 0 else cs) := by
  unfold MessageCall.gasCostAndChildGas
  split <;> split <;> simp_all
end Jaune
end

section
open Jaune
namespace Jaune
theorem except64th_le (n : Nat) : except64th n ≤ n := by
  unfold except64th
  omega
end Jaune
end

section
open Jaune
namespace Jaune
/-- Inversion for the `Option.toExcept` lifts that thread the transaction
chain: a successful lift pins the option. -/
theorem Option.toExcept_eq_ok {ξ : Type u} {υ : Type v} {x : ξ} {o : Option υ}
    {v : υ} (h : Option.toExcept x o = .ok v) : o = some v := by
  cases o with
  | none => nomatch h
  | some w => cases h; rfl
end Jaune
end
