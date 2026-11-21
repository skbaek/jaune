import Jaune.PrecompileInput
import Jaune.GasFacts

/-!
# Output lengths of the precompiles over `PrecompileInput` (goal `jaune-shape-and-names-v1`, G2b, F1b)

The output-length facts of `Jaune.MemoryAccounting` (`executeModexp_ok_output_length_lt_two_pow_160`,
`executeId_ok_output_and_cost`, `precompileRun_ok_output_length_lt_two_pow_160` and their private
chain), restated over the precompile input. The MODEXP pricing bounds
(`pragueModexpGasCost_large_modulus`, `eip198ModexpGasCost_large_modulus`) mention no machine and
are reused as they are.
-/

namespace Jaune

open Jaune

namespace Precompile

/-- A successful native MODEXP reply has at most the modulus-header width.
This uses the selected precompile execution, including its gas and length
guards; it does not assume a caller-supplied output budget. -/
theorem modexp_ok_output_length_le {input : PrecompileInput} {cost : Nat} {output : Bytes}
    (h : modexp input = .ok cost output) :
    output.length ≤ Bytes.sliceToNat input.calldata 64 32 := by
  unfold modexp at h
  dsimp only at h
  split at h
  · cases h
  · unfold chargeGas at h
    split at h
    · split at h
      · cases h
        exact Nat.zero_le _
      · split at h
        · cases h
          simp only [List.length_replicate]
          exact Nat.le_refl _
        · cases h
          simp only [Bytes.pack, List.length_takeRightD]
          exact Nat.le_refl _
    · cases h

/-- A successful MODEXP executes the selected fork's price and passes the
actual gas guard, including when its output is empty. -/
theorem modexp_ok_selected_cost {input : PrecompileInput} {cost : Nat} {output : Bytes}
    (h : modexp input = .ok cost output) :
    cost = modexpGasCost input.rules.modexpComplexity
      input.rules.modexp
      (Bytes.sliceToNat input.calldata 0 32)
      (Bytes.sliceToNat input.calldata 64 32)
      (Bytes.sliceToNat input.calldata 32 32)
      (Bytes.sliceToNat input.calldata
        (96 + Bytes.sliceToNat input.calldata 0 32)
        (min 32 (Bytes.sliceToNat input.calldata 32 32))) ∧
      cost ≤ input.gasLeft := by
  unfold modexp at h
  dsimp only at h
  split at h
  · cases h
  · unfold chargeGas at h
    split at h
    · split at h
      · cases h
        exact ⟨rfl, ‹_›⟩
      · split at h
        · cases h
          exact ⟨rfl, ‹_›⟩
        · cases h
          exact ⟨rfl, ‹_›⟩
    · cases h

private theorem modexp_ok_lengthsInBounds {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : modexp input = .ok cost output) :
    modexpLengthsInBounds input.rules.modexp
      (Bytes.sliceToNat input.calldata 0 32)
      (Bytes.sliceToNat input.calldata 32 32)
      (Bytes.sliceToNat input.calldata 64 32) = true := by
  unfold modexp at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hguard
    exact not_not.mp hguard

private theorem osaka_modexp_modulus_le (baseLength expLength modulusLength : Nat)
    (h : modexpLengthsInBounds osakaModexpRules
      baseLength expLength modulusLength = true) :
    modulusLength ≤ 1024 := by
  simp only [modexpLengthsInBounds, osakaModexpRules] at h
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_eq] at h
  exact h.2

private theorem initialized_modexp_rules (input : PrecompileInput) :
    (input.rules.modexpComplexity = .eip2565 ∧
      input.rules.modexp = pragueModexpRules) ∨
    (input.rules.modexpComplexity = .eip2565 ∧
      input.rules.modexp = osakaModexpRules) ∨
    (input.rules.modexpComplexity = .eip198 ∧
      input.rules.modexp = eip198ModexpRules) := by
  change ((Fork.ruleSet input.fork).modexpComplexity = .eip2565 ∧
      (Fork.ruleSet input.fork).modexp = pragueModexpRules) ∨
    ((Fork.ruleSet input.fork).modexpComplexity = .eip2565 ∧
      (Fork.ruleSet input.fork).modexp = osakaModexpRules) ∨
    ((Fork.ruleSet input.fork).modexpComplexity = .eip198 ∧
      (Fork.ruleSet input.fork).modexp = eip198ModexpRules)
  cases input.fork <;>
    first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨rfl, rfl⟩) |
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Under a word-sized gas grant, a successful initialized MODEXP reply has
the strict size needed by CALL return-data accounting on every selected fork. -/
theorem modexp_ok_output_length_lt_two_pow_160
    {input : PrecompileInput} {cost : Nat} {output : Bytes}
    (h : modexp input = .ok cost output)
    (hgas : input.gasLeft < 2 ^ 256 + Gas.callStipend) :
    output.length < 2 ^ 160 := by
  have hlen := modexp_ok_output_length_le h
  have hprice := modexp_ok_selected_cost h
  rcases initialized_modexp_rules input with ⟨hc, hm⟩ | ⟨hc, hm⟩ | ⟨hc, hm⟩
  · rw [hc, hm] at hprice
    by_contra hnot
    have hmod : 2 ^ 160 ≤ Bytes.sliceToNat input.calldata 64 32 := by omega
    have hlarge := pragueModexpGasCost_large_modulus
      (baseLength := Bytes.sliceToNat input.calldata 0 32)
      (modulusLength := Bytes.sliceToNat input.calldata 64 32)
      (expLength := Bytes.sliceToNat input.calldata 32 32)
      (expHead := Bytes.sliceToNat input.calldata
        (96 + Bytes.sliceToNat input.calldata 0 32)
        (min 32 (Bytes.sliceToNat input.calldata 32 32))) hmod
    omega
  · have hbound := osaka_modexp_modulus_le
      (Bytes.sliceToNat input.calldata 0 32)
      (Bytes.sliceToNat input.calldata 32 32)
      (Bytes.sliceToNat input.calldata 64 32) (by
        rw [← hm]
        exact modexp_ok_lengthsInBounds h)
    have hsmall : 1024 < (2 : Nat) ^ 160 := by decide
    omega
  · rw [hc, hm] at hprice
    by_contra hnot
    have hmod : 2 ^ 160 ≤ Bytes.sliceToNat input.calldata 64 32 := by omega
    have hlarge := eip198ModexpGasCost_large_modulus
      (baseLength := Bytes.sliceToNat input.calldata 0 32)
      (modulusLength := Bytes.sliceToNat input.calldata 64 32)
      (expLength := Bytes.sliceToNat input.calldata 32 32)
      (expHead := Bytes.sliceToNat input.calldata
        (96 + Bytes.sliceToNat input.calldata 0 32)
        (min 32 (Bytes.sliceToNat input.calldata 32 32))) hmod
    omega

/-- An initialized identity reply is exactly the paid input. -/
theorem identity_ok_output_and_cost {input : PrecompileInput} {cost : Nat} {output : Bytes}
    (h : identity input = .ok cost output) :
    output = input.calldata ∧
      cost = 15 + 3 * ceilDiv input.calldata.length 32 ∧
      cost ≤ input.gasLeft := by
  unfold identity chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, rfl, ‹_›⟩
  · cases h

private theorem altBn128G1_toBytes_length (p : AltBn128G1) : (AltBn128G1.toBytes p).length = 64 := by
  simp only [AltBn128G1.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem bls12G1_toBytes_length (p : Bls12G1) : (Bls12G1.toBytes p).length = 128 := by
  simp only [Bls12G1.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem bls12Fp2_toBytes_length (x : Bls12Fp2) : x.toBytes.length = 128 := by
  simp only [Bls12Fp2.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem bls12G2_toBytes_length (p : Bls12G2) : (Bls12G2.toBytes p).length = 256 := by
  simp only [Bls12G2.toBytes, List.length_append, bls12Fp2_toBytes_length]

private theorem ecAdd_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : ecAdd input = .ok cost output) :
    output.length = 64 := by
  unfold ecAdd chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact altBn128G1_toBytes_length _

private theorem ecMul_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : ecMul input = .ok cost output) :
    output.length = 64 := by
  unfold ecMul chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact altBn128G1_toBytes_length _

private theorem bls12G1Add_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : bls12G1Add input = .ok cost output) :
    output.length = 128 := by
  unfold bls12G1Add chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bls12G1_toBytes_length _

private theorem bls12G1Msm_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : bls12G1Msm input = .ok cost output) :
    output.length = 128 := by
  unfold bls12G1Msm chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bls12G1_toBytes_length _

private theorem bls12G2Add_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : bls12G2Add input = .ok cost output) :
    output.length = 256 := by
  unfold bls12G2Add chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bls12G2_toBytes_length _

private theorem bls12G2Msm_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : bls12G2Msm input = .ok cost output) :
    output.length = 256 := by
  unfold bls12G2Msm chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bls12G2_toBytes_length _

private theorem bls12MapFpToG1_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : bls12MapFpToG1 input = .ok cost output) :
    output.length = 128 := by
  unfold bls12MapFpToG1 chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bls12G1_toBytes_length _

private theorem bls12MapFp2ToG2_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : bls12MapFp2ToG2 input = .ok cost output) :
    output.length = 256 := by
  unfold bls12MapFp2ToG2 chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bls12G2_toBytes_length _

private theorem sha256_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : sha256 input = .ok cost output) :
    output.length = 32 := by
  unfold sha256 chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact U256.length_toBytes _
  · cases h

private theorem ripemd160_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : ripemd160 input = .ok cost output) :
    output.length = 32 := by
  unfold ripemd160 chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact U256.length_toBytes _
  · cases h

private theorem p256verify_ok_output_length_le {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : p256verify input = .ok cost output) :
    output.length ≤ 32 := by
  unfold p256verify chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_nil, U256.length_toBytes]
  all_goals omega

private theorem ecrecover_ok_output_length_le {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : ecrecover input = .ok cost output) :
    output.length ≤ 32 := by
  unfold ecrecover chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_nil, U256.length_toBytes]
  all_goals omega

private theorem pointEvaluation_ok_output_length {input : PrecompileInput} {cost : Nat}
    {output : Bytes} (h : pointEvaluation input = .ok cost output) :
    output.length = 64 := by
  unfold pointEvaluation chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_append, U256.length_toBytes]

private theorem executePairingCheckInner_ok_output_length {data : Bytes}
    {charged reported : Nat} {output : Bytes}
    (h : executePairingCheckInner data charged = .ok (reported, output)) :
    output.length = 32 := by
  unfold executePairingCheckInner at h
  dsimp only at h
  repeat split at h
  all_goals try cases h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    all_goals cases h
    all_goals simp only [U256.length_toBytes]

private theorem executeBls12PairingInner_ok_output_length {data : Bytes}
    {charged reported : Nat} {output : Bytes}
    (h : executeBls12PairingInner data charged = .ok (reported, output)) :
    output.length = 32 := by
  unfold executeBls12PairingInner at h
  dsimp only at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    all_goals cases h
    all_goals simp only [U256.length_toBytes]

private theorem ecPairingCheck_ok_output_length {input : PrecompileInput}
    {cost : Nat} {output : Bytes}
    (h : ecPairingCheck input = .ok cost output) : output.length = 32 := by
  unfold ecPairingCheck chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals try cases h
  all_goals exact executePairingCheckInner_ok_output_length ‹_›

private theorem bls12PairingCheck_ok_output_length {input : PrecompileInput}
    {cost : Nat} {output : Bytes}
    (h : bls12PairingCheck input = .ok cost output) : output.length = 32 := by
  unfold bls12PairingCheck chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact executeBls12PairingInner_ok_output_length ‹_›

private theorem eight_byte_chunks_length (xs : List UInt64) :
    (List.flatten (xs.map fun n => (Jaune.UInt64.toBytes n).reverse.takeD 8 (0x00 : UInt8))).length =
      xs.length * 8 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      List.takeD_length, ih, List.length_cons]
    omega

private theorem _root_.Jaune.Blake2.compress_ok_output_length {rounds : Nat} {h m : List UInt64}
    {t0 t1 : UInt64} {f : Bool} {output : Bytes}
    (hok : Blake2.compress rounds h m t0 t1 f = some output) : output.length = 64 := by
  unfold Blake2.compress at hok
  split at hok
  · split at hok
    · simp only [Option.some.injEq] at hok
      subst output
      simp only [eight_byte_chunks_length, Vector.length_toList]
    · cases hok
  · cases hok

private theorem blake2f_ok_output_length {input : PrecompileInput}
    {cost : Nat} {output : Bytes}
    (h : blake2f input = .ok cost output) : output.length = 64 := by
  unfold blake2f chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact Blake2.compress_ok_output_length ‹_›

/-- Every successful initialized native precompile has a fixed-width reply
unless it is identity or MODEXP; those two use their paid input and gas. -/
theorem run_ok_output_length_lt_two_pow_160
    {input : PrecompileInput} {adr : Address} {cost : Nat} {output : Bytes}
    (h : run input adr = .ok cost output)
    (hdata : input.calldata.length < 2 ^ 160)
    (hgas : input.gasLeft < 2 ^ 256 + Gas.callStipend) :
    output.length < 2 ^ 160 := by
  unfold run at h
  split at h
  all_goals first
    | have := ecrecover_ok_output_length_le h; omega
    | have := sha256_ok_output_length h; omega
    | have := ripemd160_ok_output_length h; omega
    | have hout := (identity_ok_output_and_cost h).1; rw [hout]; exact hdata
    | exact modexp_ok_output_length_lt_two_pow_160 h hgas
    | have := ecAdd_ok_output_length h; omega
    | have := ecMul_ok_output_length h; omega
    | have := ecPairingCheck_ok_output_length h; omega
    | have := blake2f_ok_output_length h; omega
    | have := pointEvaluation_ok_output_length h; omega
    | have := bls12G1Add_ok_output_length h; omega
    | have := bls12G1Msm_ok_output_length h; omega
    | have := bls12G2Add_ok_output_length h; omega
    | have := bls12G2Msm_ok_output_length h; omega
    | have := bls12PairingCheck_ok_output_length h; omega
    | have := bls12MapFpToG1_ok_output_length h; omega
    | have := bls12MapFp2ToG2_ok_output_length h; omega
    | have := p256verify_ok_output_length_le h; omega
    | cases h


end Precompile

end Jaune
