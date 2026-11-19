import Jaune.PrecompileInput

/-!
# Bridge: the `Evm` precompile wrappers and the precompile input (goal `jaune-shape-and-names-v1`, G2b, F1b)

The old side is `precompileRun` and its eighteen `execute*` wrappers over `Evm`
(`Jaune.Precompiles`, unedited); the new side is `Precompile.run` over `PrecompileInput`. The input
projected from an `Evm` is its input bytes, its gas left and its block's fork. Each wrapper agrees
with its counterpart, and the dispatch agrees, for every `Evm` and every address, hence every fork.
-/

namespace Jaune

open Jaune

/-- The precompile input an `Evm` presents: its input bytes, its gas left, its block's fork. -/
def PrecompileInput.ofEvm (evm : Evm) : PrecompileInput :=
  { calldata := evm.sta.data, gasLeft := evm.dyna.gasLeft, fork := evm.sta.benvStat.fork }

@[simp] theorem PrecompileInput.ofEvm_calldata (evm : Evm) :
    (PrecompileInput.ofEvm evm).calldata = evm.sta.data := rfl

@[simp] theorem PrecompileInput.ofEvm_gasLeft (evm : Evm) :
    (PrecompileInput.ofEvm evm).gasLeft = evm.dyna.gasLeft := rfl

@[simp] theorem PrecompileInput.ofEvm_rules (evm : Evm) :
    (PrecompileInput.ofEvm evm).rules = evm.sta.benvStat.rules := rfl

namespace Precompile

theorem chargeGas_ofEvm (cost : Nat) (evm : Evm) (pr : Unit → PrecompileResult) :
    PrecompileResult.chargeGas cost evm pr = chargeGas cost (.ofEvm evm) pr := rfl

theorem ecrecover_ofEvm (evm : Evm) : executeEcrecover evm = ecrecover (.ofEvm evm) := by
  delta executeEcrecover ecrecover PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem sha256_ofEvm (evm : Evm) : executeSha256 evm = sha256 (.ofEvm evm) := by
  delta executeSha256 sha256 PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem ripemd160_ofEvm (evm : Evm) : executeRipemd160 evm = ripemd160 (.ofEvm evm) := by
  delta executeRipemd160 ripemd160 PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem identity_ofEvm (evm : Evm) : executeId evm = identity (.ofEvm evm) := by
  delta executeId identity PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem modexp_ofEvm (evm : Evm) : executeModexp evm = modexp (.ofEvm evm) := by
  delta executeModexp modexp PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem ecAdd_ofEvm (evm : Evm) : executeEcadd evm = ecAdd (.ofEvm evm) := by
  delta executeEcadd ecAdd PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem ecMul_ofEvm (evm : Evm) : executeEcmul evm = ecMul (.ofEvm evm) := by
  delta executeEcmul ecMul PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem ecPairing_ofEvm (evm : Evm) : executePairingCheck evm = ecPairing (.ofEvm evm) := by
  delta executePairingCheck ecPairing PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem blake2f_ofEvm (evm : Evm) : executeBlake2F evm = blake2f (.ofEvm evm) := by
  delta executeBlake2F blake2f PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem pointEvaluation_ofEvm (evm : Evm) : executePointEval evm = pointEvaluation (.ofEvm evm) := by
  delta executePointEval pointEvaluation PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12G1Add_ofEvm (evm : Evm) : executeBls12G1Add evm = bls12G1Add (.ofEvm evm) := by
  delta executeBls12G1Add bls12G1Add PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12G1Msm_ofEvm (evm : Evm) : executeBls12G1Msm evm = bls12G1Msm (.ofEvm evm) := by
  delta executeBls12G1Msm bls12G1Msm PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12G2Add_ofEvm (evm : Evm) : executeBls12G2Add evm = bls12G2Add (.ofEvm evm) := by
  delta executeBls12G2Add bls12G2Add PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12G2Msm_ofEvm (evm : Evm) : executeBls12G2Msm evm = bls12G2Msm (.ofEvm evm) := by
  delta executeBls12G2Msm bls12G2Msm PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12PairingCheck_ofEvm (evm : Evm) : executeBls12Pairing evm = bls12PairingCheck (.ofEvm evm) := by
  delta executeBls12Pairing bls12PairingCheck PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12MapFpToG1_ofEvm (evm : Evm) : executeBls12MapFpToG1 evm = bls12MapFpToG1 (.ofEvm evm) := by
  delta executeBls12MapFpToG1 bls12MapFpToG1 PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem bls12MapFp2ToG2_ofEvm (evm : Evm) : executeBls12MapFp2ToG2 evm = bls12MapFp2ToG2 (.ofEvm evm) := by
  delta executeBls12MapFp2ToG2 bls12MapFp2ToG2 PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

theorem p256Verify_ofEvm (evm : Evm) : executeP256Verify evm = p256Verify (.ofEvm evm) := by
  delta executeP256Verify p256Verify PrecompileResult.chargeGas chargeGas PrecompileInput.ofEvm
  rfl

/-- **The precompile bridge.** The `Evm` dispatch equals the input dispatch on the input projected
from the `Evm`, for every `Evm` and every address. -/
theorem run_ofEvm (evm : Evm) (address : Address) :
    precompileRun evm address = run (.ofEvm evm) address := by
  unfold precompileRun run
  split <;> first
    | rfl
    | (split <;> first | rfl | contradiction | (exfalso; simp_all; done))

end Precompile

end Jaune
