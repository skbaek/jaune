import Jaune.Precompiles

/-!
# Gas schedule facts (goal `jaune-shape-and-names-v1`, G2b N4-0)

Monotonicity of the memory cost, the message-call gas bounds, the 63/64 rule and the modexp
cost bounds. Extracted from `Jaune.MemoryAccounting` and `Jaune.Sufficiency`; the
message-call lemmas take the `calculateMessageCallGas_*` names.
-/
