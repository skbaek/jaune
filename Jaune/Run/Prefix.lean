import Jaune.Transaction.Parts

/-!
# A block body's prefix, its operations and the block checks (goal `jaune-shape-and-names-v1`, G2b N4-0)

`Body.Prefix` (what a block body has produced so far), `BodyOp` and the transaction operations of
a body, `creditAll`, and the block's commitments and header checks. Extracted unchanged from the
`Devm`-era `Jaune.Run` modules.
-/
