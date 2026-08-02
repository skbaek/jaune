-- BLSGuards.lean : the bilinearity sanity check on `blsPairing`, held outside
-- the `Jaune` library root purely for what it costs to elaborate.
--
-- Like `FixtureException` and `ChainStore`, this module is imported by
-- `Main.lean` only and deliberately not from the `Jaune` library root. The
-- reason differs from theirs: those are fixture-runner infrastructure that no
-- proof client should depend on, whereas this is a genuine correctness check on
-- the pairing. It sits here because of its price, not its nature.
--
-- The guard evaluates four full BLS12-381 pairings during elaboration. Measured
-- 2026-08-01: 9.6s of `Jaune/BLS.lean`'s 11.8s — 83% of the slowest module in
-- the project, against ~0.1s for that file's twenty other guards. `BLS.lean`
-- sits on the longest chain in the import DAG
-- (Basic → Types → EC → BLS → Machine → … → Main), so that cost was serialised
-- ahead of every dependent module rather than overlapping it. Here it overlaps,
-- and the whole-library rebuild after touching a root module fell from ~38.8s
-- to ~29.9s. Note that total work rose ~1.7s in the process: evaluating
-- definitions imported from an olean is dearer than evaluating ones just
-- elaborated in-file. This is a critical-path win, not a work reduction, and
-- summing per-module elaboration times would wrongly predict a regression.
--
-- Coverage is unchanged. `lean_exe «jaune»` is a default target and `Main.lean`
-- imports this module, so the guard still elaborates on every `lake build`.
-- What changed is when a failure surfaces: at the next build, rather than as a
-- live diagnostic while editing `BLS.lean`.
--
-- Do not treat this module as the home for guards in general. Guard *count*
-- does not predict elaboration cost — content does, and every other guard in
-- the library is cheap. A guard belongs beside the code it checks unless it is
-- expensive for the reason this one is: interpreted cryptography, on a module
-- with dependents.

import Jaune.BLS

namespace Jaune

-- Bilinearity sanity checks: e(2*G1gen, G2gen) = e(G1gen, 2*G2gen)
-- = e(G1gen + G1gen, G2gen) = e(G1gen, G2gen)^2 ≠ 1.  Each pairing is
-- bound once; the squared form and the final inequality also rule out
-- a degenerate implementation mapping everything to 1.
#guard
  let eg := blsPairing blsG2Generator blsG1Generator
  let e2g := blsPairing blsG2Generator (blsG1Generator.mulBy 2)
  let eg2 := blsPairing (blsG2Generator.mulBy 2) blsG1Generator
  let egg := blsPairing blsG2Generator (blsG1Generator + blsG1Generator)
  e2g = eg2 ∧ e2g = egg ∧ e2g = eg.map (fun f => f * f) ∧ eg ≠ some 1

end Jaune
