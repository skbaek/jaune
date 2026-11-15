import Lean

/-!
# jsn-s6d: per-declaration elaboration and kernel cost

`s6d_time <command>` elaborates the command and logs, for each theorem it adds:

* `total_ms`: wall time of elaborating the command (elaboration plus the kernel check that
  `addDecl` performs; run with `Elab.async false` so both happen inside the measurement);
* `kernel_ms`: wall time of a second, separate kernel check of the same theorem value under a
  fresh name, in a throw-away environment;
* `heartbeats`: Lean heartbeats consumed by the command (deterministic, load-independent).
-/

open Lean Elab Command

syntax (name := s6dTime) "s6d_time " command : command

@[command_elab s6dTime] def elabS6dTime : CommandElab := fun stx => do
  let cmd := stx[1]
  let envBefore ← getEnv
  let hb0 ← IO.getNumHeartbeats
  let t0 ← IO.monoNanosNow
  elabCommand cmd
  let t1 ← IO.monoNanosNow
  let hb1 ← IO.getNumHeartbeats
  let env ← getEnv
  for (n, ci) in env.constants.map₂.toList do
    if envBefore.constants.map₂.contains n then continue
    let .thmInfo v := ci | continue
    if n.isInternal then continue
    let decl := Declaration.thmDecl { v with name := n ++ `s6dKernelRecheck }
    let k0 ← IO.monoNanosNow
    liftCoreM <| withoutModifyingEnv <| addDecl decl
    let k1 ← IO.monoNanosNow
    let ms (a b : Nat) : Float := (b - a).toFloat / 1000000.0
    logInfo m!"S6D_TIME {n} total_ms={ms t0 t1} kernel_ms={ms k0 k1} heartbeats={(hb1 - hb0) / 1000}"
