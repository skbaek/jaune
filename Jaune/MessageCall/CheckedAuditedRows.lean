import Jaune.MessageCall.CheckedChronology
import Jaune.MessageCall.CheckedSpawnFacts

/-!
# Checked counterparts of audited rows 29-42 (goal `jaune-shape-and-names-v1`, G2b, F1f)

The destination axiom audit's settlement rows (29-37) and block-context rows (38-42), restated with
the same names under `Jaune.Checked` and the same conclusions over the checked interpreter. Rows
30-33, 36 and 37 are stated over `Checked.Exec`; their `Checked.Frame.Run` forms are the `callRan`
rows of `FrameRun/CheckedSettlementViews.lean`. Rows 29 and 35 do not mention `Exec` and live in
`FrameRun/CheckedBasic.lean`. Row 38 (`benvAfterTransfer_stat`) has no counterpart: a checked
transfer returns a `World`, so the block record cannot change by its type. Its proposed replacement
is `Frame.enter_run_context`; the spawn-context rows (`genericCall.step_spawn_context`,
`genericCreate.step_spawn_context`, `MessageOp.step_spawn_context`) are the proposed replacements of
rows 39-42. `Frame.enter_run_context` and `genericCreate.step_spawn_context` live in
`MessageCall/CheckedSpawnFacts.lean`.
-/

namespace Jaune.Checked

/-! ## Rows 30-33, 36, 37: settlement over `Exec` -/

section RunOk

variable {r : Checked.Frame.Running} {child : Checked.Frame} {pending : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
  {raw out : Except Fault Checked.Frame.Exit} {state : Checked.Frame.State}
  (hstep : step r = .ok (.spawn child pending pc)) (henter : enter child = .run cr)
  (childRun : Exec cr raw)
  (hr : resumeCaller r.context.block.rules child pending (raw >>= settle child) = .ok state)
  (next : Exec ⟨pc, r.context, state⟩ out)

/-- Row 30. A spawn retains its settlement-committing child before the child's descendants and
before the caller's continuation's descendants. -/
theorem Exec.descendantFrames_runOk_of_settlementCommits (hcommit : Frame.settlementCommits child raw = true) :
    Exec.descendantFrames (Exec.runOk hstep henter childRun hr next) =
      Exec.Frame.ofRun childRun (Frame.finished_of_settlementCommits hcommit) ::
        Exec.descendantFrames childRun ++ Exec.descendantFrames next := by
  simp [Exec.descendantFrames, hcommit]

/-- Row 31. A spawned child whose settlement does not commit contributes no retained frame. -/
theorem Exec.descendantFrames_runOk_of_not_settlementCommits (hnot : Frame.settlementCommits child raw ≠ true) :
    Exec.descendantFrames (Exec.runOk hstep henter childRun hr next) = Exec.descendantFrames next := by
  rw [Exec.descendantFrames, dite_eq_right hnot, List.nil_append]

/-- Row 32. A creation whose raw result finished but whose settlement fails (a failed code
deposit) contributes no descendant frame. -/
theorem Exec.descendantFrames_runOk_create_codeDepositRollback {result : Jaune.Frame.Result}
    (_rawCommits : Exec.finished raw = true) (_hcreate : child.message.kind = Jaune.Message.Kind.create)
    (hsettled : (raw >>= settle child) = .ok result) (hfailed : result.failed = true) :
    Exec.descendantFrames (Exec.runOk hstep henter childRun hr next) = Exec.descendantFrames next := by
  apply Exec.descendantFrames_runOk_of_not_settlementCommits
  intro hcommit
  obtain ⟨_, _, _, _, _, _, hs⟩ := Frame.settlementCommits_iff.mp hcommit
  rw [hsettled] at hs
  cases hs
  cases hfailed

/-- Row 36. Under a committing root, a settling child's retained nodes follow the root. -/
theorem Exec.retainedNodes_runOk_of_settlementCommits (rootCommits : Exec.finished out = true)
    (childSettles : Frame.settlementCommits child raw = true) :
    Exec.retainedNodes (.runOk hstep henter childRun hr next) =
      ⟨r, out, Exec.runOk hstep henter childRun hr next⟩ ::
        (Exec.retainedNodes childRun ++ Exec.retainedNodes next) := by
  rw [Exec.retainedNodes]
  simp [rootCommits, childSettles]

/-- Row 37. Under a committing root, a child whose settlement does not commit retains nothing. -/
theorem Exec.retainedNodes_runOk_of_not_settlementCommits (rootCommits : Exec.finished out = true)
    (childDoesNotSettle : Frame.settlementCommits child raw ≠ true) :
    Exec.retainedNodes (.runOk hstep henter childRun hr next) =
      ⟨r, out, Exec.runOk hstep henter childRun hr next⟩ :: Exec.retainedNodes next := by
  rw [Exec.retainedNodes]
  simp [rootCommits, childDoesNotSettle]

end RunOk

/-- Row 33. A root that did not finish commits no frame. -/
theorem Exec.committedFrames_eq_nil_of_not_commits {r out} (run : Exec r out)
    (h : Exec.finished out ≠ true) : Exec.committedFrames run = [] := by
  simp [Exec.committedFrames, h]

/-! ## Rows 39-42: block context across a frame boundary, and their proposed replacements -/

/-- Row 39. Entering a frame runs it under the block record its message carries. -/
theorem Frame.enter_run_benvStat {f : Frame} {r : Frame.Running} (h : enter f = .run r) :
    r.context.block = f.message.context.block := by
  rw [Frame.enter_run_context h]

/-- Row 40. A CALL-family spawn hands the parent's block record to the child frame. -/
theorem genericCall.step_spawn_benvStat {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Staging.Pending}
    (h : genericCall.step ctx parent gas value caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles = .spawn child pending) :
    child.message.context.block = ctx.block :=
  (genericCall.step_spawn_context h).1

/-- Row 41. A CREATE-family spawn hands the parent's block record to the child frame. -/
theorem genericCreate.step_spawn_benvStat {ctx : CallContext} {s : Frame.State} {value : U256}
    {a : Address} {i len : Nat} {child : Frame} {p : Staging.Pending}
    (h : genericCreate.step ctx s value a i len = .spawn child p) :
    child.message.context.block = ctx.block :=
  (genericCreate.step_spawn_context h).1

/-- Row 42. Every spawning instruction hands the parent's block record to the child. -/
theorem MessageOp.step_spawn_benvStat {ctx : CallContext} {s : Frame.State} {x : Jaune.MessageOp}
    {child : Frame} {p : Staging.Pending} (h : MessageOp.step ctx s x = .spawn child p) :
    child.message.context.block = ctx.block :=
  (MessageOp.step_spawn_context h).1

end Jaune.Checked
