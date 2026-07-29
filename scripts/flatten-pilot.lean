/-
  Step-1 pilot for `~/plans/flatten.md` ("Flatten the interpreter recursion").

  This file is DELIBERATELY OUTSIDE the `Jaune` library root: `lakefile.lean`
  declares `lean_lib «Jaune»` with the default glob (root module only), so a
  file under `scripts/` is never elaborated by `lake build`.  Elaborate it with

      lake env lean scripts/flatten-pilot.lean

  Purpose (plan Step 1, "the pilot"):

  * exhibit the flattened design's actual types and the single fueled driver,
    so that the design note is not paper-only;
  * carry two step functions -- one ordinary-instruction path (`evmStep*`,
    covering decode / PUSH / REG / JUMP / LAST dispatch) and one call-type path
    through spawn/resume (`xstepCall*` + `genericCallStep*` + `Resume.run`) --
    each written twice, once in the `← .ok <|` bind-seam idiom that
    `0a469c4` introduced and once in the plain-`let` idiom that `67053b6` used;
  * carry a toy inversion proof over each, of exactly the shape Blanc's
    `Semantics.lean` performs, so the two idioms can be compared on the metric
    that matters (proof-facing term size and elaboration time), not on taste.

  Coverage is partial ON PURPOSE: only `Xinst.call` is given a real step body.
  The other five call-type instructions are stubbed, because the pilot measures
  the *idiom*, not the transcription.  Step 2 transcribes all six.
-/

import Jaune
import Mathlib.Util.CountHeartbeats

set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FlattenPilot

/-! ## 1.  Shared vocabulary

Frames, resume records, step outcomes.  Everything here is non-recursive and
fuel-free; the only recursion in the whole design is `drive`, in §3. -/

/-- A suspended child frame.  `outer` is the message as seen by
`processCreateMessage` (create) or `processMessage` (call); `inner` is the
message as seen by `processMessage`.  Built only by the two smart constructors
below, so `inner` is always the correct function of `outer`; storing it avoids
recomputing `processCreateMessage.msg` in both `enter` and `settle`. -/
structure Frame : Type where
  outer : Msg
  inner : Msg
  isCreate : Bool

def Frame.ofCall (msg : Msg) : Frame := ⟨msg, msg, false⟩

def Frame.ofCreate (msg : Msg) : Frame := ⟨msg, processCreateMessage.msg msg, true⟩

/-- The tail of the old `processMessage` body, as a pure function of the
inner result. -/
def processMessage.settle (msg : Msg)
    (r : Except (String × State × AdrSet × Tra) Devm) :
    Except (String × State × AdrSet × Tra) Devm := do
  let evm ← r
  if evm.error.isSome then
    .ok (evm.rollback msg.benv.state msg.tenv.transientStorage)
  else
    .ok evm

/-- The tail of the old `processCreateMessage` body, as a pure function of the
inner result. -/
def processCreateMessage.settle (msg : Msg)
    (r : Except (String × State × AdrSet × Tra) Devm) :
    Except (String × State × AdrSet × Tra) Devm := do
  let evm ← r
  if evm.error.isNone then
    match processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
    | .ok evm => .ok (evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩)
    | .error ⟨err, evm⟩ =>
      if isExceptionalHalt err then
        .ok
          ( processCreateMessage.exceptionalHalt evm err
              msg.benv.state msg.tenv.transientStorage )
      else
        .error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩
  else
    .ok (evm.rollback msg.benv.state msg.tenv.transientStorage)

/-- Frame-level settle from a message-level result (no `executeCode` layer). -/
def Frame.settleMsg (f : Frame)
    (r : Except (String × State × AdrSet × Tra) Devm) :
    Except (String × State × AdrSet × Tra) Devm :=
  let r := processMessage.settle f.inner r
  if f.isCreate then processCreateMessage.settle f.outer r else r

/-- Frame-level settle from the raw interpreted result of the frame's code. -/
def Frame.settle (f : Frame) (raw : Execution) :
    Except (String × State × AdrSet × Tra) Devm :=
  f.settleMsg (executeCode.handleError raw)

/-- What entering a frame yields: either the frame's result is already known
(value transfer failed, or the code address is a precompile), or an `Evm` that
the driver must interpret. -/
inductive FrameEntry : Type
  | done (r : Except (String × State × AdrSet × Tra) Devm)
  | run (evm : Evm)

/-- The head of the old `processMessage`/`executeCode` tower, non-recursively.
`processCreateMessage`'s head is `processCreateMessage.msg`, already applied by
`Frame.ofCreate`. -/
def Frame.enter (f : Frame) : FrameEntry :=
  match f.inner.benvAfterTransfer with
  | .error e => .done (f.settleMsg (.error e))
  | .ok benv =>
    let msg := f.inner.withBenv benv
    let evm := initEvm msg
    match msg.codeAddress with
    | .none => .run evm
    | .some adr =>
      if !msg.disablePrecompiles && msg.benv.stat.rules.isPrecomp adr then
        .done (f.settle (executePrecomp evm adr))
      else
        .run evm

/-- Defunctionalized continuation of a call-type instruction: the parent state
plus the little that post-return work needs.  Six call-type instructions but
only two shapes, because everything that distinguishes CALL from DELEGATECALL
(or CREATE from CREATE2) is already baked into the child `Msg` before the
spawn. -/
inductive Resume : Type
  | create (parent : Devm) (newAddress : Adr)
  | call (parent : Devm) (outputIndex outputSize : Nat)

def Resume.run :
    Resume → Except (String × State × AdrSet × Tra) Devm → Execution
  | .create parent newAddress, r => do
    let child ← liftToExecution parent r
    if child.error.isSome then
      (incorporateChildOnError parent child child.output).push 0
    else
      (incorporateChildOnSuccess parent child []).push newAddress.toB256
  | .call parent outputIndex outputSize, r => do
    let child ← liftToExecution parent r
    let actualOutput := child.output.take outputSize
    if child.error.isSome then
      let evm2 ← (incorporateChildOnError parent child child.output).push 0
      .ok (evm2.memWrite outputIndex actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent child child.output).push 1
      .ok (evm2.memWrite outputIndex actualOutput)

/-- Outcome of one call-type instruction, frame-locally. -/
inductive XStep : Type
  | done (ex : Execution)
  | spawn (frame : Frame) (rsm : Resume)

def XStep.ofExcept : Except (String × Devm) XStep → XStep
  | .error e => .done (.error e)
  | .ok s => s

/-- Outcome of one interpreter step. -/
inductive Step : Type
  | halt (ex : Execution)
  | cont (pc : Nat) (devm : Devm)
  | spawn (frame : Frame) (rsm : Resume) (pc : Nat)

def Step.ofExecution (pc : Nat) : Execution → Step
  | .error e => .halt (.error e)
  | .ok devm => .cont pc devm

/-- Jump results already carry their own target `pc`. -/
def Step.ofJump : Except (String × Devm) (Nat × Devm) → Step
  | .error e => .halt (.error e)
  | .ok ⟨pc, devm⟩ => .cont pc devm

def XStep.toStep (pc : Nat) : XStep → Step
  | .done ex => Step.ofExecution pc ex
  | .spawn f rsm => .spawn f rsm pc

/-! ## 2.  The two pilot step functions, in both idioms.

`genericCallStep*` / `xstepCall*` are the call-type path; `evmStep*` is the
ordinary-instruction path (decode + PUSH + REG + JUMP + LAST), which also
dispatches into the call path so the driver has something to run. -/

#count_heartbeats in
/-- Call-type path, bind-seam idiom (`0a469c4`'s convention). -/
def genericCallStepBind
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) : XStep :=
  XStep.ofExcept do
    let evm1 ← .ok <| devm.withReturnData []
    if sevm.depth = 0 then
      return .done ((evm1.withGasLeft (evm1.gasLeft + gas)).push 0)
    let calldata ← .ok <| evm1.memory.data.sliceD inputIndex inputSize 0
    let childMsg ← .ok <|
      callMsg sevm evm1 gas value caller target codeAddress
        shouldTransferValue isStaticcall calldata code disablePrecompiles
    return .spawn (Frame.ofCall childMsg) (.call evm1 outputIndex outputSize)

#count_heartbeats in
/-- Call-type path, plain-`let` idiom (`67053b6`'s convention). -/
def genericCallStepLet
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) : XStep :=
  let evm1 := devm.withReturnData []
  if sevm.depth = 0 then
    .done ((evm1.withGasLeft (evm1.gasLeft + gas)).push 0)
  else
    let calldata := evm1.memory.data.sliceD inputIndex inputSize 0
    let childMsg :=
      callMsg sevm evm1 gas value caller target codeAddress
        shouldTransferValue isStaticcall calldata code disablePrecompiles
    .spawn (Frame.ofCall childMsg) (.call evm1 outputIndex outputSize)

#count_heartbeats in
/-- CALL, bind-seam idiom.  Transcribed from `Execution.lean:4012-4065`. -/
def xstepCallBind (sevm : Sevm) (devm : Devm) : XStep :=
  XStep.ofExcept do
    let ⟨gas, devm⟩ ← devm.pop
    let ⟨callee, devm⟩ ← devm.popToAdr
    let ⟨value, devm⟩ ← devm.pop
    let ⟨inputIndex, devm⟩ ← devm.popToNat
    let ⟨inputSize, devm⟩ ← devm.popToNat
    let ⟨outputIndex, devm⟩ ← devm.popToNat
    let ⟨outputSize, devm⟩ ← devm.popToNat
    let extendCost ← .ok <|
      devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost ← .ok <| access_cost callee devm.accessedAddresses
    let devm ← .ok <| addAccessedAddress devm callee
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm⟩ ← .ok <|
      accessDelegation devm callee
    let accessCost ← .ok <| preAccessCost + delegatedAccessGasCost
    let createCost ← .ok <|
      if (¬ (devm.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost ← .ok <| if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ ← .ok <|
      calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let devm ← chargeGas (msgCallCost + extendCost) devm
    Except.assert (!sevm.isStatic ∨ value = 0) ⟨"WriteInStaticContext", devm⟩
    let devm ← .ok <|
      devm.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal ← .ok <| (devm.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let devm ← devm.push 0
      return .done
        (.ok ((devm.withReturnData []).withGasLeft (devm.gasLeft + msgCallStipend)))
    else
      return genericCallStepBind sevm devm msgCallStipend value
        sevm.currentTarget callee callee true false
        inputIndex inputSize outputIndex outputSize code disablePrecompiles

#count_heartbeats in
/-- CALL, plain-`let` idiom: every pure intermediate is a `let`, only the
genuinely fallible operations stay binds. -/
def xstepCallLet (sevm : Sevm) (devm : Devm) : XStep :=
  XStep.ofExcept do
    let ⟨gas, devm⟩ ← devm.pop
    let ⟨callee, devm⟩ ← devm.popToAdr
    let ⟨value, devm⟩ ← devm.pop
    let ⟨inputIndex, devm⟩ ← devm.popToNat
    let ⟨inputSize, devm⟩ ← devm.popToNat
    let ⟨outputIndex, devm⟩ ← devm.popToNat
    let ⟨outputSize, devm⟩ ← devm.popToNat
    let extendCost :=
      devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let preAccessCost := access_cost callee devm.accessedAddresses
    let devm := addAccessedAddress devm callee
    let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm⟩ :=
      accessDelegation devm callee
    let accessCost := preAccessCost + delegatedAccessGasCost
    let createCost :=
      if (¬ (devm.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
    let transferCost := if value = 0 then 0 else gasCallValue
    let ⟨msgCallCost, msgCallStipend⟩ :=
      calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
        (accessCost + createCost + transferCost)
    let devm ← chargeGas (msgCallCost + extendCost) devm
    Except.assert (!sevm.isStatic ∨ value = 0) ⟨"WriteInStaticContext", devm⟩
    let devm := devm.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
    let senderBal := (devm.getAcct sevm.currentTarget).bal
    if senderBal < value then
      let devm ← devm.push 0
      return .done
        (.ok ((devm.withReturnData []).withGasLeft (devm.gasLeft + msgCallStipend)))
    else
      return genericCallStepLet sevm devm msgCallStipend value
        sevm.currentTarget callee callee true false
        inputIndex inputSize outputIndex outputSize code disablePrecompiles

/-- Pilot stub for the five call-type instructions the pilot does not
transcribe.  Step 2 replaces this with the real bodies. -/
def xstepStub (devm : Devm) : XStep := .done (.error ⟨"PilotStub", devm⟩)

#count_heartbeats in
/-- Ordinary-instruction path, bind-seam idiom. -/
def evmStepBind (evm : Evm) : Step :=
  match evm.getInst with
  | .none => .halt (.error ⟨"InvalidOpcode", evm.dyna⟩)
  | .some (.last l) => .halt (l.run evm.sta evm.dyna)
  | .some (.jump j) => Step.ofJump (j.run evm)
  | .some (.next n) =>
    match n with
    | .push xs h =>
      Step.ofExecution (evm.pc + (Ninst.push xs h).size) <| do
        let devm ← chargeGas (if xs = [] then gBase else gVerylow) evm.dyna
        devm.push xs.toB256
    | .reg r => Step.ofExecution (evm.pc + (Ninst.reg r).size) (r.run evm)
    | .exec x =>
      XStep.toStep (evm.pc + (Ninst.exec x).size) <|
        match x with
        | .call => xstepCallBind evm.sta evm.dyna
        | _ => xstepStub evm.dyna

#count_heartbeats in
/-- Ordinary-instruction path, plain-`let` idiom. -/
def evmStepLet (evm : Evm) : Step :=
  match evm.getInst with
  | .none => .halt (.error ⟨"InvalidOpcode", evm.dyna⟩)
  | .some (.last l) => .halt (l.run evm.sta evm.dyna)
  | .some (.jump j) => Step.ofJump (j.run evm)
  | .some (.next n) =>
    let pc' := evm.pc + n.size
    match n with
    | .push xs _ =>
      let cost := if xs = [] then gBase else gVerylow
      Step.ofExecution pc' <| do
        let devm ← chargeGas cost evm.dyna
        devm.push xs.toB256
    | .reg r => Step.ofExecution pc' (r.run evm)
    | .exec x =>
      XStep.toStep pc' <|
        match x with
        | .call => xstepCallLet evm.sta evm.dyna
        | _ => xstepStub evm.dyna

/-! ## 3.  The single fueled driver.

One recursive function, `termination_by fuel`.  Fuel is burnt exactly once per
interpreter step, which is exactly what the old `exec` burnt; the 5-6 wrapper
units the old tower burnt at every frame entry are gone. -/

#count_heartbeats in
def drive : Nat → Evm → Fueled (String × Devm) Devm
  | 0, _ => Fueled.exhausted
  | fuel + 1, evm =>
    match evmStepBind evm with
    | .halt ex => Fueled.ofExcept ex
    | .cont pc devm => drive fuel ⟨pc, evm.sta, devm⟩
    | .spawn f rsm pc =>
      match f.enter with
      | .done r =>
        match rsm.run r with
        | .error e => Fueled.ofExcept (.error e)
        | .ok devm => drive fuel ⟨pc, evm.sta, devm⟩
      | .run cevm =>
        match (drive fuel cevm).run with
        | .none => Fueled.exhausted
        | .some raw =>
          match rsm.run (f.settle raw) with
          | .error e => Fueled.ofExcept (.error e)
          | .ok devm => drive fuel ⟨pc, evm.sta, devm⟩
  termination_by fuel => fuel

/-- The non-recursive frame wrapper the two public entry points use. -/
def runFrame (f : Frame) (fuel : Nat) :
    Fueled (String × State × AdrSet × Tra) Devm :=
  match f.enter with
  | .done r => Fueled.ofExcept r
  | .run evm => Fueled.mapResult f.settle (drive fuel evm)

def processMessage' (msg : Msg) (fuel : Nat) :
    Fueled (String × State × AdrSet × Tra) Devm :=
  runFrame (Frame.ofCall msg) fuel

def processCreateMessage' (msg : Msg) (fuel : Nat) :
    Fueled (String × State × AdrSet × Tra) Devm :=
  runFrame (Frame.ofCreate msg) fuel

/-! ## 4.  Toy inversion proofs, in the shape Blanc performs them.

Each proof recovers, from a single equation about the step function, the named
intermediates a downstream relational proof needs.  These are the measurement
subjects. -/

#count_heartbeats in
/-- Ordinary path, bind idiom: a successful PUSH step exposes its two seams. -/
theorem invPushBind {evm : Evm} {xs : Bytes} {h : xs.length ≤ 32} {pc devm'}
    (hi : evm.getInst = .some (.next (.push xs h)))
    (hs : evmStepBind evm = .cont pc devm') :
    ∃ d, chargeGas (if xs = [] then gBase else gVerylow) evm.dyna = .ok d ∧
      d.push xs.toB256 = .ok devm' ∧ pc = evm.pc + (Ninst.push xs h).size := by
  simp only [evmStepBind, hi, Bind.bind, Except.bind] at hs
  split at hs
  · simp only [Step.ofExecution] at hs; cases hs
  · rename_i d hd
    rcases hp : d.push xs.toB256 with e | devm''
    · rw [hp] at hs; simp only [Step.ofExecution] at hs; cases hs
    · rw [hp] at hs; simp only [Step.ofExecution, Step.cont.injEq] at hs
      exact ⟨d, hd, hp.trans (by rw [hs.2]), hs.1.symm⟩

#count_heartbeats in
/-- Ordinary path, `let` idiom: same statement, same tactic script. -/
theorem invPushLet {evm : Evm} {xs : Bytes} {h : xs.length ≤ 32} {pc devm'}
    (hi : evm.getInst = .some (.next (.push xs h)))
    (hs : evmStepLet evm = .cont pc devm') :
    ∃ d, chargeGas (if xs = [] then gBase else gVerylow) evm.dyna = .ok d ∧
      d.push xs.toB256 = .ok devm' ∧ pc = evm.pc + (Ninst.push xs h).size := by
  simp only [evmStepLet, hi, Bind.bind, Except.bind] at hs
  split at hs
  · simp only [Step.ofExecution] at hs; cases hs
  · rename_i d hd
    rcases hp : d.push xs.toB256 with e | devm''
    · rw [hp] at hs; simp only [Step.ofExecution] at hs; cases hs
    · rw [hp] at hs; simp only [Step.ofExecution, Step.cont.injEq] at hs
      exact ⟨d, hd, hp.trans (by rw [hs.2]), hs.1.symm⟩

#count_heartbeats in
/-- Call path, bind idiom: a spawn implies the child frame sits one depth
below the parent.  This is exactly the side condition Blanc's depth-based
strong induction needs, and proving it walks the entire CALL body. -/
theorem invCallBind {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (hs : xstepCallBind sevm devm = .spawn f rsm) :
    f.outer.depth < sevm.depth := by
  simp only [xstepCallBind, genericCallStepBind, Bind.bind, Except.bind,
    Except.assert, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Frame.ofCall, callMsg]
  all_goals omega

#count_heartbeats in
/-- Call path, `let` idiom: same statement, same tactic script. -/
theorem invCallLet {sevm : Sevm} {devm : Devm} {f : Frame} {rsm : Resume}
    (hs : xstepCallLet sevm devm = .spawn f rsm) :
    f.outer.depth < sevm.depth := by
  simp only [xstepCallLet, genericCallStepLet, Bind.bind, Except.bind,
    Except.assert, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hs
  all_goals obtain ⟨rfl, -⟩ := hs
  all_goals simp only [Frame.ofCall, callMsg]
  all_goals omega

#count_heartbeats in
/-- Toy driver inversion: the shape Blanc's adequacy proof performs at every
recursion site.  A completed run at fuel `fuel+1` is decided by the step
outcome, and each branch hands back a strictly smaller-fuel completed run. -/
theorem invDrive {fuel : Nat} {evm : Evm} {ex : Execution}
    (hd : drive (fuel + 1) evm = Fueled.ofExcept ex) :
    (evmStepBind evm = .halt ex) ∨
    (∃ pc devm, evmStepBind evm = .cont pc devm ∧
      drive fuel ⟨pc, evm.sta, devm⟩ = Fueled.ofExcept ex) ∨
    (∃ f rsm pc, evmStepBind evm = .spawn f rsm pc) := by
  rw [drive] at hd
  split at hd
  · rename_i ex' hstep
    left
    have h2 : ex' = ex := by
      have hr := congrArg ExceptT.run hd
      simpa using hr
    rw [hstep, h2]
  · rename_i pc devm hstep
    exact Or.inr (Or.inl ⟨pc, devm, hstep, hd⟩)
  · rename_i f rsm pc hstep
    exact Or.inr (Or.inr ⟨f, rsm, pc, hstep⟩)

/-! ## 5.  Measurement.

Two numbers per subject:

* `body`  -- the size of the definition's value as stored, i.e. what a proof
             sees before any unfolding;
* `zeta`  -- the size after top-level `let`s are substituted away, i.e. what a
             proof sees after `simp only [thatDef]` / `delta`, which is where
             the plain-`let` idiom pays for itself or does not.

For theorems the interesting number is the proof term's size, plus the
elaboration time reported by the profiler. -/

open Lean in
private partial def exprSize : Expr → Nat
  | .app f a => 1 + exprSize f + exprSize a
  | .lam _ t b _ => 1 + exprSize t + exprSize b
  | .forallE _ t b _ => 1 + exprSize t + exprSize b
  | .letE _ t v b _ => 1 + exprSize t + exprSize v + exprSize b
  | .mdata _ e => 1 + exprSize e
  | .proj _ _ e => 1 + exprSize e
  | _ => 1

open Lean in
private partial def zetaAll : Expr → Expr
  | .letE _ _ v b _ => zetaAll (b.instantiate1 (zetaAll v))
  | .app f a => .app (zetaAll f) (zetaAll a)
  | .lam n t b i => .lam n (zetaAll t) (zetaAll b) i
  | .forallE n t b i => .forallE n (zetaAll t) (zetaAll b) i
  | .mdata _ e => zetaAll e
  | .proj s i e => .proj s i (zetaAll e)
  | e => e

open Lean Elab Command in
private def report (ns : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for n in ns do
    let some ci := env.find? n | throwError m!"missing constant {n}"
    let some v := ci.value? | logInfo m!"{n}  (no stored value)"; continue
    logInfo m!"{n}  body={exprSize v}  zeta={exprSize (zetaAll v)}"

open Lean Elab Command in
#eval report
  [ ``genericCallStepBind, ``genericCallStepLet,
    ``xstepCallBind, ``xstepCallLet,
    ``evmStepBind, ``evmStepLet ]

end FlattenPilot
