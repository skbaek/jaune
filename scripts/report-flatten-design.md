# Flatten the interpreter recursion — Step 1 design note

**Plan:** `~/plans/flatten.md`, Step 1 ("Fix the design and measure the pilot").
**Date:** 2026-07-28 (Asia/Seoul).
**Branches:** `elevm` `codex/flatten` (from `be33a2cfd6c9eefbe69a13bb6389164893c9a1e0`),
`blanc` `codex/flatten` (from `36c4ec37b656bafe457bcf99653bc4a1053071fa`).
**Status:** design fixed. Step 2 implements exactly this; a material redesign
after Step 2 has begun is a stop condition.

Artefacts of this step: this note and `scripts/flatten-pilot.lean`.
No production semantics changed.

---

## 0. Starting-point re-verification and drift

Every fact in the plan's "Verified starting point" was re-checked before any
edit. **No drift.**

| fact | plan | observed |
|---|---|---|
| `elevm` HEAD | `be33a2c…` clean, `main` | identical, clean |
| `blanc` HEAD | `36c4ec3…` clean, `main` | identical, clean |
| toolchain both | `leanprover/lean4:v4.32.1` | identical |
| Blanc's ELeVM pin, all three locations | `a40871bc69df5159f6edc7fc7c3e928675b9f54d` | `lakefile.lean`, `lake-manifest.json`, and `.lake/packages/elevm` HEAD all agree; the managed checkout is a real directory, not a symlink |
| mutual block | `Elevm/Execution.lean:3799-4237`, 8 functions | identical; `mutual` at 3799, `end` at 4237, eight `termination_by lim => lim` |
| `Fueled` | `Execution.lean:1550` | identical |
| entry points | `:4869` create, `:4913` call, both seeding `msg.gas + 50` | identical, both under the "Public compatibility boundary" comment |
| error payloads | `String × Devm`, `String × State × AdrSet × Tra` | identical; bridges at `:2958` (`liftToExecution`), `:3742` (`executeCode.handleError`) |
| Blanc reference counts | table in the plan | reproduced **exactly** with line-based `grep -c` (the plan's numbers are line counts, not occurrence counts) |
| `Exec.strong_rec` | `Common.lean:182` | identical |
| build | green | `lake build` — 1760 jobs, success |
| U256 | 21,593/21,593 | 21,593/21,593 PASS |

One fact the plan did **not** record, discovered here and load-bearing for
Step 3, is in §5.1: `weth_inv_solvent`'s *statement* mentions
`Exec 0 sevm pre (.ok post)`, so the generic relation must keep the name
`Exec` and the index shape `Nat → Sevm → Devm → Execution`.

---

## 1. Shape of the answer

The old interpreter is an eight-way mutual recursion in which fuel is threaded
through every layer. The new one is:

```
  non-recursive step functions          →  Step / XStep  (frame-local, fuel-free)
  non-recursive frame enter/settle      →  Frame.enter / Frame.settle
  ONE fueled recursive driver           →  exec   (name and signature unchanged)
  non-recursive public wrappers         →  runFrame, executeCode,
                                           processMessage, processCreateMessage
```

Every one of the eight old functions either dissolves into a step function or
survives as a *non-recursive* wrapper of the same name and signature. The
driver is `exec` itself, keeping today's signature
`Evm → Nat → Fueled (String × Devm) Devm`: the new driver does exactly what the
old `exec` did — interpret a frame's code, descending into child frames — so
reusing the name preserves the statements of `of_exec`, `of_exec'`,
`exec_iff_exec_eq` and four `Solvent.lean` lemmas stated as
`exec ⟨0, sevm, pre⟩ lim = …` (`:4123`, `:4381`, `:4414`, `:5200`). `exec` is the
only recursive definition in the interpreter. **Driver count: one.**

(The pilot module calls it `drive`, with the fuel argument first, because there
it coexists with the real `exec`. Step 2 uses the name and argument order
above.)

---

## 2. Refactor delta table

Every semantic branch of the eight functions, with its new home. Line numbers
are `Elevm/Execution.lean` at `be33a2c`. "(gone)" means the branch exists only
to thread fuel and has no successor. Dead commented debug code
(`showLim`/`showStep`/`let mut evm` at `:4222-4226`, the `.withPc` comments at
`:4208-4215`) is the only permitted omission.

### 2.1 `executeCode` (3815–3828)

| # | branch | new home |
|---|---|---|
| 1 | `\| 0 => Fueled.exhausted` | (gone) — `executeCode` becomes non-recursive |
| 2 | `evm := initEvm msg` | `executeCode.enter` |
| 3 | `codeAddress = .none` → `mapResult handleError (exec evm lim)` | `executeCode.enter → .inl evm`; settle is `executeCode.handleError`, unchanged |
| 4 | `codeAddress = .some adr` ∧ `!disablePrecompiles && rules.isPrecomp adr` → `ofExcept (handleError (executePrecomp evm adr))` | `executeCode.enter → .inr (executePrecomp evm adr)` |
| 5 | `codeAddress = .some adr`, not a precompile → `mapResult handleError (exec evm lim)` | `executeCode.enter → .inl evm` |

`executeCode.handleError` (`:3742`) is **unchanged** and remains the sole
`Execution → Except (String × State × AdrSet × Tra) Devm` bridge.

### 2.2 `processMessage` (3830–3846)

| # | branch | new home |
|---|---|---|
| 1 | `\| 0 => Fueled.exhausted` | (gone) |
| 2 | `benv ← msg.benvAfterTransfer`, error | `Frame.enter → .done (f.settleMsg (.error e))` |
| 3 | `benv ← msg.benvAfterTransfer`, ok | `Frame.enter`, feeding `executeCode.enter (f.inner.withBenv benv)` |
| 4 | `evm ← executeCode (msg.withBenv benv) lim` | `Frame.enter .run` + the driver + `Frame.settle` |
| 5 | `evm.error.isSome` → `ok (evm.rollback msg.benv.state msg.tenv.transientStorage)` | `processMessage.settle` |
| 6 | else → `ok evm` | `processMessage.settle` |
| — | the dead-code comment about the 1024 depth check | carried verbatim onto `Frame.enter` |

Note the rollback uses the **pre-transfer** `msg.benv.state`, i.e. `Frame.inner`'s
own benv, not the post-transfer one. `Frame` stores `inner` precisely so this
stays exact.

### 2.3 `processCreateMessage` (3848–3867)

| # | branch | new home |
|---|---|---|
| 1 | `\| 0 => Fueled.exhausted` | (gone) |
| 2 | `processMessage (processCreateMessage.msg msg) lim` | `Frame.ofCreate msg` sets `inner := processCreateMessage.msg msg`; body identical to a call frame |
| 3 | `evm.error.isNone`, `chargeCodeGas = .ok evm` → `evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩` | `processCreateMessage.settle` |
| 4 | `chargeCodeGas = .error ⟨err, evm⟩`, `isExceptionalHalt err` → `exceptionalHalt evm err msg.benv.state msg.tenv.transientStorage` | `processCreateMessage.settle` |
| 5 | `chargeCodeGas` error, not exceptional → `.error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩` | `processCreateMessage.settle` |
| 6 | `evm.error.isSome` → `ok (evm.rollback msg.benv.state msg.tenv.transientStorage)` | `processCreateMessage.settle` |

Here the rollback/`setCode`/`chargeCodeGas` all use the **outer** (pre-nonce-bump)
message, so `Frame` stores `outer` too. `processCreateMessage.msg`,
`.chargeCodeGas` and `.exceptionalHalt` (`:3659`, `:3666`, `:3678`) are
**unchanged**.

### 2.4 `genericCreate` (3869–3923) → `genericCreate.step`

| # | branch | new home |
|---|---|---|
| 1 | `\| 0 => Fueled.exhausted` | (gone) |
| 2 | `calldata := memory.data.sliceD memoryIndex memorySize 0` | `genericCreate.step` |
| 3 | assert `memorySize ≤ rules.code.maxInitCodeSize` else `"OutOfGasError"` | `genericCreate.step`, `Except.assert` → `XStep.ofExcept` → `.done (.error …)` |
| 4 | `createMsgGas := except64th gasLeft`; `gasLeft -= createMsgGas` | `genericCreate.step` |
| 5 | `assertDynamic sevm devm` (static-context guard) | `genericCreate.step` → `.done (.error …)` |
| 6 | `withReturnData []` | `genericCreate.step` |
| 7 | **early exit** `sender.bal < endowment ∨ sender.nonce = B64.max ∨ sevm.depth = 0` → `(withGasLeft (gasLeft + createMsgGas)).push 0` | `genericCreate.step` → `.done` |
| 8 | `incrNonce sevm.currentTarget`; `addAccessedAddress newAddress` | `genericCreate.step` |
| 9 | **collision early exit** `target.nonce ≠ 0 ∨ target.code.size ≠ 0 ∨ target.stor.size ≠ 0` → `push 0` | `genericCreate.step` → `.done` |
| 10 | the inline child-`Msg` record literal (3899–3916) | **new named barrier `createMsg`**, sibling of `callMsg` (the `209e710` rule; see §4.3) |
| 11 | `mapResult (liftToExecution devm) (processCreateMessage childMsg lim)` | `.spawn (Frame.ofCreate childMsg) (Resume.create devm newAddress)`; the driver runs the frame, `Resume.run` applies `liftToExecution` |
| 12 | `child.error.isSome` → `(incorporateChildOnError devm child child.output).push 0` | `Resume.run (.create …)` |
| 13 | else → `(incorporateChildOnSuccess devm child []).push newAddress.toB256` | `Resume.run (.create …)` |

### 2.5 `genericCall` (3925–3959) → `genericCall.step`

| # | branch | new home |
|---|---|---|
| 1 | `\| 0 => Fueled.exhausted` | (gone) |
| 2 | `evm1 := devm.withReturnData []` | `genericCall.step` |
| 3 | **depth-0 short-circuit** `sevm.depth = 0` → `(evm1.withGasLeft (gasLeft + gas)).push 0` | `genericCall.step` → `.done` |
| 4 | `calldata := evm1.memory.data.sliceD input_index input_size 0` | `genericCall.step` |
| 5 | `callMsg …` | `genericCall.step` — `callMsg` (`:3767`) **unchanged** |
| 6 | `mapResult (liftToExecution evm1) (processMessage childMsg lim)` | `.spawn (Frame.ofCall childMsg) (Resume.call evm1 output_index output_size)` |
| 7 | `actualOutput := child.output.take output_size` | `Resume.run (.call …)` |
| 8 | `child.error.isSome` → `push 0` then `memWrite output_index actualOutput` | `Resume.run (.call …)` |
| 9 | else → `push 1` then `memWrite output_index actualOutput` | `Resume.run (.call …)` |

### 2.6 `Xinst.run` (3961–4201) → `Xinst.step`

`\| _, 0 => Fueled.exhausted` is (gone). Each of the six cases becomes one
branch of `Xinst.step : Sevm → Devm → Xinst → XStep`, written as
`XStep.ofExcept do …` so the existing `Except` sequencing is transcribed
verbatim.

| case | branches | new home |
|---|---|---|
| `.create` (3964–3983) | 3 pops · `extCost` · `initCodeCost` · `chargeGas` · `memExtends` · `compute_contract_address` · tail-call | `Xinst.step .create` → `genericCreate.step` |
| `.create2` (3984–4011) | 4 pops · `extCost` · `initCodeHashCost` · `initCodeCost` · `chargeGas` · `memExtends` · `create2NewAddress` · tail-call | `Xinst.step .create2` → `genericCreate.step` |
| `.call` (4012–4065) | 7 pops · `extCost` · `preAccessCost` · `addAccessedAddress` · `accessDelegation` · `accessCost` · **`createCost` (`gNewAccount`)** · `transferCost` · `calculateMsgCallGas` · `chargeGas` · **static-write assertion `"WriteInStaticContext"`** · `memExtends` · **`senderBal < value` early exit** → `push 0`, then `(withReturnData []).withGasLeft (gasLeft + stipend)` · else tail-call | `Xinst.step .call` → `genericCall.step` |
| `.callcode` (4066–4116) | as `.call` minus `createCost` and minus the static assertion; **`senderBal < value` early exit** → `push 0`, then `(withGasLeft (gasLeft + stipend)).withReturnData []` · target `sevm.currentTarget`, codeAddress `newCodeAddress` | `Xinst.step .callcode` → `genericCall.step` |
| `.delcall` (4117–4158) | 6 pops · costs with `value = 0` · `chargeGas` · `memExtends` · no balance check · `genericCall` with `sevm.value`, `sevm.caller`, `shouldTransferValue := false` | `Xinst.step .delcall` → `genericCall.step` |
| `.statcall` (4159–4200) | 6 pops · costs with `value = 0` · `chargeGas` · `memExtends` · no balance check · `genericCall` with `value := 0`, `isStaticcall := true` | `Xinst.step .statcall` → `genericCall.step` |

> **Transcription hazard, recorded deliberately.** `.call` and `.callcode`
> compose the two setters of their `senderBal < value` exit in the *opposite
> order* (`(withReturnData []).withGasLeft …` vs
> `(withGasLeft …).withReturnData []`). The fields are disjoint so the results
> agree, but Step 2 must transcribe each verbatim and must **not** normalise
> them, because Blanc's frame lemmas are stated against the current spellings.

### 2.7 `Ninst.run` (4203–4217) → `Ninst.step`

| branch | new home |
|---|---|
| `.push xs _` → `chargeGas (if xs = [] then gBase else gVerylow)` then `push xs.toB256` | `Ninst.step .push`, wrapped by `Step.ofExecution (evm.pc + n.size)` |
| `.reg r` → `ofExcept (r.run evm)` | `Ninst.step .reg`, same wrapper |
| `.exec _, 0 => exhausted` | (gone) |
| `.exec x, lim+1` → `Xinst.run evm.sta evm.dyna x lim` | `Ninst.step .exec` → `Xinst.step`, wrapped by `XStep.toStep (evm.pc + n.size)` |

The pc arithmetic `evm.pc + n.size` migrates from `exec`'s `.next` branch into
`Ninst.step`, because the new step outcome carries its own continuation pc.

### 2.8 `exec` (4219–4235) → `Evm.step` + the driver body

| branch | new home |
|---|---|
| `\| _, 0 => Fueled.exhausted` | unchanged: `exec _ 0 = Fueled.exhausted` |
| `getInst = none` → `.error ⟨"InvalidOpcode", evm.dyna⟩` | `Evm.step` → `.halt` |
| `.next n` → `n.run evm lim`; then `exec ⟨pc + n.size, sta, devm⟩ lim` | `Evm.step` → `Ninst.step`; the driver consumes `.cont`/`.halt`/`.spawn` |
| `.jump j` → `j.run evm`; then `exec ⟨pc, sta, devm⟩ lim` | `Evm.step` → `Step.ofJump (j.run evm)` |
| `.last l` → `ofExcept (l.run evm.sta evm.dyna)` | `Evm.step` → `.halt` |

### 2.9 Entry points and error-channel adapters

| old | new |
|---|---|
| `processMessageCall.create` collision early exit (`:4859-4862`) | **unchanged, stays where it is** |
| `processMessageCall.create` (`:4865-4869`) `Fueled.toExcept ⟨"RecursionLimit", …⟩ (processCreateMessage msg (msg.gas + 50))` | textually unchanged; `processCreateMessage` is now the non-recursive wrapper |
| `processMessageCall.call` (`:4909-4913`) `… (processMessage msgPc (msgPc.gas + 50))` | textually unchanged, same reason |
| `Fueled.mapResult executeCode.handleError` ×2 (`:3822`, `:3827`) + `Fueled.ofExcept ∘ handleError` ×1 (`:3825`) | one site: `executeCode` / `Frame.settle` |
| `Fueled.mapResult (liftToExecution …)` ×2 (`:3917`, `:3950`) | one site: `Resume.run` |
| `Fueled.ok` ×62, `Fueled.error` ×1, `Fueled.assert` ×2 | dead inside the interpreter (replaced by `Except.ok` / plain `let` / `Except.assert`) |
| `Fueled.exhausted` ×8 | 2 sites in the driver |
| `Fueled.toExcept` ×2 | unchanged |

**Deliberate narrowing of "delete now-dead `Fueled` adapters".** `Fueled.ok`,
`Fueled.error` and `Fueled.assert` become unreferenced *inside ELeVM*, but
Blanc's `Semantics.lean` (192 `Fueled` lines) and `Common.lean`
(`Fueled.eq_ok_of_toExcept_eq_ok`, `:9831`) are stated in terms of them. They
are three-line abbreviations of `pure`/`throw`/`ite`, so Step 2 keeps the
`Fueled` namespace intact and only removes the *call sites*; the final
deletion, if any, belongs to Step 3 once Blanc's lemma library is rebuilt, and
is recorded there. This costs nothing and removes a gratuitous source of red in
the Step-3 pin bump.

---

## 3. Exact new types

All of the following live in `Elevm/Execution.lean`, immediately before the
(deleted) mutual block, and all are **non-recursive and fuel-free** except
`exec`.

### 3.1 Frames

```lean
structure Frame : Type where
  outer : Msg          -- argument of processCreateMessage (create) / processMessage (call)
  inner : Msg          -- argument of processMessage
  isCreate : Bool

def Frame.ofCall   (msg : Msg) : Frame := ⟨msg, msg, false⟩
def Frame.ofCreate (msg : Msg) : Frame := ⟨msg, processCreateMessage.msg msg, true⟩
```

`inner` is stored rather than recomputed so that `processCreateMessage.msg`
(three `State` updates) runs once per CREATE instead of once in `enter` and
once in `settle`. The two smart constructors are the only construction sites,
so `inner` is always the correct function of `outer`, by `rfl`.

### 3.2 Frame enter

```lean
inductive FrameEntry : Type
  | done (r : Except (String × State × AdrSet × Tra) Devm)   -- frame result already known
  | run  (evm : Evm)                                          -- interpret this

def executeCode.enter (msg : Msg) : Evm ⊕ Execution :=
  let evm := initEvm msg
  match msg.codeAddress with
  | .none => .inl evm
  | .some adr =>
    if !msg.disablePrecompiles && msg.benv.stat.rules.isPrecomp adr
    then .inr (executePrecomp evm adr) else .inl evm

def Frame.enter (f : Frame) : FrameEntry :=
  match f.inner.benvAfterTransfer with
  | .error e => .done (f.settleMsg (.error e))
  | .ok benv =>
    match executeCode.enter (f.inner.withBenv benv) with
    | .inl evm => .run evm
    | .inr raw => .done (f.settle raw)
```

`Frame.enter` absorbs `Msg.benvAfterTransfer` (`:3732`), `initEvm` (`:3725`)
and the precompile dispatch. `processCreateMessage.msg` is absorbed by
`Frame.ofCreate`.

### 3.3 Frame settle

```lean
def processMessage.settle (msg : Msg) (r : Except (String × State × AdrSet × Tra) Devm)
    : Except (String × State × AdrSet × Tra) Devm := do
  let evm ← r
  if evm.error.isSome then .ok (evm.rollback msg.benv.state msg.tenv.transientStorage)
  else .ok evm

def processCreateMessage.settle (msg : Msg) (r : …) : … := do
  let evm ← r
  if evm.error.isNone then
    match processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
    | .ok evm => .ok (evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩)
    | .error ⟨err, evm⟩ =>
      if isExceptionalHalt err then
        .ok (processCreateMessage.exceptionalHalt evm err msg.benv.state msg.tenv.transientStorage)
      else .error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩
  else .ok (evm.rollback msg.benv.state msg.tenv.transientStorage)

def Frame.settleMsg (f : Frame) (r : …) : … :=
  let r := processMessage.settle f.inner r
  if f.isCreate then processCreateMessage.settle f.outer r else r

def Frame.settle (f : Frame) (raw : Execution) : … :=
  f.settleMsg (executeCode.handleError raw)
```

Both settles are the identity on `.error`, which is what makes the
transfer-failure path of `Frame.enter` uniform.

### 3.4 Resume records

```lean
inductive Resume : Type
  | create (parent : Devm) (newAddress : Adr)
  | call   (parent : Devm) (outputIndex outputSize : Nat)

def Resume.run : Resume → Except (String × State × AdrSet × Tra) Devm → Execution
  | .create parent newAddress, r => do
    let child ← liftToExecution parent r
    if child.error.isSome then (incorporateChildOnError parent child child.output).push 0
    else (incorporateChildOnSuccess parent child []).push newAddress.toB256
  | .call parent outputIndex outputSize, r => do
    let child ← liftToExecution parent r
    let actualOutput := child.output.take outputSize
    if child.error.isSome then
      let evm2 ← (incorporateChildOnError parent child child.output).push 0
      .ok (evm2.memWrite outputIndex actualOutput)
    else
      let evm2 ← (incorporateChildOnSuccess parent child child.output).push 1
      .ok (evm2.memWrite outputIndex actualOutput)
```

**Six call-type instructions, two resume shapes.** The plan asks for a resume
record per call kind. There are only two, and this is a fact about the EVM,
not a shortcut: everything that distinguishes CALL from CALLCODE from
DELEGATECALL from STATICCALL — caller, target, code address, value, static
flag, transfer flag — is computed *before* the spawn and lives in the child
`Msg`; likewise CREATE vs CREATE2 differ only in `newAddress` and the salt/hash
gas, both settled before the spawn. Post-return work is
`incorporateChild*` + `push` (+ `memWrite` for the call family), so:

| instruction | frame | resume |
|---|---|---|
| CALL | `Frame.ofCall (callMsg …)` | `.call evm1 outputIndex outputSize` |
| CALLCODE | `Frame.ofCall (callMsg …)` | `.call evm1 outputIndex outputSize` |
| DELEGATECALL | `Frame.ofCall (callMsg …)` | `.call evm1 outputIndex outputSize` |
| STATICCALL | `Frame.ofCall (callMsg …)` | `.call evm1 outputIndex outputSize` |
| CREATE | `Frame.ofCreate (createMsg …)` | `.create devm newAddress` |
| CREATE2 | `Frame.ofCreate (createMsg …)` | `.create devm newAddress` |

`Resume` is **data**, consumed by the named top-level `Resume.run`; there is no
closure anywhere in the outcome types.

### 3.5 Step outcomes

```lean
inductive XStep : Type                      -- one call-type instruction, frame-locally
  | done  (ex : Execution)
  | spawn (frame : Frame) (rsm : Resume)

def XStep.ofExcept : Except (String × Devm) XStep → XStep
  | .error e => .done (.error e)
  | .ok s => s

inductive Step : Type                       -- one interpreter step
  | halt  (ex : Execution)
  | cont  (pc : Nat) (devm : Devm)
  | spawn (frame : Frame) (rsm : Resume) (pc : Nat)

def Step.ofExecution (pc : Nat) : Execution → Step
  | .error e => .halt (.error e)
  | .ok devm => .cont pc devm

def Step.ofJump : Except (String × Devm) (Nat × Devm) → Step
  | .error e => .halt (.error e)
  | .ok ⟨pc, devm⟩ => .cont pc devm

def XStep.toStep (pc : Nat) : XStep → Step
  | .done ex => Step.ofExecution pc ex
  | .spawn f rsm => .spawn f rsm pc
```

`XStep.ofExcept` is what lets each `Xinst.step` body be written as a plain
`Except (String × Devm) XStep` do-block, i.e. as a verbatim transcription of the
old `Fueled` body with the fuel removed.

### 3.6 The error payloads: two layers, two named conversions

The plan asks for "the unified internal error payload". **The design does not
unify them, deliberately**, and this is the one place where it argues against
the plan's phrasing rather than following it.

Unifying would require either changing the result type of `Rinst.run`,
`Jinst.run`, `Linst.run` and the precompiles — which is the plan's own stop
condition (non-goal: "any change to the instruction-semantics layer") — or
inserting an adapter at every instruction site, which is strictly worse than
what exists. What the flattening *can* do, and does, is turn the two payloads
into clean **layer types** with the conversions at exactly two named sites:

| type | meaning | who uses it |
|---|---|---|
| `Execution = Except (String × Devm) Devm` | intra-frame | `Evm.step`, `Ninst.step`, `Xinst.step`, `genericCall.step`, `genericCreate.step`, `exec` |
| `Except (String × State × AdrSet × Tra) Devm` | inter-frame | `Frame.enter`/`.settle`, `runFrame`, `executeCode`, `processMessage`, `processCreateMessage` |

* **out of a frame:** `Frame.settle` = `Frame.settleMsg ∘ executeCode.handleError`;
* **into the parent:** `Resume.run` applies `liftToExecution parent`.

The old code performs these five and two times respectively (§2.9). The
`String × State × AdrSet × Tra` payload is *reconstituted* exactly where it was
before — in `executeCode.handleError`'s `.error` arm and in
`processCreateMessage.settle`'s non-exceptional `chargeCodeGas` failure — and is
consumed exactly where it was before, in `liftToExecution`.

---

## 4. The driver

### 4.1 Definition

```lean
def exec : Evm → Nat → Fueled (String × Devm) Devm
  | _, 0 => Fueled.exhausted
  | evm, lim + 1 =>
    match evm.step with
    | .halt ex => Fueled.ofExcept ex
    | .cont pc devm => exec ⟨pc, evm.sta, devm⟩ lim
    | .spawn f rsm pc =>
      match f.enter with
      | .done r =>
        match rsm.run r with
        | .error e => Fueled.ofExcept (.error e)
        | .ok devm => exec ⟨pc, evm.sta, devm⟩ lim
      | .run cevm =>
        match (exec cevm lim).run with
        | .none => Fueled.exhausted
        | .some raw =>
          match rsm.run (f.settle raw) with
          | .error e => Fueled.ofExcept (.error e)
          | .ok devm => exec ⟨pc, evm.sta, devm⟩ lim
  termination_by _ lim => lim
```

Three recursion sites, all at fuel `lim` under `lim + 1`, all structural:

1. `.cont` — the next instruction of the same frame;
2. `.spawn`/`.run` — the child frame (`exec cevm lim`);
3. `.spawn` resume-ok — the next instruction after a returned call.

`evm.sta` is threaded unchanged, so it is a frame invariant; that is what makes
`evm.sta.depth` the frame's depth for §5.2.

The `match (exec cevm lim).run with` is the "run a child and capture its
result rather than propagate it" seam: the child's semantic error must become
the parent's `child` value, not the parent's error, while fuel exhaustion must
still propagate. `Fueled ε α = ExceptT ε Option α`, so `.run : Option (Except ε α)`
distinguishes exactly those two. It is written inline rather than as a
combinator with a function argument, so that no lambda containing a recursive
call appears in the body.

**Why not fewer or more.** Zero recursive functions is impossible (the language
has no other fixed point available here without well-founded recursion on gas,
which `depythonization-notes.md` §5 rules out). Two would arise from factoring
the duplicated three-line "resume then continue" tail into a helper that itself
calls `exec`; the duplication is three lines twice and is cheaper than a
mutual block, for ELeVM and for Blanc. A frame-stack (defunctionalized-stack)
driver would also be one function but would make the derivation relation
stack-shaped rather than tree-shaped, destroying the correspondence with
Blanc's existing `Exec` and its depth induction. **One driver.**

### 4.2 Wrappers (non-recursive)

```lean
def runFrame (f : Frame) (lim : Nat) : Fueled (String × State × AdrSet × Tra) Devm :=
  match f.enter with
  | .done r  => Fueled.ofExcept r
  | .run evm => Fueled.mapResult f.settle (exec evm lim)

def executeCode (msg : Msg) (lim : Nat) : Fueled (String × State × AdrSet × Tra) Devm :=
  match executeCode.enter msg with
  | .inr raw => Fueled.ofExcept (executeCode.handleError raw)
  | .inl evm => Fueled.mapResult executeCode.handleError (exec evm lim)

def processMessage       (msg : Msg) (lim : Nat) := runFrame (Frame.ofCall   msg) lim
def processCreateMessage (msg : Msg) (lim : Nat) := runFrame (Frame.ofCreate msg) lim
```

All three keep their **exact current names, argument order and types**. This is
not cosmetic: `Blanc/Solvent.lean` states ten lemmas directly about
`executeCode msg lim = .ok evm`, `processMessage msg lim = .ok evm` and
`processCreateMessage msg lim = .ok evm` (`:4507`, `:4591`, `:5206`, `:5239`,
`:5264`, `:5732`, `:5847`, …). Those statements survive verbatim; only their
proofs change, and they get *shorter*, because the `induction lim` /
`rw [executeCode]` fuel case split disappears.

### 4.3 New named barriers

Per design decision 8 and the `209e710` precedent, every new definition a proof
will unfold gets a name rather than an inline literal. The new names are
`Frame`, `Frame.ofCall`, `Frame.ofCreate`, `Frame.enter`, `Frame.settle`,
`Frame.settleMsg`, `FrameEntry`, `Resume`, `Resume.run`, `XStep`,
`XStep.ofExcept`, `XStep.toStep`, `Step`, `Step.ofExecution`, `Step.ofJump`,
`Evm.step`, `Ninst.step`, `Xinst.step`, `genericCall.step`,
`genericCreate.step`, `executeCode.enter`, `processMessage.settle`,
`processCreateMessage.settle`, `runFrame`, and **`createMsg`** — the
last being the promotion of `genericCreate`'s inline 17-field record literal
(`:3899-3916`) to a named function, exactly parallel to `callMsg`'s
"factored out as a named definition to prevent context blowup in proofs".

### 4.4 Fuel accounting — branch by branch

Write `E` for the fuel argument of the old `exec` and `A` for the fuel argument
of the new one, both taken at the same instruction of the same frame. Both
functions are monotone in fuel (more fuel never turns a completed run into
exhaustion), so it suffices to show `A ≥ E` everywhere given the seeds.

**Within a frame — equal.**

| event | old tower | new driver |
|---|---|---|
| enter instruction `i` | matches `E_i = lim + 1`, needs `E_i ≥ 1` | matches `A_i = lim + 1`, needs `A_i ≥ 1` |
| `.last` / decode failure / instruction error | returns at `E_i ≥ 1` | `.halt` at `A_i ≥ 1` |
| `.reg`, `.push`, `.jump`, non-spawning `.exec` → next instruction | `E_{i+1} = E_i - 1` | `.cont` → `A_{i+1} = A_i - 1` |
| spawning `.exec` → next instruction after the call returns | `E_{i+1} = E_i - 1` (the old `exec` continues with the same `lim` it gave `n.run`) | resume-ok → `exec … lim`, so `A_{i+1} = A_i - 1` |

So *per instruction the two burn exactly one unit*. The `Ninst.run`,
`Xinst.run`, `genericCall`, `genericCreate` layers used to burn a unit each;
those layers are now fuel-free, so the saving is entirely at frame entry.

**Frame entry — strictly cheaper.**

| step | old | new |
|---|---|---|
| `exec` → `Ninst.run` | 1 | 0 (`Evm.step` is pure) |
| `Ninst.run` → `Xinst.run` | 1 | 0 |
| `Xinst.run` → `genericCall` / `genericCreate` | 1 | 0 |
| `genericCall` → `processMessage` / `genericCreate` → `processCreateMessage` | 1 | 0 |
| `processCreateMessage` → `processMessage` (create only) | 1 | 0 (`Frame.ofCreate`) |
| `processMessage` → `executeCode` | 1 | 0 (`Frame.enter`) |
| `executeCode` → child frame (`exec cevm lim`) | 1 | 1 |
| **total** | **6 (call) / 7 (create)** | **1** |

i.e. `E_child = E_parent,i - 6` (call) or `- 7` (create), while
`A_child = A_parent,i - 1`.

**Seeds — the new driver starts with more.**

| entry point | old | new |
|---|---|---|
| `processMessageCall.call` | `processMessage (gas+50)` → `executeCode (gas+49)` → `exec (gas+48)` | `runFrame … (gas+50)` → `exec … (gas+50)` |
| `processMessageCall.create` | `processCreateMessage (gas+50)` → `processMessage (gas+49)` → `executeCode (gas+48)` → `exec (gas+47)` | `runFrame … (gas+50)` → `exec … (gas+50)` |

**Conclusion.** `A_0 - E_0 ∈ {2, 3}` at the outermost frame, and the difference
grows by 5 (call) or 6 (create) at every nesting level, while within a frame the
difference is constant. Hence `A ≥ E` at every execution point, with equality
nowhere; **the new driver consumes strictly less fuel than the old code at every
point, and never more.** `msg.gas + 50` sufficiency is therefore preserved and
strictly improved, and no new recursion site was introduced that the old code
did not already pay for. The two *fixed* early exits that used to cost 3–4 units
of fuel before short-circuiting (depth-0 in `genericCall`, and the
balance/nonce/depth exit in `genericCreate`) now cost one, which is the largest
single per-instruction improvement.

Empirical enforcement, per the plan: `scripts/check.sh --depth` at every
internal checkpoint of Step 2, plus the full suites.

---

## 5. The Blanc target

### 5.1 The relation keeps the name `Exec` — this is forced

`Blanc/Solvent.lean:4058`:

```lean
theorem weth_inv_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  → …
```

`Exec` appears in a **protected statement**, which the plan requires to be
textually unchanged. So the generic derivation relation must be `Exec` itself,
with the index shape `Nat → Sevm → Devm → Execution → Type`. Since the driver
is indexed by `Evm = ⟨pc, sta, dyna⟩`, this costs nothing.

```lean
inductive Exec : Nat → Sevm → Devm → Execution → Type
  | halt {pc sevm devm ex} :
      Evm.step ⟨pc, sevm, devm⟩ = .halt ex →
      Exec pc sevm devm ex
  | cont {pc sevm devm pc' devm' ex} :
      Evm.step ⟨pc, sevm, devm⟩ = .cont pc' devm' →
      Exec pc' sevm devm' ex →
      Exec pc sevm devm ex
  | doneErr {pc sevm devm f rsm pc' r e} :
      Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
      f.enter = .done r → rsm.run r = .error e →
      Exec pc sevm devm (.error e)
  | doneOk {pc sevm devm f rsm pc' r devm' ex} :
      Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
      f.enter = .done r → rsm.run r = .ok devm' →
      Exec pc' sevm devm' ex →
      Exec pc sevm devm ex
  | runErr {pc sevm devm f rsm pc' cevm raw e} :
      Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
      f.enter = .run cevm →
      Exec cevm.pc cevm.sta cevm.dyna raw →
      rsm.run (f.settle raw) = .error e →
      Exec pc sevm devm (.error e)
  | runOk {pc sevm devm f rsm pc' cevm raw devm' ex} :
      Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' →
      f.enter = .run cevm →
      Exec cevm.pc cevm.sta cevm.dyna raw →
      rsm.run (f.settle raw) = .ok devm' →
      Exec pc' sevm devm' ex →
      Exec pc sevm devm ex
```

Six constructors instead of eight, and — the point of the whole arc — every
premise other than a sub-derivation is an **equation about a non-recursive
function**. The eight hand-maintained mirrors
(`ExecuteCode`/`ProcessMessage`/`ProcessCreateMessage`/`GenericCall`/
`GenericCreate`/`Xinst.Run`/`Ninst.Run'`) are no longer part of the definition
of the relation at all; they become derived one-liners (§5.4).

### 5.2 Depth strong induction is recovered

`Common.lean:169-192` (`Exec.Pred`, `Exec.Fa`, `Fortify`, `Exec.strong_rec`)
transfers **verbatim**: it is generic in the constructors, performing
`Nat.strongRecOn` on `sevm.depth`, and only requires that users supply the
strict decrease when they apply the inner hypothesis to a child derivation.
That obligation is discharged once, by a new lemma:

```lean
lemma Step.spawn_depth_lt {pc sevm devm f rsm pc'} :
    Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc' → f.inner.depth < sevm.depth

lemma Frame.enter_run_depth {f cevm} :
    f.enter = .run cevm → cevm.sta.depth = f.inner.depth
```

The first holds because every `.spawn` is guarded: `genericCall.step`
short-circuits on `sevm.depth = 0`, `genericCreate.step` short-circuits on
`… ∨ sevm.depth = 0`, and both `callMsg` and `createMsg` set
`depth := sevm.depth - 1`; `processCreateMessage.msg` (applied by
`Frame.ofCreate`) touches only `benv`, so it preserves `depth`. The second holds
because `Frame.enter`'s `.run` yields `initEvm (f.inner.withBenv benv)`,
`initSevm` copies `depth`, and `withBenv` does not touch it. The pilot proves
exactly the CALL instance of the first lemma (§6, `invCallBind`/`invCallLet`),
so the shape is validated, not assumed (for a call frame `outer = inner`, which
is why the pilot states it with `f.outer`).

### 5.3 Adequacy and monotonicity — one theorem each

Replacing today's eight-field `Saturation` record (`Semantics.lean:976-1001`),
its 90-line `saturation` proof (`:1016-1104`), the `eee_bind` and
`efg_step_splitXl` macros, and the eight `of_*`/`of_*'` pairs:

```lean
-- monotonicity: one induction on `lim`, statement quantified over `Evm`
--               (replaces the 8-field `Saturation` record and `saturation`)
theorem exec_saturates (lim : Nat) : ∀ evm : Evm, Saturates lim (exec evm)

-- adequacy, executable → relational: statement UNCHANGED, Semantics.lean:1774
@[reducible] def of_exec :
    ∀ (lim pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      (exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept exn) →
      Nonempty (Exec pc sevm devm exn)

-- adequacy, relational → executable: statement UNCHANGED, Semantics.lean:1419
lemma of_exec' : ∀ pc sevm devm exn, Exec pc sevm devm exn →
    ∃ lim, ∀ lim' > lim, exec ⟨pc, sevm, devm⟩ lim' = Fueled.ofExcept exn

-- the interface Common/Solvent consume: statement UNCHANGED, Semantics.lean:1826
lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔
      ∃ lim, exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept exn
```

Keeping the driver's name means **all of these statements are unchanged**; only
the proofs shrink. `Saturates` (`Semantics.lean:973`) survives unchanged as a
definition; the eight-field `Saturation` record and its 90-line proof are
replaced by the single `exec_saturates`, a plain induction on `lim` with the
statement quantified over `evm` (the child recursion needs the induction
hypothesis at the *same* `lim`, which the quantifier supplies). `of_exec` stays
`Nat.strongRec` on `lim` exactly as today, but with six cases and no
bind-walking.

### 5.4 The former mirrors, as thin wrappers

`Xlot` keeps its name and its `Option`-of-a-suspension shape, retyped from the
old triple to the pair the driver actually suspends on:

```lean
def Xlot : Type := Option (Evm × Execution)          -- was Option (Sevm × Devm × Execution)

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨evm, ex⟩ => Nonempty (Exec evm.pc evm.sta evm.dyna ex)

def RunFrame (f : Frame) (xl : Xlot) (r : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  match f.enter with
  | .done r'  => xl = .none ∧ r = r'
  | .run evm  => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ r = f.settle raw
```

| former mirror | new definition | statement preserved? |
|---|---|---|
| `ProcessMessage msg xl ex` | `RunFrame (Frame.ofCall msg) xl ex` | **yes** — same name, arity, argument types |
| `ProcessCreateMessage msg xl ex` | `RunFrame (Frame.ofCreate msg) xl ex` | **yes** |
| `ExecuteCode msg xl ex` | `match executeCode.enter msg with \| .inr raw => xl = .none ∧ ex = executeCode.handleError raw \| .inl evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ ex = executeCode.handleError raw` | **yes** |
| `Xinst.Run sevm devm x xl ex` | `match Xinst.step sevm devm x with \| .done ex' => xl = .none ∧ ex = ex' \| .spawn f rsm => ∃ r, RunFrame f xl r ∧ ex = rsm.run r` | **yes** |
| `GenericCall sevm devm gas … xl ex` | same shape over `genericCall.step` | **yes** (15 arguments unchanged) |
| `GenericCreate sevm devm endowment newAddress mi ms xl ex` | same shape over `genericCreate.step` | **yes** |
| `Ninst.Run' pc sevm devm n xl ex` | `match Ninst.step ⟨pc, sevm, devm⟩ n with …` | **yes** |
| `Ninst.Run sevm devm n devm'` | unchanged text (`∃ xl, xl.Filled ∧ ∃ pc, Ninst.Run' pc sevm devm n xl (.ok devm')`) | **yes** |
| `Func.Run`, `Prog.Run` | unchanged | **yes** |
| `Jinst.Run`, `Linst.Run`, the five `*.At` predicates, `Devm.Rel(s)`, `Devm.Burn`, `Devm.PopBurn`, `Stack.Push/Pop`, `Except.Split`, `Except.SplitXl`, `ExistsEq` | unchanged | **yes** |
| `Exec` | §5.1 — same name and indices, six new constructors | **name and indices yes; constructors no** |

**Statements that cannot be preserved**, listed as the plan requires:

1. **`Exec`'s eight constructors** (`invOp`, `nextNoneErr`, `nextSomeErr`,
   `nextNoneRec`, `nextSomeRec`, `jumpErr`, `jumpRec`, `last`) are replaced by
   the six of §5.1. Consumer surface, grep-measured on `36c4ec3`:
   `Semantics.lean` 14 lines (the definition plus the three intro sites in
   `of_exec`), `Common.lean` 64 lines in **seven** regions —
   `480-498`, `719-755`, `857-906`, `1158-1167`, `5889-5899`, `6456-6572`,
   `6598-6612` — and **zero** lines in `Solvent.lean` and `Weth.lean`.
   *Mitigation, to be attempted first in Step 3:* derive an eliminator
   `Exec.instCases` whose case names and argument shapes reproduce the current
   eight constructors, by inverting `Evm.step` once. Then the seven Common.lean
   regions are repaired by swapping the eliminator, not by rewriting. Fallback
   if the derived eliminator is awkward: repair the seven regions directly.
   This is the single largest Step-3 risk and is where the ★★★★★ rating lives.
2. **`Xlot`'s type** changes from `Option (Sevm × Devm × Execution)` to
   `Option (Evm × Execution)`. All *statements* mentioning `Xlot` survive
   textually (`Xlot`, `Xlot.Filled`, `Xlot.Good`, `Xlot.Good'`,
   `Xlot.InvGetCode`, `Xlot.good_mono`, …: 41 lines in `Semantics.lean`,
   48 in `Common.lean`, 25 in `Solvent.lean`), but the ones that destructure the
   triple need their proofs adjusted to the pair.
3. **`Saturation`/`saturation`** (but not `Saturates`, which survives) and the `eee_bind`,
   `efg_step_splitXl`, `efg_step_exec`, `efg_end_exec`, `efg_step_exists`,
   `efg_step_early`, `efg_step_ite`, `bind_step_good`, `okStep1`, `bind_step'`
   macros are deleted outright; grep-confirmed that nothing in `Common.lean`,
   `Solvent.lean` or `Weth.lean` names any of them.
4. **`of_execute_code'`, `of_process_message'`, `of_process_create_message'`,
   `of_generic_create'`, `of_generic_call'`, `Xinst.run_eq_of_run`,
   `Ninst.run_of_run'`, `of_executeCode`, `of_genericCreate`, `of_genericCall`,
   `Xinst.run_of_run_eq`, `Ninst.run_of_run_eq`** collapse into the two
   adequacy theorems of §5.3 and are deleted. `of_exec`, `of_exec'` and
   `exec_iff_exec_eq` keep their statements (§5.3). `of_processMessage` and
   `of_processCreateMessage` are consumed by `Common.lean:9856` and `:9865`, so
   they are **retained as derived corollaries with unchanged statements**.

The four protected theorems (`weth_inv_solvent`,
`stateTransition_inv_solvent`, `chain_inv_solvent`,
`addBlockToChain_inv_solvent`) and the generic `…With/…At/…Using` variants
mention only `Exec` (in `weth_inv_solvent`) and pipeline-level names; with
`Exec`'s name and indices preserved, **all four statements are unchanged**.

---

## 6. The pilot and the term-surface convention

### 6.1 What was built

`scripts/flatten-pilot.lean`, outside the library root (`lakefile.lean` declares
`lean_lib «Elevm»` with the default single-root glob, so `lake build` is
untouched — verified: 1760 jobs before and after). It contains the real types of
§3, the real driver of §4.1, and:

* an **ordinary-instruction path** — `evmStepBind` / `evmStepLet`: decode,
  `.last`, `.jump`, PUSH (charge + push), REG, and dispatch into the call path;
* a **call-type path through spawn/resume** — `xstepCallBind` / `xstepCallLet`
  (the full CALL body, 19 seams) over `genericCallStepBind` /
  `genericCallStepLet`, producing a `Frame.ofCall` + `Resume.call` spawn;
* four **toy inversion proofs** of the shape Blanc performs — `invPushBind` /
  `invPushLet` recover the two seams of a successful PUSH; `invCallBind` /
  `invCallLet` prove `f.outer.depth < sevm.depth` from a spawn, which is exactly
  the §5.2 side condition and requires walking the entire CALL body;
* a **driver inversion** `invDrive`, the three-way case split Blanc's adequacy
  proof performs at every recursion site.

Each pair uses an **identical tactic script**, so the only variable is the
idiom. Elaboration is clean: no errors, no warnings, no `sorry`, no `admit`.

### 6.2 What was measured

* `heartbeats` — `#count_heartbeats in`, a deterministic elaboration-cost
  counter, one per declaration.
* `body` — size of the stored definition value (number of `Expr` nodes): what a
  proof faces before unfolding.
* `zeta` — size after **all** `let`s are substituted away: what a proof faces
  after `simp only [thatDef]`, i.e. where plain `let`s pay their duplication.
  For the bind idiom there are no `let`s, so `zeta = body`.

| declaration | heartbeats | `body` | `zeta` |
|---|---:|---:|---:|
| `genericCallStepBind` | 142 | 405 | 405 |
| `genericCallStepLet` | **99** | **182** | **195** |
| `xstepCallBind` | 899 | 1831 | 1831 |
| `xstepCallLet` | **798** | **1335** | **1503** |
| `evmStepBind` | 217 | 289 | 289 |
| `evmStepLet` | **187** | **247** | **281** |
| `drive` | 1540 | — | — |
| `invPushBind` | 258 | — | — |
| `invPushLet` | **224** | — | — |
| `invCallBind` | 6319 | — | — |
| `invCallLet` | **6246** | — | — |
| `invDrive` | 197 | — | — |

Reproduce with `lake env lean scripts/flatten-pilot.lean` (~2 s warm).

### 6.3 Reading, and the convention this fixes

The `← .ok <|` seam is not free: each one costs an `Except.ok`, an
`Except.bind`, and a lambda. On the CALL body that overhead is **496 `Expr`
nodes** (1831 vs 1335, +37 %). Zeta-substituting every `let` in the plain-`let`
version costs **168 nodes** (1335 → 1503, +12.6 %). So the duplication the
seams exist to prevent is, for these bodies, a third of what the seams
themselves cost: the fully-unfolded `let` version (1503) is still **18 % smaller
than the un-unfolded bind version** (1831), and the `let` idiom also wins on
elaboration cost for both definitions (−11 % on CALL) and inversion proofs
(−13 % on PUSH, −1 % on CALL).

The reason is structural and worth recording, because it bounds the result:
every pure intermediate in these bodies is used **once or twice**. `devm` is
threaded linearly; `extendCost` appears twice; `msgCallStipend` twice. Zeta
duplication is linear in use count, so with use counts near one it is small.
This is *not* the situation `209e710` fixed — there the duplicated things were
naked `{x with …}` record updates nested inside each other, where each
substitution multiplied.

**Convention fixed by this measurement, binding on Step 2:**

1. In the new step/enter/settle bodies, **pure intermediates are plain `let`s**;
   `←` binds are reserved for genuinely fallible operations (`Devm.pop`,
   `popToNat`, `popToAdr`, `chargeGas`, `Devm.push`, `Except.assert`,
   `assertDynamic`, `benvAfterTransfer`, `chargeCodeGas`).
2. **Named abstraction barriers remain the primary size instrument**, not the
   let/bind choice: `callMsg`, the new `createMsg`, `Frame.*`, `Resume.run`,
   `*.settle`, `*.enter` are all barriers, and behind a barrier the idiom is
   irrelevant. Rule 1 is a tiebreak *inside* a barrier, nothing more.
3. **No blanket reconversion.** The existing `← .ok <|` seams outside the
   flattened core (`Rinst.runCore`, the precompiles, the upper pipeline) are not
   touched. Design decision 8 forbids it and this measurement does not license
   it: the result is about bodies whose intermediates are near-linearly used,
   which is a property of the flattened step functions, not of ELeVM at large.
4. If a Step-2 body turns out to have an intermediate used **three or more**
   times, keep that one as a seam. Record any such site in the Step-2 report.

### 6.4 Honest limits of the pilot

* Only CALL is transcribed; the other five call-type instructions are stubbed.
  The pilot measures the *idiom*, not the transcription. CALL is the longest of
  the six, so it is the right representative.
* `zeta` is a proxy for post-`simp only` goal size, not a measurement of an
  actual proof context; the inversion-proof heartbeats are the end-to-end check
  and they agree with it.
* The margins on the CALL inversion (6246 vs 6319, ~1 %) are small. The decision
  rests on the definition-level numbers, which are large and consistent, and on
  the fact that the `let` idiom is never worse on any of the six measurements.

---

## 7. Stop conditions — none triggered

The plan names two stop conditions for Step 1.

* *"the single-driver design cannot express the old semantics without touching
  the instruction layer"* — **not triggered.** One driver expresses all eight
  functions. `Rinst.runCore`/`run`, `Jinst.runCore`/`run`, `Linst.run`,
  `executePrecomp`, `ByteArray.getInst`, the `Footprint`/`liftMach*` machinery,
  and every gas constant keep their names, types and behaviour; the step
  functions call them exactly as `Ninst.run`/`exec` did.
* *"preserving any protected-theorem-relevant statement appears impossible"* —
  **not triggered**, but it came close: `weth_inv_solvent` mentions `Exec`, so
  the generic relation is forced to keep that name and index shape (§5.1). It
  can, and does.

One item is flagged for the user's awareness rather than as a stop: §3.6
declines the plan's "unified internal error payload", because unifying the two
payloads would require changing the instruction layer's result types, which is
the plan's own non-goal. The design instead reduces the conversions from seven
sites to two named ones and keeps both payload types. If the intended reading
of the plan was stricter, say so before Step 2 begins.

---

## 8. Verification for this step

| gate | command | verdict |
|---|---|---|
| library build | `lake build` | **PASS** — 1760 jobs, identical job count with the pilot present |
| U256 canary | `scripts/check-u256.sh` | **PASS** — 21,593/21,593 |
| pilot elaboration | `lake env lean scripts/flatten-pilot.lean` | **PASS** — no errors, no warnings, no `sorry`/`admit`/`ofReduce*` |

No production file was modified. No fixture suite was run: this step changes no
semantics, so `--depth` and the mainnet suites have nothing to discriminate;
they begin at Step 2's first checkpoint.

---

## 9. Handoff to Step 2

Implement §2–§4 exactly:

1. add `Frame`, `FrameEntry`, `Resume`, `XStep`, `Step` and their helpers;
2. add `createMsg`; add `executeCode.enter`, `processMessage.settle`,
   `processCreateMessage.settle`, `Frame.enter`, `Frame.settle/settleMsg`;
3. add `genericCall.step`, `genericCreate.step`, `Xinst.step`, `Ninst.step`,
   `Evm.step` — verbatim transcriptions, respecting the §2.6 hazard note;
4. rewrite `exec`'s body as the §4.1 driver and add `runFrame`;
   **checkpoint 1** — new core alongside the old block, `#guard`s on the seven representative states the plan lists, gates:
   build, U256, DEPTH, SMOKE, current smoke;
5. rewrite `executeCode`, `processMessage`, `processCreateMessage` as the §4.2
   wrappers, delete the mutual block and the now-dead `Fueled` *call sites*
   (keeping the `Fueled` namespace per §2.9), leaving
   `processMessageCall.call/.create` textually unchanged; **checkpoint 2** —
   full gate battery plus the one authorised run each of current prague, osaka,
   transitions; commit and push, that commit is Step 3's pin target.

Follow the §6.3 convention. Run `--depth` after every substantive edit; any
classification change is a stop-and-diagnose.
