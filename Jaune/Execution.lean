import Jaune.Precompiles

namespace Jaune

open Jaune


private def rlpTags : List String :=
  [ rlpStructureTag, rlpFixedWidthTag, rlpFieldOverflow64Tag,
    rlpFieldOverflow256Tag, rlpLeadingZerosTag,
    rlpWithdrawalsNotReadTag, rlpRoundTripTag ]

-- The tags are distinct, and none is a prefix of another, so no rendered
-- decode reason can be read as another by a `" : "`-delimited reader.
#guard rlpTags.eraseDups.length = 7
#guard rlpTags.all fun t => (rlpTags.filter fun u => t.isPrefixOf u).length = 1


/-- The reason of a failing strict decode, for the boundary guards below:
constructor identity is the discriminant now, so the guards match reasons
rather than reading rendered text back. -/
private def failsAs {α : Type} (p : DecodeError → Bool) :
    Except DecodeError α → Bool
  | .error e => p e
  | .ok _ => false

private def isFixedWidth : DecodeError → Bool
  | .fixedWidth _ => true | _ => false
private def isOverflow64 : DecodeError → Bool
  | .fieldOverflow64 _ => true | _ => false
private def isOverflow256 : DecodeError → Bool
  | .fieldOverflow256 _ => true | _ => false
private def isLeadingZeros : DecodeError → Bool
  | .leadingZeros _ => true | _ => false

-- Fixed-width fields: both the short and the long side are width errors.
#guard (Bytes.toRlpFixed "root" 32 (List.replicate 32 (0x11 : UInt8))).toOption.isSome
#guard failsAs isFixedWidth (Bytes.toRlpFixed "root" 32 (List.replicate 31 (0x11 : UInt8)))
#guard failsAs isFixedWidth (Bytes.toRlpFixed "root" 32 (List.replicate 33 (0x11 : UInt8)))
-- The renderer template for the fixed-width family, pinned end to end once.
#guard (Bytes.toRlpFixed "root" 32 (List.replicate 31 (0x11 : UInt8)))
  = .error (.fixedWidth (.text "root must be exactly 32 bytes, but is 31"))

-- 64-bit scalars: accepted widths convert exactly, nine bytes is an overflow
-- rather than a truncation, and a leading zero is a distinct reason from an
-- overflow. This is the withdrawal-index case.
#guard (Bytes.toRlpB64 "index" []).toOption.map UInt64.toNat = some 0
#guard (Bytes.toRlpB64 "index" (List.replicate 8 (0xFF : UInt8))).toOption.map UInt64.toNat
  = some (2 ^ 64 - 1)
#guard failsAs isOverflow64
  (Bytes.toRlpB64 "index" (0x01 :: List.replicate 8 (0x00 : UInt8)))
#guard failsAs isLeadingZeros (Bytes.toRlpB64 "index" [0x00, 0x01])
#guard ¬ failsAs isOverflow64 (Bytes.toRlpB64 "index" [0x00, 0x01])
#guard ¬ failsAs isLeadingZeros
  (Bytes.toRlpB64 "index" (0x01 :: List.replicate 8 (0x00 : UInt8)))

-- 256-bit scalars: same reasons, one width up, under the 256-bit overflow
-- constructor.
#guard (Bytes.toRlpB256 "amount" (List.replicate 32 (0xFF : UInt8))).toOption.map B256.toNat
  = some (2 ^ 256 - 1)
#guard failsAs isOverflow256
  (Bytes.toRlpB256 "amount" (List.replicate 33 (0x01 : UInt8)))
#guard failsAs isLeadingZeros (Bytes.toRlpB256 "amount" [0x00, 0x01])
#guard (Bytes.toRlpNat "value" 32 (List.replicate 32 (0xFF : UInt8))).toOption
  = some (2 ^ 256 - 1)
#guard failsAs isOverflow256 (Bytes.toRlpNat "value" 32 (List.replicate 33 (0x01 : UInt8)))
-- The renderer templates for both scalar families and the canonicality rule.
#guard (Bytes.toRlpB64 "index" (0x01 :: List.replicate 8 (0x00 : UInt8)))
  = .error (.fieldOverflow64
      (.text "index scalar is 9 bytes, exceeding its 8-byte width"))
#guard (Bytes.toRlpB64 "index" [0x00, 0x01])
  = .error (.leadingZeros
      (.text "index scalar 0x0001 is not canonically encoded (leading zero byte)"))

-- Addresses and optional receivers: a width error, never a silent creation.
#guard (Bytes.toRlpAdr "recipient" (List.replicate 20 (0x11 : UInt8))).toOption.isSome
#guard failsAs isFixedWidth (Bytes.toRlpAdr "recipient" (List.replicate 19 (0x11 : UInt8)))
#guard failsAs isFixedWidth (Bytes.toRlpAdr "recipient" (List.replicate 21 (0x11 : UInt8)))
#guard failsAs isFixedWidth (Bytes.toRlpAdr "recipient" [])
#guard (Bytes.toRlpReceiver "receiver" []).toOption = some none
#guard (Bytes.toRlpReceiver "receiver" (List.replicate 20 (0x11 : UInt8))).toOption.isSome
#guard failsAs isFixedWidth (Bytes.toRlpReceiver "receiver" (List.replicate 21 (0x11 : UInt8)))

-- A structure failure is its own reason, not a width or overflow one, and its
-- render is byte-for-byte the retired string helper's.
#guard DecodeError.structure "block" "expected a 4-item list"
  = .rlpStructure (.text "block : expected a 4-item list")
#guard (DecodeError.structure "block" "expected a 4-item list").render
  = "RlpStructureError : block : expected a 4-item list"

def Inst.toOpString : Inst → String
  | .next n => n.toOpString
  | .jump j => j.toString
  | .last l => l.toString

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def State.getStor (w : State) (a : Adr) : Stor := (w.get a).stor
def State.getNonce (w : State) (a : Adr) : UInt64 := (w.get a).nonce
def State.getCode (w : State) (a : Adr) : ByteArray := (w.get a).code

def isValidDelegation (code: ByteArray) : Prop :=
  code.size = eoaDelegatedCodeLength ∧
  code.sliceD 0 3 (0 : UInt8) = eoaDelegationMarker

instance {code} : Decidable (isValidDelegation code) := instDecidableAnd

def getDelegatedCodeAddress (code : ByteArray) : Option Adr :=
  if isValidDelegation code
  then
    let adrBytes := code.sliceD eoaDelegationMarker.length 20 (0 : UInt8)
    adrBytes.toAdr?
  else none

instance : Inhabited Adr := ⟨0⟩

def accessDelegation (devm : Devm) (adr : Adr) :
  Bool × Adr × ByteArray × Nat × Devm :=
  let state := devm.state
  let code := state.getCode adr
  -- P0.6 item 3: the delegated address is extracted by the total match below,
  -- never by a partial projection. `getDelegatedCodeAddress` answers `some`
  -- exactly on valid delegation designators, so the `none` arm is the ordinary
  -- no-delegation path.
  match getDelegatedCodeAddress code with
  | some adr =>
    let accessGasCost := accessCost adr devm.accessedAddresses
    let devm := addAccessedAddress devm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, devm⟩
  | none => ⟨false, adr, code, 0, devm⟩

def processCreateMessage.msg (msg : Msg) : Msg :=
  let adr := msg.currentTarget
  let benv := msg.benv.setStor adr .empty
  let benv := addCreatedAccount benv adr
  let benv := benv.incrNonce adr
  msg.withBenv benv

def processCreateMessage.chargeCodeGas (rules : ForkRules) (devm : Devm) :
    Execution :=
  let contractCode := devm.output
  let contractCodeGas := contractCode.length * gasCodeDeposit
  match contractCode with
  | 0xEF :: _ => .error ⟨.halt (.invalidContractPrefix .none), devm⟩
  | _ => do
    let devm ← chargeGas contractCodeGas devm
    if rules.code.maxCodeSize < contractCode.length
    then .error ⟨.halt (.outOfGas .none), devm⟩
    else .ok devm

def processCreateMessage.exceptionalHalt
    (devm : Devm) (reason : ExceptionalHalt) (st : State) (tra : Tra) : Devm :=
  let devm := (devm.rollback st tra).withGasLeft 0
  devm.setMeta {devm.meta with output := [], error := .some (.halt reason)}

def initSevm (msg : Msg) : Sevm :=
  {
    caller := msg.caller
    target := msg.target
    currentTarget := msg.currentTarget
    gas := msg.gas
    value := msg.value
    data := msg.data
    codeAddress := msg.codeAddress
    code := msg.code
    depth := msg.depth
    shouldTransferValue := msg.shouldTransferValue
    isStatic := msg.isStatic
    disablePrecompiles := msg.disablePrecompiles
    benvStat := msg.benv.stat
    tenvStat := msg.tenv.stat
  }

def initDevm (msg : Msg) : Devm :=
  {
    mach := {
      stack := []
      memory := .empty
      gasLeft := msg.gas
    }
    «meta» := {
      logs := []
      refundCounter := 0
      output := []
      accountsToDelete := .emptyWithCapacity
      returnData := []
      error := .none
      accessedAddresses := msg.accessedAddresses
      accessedStorageKeys := msg.accessedStorageKeys
      createdAccounts := msg.benv.createdAccounts
    }
    world := {
      state := msg.benv.state
      transientStorage := msg.tenv.transientStorage
    }
  }

def initEvm (msg : Msg) : Evm :=
  {
    pc := 0
    sta := initSevm msg
    dyna := initDevm msg
  }

def Msg.benvAfterTransfer (msg : Msg) :
    Except (EvmError × State × AdrSet × Tra) Benv :=
  if msg.shouldTransferValue then do
    let benv ←
      (msg.benv.subBal msg.caller msg.value).toExcept
        ⟨.internal (.assertion .none), msg.benv.state, msg.benv.createdAccounts,
          msg.tenv.transientStorage⟩
    .ok <| benv.addBal msg.currentTarget msg.value
  else
    .ok msg.benv

def executeCode.handleError :
    Execution → Except (EvmError × State × AdrSet × Tra) Devm
  | .ok evm => .ok evm
  | .error ⟨.halt reason, evm⟩ =>
    let evm := evm.withGasLeft 0
    .ok (evm.setMeta {evm.meta with output := [], error := some (.halt reason)})
  | .error ⟨.revert, evm⟩ => .ok (evm.withError (some .revert))
  | .error ⟨.crypto reason, evm⟩ =>
    .error ⟨.crypto reason, evm.state, evm.createdAccounts, evm.transientStorage⟩
  | .error ⟨.internal reason, evm⟩ =>
    .error ⟨.internal reason, evm.state, evm.createdAccounts, evm.transientStorage⟩

def Execution.withPc (pc : Nat) (exn : Execution) :
     Except (EvmError × Devm) (Nat × Devm) := do
  let devm ← exn
  .ok ⟨pc, devm⟩

def Ninst.size : Ninst → Nat
  | reg _ => 1
  | exec _ => 1
  | push xs _ => xs.length + 1

-- the message passed to the sub-call performed by a call-type instruction.
-- factored out as a named definition to prevent context blowup in proofs.
def callMsg
    (sevm: Sevm)
    (evm1: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (calldata: Bytes)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Msg :=
  {
    benv := {state := evm1.state, createdAccounts := evm1.createdAccounts, stat := sevm.benvStat}
    tenv := {transientStorage := evm1.transientStorage, stat := sevm.tenvStat}
    caller := caller
    target := target
    gas := gas
    currentTarget := target
    value := value
    data := calldata
    codeAddress := codeAddress
    code := code
    depth := sevm.depth - 1
    shouldTransferValue := shouldTransferValue
    isStatic := isStaticcall || sevm.isStatic
    accessedAddresses := evm1.accessedAddresses
    accessedStorageKeys := evm1.accessedStorageKeys
    disablePrecompiles := disablePrecompiles
  }

/-!
Flattened interpreter core.  All frame-local definitions below are
non-recursive and fuel-free; `execFueled` is the single fueled driver.
-/

/-- The message passed to a CREATE/CREATE2 child.  This named barrier is the
CREATE-family counterpart of `callMsg`. -/
def createMsg
    (sevm : Sevm) (devm : Devm) (createGas : Nat) (endowment : B256)
    (newAddress : Adr) (calldata : Bytes) : Msg :=
  {
    benv := Benv.mk devm.state devm.createdAccounts sevm.benvStat
    tenv := {transientStorage := devm.transientStorage, stat := sevm.tenvStat}
    caller := sevm.currentTarget
    target := .none
    gas := createGas
    value := endowment
    data := []
    code := .mk <| .mk calldata
    currentTarget := newAddress
    depth := sevm.depth - 1
    codeAddress := .none
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := devm.accessedAddresses
    accessedStorageKeys := devm.accessedStorageKeys
    disablePrecompiles := false
  }

structure Frame : Type where
  outer : Msg
  inner : Msg
  isCreate : Bool

def Frame.ofCall (msg : Msg) : Frame := ⟨msg, msg, false⟩

def Frame.ofCreate (msg : Msg) : Frame :=
  ⟨msg, processCreateMessage.msg msg, true⟩

/-- Both saved states a call frame can restore from are canonical.

A `Frame` holds two messages and `Frame.settleMsg` can roll back to either:
`processMessage.settle` restores the *inner* message's saved pair, and a create
whose code-deposit charge fails restores the *outer* one. The invariant
therefore has to name both, which is exactly the "every saved parent/rollback
state" clause of P0.4 item 5. Statement only -- Step 4 of
`~/plans/integrity.md` owns the preservation proofs. -/
def Frame.Canonical (f : Frame) : Prop :=
  Msg.Canonical f.outer ∧ Msg.Canonical f.inner

instance {f : Frame} : Decidable (Frame.Canonical f) := by
  unfold Frame.Canonical; infer_instance

theorem Frame.canonical_ofCall {msg : Msg} (h : Msg.Canonical msg) :
    Frame.Canonical (Frame.ofCall msg) := ⟨h, h⟩

def processMessage.settle (msg : Msg)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except (EvmError × State × AdrSet × Tra) Devm := do
  let evm ← r
  if evm.error.isSome then
    .ok (evm.rollback msg.benv.state msg.tenv.transientStorage)
  else
    .ok evm

def processCreateMessage.settle (msg : Msg)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except (EvmError × State × AdrSet × Tra) Devm := do
  let evm ← r
  if evm.error.isNone then
    match processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
    | .ok evm => .ok (evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩)
    | .error ⟨.halt reason, evm⟩ =>
      .ok
        (processCreateMessage.exceptionalHalt evm reason
          msg.benv.state msg.tenv.transientStorage)
    | .error ⟨.revert, evm⟩ =>
      .error ⟨.revert, evm.state, evm.createdAccounts, evm.transientStorage⟩
    | .error ⟨.crypto reason, evm⟩ =>
      .error ⟨.crypto reason, evm.state, evm.createdAccounts, evm.transientStorage⟩
    | .error ⟨.internal reason, evm⟩ =>
      .error ⟨.internal reason, evm.state, evm.createdAccounts,
        evm.transientStorage⟩
  else
    .ok (evm.rollback msg.benv.state msg.tenv.transientStorage)

def Frame.settleMsg (f : Frame)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Except (EvmError × State × AdrSet × Tra) Devm :=
  let r := processMessage.settle f.inner r
  if f.isCreate then processCreateMessage.settle f.outer r else r

def Frame.settle (f : Frame) (raw : Execution) :
    Except (EvmError × State × AdrSet × Tra) Devm :=
  f.settleMsg (executeCode.handleError raw)

def executeCode.enter (msg : Msg) : Evm ⊕ Execution :=
  let evm := initEvm msg
  match msg.codeAddress with
  | .none => .inl evm
  | .some adr =>
    if !msg.disablePrecompiles && msg.benv.stat.rules.isPrecomp adr then
      .inr (executePrecomp evm adr)
    else
      .inl evm

inductive FrameEntry : Type
  | done (r : Except (EvmError × State × AdrSet × Tra) Devm)
  | run (evm : Evm)

def Frame.enter (f : Frame) : FrameEntry :=
  /- In the original reference python implementation, there is a test here that
     checks the msg.depth value, and fails with a "stack depth limit error" if
     it is larger than 1024. However, due to the way processMessage is defined
     and used, there is no way msg.depth ever has a value larger than 1024, and
     the error reporting is a dead code path that never will never get used, so
     it is omitted here. -/
  match f.inner.benvAfterTransfer with
  | .error e => .done (f.settleMsg (.error e))
  | .ok benv =>
    match executeCode.enter (f.inner.withBenv benv) with
    | .inl evm => .run evm
    | .inr raw => .done (f.settle raw)

inductive Resume : Type
  | create (parent : Devm) (newAddress : Adr)
  | call (parent : Devm) (outputIndex outputSize : Nat)

def Resume.run :
    Resume → Except (EvmError × State × AdrSet × Tra) Devm → Execution
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

inductive XStep : Type
  | done (ex : Execution)
  | spawn (frame : Frame) (rsm : Resume)

def XStep.ofExcept : Except (EvmError × Devm) XStep → XStep
  | .error e => .done (.error e)
  | .ok step => step

inductive Step : Type
  | halt (ex : Execution)
  | cont (pc : Nat) (devm : Devm)
  | spawn (frame : Frame) (rsm : Resume) (pc : Nat)

def Step.ofExecution (pc : Nat) : Execution → Step
  | .error e => .halt (.error e)
  | .ok devm => .cont pc devm

def Step.ofJump : Except (EvmError × Devm) (Nat × Devm) → Step
  | .error e => .halt (.error e)
  | .ok ⟨pc, devm⟩ => .cont pc devm

def XStep.toStep (pc : Nat) : XStep → Step
  | .done ex => Step.ofExecution pc ex
  | .spawn frame rsm => .spawn frame rsm pc

def genericCreate.step
    (sevm : Sevm) (devm : Devm) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) : XStep :=
  XStep.ofExcept do
    let calldata := devm.memory.data.sliceD memoryIndex memorySize 0
    Except.assert
      (memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
      ⟨.halt (.outOfGas .none), devm⟩
    let createGas := except64th devm.gasLeft
    let devm := devm.withGasLeft (devm.gasLeft - createGas)
    assertDynamic sevm devm
    let devm := devm.withReturnData []
    let sender := devm.state.get sevm.currentTarget
    if sender.bal < endowment ∨ sender.nonce = UInt64.max ∨ sevm.depth = 0 then
      let devm ← (devm.withGasLeft (devm.gasLeft + createGas)).push 0
      return .done (.ok devm)
    let devm := devm.incrNonce sevm.currentTarget
    let devm := addAccessedAddress devm newAddress
    if
      (let target := devm.state.get newAddress
       target.nonce ≠ (0 : UInt64) ∨
       target.code.size ≠ 0 ∨
       target.stor.size ≠ 0) then
      let devm ← devm.push 0
      return .done (.ok devm)
    let childMsg :=
      createMsg sevm devm createGas endowment newAddress calldata
    return .spawn (Frame.ofCreate childMsg) (.create devm newAddress)

def genericCall.step
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) : XStep :=
  let evm1 := devm.withReturnData []
  if sevm.depth = 0 then
    XStep.ofExcept do
      let devm ← (evm1.withGasLeft (evm1.gasLeft + gas)).push 0
      return .done (.ok devm)
  else
    let calldata := evm1.memory.data.sliceD inputIndex inputSize 0
    let childMsg :=
      callMsg sevm evm1 gas value caller target codeAddress
        shouldTransferValue isStaticcall calldata code disablePrecompiles
    .spawn (Frame.ofCall childMsg) (.call evm1 outputIndex outputSize)

/-! The native driver keeps one exact calldata slice available for structural
sharing.  The key is only the compact backing array plus the requested range;
the potentially large padded `Bytes` value is allocated once and then reused
when a later call asks for the identical slice.  The proof field is erased by
code generation and makes every cache hit definitionally accountable to the
ordinary `Array.sliceD` result. -/

private structure CalldataCacheKey where
  data : Array UInt8
  inputIndex : Nat
  inputSize : Nat
deriving DecidableEq

private structure CalldataCache where
  key : CalldataCacheKey
  calldata : Bytes
  valid : calldata = key.data.sliceD key.inputIndex key.inputSize 0

private def CalldataCache.get
    (cache : Option CalldataCache) (data : Array UInt8)
    (inputIndex inputSize : Nat) : Bytes × Option CalldataCache :=
  let key : CalldataCacheKey := ⟨data, inputIndex, inputSize⟩
  match cache with
  | some cached =>
    if h : cached.key = key then
      let current : CalldataCache :=
        { key := key
          calldata := cached.calldata
          valid := by simpa [← h] using cached.valid }
      (current.calldata, some current)
    else
      let calldata := data.sliceD inputIndex inputSize 0
      (calldata, some ⟨key, calldata, rfl⟩)
  | none =>
    let calldata := data.sliceD inputIndex inputSize 0
    (calldata, some ⟨key, calldata, rfl⟩)

private theorem CalldataCache.get_fst
    (cache : Option CalldataCache) (data : Array UInt8)
    (inputIndex inputSize : Nat) :
    (CalldataCache.get cache data inputIndex inputSize).1 =
      data.sliceD inputIndex inputSize 0 := by
  unfold CalldataCache.get
  rcases cache with _ | cached
  · rfl
  · dsimp only
    split
    · rename_i h
      simpa [h] using cached.valid
    · rfl

private def genericCall.stepCached
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool)
    (cache : Option CalldataCache) : XStep × Option CalldataCache :=
  let evm1 := devm.withReturnData []
  if sevm.depth = 0 then
    (XStep.ofExcept do
      let devm ← (evm1.withGasLeft (evm1.gasLeft + gas)).push 0
      return .done (.ok devm), cache)
  else
    let (calldata, cache) :=
      CalldataCache.get cache evm1.memory.data inputIndex inputSize
    let childMsg :=
      callMsg sevm evm1 gas value caller target codeAddress
        shouldTransferValue isStaticcall calldata code disablePrecompiles
    (.spawn (Frame.ofCall childMsg) (.call evm1 outputIndex outputSize), cache)

private theorem genericCall.stepCached_fst
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool)
    (cache : Option CalldataCache) :
    (genericCall.stepCached sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles cache).1 =
    genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles := by
  unfold genericCall.stepCached genericCall.step
  dsimp only
  split
  · rfl
  · simp only [CalldataCache.get_fst]

def Xinst.step (sevm : Sevm) (devm : Devm) : Xinst → XStep
  | .create =>
    XStep.ofExcept do
      let ⟨endowment, devm⟩ ← devm.pop
      let ⟨memoryIndex, devm⟩ ← devm.popToNat
      let ⟨memorySize, devm⟩ ← devm.popToNat
      let extendCost := devm.extCost [⟨memoryIndex, memorySize⟩]
      let initCodeCost := gasInitCodeWordCost * ceilDiv memorySize 32
      let devm ← chargeGas (gasCreate + extendCost + initCodeCost) devm
      let devm := devm.memExtends [⟨memoryIndex, memorySize⟩]
      let newAddress :=
        computeContractAddress
          sevm.currentTarget (devm.state.get sevm.currentTarget).nonce
      return genericCreate.step
        sevm devm endowment newAddress memoryIndex memorySize
  | .create2 =>
    XStep.ofExcept do
      let ⟨endowment, devm⟩ ← devm.pop
      let ⟨memoryIndex, devm⟩ ← devm.popToNat
      let ⟨memorySize, devm⟩ ← devm.popToNat
      let ⟨salt, devm⟩ ← devm.pop
      let extendCost := devm.extCost [⟨memoryIndex, memorySize⟩]
      let initCodeHashCost := gasKeccak256Word * ceilDiv memorySize 32
      let initCodeCost := gasInitCodeWordCost * ceilDiv memorySize 32
      let devm ←
        chargeGas (gasCreate + initCodeHashCost + extendCost + initCodeCost) devm
      let devm := devm.memExtends [⟨memoryIndex, memorySize⟩]
      let newAddress :=
        create2NewAddress
          sevm.currentTarget salt
          (devm.memory.data.sliceD memoryIndex memorySize 0)
      return genericCreate.step
        sevm devm endowment newAddress memoryIndex memorySize
  | .call =>
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
      let preAccessCost := accessCost callee devm.accessedAddresses
      let devm := addAccessedAddress devm callee
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        accessDelegation devm callee
      let accessCost := preAccessCost + delegatedAccessGasCost
      let createCost :=
        if (¬ (devm.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount
      let transferCost := if value = 0 then 0 else gasCallValue
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
          (accessCost + createCost + transferCost)
      let devm ← chargeGas (msgCallCost + extendCost) devm
      Except.assert (!sevm.isStatic ∨ value = 0) ⟨.halt (.writeInStaticContext .none), devm⟩
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal := (devm.getAcct sevm.currentTarget).bal
      if senderBal < value then
        let devm ← devm.push 0
        return .done
          (.ok
            ((devm.withReturnData []).withGasLeft
              (devm.gasLeft + msgCallStipend)))
      else
        return genericCall.step
          sevm devm msgCallStipend value sevm.currentTarget callee
          newCodeAddress true false inputIndex inputSize outputIndex outputSize
          code disablePrecompiles
  | .callcode =>
    XStep.ofExcept do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨codeAddress, devm⟩ ← devm.popToAdr
      let ⟨value, devm⟩ ← devm.pop
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost := accessCost codeAddress devm.accessedAddresses
      let devm := addAccessedAddress devm codeAddress
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        accessDelegation devm codeAddress
      let accessCost := preAccessCost + delegatedAccessGasCost
      let transferCost := if value = 0 then 0 else gasCallValue
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
          (accessCost + transferCost)
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal := (devm.getAcct sevm.currentTarget).bal
      if senderBal < value then
        let devm ← devm.push 0
        return .done
          (.ok
            ((devm.withGasLeft (devm.gasLeft + msgCallStipend)).withReturnData []))
      else
        return genericCall.step
          sevm devm msgCallStipend value sevm.currentTarget
          sevm.currentTarget newCodeAddress true false
          inputIndex inputSize outputIndex outputSize code disablePrecompiles
  | .delcall =>
    XStep.ofExcept do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨codeAddress, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost := accessCost codeAddress devm.accessedAddresses
      let devm := addAccessedAddress devm codeAddress
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        accessDelegation devm codeAddress
      let accessCost := preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost accessCost
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      return genericCall.step
        sevm devm msgCallStipend sevm.value sevm.caller
        sevm.currentTarget newCodeAddress false false
        inputIndex inputSize outputIndex outputSize code disablePrecompiles
  | .statcall =>
    XStep.ofExcept do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨target, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost := accessCost target devm.accessedAddresses
      let devm := addAccessedAddress devm target
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        accessDelegation devm target
      let accessCost := preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost accessCost
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      return genericCall.step
        sevm devm msgCallStipend 0 sevm.currentTarget target newCodeAddress
        true true inputIndex inputSize outputIndex outputSize code
        disablePrecompiles

/-- Cache-threaded native specialization. The first component is proved below
to be exactly `Xinst.step`; only STATICCALL is specialized because it is the
measured pathological family, while every other instruction takes the ordinary
definition verbatim. -/
private def Xinst.stepCached
    (sevm : Sevm) (devm : Devm) (cache : Option CalldataCache) :
    Xinst → XStep × Option CalldataCache
  | .statcall =>
    match (do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨target, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost := accessCost target devm.accessedAddresses
      let devm := addAccessedAddress devm target
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        accessDelegation devm target
      let accessCost := preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost accessCost
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      return genericCall.stepCached
        sevm devm msgCallStipend 0 sevm.currentTarget target newCodeAddress
        true true inputIndex inputSize outputIndex outputSize code
        disablePrecompiles cache :
      Except (EvmError × Devm) (XStep × Option CalldataCache)) with
    | .error e => (.done (.error e), cache)
    | .ok result => result
  | x => (Xinst.step sevm devm x, cache)

private theorem Xinst.stepCached_fst
    (sevm : Sevm) (devm : Devm) (cache : Option CalldataCache) (x : Xinst) :
    (Xinst.stepCached sevm devm cache x).1 = Xinst.step sevm devm x := by
  cases x <;> simp [Xinst.stepCached, Xinst.step]
  case statcall =>
    rcases h₁ : devm.pop with e | ⟨gas, d₁⟩
    · simp only [Bind.bind, Except.bind, XStep.ofExcept]
    simp only [Bind.bind, Except.bind]
    rcases h₂ : d₁.popToAdr with e | ⟨target, d₂⟩
    · simp_all [XStep.ofExcept]
    rcases h₃ : d₂.popToNat with e | ⟨inputIndex, d₃⟩
    · simp_all [XStep.ofExcept]
    rcases h₄ : d₃.popToNat with e | ⟨inputSize, d₄⟩
    · simp_all [XStep.ofExcept]
    rcases h₅ : d₄.popToNat with e | ⟨outputIndex, d₅⟩
    · simp_all [XStep.ofExcept]
    rcases h₆ : d₅.popToNat with e | ⟨outputSize, d₆⟩
    · simp_all [XStep.ofExcept]
    rcases h₇ :
        chargeGas
          ((calculateMsgCallGas 0 gas.toNat
                (accessDelegation (addAccessedAddress d₆ target) target).2.2.2.2.gasLeft
                (d₆.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
                (accessCost target d₆.accessedAddresses +
                  (accessDelegation (addAccessedAddress d₆ target) target).2.2.2.1)).1 +
            d₆.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
          (accessDelegation (addAccessedAddress d₆ target) target).2.2.2.2 with e | d₇
    · simp_all [XStep.ofExcept]
    simp_all [XStep.ofExcept, genericCall.stepCached_fst]

def Ninst.step (evm : Evm) (n : Ninst) : Step :=
  let pc := evm.pc + n.size
  match n with
  | .push xs _ =>
    let cost := if xs = [] then gBase else gVerylow
    Step.ofExecution pc <| do
      let devm ← chargeGas cost evm.dyna
      devm.push xs.toB256
  | .reg r => Step.ofExecution pc (r.run evm)
  | .exec x => XStep.toStep pc (Xinst.step evm.sta evm.dyna x)

def Evm.step (evm : Evm) : Step :=
  match evm.getInst with
  | .none => .halt (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩)
  | .some (.next n) => Ninst.step evm n
  | .some (.jump j) => Step.ofJump (j.run evm)
  | .some (.last l) => .halt (l.run evm.sta evm.dyna)

private def Ninst.stepCached
    (evm : Evm) (cache : Option CalldataCache) (n : Ninst) :
    Step × Option CalldataCache :=
  let pc := evm.pc + n.size
  match n with
  | .exec x =>
    let result := Xinst.stepCached evm.sta evm.dyna cache x
    (XStep.toStep pc result.1, result.2)
  | _ => (Ninst.step evm n, cache)

private theorem Ninst.stepCached_fst
    (evm : Evm) (cache : Option CalldataCache) (n : Ninst) :
    (Ninst.stepCached evm cache n).1 = Ninst.step evm n := by
  cases n <;>
    simp [Ninst.stepCached, Ninst.step, Xinst.stepCached_fst]

private def Evm.stepCached
    (evm : Evm) (cache : Option CalldataCache) :
    Step × Option CalldataCache :=
  match evm.getInst with
  | .none =>
    (.halt (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩), cache)
  | .some (.next n) => Ninst.stepCached evm cache n
  | .some (.jump j) => (Step.ofJump (j.run evm), cache)
  | .some (.last l) => (.halt (l.run evm.sta evm.dyna), cache)

private theorem Evm.stepCached_fst
    (evm : Evm) (cache : Option CalldataCache) :
    (Evm.stepCached evm cache).1 = Evm.step evm := by
  unfold Evm.stepCached Evm.step
  cases h : evm.getInst with
  | none => rfl
  | some inst =>
    cases inst with
    | next n => exact Ninst.stepCached_fst evm cache n
    | jump j => rfl
    | last l => rfl

/-- The single recursive interpreter driver, structurally recursive on its fuel
parameter and therefore obliged to report exhaustion as an outcome.

`Jaune.Sufficiency` proves that fuel seeded from the frame's remaining gas is
always enough, and wraps this function as the total `exec`. -/
def execFueled : Evm → Nat → Fueled (EvmError × Devm) Devm
  | _, 0 => Fueled.exhausted
  | evm, fuel + 1 =>
    match evm.step with
    | .halt ex => Fueled.ofExcept ex
    | .cont pc devm => execFueled ⟨pc, evm.sta, devm⟩ fuel
    | .spawn frame rsm pc =>
      match frame.enter with
      | .done r =>
        match rsm.run r with
        | .error e => Fueled.ofExcept (.error e)
        | .ok devm => execFueled ⟨pc, evm.sta, devm⟩ fuel
      | .run child =>
        match (execFueled child fuel).run with
        | .none => Fueled.exhausted
        | .some raw =>
          match rsm.run (frame.settle raw) with
          | .error e => Fueled.ofExcept (.error e)
          | .ok devm => execFueled ⟨pc, evm.sta, devm⟩ fuel
  termination_by _ fuel => fuel

/-- Cache-threaded native driver. Its semantic component is proved below to be
exactly `execFueled`; the extra component only retains a shareable physical
representative of an exact calldata slice. -/
private def execFueledCachedCore :
    Evm → Nat → Option CalldataCache →
      Fueled (EvmError × Devm) Devm × Option CalldataCache
  | _, 0, cache => (Fueled.exhausted, cache)
  | evm, fuel + 1, cache =>
    let ⟨step, cache⟩ := Evm.stepCached evm cache
    match step with
    | .halt ex => (Fueled.ofExcept ex, cache)
    | .cont pc devm => execFueledCachedCore ⟨pc, evm.sta, devm⟩ fuel cache
    | .spawn frame rsm pc =>
      match frame.enter with
      | .done r =>
        match rsm.run r with
        | .error e => (Fueled.ofExcept (.error e), cache)
        | .ok devm => execFueledCachedCore ⟨pc, evm.sta, devm⟩ fuel cache
      | .run child =>
        let ⟨childResult, cache⟩ := execFueledCachedCore child fuel cache
        match childResult.run with
        | .none => (Fueled.exhausted, cache)
        | .some raw =>
          match rsm.run (frame.settle raw) with
          | .error e => (Fueled.ofExcept (.error e), cache)
          | .ok devm => execFueledCachedCore ⟨pc, evm.sta, devm⟩ fuel cache
  termination_by _ fuel _ => fuel

private theorem execFueledCachedCore_fst :
    ∀ fuel evm cache,
      (execFueledCachedCore evm fuel cache).1 = execFueled evm fuel := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm cache
    simp [execFueledCachedCore, execFueled]
  | succ fuel ih =>
    intro evm cache
    rcases hstep : Evm.stepCached evm cache with ⟨step, cache'⟩
    have hs : step = Evm.step evm := by
      simpa [hstep] using Evm.stepCached_fst evm cache
    simp only [execFueledCachedCore, hstep, execFueled, ← hs]
    cases step with
    | halt ex => rfl
    | cont pc devm => exact ih ⟨pc, evm.sta, devm⟩ cache'
    | spawn frame rsm pc =>
      dsimp only
      cases hentry : frame.enter with
      | done r =>
        dsimp only
        cases hresume : rsm.run r with
        | error e => dsimp only
        | ok devm =>
          dsimp only
          exact ih ⟨pc, evm.sta, devm⟩ cache'
      | run child =>
        dsimp only
        rcases hchild : execFueledCachedCore child fuel cache' with
          ⟨childResult, cache''⟩
        have hc : childResult = execFueled child fuel := by
          simpa [hchild] using ih child cache'
        dsimp only
        rw [hc]
        cases hrun : (execFueled child fuel).run with
        | none => dsimp only
        | some raw =>
          dsimp only
          cases hresume : rsm.run (frame.settle raw) with
          | error e => dsimp only
          | ok devm =>
            dsimp only
            exact ih ⟨pc, evm.sta, devm⟩ cache''

private def execFueledCached
    (evm : Evm) (fuel : Nat) : Fueled (EvmError × Devm) Devm :=
  (execFueledCachedCore evm fuel none).1

@[csimp] private theorem execFueled_eq_cached :
    execFueled = execFueledCached := by
  funext evm fuel
  symm
  exact execFueledCachedCore_fst fuel evm none

/-! Focused executable checks for the flattened core.

The frame wrappers these once also covered (`runFrame`, `executeCode`,
`processMessage`, `processCreateMessage`) are total and therefore live in
`Jaune.Sufficiency`; their checks moved with them. -/

private def flattenGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

private def flattenGuardMsg (bytes : Bytes) (gas depth : Nat) : Msg :=
  {
    (default : Msg) with
    gas := gas
    code := flattenGuardCode bytes
    depth := depth
  }

-- Arithmetic loop: the driver spends one unit per instruction and exhausts.
private def flattenGuardArithmeticLoop : Bool :=
  let msg := flattenGuardMsg [0x5B, 0x60, 0x00, 0x56] 1000 8
  (execFueled (initEvm msg) 20).run.isNone

#guard flattenGuardArithmeticLoop

-- CREATE collision: a nonempty target code short-circuits with stack word 0.
private def flattenGuardCreateCollision : Bool :=
  let target : Adr := 0x40
  let state := State.setCode .empty target (flattenGuardCode [0x00])
  let msg : Msg :=
    {
      (flattenGuardMsg [] 100000 8) with
      benv := {(default : Benv) with state := state}
    }
  match
      genericCreate.step (initSevm msg) (initDevm msg)
        0 target 0 0 with
  | .done (.ok devm) => devm.stack.head? == some 0
  | _ => false

#guard flattenGuardCreateCollision

-- Precompile dispatch is taken normally and bypassed when explicitly disabled.
private def flattenGuardPrecompileDispatch : Bool :=
  let msg : Msg :=
    {
      (flattenGuardMsg [] 10000 8) with
      target := some 1
      currentTarget := 1
      codeAddress := some 1
    }
  let disabled := {msg with disablePrecompiles := true}
  match (Frame.ofCall msg).enter, (Frame.ofCall disabled).enter with
  | .done _, .run _ => true
  | _, _ => false

#guard flattenGuardPrecompileDispatch

-- Depth zero prevents spawning and returns failure word 0 to the caller.
private def flattenGuardDepthZero : Bool :=
  let msg := flattenGuardMsg [] 100 0
  match
      genericCall.step (initSevm msg) (initDevm msg) 17 0
        0 0 0 false false 0 0 0 0 .empty false with
  | .done (.ok devm) =>
    devm.stack.head? == some 0 && devm.gasLeft == 117
  | _ => false

#guard flattenGuardDepthZero

private def flattenGuardCallData
    (codeBytes : Bytes) (codeAddress : Adr) (disablePrecompiles : Bool) : Option Bytes :=
  let msg := flattenGuardMsg [] 100 8
  let devm := (initDevm msg).withMemory ⟨#[0xAA], 1⟩
  match
      genericCall.step (initSevm msg) devm 17 0
        0 codeAddress codeAddress false false 0 1 0 0
        (flattenGuardCode codeBytes) disablePrecompiles with
  | .spawn frame _ => some frame.inner.data
  | _ => none

-- `genericCall.step` keeps its exact original spawned-message construction;
-- the native driver only reuses an equal calldata allocation.
#guard flattenGuardCallData [0x00] 0 false = some [0xAA]
#guard flattenGuardCallData [0x35] 0 false = some [0xAA]
#guard flattenGuardCallData [0x60, 0x35, 0x00] 0 false = some [0xAA]
#guard flattenGuardCallData [0x60, 0x35, 0x35] 0 false = some [0xAA]
#guard flattenGuardCallData [
  0x73, 0x58, 0x3a, 0xa5, 0x87, 0xd7, 0xd8, 0x52, 0xa5, 0xb8, 0x44,
  0x8c, 0xc4, 0x16, 0x05, 0x37, 0xd9, 0xbd, 0x12, 0xc8, 0x89, 0x00
] 0 false = some [0xAA]
#guard flattenGuardCallData [] 1 false = some [0xAA]
#guard flattenGuardCallData [] 1 true = some [0xAA]

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def flattenGuardOog : Bool :=
  let msg := flattenGuardMsg [0x60, 0x01, 0x00] 0 8
  match (execFueled (initEvm msg) 10).run with
  | .some (.error ⟨err, _⟩) => err == .halt (.outOfGas .none)
  | _ => false

#guard flattenGuardOog

-- P0.6 item 2 regressions: JUMP and JUMPI to a destination beyond the end of
-- code render the legacy InvalidJumpDestError through the ordinary error
-- channel, with nothing written by a host-level partial read (typed
-- construction is Step 9). The destination read is total; out of range is
-- semantically `false`.
private def flattenGuardJumpOob : Bool :=
  -- PUSH1 0xFF; JUMP — destination 255 is out of range for 3 bytes of code.
  let msg := flattenGuardMsg [0x60, 0xFF, 0x56] 100 8
  match (execFueled (initEvm msg) 10).run with
  | .some (.error ⟨err, _⟩) => err == .halt (.invalidJumpDest .none)
  | _ => false

#guard flattenGuardJumpOob

private def flattenGuardJumpiOob : Bool :=
  -- PUSH1 0x01 (condition); PUSH1 0xFF (destination); JUMPI — taken branch,
  -- destination 255 is out of range for 5 bytes of code.
  let msg := flattenGuardMsg [0x60, 0x01, 0x60, 0xFF, 0x57] 100 8
  match (execFueled (initEvm msg) 10).run with
  | .some (.error ⟨err, _⟩) => err == .halt (.invalidJumpDest .none)
  | _ => false

#guard flattenGuardJumpiOob

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases w[a]?
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

def State.code (w : State) (a : Adr) : ByteArray :=
  match w[a]? with
  | none => ByteArray.mk #[]
  | some x => x.code

-- P0.6 item 3: the leading byte of the fixed 32-byte hash is read through the
-- total `head?`, never a partial index; an (unrepresentable) empty byte list
-- would simply fail the predicate.
def correctBlobHashVersion (h : B256) : Prop :=
  h.toBytes.head? = some 0x01

instance : DecidablePred correctBlobHashVersion := by
  intro h; simp [correctBlobHashVersion]; infer_instance

def Log.toBLT (l : Log) : BLT :=
  .list [
    .bytes l.address.toBytes,
    .list (l.topics.map B256.toBLT),
    .bytes l.data
  ]

def List.putIndex {ξ : Type u} (xs : List ξ) : List (Nat × ξ) :=
  let rec aux : Nat → List ξ → List (Nat × ξ)
    | _, [] => []
    | k, x :: xs => (k, x) :: aux (k + 1) xs
  aux 0 xs

inductive ExpectedWorldState : Type
  | wor : State → ExpectedWorldState
  | root : B256 → ExpectedWorldState

structure Test where
  (name : String)
  (info : Lean.Json)
  (blocks : Lean.Json)
  (gbh : Lean.Json)
  (grlp : Lean.Json)
  (lbh : Lean.Json)
  (network : Lean.Json)
  (pre : Lean.Json)
  (post : ExpectedWorldState)
  (sealEngine : Lean.Json)

def Bytes.toByteArray (xs : Bytes) : ByteArray := .mk <| .mk xs

def nibbleKey (pr : Bytes × Bytes) : Bytes × Bytes :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨Bytes.toNibbles ad, ac⟩

def receiptRoot (w : List (Bytes × Bytes)) : B256 :=
  let keyVals : List (Bytes × Bytes) := (List.map nibbleKey w)
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
  trie finalNTB

def addIndexToBloom (hash : Bytes) (index : Nat) (bloom : Bytes) : Bytes :=
  let bitToSet : UInt16 :=
    (UInt16.ofBytes (hash.getD index 0) (hash.getD (index + 1) 0)) &&& (0x07FF : UInt16)
  let bitIndex : UInt16 := 0x07FF - bitToSet
  let byteIndex : Nat := (bitIndex / 8).toNat
  let bitValue : UInt8 := 0x01 <<< (0x07 - (bitIndex.lows &&& 0x07))
  let origValue : UInt8 := bloom.getD byteIndex 0
  bloom.set byteIndex (origValue ||| bitValue)

def addEntryToBloom (bloom : Bytes) (entry : Bytes) : Bytes :=
  let hash := (Bytes.keccak entry).toBytes
  addIndexToBloom hash 4 <|
  addIndexToBloom hash 2 <|
  addIndexToBloom hash 0 bloom

def addLogToBloom (bloom : Bytes) (log : Log) : Bytes :=
  let bloom' := addEntryToBloom bloom log.address.toBytes
  List.foldl addEntryToBloom bloom' (log.topics.map B256.toBytes)

def logsBloom (l : List Log) : Bytes :=
  List.foldl addLogToBloom (List.replicate 256 0x00) l

def BLT.toExHeader : BLT → Except DecodeError Header
  | .list (
      .bytes parentHash ::
      .bytes ommersHash ::
      .bytes coinbase ::
      .bytes stateRoot ::
      .bytes txsRoot ::
      .bytes receiptRoot ::
      .bytes bloom ::
      .bytes difficulty ::
      .bytes number ::
      .bytes gasLimit ::
      .bytes gasUsed ::
      .bytes timestamp ::
      .bytes extraData ::
      .bytes prevRandao ::
      .bytes nonce ::
      .bytes baseFeePerGas ::
      .bytes withdrawalsRoot ::
      .bytes blobGasUsed ::
      .bytes excessBlobGas ::
      .bytes parentBeaconBlockRoot ::
      tail
    ) => do
      -- Every field is checked for shape before its value is converted. The
      -- shapes are not uniform and the difference matters: hashes, roots, the
      -- coinbase, the bloom and the nonce are *fixed-width bytes*, where a
      -- leading zero is content; the integers are *canonical scalars*, where a
      -- leading zero is malformed and zero is the empty string. Widths follow
      -- execution-specs' header types -- `Uint`/`U256` for the numbers modelled
      -- here as `Nat`, and `U64` for the two blob-gas fields, which is the one
      -- place a header field carries the 64-bit overflow identity.
      let parentHash ← parentHash.toRlpHash "header parentHash"
      let ommersHash ← ommersHash.toRlpHash "header ommersHash"
      let coinbase ← coinbase.toRlpAdr "header coinbase"
      let stateRoot ← stateRoot.toRlpHash "header stateRoot"
      let txsRoot ← txsRoot.toRlpHash "header transactionsRoot"
      let receiptRoot ← receiptRoot.toRlpHash "header receiptRoot"
      let bloom ← bloom.toRlpFixed "header bloom" 256
      let difficulty ← difficulty.toRlpNat "header difficulty" 32
      let number ← number.toRlpNat "header number" 32
      let gasLimit ← gasLimit.toRlpNat "header gasLimit" 32
      let gasUsed ← gasUsed.toRlpNat "header gasUsed" 32
      let timestamp ← timestamp.toRlpNat "header timestamp" 32
      let prevRandao ← prevRandao.toRlpHash "header prevRandao"
      let nonce ← nonce.toRlpFixedB64 "header nonce"
      let baseFeePerGas ← baseFeePerGas.toRlpNat "header baseFeePerGas" 32
      let withdrawalsRoot ← withdrawalsRoot.toRlpHash "header withdrawalsRoot"
      let blobGasUsed := (← blobGasUsed.toRlpB64 "header blobGasUsed").toNat
      let excessBlobGas := (← excessBlobGas.toRlpB64 "header excessBlobGas").toNat
      let previousBeaconBlockRoot ←
        parentBeaconBlockRoot.toRlpHash "header parentBeaconBlockRoot"
      -- The requests hash is optional in shape, but exactly 32 bytes when
      -- present: an absent field and a malformed one are different failures.
      let requestsHash : Option B256 ←
        match tail with
        | [] => .ok none
        | [.bytes requestsHash] =>
          (requestsHash.toRlpHash "header requestsHash").map some
        | _ =>
          .error <| DecodeError.structure "header"
            s!"expected 20 or 21 fields, but found {20 + tail.length}"
      .ok {
        parentHash := parentHash
        ommersHash := ommersHash
        coinbase := coinbase
        stateRoot := stateRoot
        txsRoot := txsRoot
        receiptRoot := receiptRoot
        bloom := bloom
        difficulty := difficulty
        number := number
        gasLimit := gasLimit
        gasUsed := gasUsed
        timestamp := timestamp
        extraData := extraData
        prevRandao := prevRandao
        nonce := nonce
        baseFeePerGas := baseFeePerGas
        withdrawalsRoot := withdrawalsRoot
        blobGasUsed := blobGasUsed
        excessBlobGas := excessBlobGas
        parentBeaconBlockRoot := previousBeaconBlockRoot
        requestsHash := requestsHash
      }
  | _ =>
    .error <| DecodeError.structure "header"
      "expected a list of 20 or 21 byte-string fields"

/-- Strict header-decoder soundness (P0.3/P0.4). Every header this decoder
produces satisfies `Header.WireWellFormed`, which is what makes that predicate
a *lift* of the decoder rather than an independently invented policy: it holds
of exactly the values the wire can deliver. -/
theorem BLT.toExHeader_wireWellFormed {blt : BLT} {hdr : Header}
    (h : blt.toExHeader = .ok hdr) : hdr.WireWellFormed := by
  unfold BLT.toExHeader at h
  split at h
  · simp only [Except.bind_eq_ok_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hbl, _, hdf, _, hnb,
      _, hgl, _, hgu, _, hts, _, _, _, _, _, hbf, _, _, bgu, _, ebg, _,
      _, _, hm⟩ := h
    have hb := Bytes.toRlpFixed_eq_ok hbl
    have h2 := Bytes.toRlpNat_lt_two_pow_256 hdf
    have h3 := Bytes.toRlpNat_lt_two_pow_256 hnb
    have h4 := Bytes.toRlpNat_lt_two_pow_256 hgl
    have h5 := Bytes.toRlpNat_lt_two_pow_256 hgu
    have h6 := Bytes.toRlpNat_lt_two_pow_256 hts
    have h7 := Bytes.toRlpNat_lt_two_pow_256 hbf
    have h8 : bgu.toNat < 2 ^ 64 := bgu.toNat_lt
    have h9 : ebg.toNat < 2 ^ 64 := ebg.toNat_lt
    split at hm
    · simp only [Except.bind_eq_ok_iff, Except.ok.injEq] at hm
      obtain ⟨_, _, rfl⟩ := hm
      exact ⟨hb, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · simp only [Except.bind_eq_ok_iff, Except.ok.injEq] at hm
      obtain ⟨_, _, rfl⟩ := hm
      exact ⟨hb, h2, h3, h4, h5, h6, h7, h8, h9⟩
    · simp only [Except.bind_eq_ok_iff] at hm
      exact absurd hm (by simp)
  · exact absurd h (by simp)

/-- The child's excess blob gas.

Every parameter is read from the *child's* blob schedule, which is what makes a
BPO transition take effect on the first block of the new schedule rather than
one block late. Osaka's EIP-7918 branch also reads both fees from the parent
header: the blob fee at the parent's excess and the execution base fee the
parent actually carried. -/
def calculateExcessBlobGas (blob : BlobSchedule) (parentHeader : Header) : Nat :=
  let parentBlobGas : Nat :=
    parentHeader.excessBlobGas + parentHeader.blobGasUsed
  if parentBlobGas < blob.target then
    0
  else
    match blob.reserveBaseCost with
    | none =>
      parentBlobGas - blob.target
    | some reserveBaseCost =>
      let targetBlobGasPrice :=
        gasPerBlob *
          calculateBlobGasPrice blob parentHeader.excessBlobGas
      let baseBlobTxPrice :=
        reserveBaseCost * parentHeader.baseFeePerGas
      if baseBlobTxPrice > targetBlobGasPrice then
        parentHeader.excessBlobGas +
          parentHeader.blobGasUsed * (blob.max - blob.target) / blob.max
      else
        parentBlobGas - blob.target


structure MsgCallOutput : Type where
  gasLeft : Nat
  refundCounter : Int
  logs : List Log
  accountsToDelete : AdrSet
  error: Option SettledHalt
  returnData : Bytes

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def accountHasCodeOrNonce (state : State) (adr : Adr) : Bool :=
  state.getNonce adr > 0 || !(state.getCode adr).isEmpty

def accountHasStorage (state : State) (adr : Adr) : Bool :=
  !(state.getStor adr).isEmpty

def Tx.signingHash (tx : Tx) : Option B256 :=
  match tx.type with
  | .zero gasPrice receiver =>
    if tx.v = 27 || tx.v = 28
    then
      -- signing_hash_pre155
      some <|
        Bytes.keccak <|
          BLT.toBytes <|
            .list [
              .bytes tx.nonce.toBytes.sig,
              .bytes gasPrice.toBytes,
              .bytes tx.gas.toBytes,
              .bytes ((receiver <&> Adr.toBytes).getD []),
              .bytes tx.value.toBytes,
              .bytes tx.data
            ]
    else do
      -- signing_hash155
      let chainId : Nat := (tx.v - 35) / 2
      some <|
        Bytes.keccak <|
          BLT.toBytes <|
            .list [
              .bytes tx.nonce.toBytes.sig,
              .bytes gasPrice.toBytes,
              .bytes tx.gas.toBytes,
              .bytes ((receiver <&> Adr.toBytes).getD []),
              .bytes tx.value.toBytes,
              .bytes tx.data,
              .bytes chainId.toBytes,
              .bytes [],
              .bytes []
            ]
  -- def signing_hash2930
  | .one chainId gasPrice receiver accessList =>
    Bytes.keccak <|
      .cons (0x01 : UInt8) <|
        BLT.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes gasPrice.toBytes,
            .bytes tx.gas.toBytes,
            .bytes ((receiver <&> Adr.toBytes).getD []),
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toBLT
          ]
  -- signing_hash1559
  | .two chainId maxPriorityFee maxFee receiver accessList =>
    Bytes.keccak <|
      .cons (0x02 : UInt8) <|
        BLT.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes maxPriorityFee.toBytes,
            .bytes maxFee.toBytes,
            .bytes tx.gas.toBytes,
            .bytes ((receiver <&> Adr.toBytes).getD []),
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toBLT
          ]
  -- def signing_hash4844
  | .three chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    Bytes.keccak <|
      .cons (0x03 : UInt8) <|
        BLT.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes maxPriorityFee.toBytes,
            .bytes maxFee.toBytes,
            .bytes tx.gas.toBytes,
            .bytes receiver.toBytes,
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toBLT,
            .bytes maxBlobFee.toBytes,
            .list <| blobHashes.map <| .bytes ∘ B256.toBytes
          ]
  | .four chainId maxPriorityFee maxFee receiver accessList auths =>
    Bytes.keccak <|
      .cons (0x04 : UInt8) <|
        BLT.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes maxPriorityFee.toBytes,
            .bytes maxFee.toBytes,
            .bytes tx.gas.toBytes,
            .bytes receiver.toBytes,
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toBLT,
            .list <| auths.map Auth.toBLT
          ]

def recoverSender (chain_id: UInt64) (tx: Tx) : Except CryptoError Adr := do
  let r := tx.r.toB256
  let s := tx.s.toB256
  if (r = 0 ∨ secp256k1.curveOrder.toB256 ≤ r) then
    .error (.invalidSignature (.text "bad r"))
  if (s = 0 ∨ secp256k1.curveOrder.toB256 / 2 < s) then
    .error (.invalidSignature (.text "bad s"))
  let v := tx.v
  let signingHash ←
    tx.signingHash.toExcept (.invalidSignature (.text "signing hash is None"))
  match tx.type with
  | .zero _ _ =>
    if v = 27 ∨ v = 28
    then
      (secp256k1.recover signingHash (v - 27).toBool r s).toExcept
        (.invalidSignature (.text "sender recovery failed"))
    else
      let chain_id_x2 := (chain_id.toNat) * (2)
      .assert (v = 35 + chain_id_x2 ∨ v = 36 + chain_id_x2)
        (CryptoError.invalidSignature (.text "bad v"))
      (secp256k1.recover signingHash (v - 35 - chain_id_x2).toBool r s).toExcept
        (.invalidSignature (.text "sender recovery failed"))
  | _ =>
    .assert (v < 2) (CryptoError.invalidSignature .none)
    (secp256k1.recover signingHash v.toBool r s).toExcept
      (.invalidSignature (.text "sender recovery failed"))

def recoverAuthority (auth : Auth) : Except CryptoError Adr := do
  let yParity := auth.yParity
  let r := auth.r
  let s := auth.s
  if (
    1 < yParity ∨
    r = 0 ∨  secp256k1.curveOrder.toB256 ≤ r ∨
    s = 0 ∨ (secp256k1.curveOrder.toB256 / 2) < s
  ) then
    .error (.invalidSignature .none)
  let signingHash : B256 :=
    Bytes.keccak <|
      List.append setCodeTxMagic <|
        BLT.toBytes <| .list [
          .bytes auth.chainId.toBytes.sig,
          .bytes auth.address.toBytes,
          .bytes auth.nonce.toBytes.sig
        ]
  -- EIP-7702 invalidates an authorization tuple, not its enclosing
  -- transaction: a recovery failure is therefore handled by
  -- `setDelegationStep` exactly like the other invalid-signature forms.
  (secp256k1.recover signingHash yParity.toBool r s ).toExcept (.invalidSignature .none)

def setDelegationStep
    (auth : Auth) (msg : Msg) (refundCounter : B256) :
    Except EvmError (Msg × B256) := do
  if auth.chainId != msg.benv.stat.chainId.toB256 && auth.chainId != 0 then
    .ok ⟨msg, refundCounter⟩
  else if auth.nonce = UInt64.max then
    .ok ⟨msg, refundCounter⟩
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) =>
      -- EIP-7702 invalidates the authorization tuple on exactly this reason
      -- and on no other: the tuple is skipped and processing continues.
      .ok ⟨msg, refundCounter⟩
    | .error err => .error (.crypto err)
    | .ok authority =>
      let msg := {msg with accessedAddresses := msg.accessedAddresses.insert authority}
      let authorityAccount : Acct :=
        msg.benv.state.get authority
      let authorityCode : ByteArray := authorityAccount.code
      if ¬ (authorityCode.isEmpty ∨ isValidDelegation authorityCode) then
        .ok ⟨msg, refundCounter⟩
      else if authorityAccount.nonce != auth.nonce then
        .ok ⟨msg, refundCounter⟩
      else
        let refundCounter :=
          if AccountExists msg.benv.state authority then
            refundCounter + (perEmptyAccountCost - perAuthBaseCost).toB256
          else
            refundCounter
        let codeToSet : ByteArray :=
          if auth.address = 0 then
            .empty
          else
            (eoaDelegationMarker ++ auth.address.toBytes).toByteArray
        let msg := msg.setCode authority codeToSet
        let msg := msg.incrNonce authority
        .ok ⟨msg, refundCounter⟩

def setDelegationLoop : List Auth → Msg → B256 → Except EvmError (Msg × B256)
  | [], msg, refundCounter => .ok ⟨msg, refundCounter⟩
  | auth :: auths, msg, refundCounter => do
    let ⟨msg, refundCounter⟩ ← setDelegationStep auth msg refundCounter
    setDelegationLoop auths msg refundCounter

def setDelegation (msg : Msg) : Except EvmError (Msg × B256) := do
  let ⟨msg, refundCounter⟩ ← setDelegationLoop msg.tenv.stat.auths msg 0
  let msg ←
    match msg.codeAddress with
    | none =>
      -- Unreachable: a validated type-4 transaction has a receiver, so its
      -- message always carries a code address. A breach is an internal
      -- invariant failure and must fail closed, never read as a block verdict.
      .error (.internal (.invariant (.text "Invalid type 4 transaction: no target")))
    | some ca =>
      .ok {
        msg with
        code := msg.benv.state.getCode ca
      }
  .ok ⟨msg, refundCounter⟩

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 2, frame half: canonicality through delegation access, message
-- initialisation, frame enter/settle/resume, the step machinery, and the
-- fueled driver. Restoration sources are exactly the ones the invariant
-- carries: a message's saved pair (`Frame.Canonical`, both messages), a
-- settlement error payload (`Except.CanonicalSettle`), and a child world
-- incorporated wholesale.

/-- Delegation access touches only the accessed-address set. Stated over the
projection because callers consume the result through an irrefutable `let`. -/
theorem accessDelegation_canonical {devm : Devm} (h : devm.Canonical)
    (adr : Adr) : (accessDelegation devm adr).2.2.2.2.Canonical := by
  unfold accessDelegation
  dsimp only
  split
  · exact Devm.Canonical.of_world_eq h rfl
  · exact h

/-- The eq-conditioned form, for walks that destructure the tuple. -/
theorem accessDelegation_eq_canonical {devm d' : Devm} {adr : Adr} {b : Bool}
    {a2 : Adr} {code : ByteArray} {n : Nat} (h : devm.Canonical)
    (heq : accessDelegation devm adr = (b, a2, code, n, d')) : d'.Canonical := by
  have hc := accessDelegation_canonical h adr
  rw [heq] at hc
  exact hc

/-- The create-message initialiser clears the child's storage, marks it
created, and bumps its nonce -- all through named canonical mutators. -/
theorem processCreateMessage.msg_canonical {msg : Msg} (h : msg.Canonical) :
    (processCreateMessage.msg msg).Canonical :=
  Msg.Canonical.withBenv h
    (Benv.Canonical.incrNonce
      (Benv.Canonical.addCreatedAccount
        (Benv.Canonical.setStor h.1 _ Stor.canonical_empty) _) _)

theorem processCreateMessage.chargeCodeGas_canonical {rules : ForkRules}
    {devm : Devm} (h : devm.Canonical) :
    (processCreateMessage.chargeCodeGas rules devm).Canonical := by
  unfold processCreateMessage.chargeCodeGas
  dsimp only
  split
  · exact h
  · refine Except.CanonicalOn.bind (liftMachExecution_canonical h) fun d hd => ?_
    split
    · exact hd
    · exact hd

/-- An exceptional create halt restores the saved pair; the failing machine
contributes nothing to the world. -/
theorem processCreateMessage.exceptionalHalt_canonical {devm : Devm}
    (reason : ExceptionalHalt) {st : State} {tra : Tra}
    (hst : State.Canonical st) (htra : Tra.Canonical tra) :
    (processCreateMessage.exceptionalHalt devm reason st tra).Canonical :=
  Devm.Canonical.of_world_eq (Devm.canonical_rollback (devm := devm) hst htra) rfl

theorem initSevm_canonical {msg : Msg} (h : msg.Canonical) :
    (initSevm msg).Canonical := h.1.2

theorem initDevm_canonical {msg : Msg} (h : msg.Canonical) :
    (initDevm msg).Canonical := ⟨h.1.1, h.2⟩

theorem initEvm_canonical {msg : Msg} (h : msg.Canonical) :
    (initEvm msg).Canonical := ⟨h.1.2, h.1.1, h.2⟩

/-- A successful pre-execution value transfer moves balances through
`subBal`/`addBal` only. -/
theorem Msg.benvAfterTransfer_ok_canonical {msg : Msg} (h : msg.Canonical)
    {benv : Benv} (hb : msg.benvAfterTransfer = .ok benv) : benv.Canonical := by
  unfold Msg.benvAfterTransfer at hb
  split at hb
  · cases hsb : msg.benv.subBal msg.caller msg.value with
    | none =>
      rw [hsb] at hb
      exact absurd hb (by simp [Option.toExcept, bind, Except.bind])
    | some b1 =>
      rw [hsb] at hb
      simp only [Option.toExcept, bind, Except.bind, Except.ok.injEq] at hb
      rw [← hb]
      exact Benv.Canonical.addBal (Benv.Canonical.subBal h.1 hsb) _ _
  · cases hb
    exact h.1

/-- A failed pre-execution transfer reports exactly the message's saved
pair, which the invariant already covers. -/
theorem Msg.benvAfterTransfer_error_canonical {msg : Msg} (h : msg.Canonical)
    {e} (he : msg.benvAfterTransfer = .error e) :
    State.Canonical e.2.1 ∧ Tra.Canonical e.2.2.2 := by
  unfold Msg.benvAfterTransfer at he
  split at he
  · cases hsb : msg.benv.subBal msg.caller msg.value with
    | none =>
      rw [hsb] at he
      simp only [Option.toExcept, bind, Except.bind, Except.error.injEq] at he
      rw [← he]
      exact ⟨h.1.1, h.2⟩
    | some b1 =>
      rw [hsb] at he
      exact absurd he (by simp [Option.toExcept, bind, Except.bind])
  · exact absurd he (by simp)

/-- Settling an execution result preserves canonicality on both channels: a
halt zeroes gas and clears output (machine-only), a revert marks the error
(machine-only), and everything else forwards the failing machine's world into
the settlement payload. -/
theorem executeCode.handleError_canonicalSettle {raw}
    (hr : Execution.Canonical raw) :
    (executeCode.handleError raw).CanonicalSettle := by
  unfold executeCode.handleError
  split
  · exact hr
  · exact Devm.Canonical.of_world_eq hr rfl
  · exact Devm.Canonical.of_world_eq hr rfl
  · exact ⟨hr.1, hr.2⟩
  · exact ⟨hr.1, hr.2⟩

theorem processMessage.settle_canonicalSettle {msg : Msg} (hm : msg.Canonical)
    {r} (hr : Except.CanonicalSettle r) :
    (processMessage.settle msg r).CanonicalSettle := by
  refine Except.CanonicalSettle.bind hr fun d hd => ?_
  split
  · exact Msg.Canonical.rollback hm d
  · exact hd

theorem processCreateMessage.settle_canonicalSettle {msg : Msg}
    (hm : msg.Canonical) {r} (hr : Except.CanonicalSettle r) :
    (processCreateMessage.settle msg r).CanonicalSettle := by
  refine Except.CanonicalSettle.bind hr fun d hd => ?_
  split
  · have hcanon : ∀ {e : EvmError} {d' : Devm},
        processCreateMessage.chargeCodeGas msg.benv.stat.rules d
          = .error (e, d') → d'.Canonical := by
      intro e d' heq
      have hc := processCreateMessage.chargeCodeGas_canonical
        (rules := msg.benv.stat.rules) hd
      rw [heq] at hc
      exact hc
    split
    · next d' heq =>
        have hok : d'.Canonical := by
          have hc := processCreateMessage.chargeCodeGas_canonical
            (rules := msg.benv.stat.rules) hd
          rw [heq] at hc
          exact hc
        exact Devm.Canonical.setCode hok _ _
    · exact processCreateMessage.exceptionalHalt_canonical _ hm.1.1 hm.2
    · next d' heq => exact ⟨(hcanon heq).1, (hcanon heq).2⟩
    · next d' heq => exact ⟨(hcanon heq).1, (hcanon heq).2⟩
    · next d' heq => exact ⟨(hcanon heq).1, (hcanon heq).2⟩
  · exact Msg.Canonical.rollback hm d

/-- Both restoration targets of a frame settlement are covered: the inner
message at `processMessage.settle`, and the outer one when a create fails its
code-deposit charge. -/
theorem Frame.settleMsg_canonicalSettle {f : Frame} (hf : f.Canonical)
    {r} (hr : Except.CanonicalSettle r) :
    (f.settleMsg r).CanonicalSettle := by
  unfold Frame.settleMsg
  split
  · exact processCreateMessage.settle_canonicalSettle hf.1
      (processMessage.settle_canonicalSettle hf.2 hr)
  · exact processMessage.settle_canonicalSettle hf.2 hr

theorem Frame.settle_canonicalSettle {f : Frame} (hf : f.Canonical)
    {raw} (hraw : Execution.Canonical raw) :
    (f.settle raw).CanonicalSettle :=
  Frame.settleMsg_canonicalSettle hf (executeCode.handleError_canonicalSettle hraw)

theorem Frame.canonical_ofCreate {msg : Msg} (h : msg.Canonical) :
    (Frame.ofCreate msg).Canonical :=
  ⟨h, processCreateMessage.msg_canonical h⟩

/-- Code entry either starts a machine over the message's world or finishes a
precompile without ever touching it. -/
theorem executeCode.enter_canonical {msg : Msg} (h : msg.Canonical) :
    Sum.elim Evm.Canonical Execution.Canonical (executeCode.enter msg) := by
  unfold executeCode.enter
  split
  · exact initEvm_canonical h
  · split
    · exact executePrecomp_canonical (initDevm_canonical h) _
    · exact initEvm_canonical h

/-- What a frame entry must preserve: a finished settlement carries canonical
restoration data, a started machine is canonical outright. -/
def FrameEntry.Canonical : FrameEntry → Prop
  | .done r => r.CanonicalSettle
  | .run evm => evm.Canonical

theorem Frame.enter_canonical {f : Frame} (hf : f.Canonical) :
    f.enter.Canonical := by
  unfold Frame.enter
  rcases hbt : f.inner.benvAfterTransfer with e | benv
  · exact Frame.settleMsg_canonicalSettle hf
      (Msg.benvAfterTransfer_error_canonical hf.2 hbt)
  · have hm : (f.inner.withBenv benv).Canonical :=
      Msg.Canonical.withBenv hf.2 (Msg.benvAfterTransfer_ok_canonical hf.2 hbt)
    have hent := executeCode.enter_canonical hm
    dsimp only
    rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      rw [henter] at hent
    · exact hent
    · exact Frame.settle_canonicalSettle hf hent

/-- Resuming a parent needs only the settlement's canonicality: the error
branch rebuilds the world entirely from the settlement payload, and child
incorporation takes the child's world wholesale. The parent's own world is
never a restoration source. -/
theorem Resume.run_canonical {rsm : Resume} {r} (hr : Except.CanonicalSettle r) :
    Execution.Canonical (rsm.run r) := by
  cases rsm with
  | create parent newAddress =>
    refine Except.CanonicalOn.bind (liftToExecution_canonical hr) fun c hc => ?_
    split
    · exact liftMachExecution_canonical (incorporateChildOnError_canonical hc _)
    · exact liftMachExecution_canonical (incorporateChildOnSuccess_canonical hc _)
  | call parent outputIndex outputSize =>
    refine Except.CanonicalOn.bind (liftToExecution_canonical hr) fun c hc => ?_
    split
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical (incorporateChildOnError_canonical hc _))
        fun d hd => ?_
      exact Devm.Canonical.of_world_eq hd rfl
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical (incorporateChildOnSuccess_canonical hc _))
        fun d hd => ?_
      exact Devm.Canonical.of_world_eq hd rfl

/-- What one extended step must preserve. The spawn arm carries only the
frame: `Resume.run_canonical` shows the parent machine is not needed. -/
def XStep.Canonical : XStep → Prop
  | .done ex => Execution.Canonical ex
  | .spawn frame _ => frame.Canonical

/-- What one step must preserve. -/
def Step.Canonical : Step → Prop
  | .halt ex => Execution.Canonical ex
  | .cont _ devm => devm.Canonical
  | .spawn frame _ _ => frame.Canonical

theorem XStep.ofExcept_canonical {x} (hx : x.CanonicalOn XStep.Canonical) :
    (XStep.ofExcept x).Canonical := by
  cases x with
  | error e => exact hx
  | ok s => exact hx

theorem Step.ofExecution_canonical (pc : Nat) {x}
    (hx : Execution.Canonical x) : (Step.ofExecution pc x).Canonical := by
  cases x with
  | error e => exact hx
  | ok devm => exact hx

theorem Step.ofJump_canonical {x}
    (hx : x.CanonicalOn (fun a => a.2.Canonical)) :
    (Step.ofJump x).Canonical := by
  cases x with
  | error e => exact hx
  | ok a => exact hx

theorem XStep.toStep_canonical (pc : Nat) {s : XStep} (hs : s.Canonical) :
    (XStep.toStep pc s).Canonical := by
  cases s with
  | done ex => exact Step.ofExecution_canonical pc hs
  | spawn frame rsm => exact hs

/-- The child message of a call-type instruction lives on the caller's world
and the frame's original state. -/
theorem callMsg_canonical {sevm : Sevm} {evm1 : Devm}
    (hs : sevm.Canonical) (hd : evm1.Canonical)
    (gas : Nat) (value : B256) (caller target codeAddress : Adr)
    (shouldTransferValue isStaticcall : Bool) (calldata : Bytes)
    (code : ByteArray) (disablePrecompiles : Bool) :
    (callMsg sevm evm1 gas value caller target codeAddress
      shouldTransferValue isStaticcall calldata code
      disablePrecompiles).Canonical :=
  ⟨⟨hd.1, hs⟩, hd.2⟩

theorem createMsg_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical)
    (createGas : Nat) (endowment : B256) (newAddress : Adr)
    (calldata : Bytes) :
    (createMsg sevm devm createGas endowment newAddress calldata).Canonical :=
  ⟨⟨hd.1, hs⟩, hd.2⟩

/-- One EIP-7702 authorization step preserves the message invariant on its
success channel: every arm returns the message unchanged up to bookkeeping
fields outside the invariant, or applies `setCode`/`incrNonce`. The error
channel carries no state. -/
theorem setDelegationStep_canonical {auth : Auth} {msg : Msg} {rc : B256}
    (h : msg.Canonical) {p} (hp : setDelegationStep auth msg rc = .ok p) :
    p.1.Canonical := by
  unfold setDelegationStep at hp
  split at hp
  · cases hp; exact h
  · split at hp
    · cases hp; exact h
    · split at hp
      · cases hp; exact h
      · nomatch hp
      · dsimp only at hp
        split at hp
        · cases hp; exact h
        · split at hp
          · cases hp; exact h
          · cases hp
            exact Msg.Canonical.incrNonce (Msg.Canonical.setCode h _ _) _

theorem setDelegationLoop_canonical :
    ∀ (auths : List Auth) {msg : Msg} {rc : B256}, msg.Canonical →
      ∀ {p}, setDelegationLoop auths msg rc = .ok p → p.1.Canonical
  | [], _, _, h, _, hp => by cases hp; exact h
  | auth :: auths, msg, rc, h, p, hp => by
    unfold setDelegationLoop at hp
    rcases hq : setDelegationStep auth msg rc with e | q <;> rw [hq] at hp
    · nomatch hp
    · exact setDelegationLoop_canonical auths
        (setDelegationStep_canonical h hq) hp

/-- Processing an authorization list preserves the message invariant; the
final code refresh is outside the invariant. -/
theorem setDelegation_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : setDelegation msg = .ok p) : p.1.Canonical := by
  unfold setDelegation at hp
  rcases hq : setDelegationLoop msg.tenv.stat.auths msg 0 with e | q <;>
    rw [hq] at hp
  · nomatch hp
  · have hq1 := setDelegationLoop_canonical _ h hq
    simp only [bind, Except.bind] at hp
    split at hp
    · nomatch hp
    · cases hp
      exact hq1

/-- The CREATE-family step: the only world change on the parent's side is the
sender nonce increment, through its named mutator; the child frame is built
over the parent's world and the frame's original state. -/
theorem genericCreate.step_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) :
    (genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize).Canonical := by
  unfold genericCreate.step
  refine XStep.ofExcept_canonical ?_
  refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
  refine Except.CanonicalOn.bind
    (Except.canonicalOn_assert (by exact hd)) fun _ _ => ?_
  dsimp only
  split
  · refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (by exact hd)) fun d hd1 => ?_
    exact hd1
  · split
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical
          (by exact Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd _) rfl))
        fun d hd1 => ?_
      exact hd1
    · refine Except.canonicalOn_ok ?_
      exact Frame.canonical_ofCreate
        (createMsg_canonical hs
          (by exact Devm.Canonical.of_world_eq (Devm.Canonical.incrNonce hd _) rfl)
          _ _ _ _)

/-- The CALL-family step never changes the parent world: it either refunds
the stipend at depth zero or spawns the child frame. -/
theorem genericCall.step_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).Canonical := by
  unfold genericCall.step
  dsimp only
  split
  · refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (by exact hd)) fun d hd1 => ?_
    exact hd1
  · exact Frame.canonical_ofCall
      (callMsg_canonical hs (by exact hd) _ _ _ _ _ _ _ _ _ _)

theorem Xinst.step_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical) (x : Xinst) :
    (Xinst.step sevm devm x).Canonical := by
  cases x <;> simp only [Xinst.step]
  case create =>
    refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical hc) fun d hd1 => ?_
    exact Except.canonicalOn_ok
      (genericCreate.step_canonical hs (by exact hd1) _ _ _ _)
  case create2 =>
    refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun e he => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical he) fun d hd1 => ?_
    exact Except.canonicalOn_ok
      (genericCreate.step_canonical hs (by exact hd1) _ _ _ _)
  case call =>
    refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hf) fun g hg => ?_
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (accessDelegation_canonical (by exact hg) _))
      fun d2 hd2 => ?_
    refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd2) fun _ _ => ?_
    split
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical (by exact hd2)) fun d3 hd3 => ?_
      exact hd3
    · exact Except.canonicalOn_ok
        (genericCall.step_canonical hs (by exact hd2)
          _ _ _ _ _ _ _ _ _ _ _ _ _)
  case callcode =>
    refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hf) fun g hg => ?_
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (accessDelegation_canonical (by exact hg) _))
      fun d2 hd2 => ?_
    split
    · refine Except.CanonicalOn.bind
        (liftMachExecution_canonical (by exact hd2)) fun d3 hd3 => ?_
      exact hd3
    · exact Except.canonicalOn_ok
        (genericCall.step_canonical hs (by exact hd2)
          _ _ _ _ _ _ _ _ _ _ _ _ _)
  case delcall =>
    refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (accessDelegation_canonical (by exact hf) _))
      fun d2 hd2 => ?_
    exact Except.canonicalOn_ok
      (genericCall.step_canonical hs (by exact hd2)
        _ _ _ _ _ _ _ _ _ _ _ _ _)
  case statcall =>
    refine XStep.ofExcept_canonical ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun d hd1 => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hd1) fun e he => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn he) fun f hf => ?_
    refine Except.CanonicalOn.bind
      (liftMachExecution_canonical (accessDelegation_canonical (by exact hf) _))
      fun d2 hd2 => ?_
    exact Except.canonicalOn_ok
      (genericCall.step_canonical hs (by exact hd2)
        _ _ _ _ _ _ _ _ _ _ _ _ _)

theorem Ninst.step_canonical {evm : Evm} (h : evm.Canonical) (n : Ninst) :
    (Ninst.step evm n).Canonical := by
  cases n with
  | push xs prf =>
    refine Step.ofExecution_canonical _ ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical h.2)
      fun d hd => liftMachExecution_canonical hd
  | reg r => exact Step.ofExecution_canonical _ (Rinst.run_canonical h.2 r)
  | exec x => exact XStep.toStep_canonical _ (Xinst.step_canonical h.1 h.2 x)

/-- One interpreter step preserves the invariant: whatever the step decides --
halt, continue, or spawn -- every state it hands on is canonical. -/
theorem Evm.step_canonical {evm : Evm} (h : evm.Canonical) :
    evm.step.Canonical := by
  unfold Evm.step
  split
  · exact h.2
  · exact Ninst.step_canonical h _
  · exact Step.ofJump_canonical (Jinst.run_canonicalOn h.2 _)
  · exact Linst.run_canonical h.2 _

/-- **Canonicality through the fueled interpreter.** Any result the driver
reaches from a canonical frame is canonical, on both channels. The induction
mirrors `execFueled_run_mono`; the spawn arm threads `Frame.enter_canonical`,
`Frame.settle_canonicalSettle`, and `Resume.run_canonical`, so no parent
world is ever needed as a restoration source. -/
theorem execFueled_run_canonical :
    ∀ (fuel : Nat) (evm : Evm), evm.Canonical →
      ∀ {raw : Execution}, (execFueled evm fuel).run = some raw →
        Execution.Canonical raw := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm _ raw h
    rw [execFueled] at h
    simp only [Fueled.exhausted_run] at h
    nomatch h
  | succ fuel ih =>
    intro evm hevm raw h
    have hst := Evm.step_canonical hevm
    rw [execFueled] at h
    rcases hs : evm.step with ⟨ex⟩ | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩ <;>
      rw [hs] at h hst <;> dsimp only at h
    · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      rw [← h]
      exact hst
    · exact ih ⟨pc, evm.sta, devm⟩ ⟨hevm.1, hst⟩ h
    · have hent := Frame.enter_canonical hst
      rcases he : frame.enter with r | child <;> rw [he] at h hent <;>
        dsimp only at h
      · have hcan := Resume.run_canonical (rsm := rsm) hent
        rcases hrun : rsm.run r with ⟨e⟩ | d1 <;> rw [hrun] at h hcan <;>
          dsimp only at h
        · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          rw [← h]
          exact hcan
        · exact ih ⟨pc, evm.sta, d1⟩ ⟨hevm.1, hcan⟩ h
      · rcases hc : (execFueled child fuel).run with _ | raw2
        · rw [hc] at h
          simp only [Fueled.exhausted_run] at h
          nomatch h
        · rw [hc] at h
          dsimp only at h
          have hsettle := Frame.settle_canonicalSettle hst (ih child hent hc)
          have hcan := Resume.run_canonical (rsm := rsm) hsettle
          rcases hrun : rsm.run (frame.settle raw2) with ⟨e⟩ | d1 <;>
            rw [hrun] at h hcan <;> dsimp only at h
          · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
            rw [← h]
            exact hcan
          · exact ih ⟨pc, evm.sta, d1⟩ ⟨hevm.1, hcan⟩ h

end Jaune
