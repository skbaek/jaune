import Jaune.MessageCall.CheckedDriver

/-! The cached calldata interpreter for checked frames, with its exact specification equation. -/

namespace Jaune.Checked

open Jaune

/-! The cache: one exact calldata slice kept available for structural sharing. The key is the
compact backing array plus the requested range; the padded `Bytes` value is allocated once and
reused when a later call asks for the identical slice. The proof field is erased by code
generation and makes every hit definitionally accountable to the ordinary `Array.sliceD`
result. -/

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

/-- The cached producer of a call's spawn: `Checked.genericCall.step` with the calldata slice
taken through the cache. -/
private def genericCall.stepCached (ctx : CallContext) (s : Frame.State) (gas : Nat)
    (value : U256) (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles : Bool) (cache : Option CalldataCache) :
    MessageOp.Outcome × Option CalldataCache :=
  let s1 := s.withReturnData []
  if ctx.depthLeft = 0 then
    (MessageOp.Outcome.ofExcept do
      let s ← (s1.withGasLeft (s1.gasLeft + gas)).push 0
      return .done (.ok s), cache)
  else
    let (calldata, cache) := CalldataCache.get cache s1.memory.data inputIndex inputSize
    let message :=
      callMessage ctx gas value caller target codeAddress shouldTransferValue isStaticcall
        calldata code disablePrecompiles
    (.spawn ⟨message, s1⟩ ⟨.call outputIndex outputSize, false⟩, cache)

private theorem genericCall.stepCached_fst (ctx : CallContext) (s : Frame.State) (gas : Nat)
    (value : U256) (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles : Bool) (cache : Option CalldataCache) :
    (genericCall.stepCached ctx s gas value caller target codeAddress shouldTransferValue
      isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles cache).1 =
    genericCall.step ctx s gas value caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles := by
  unfold genericCall.stepCached genericCall.step
  dsimp only
  split
  · rfl
  · simp only [CalldataCache.get_fst]

/-- The cache-threaded counterpart of `Checked.MessageOp.Outcome.ofExcept`: an `Except` whose
value already carries the threaded cache, with the untouched cache restored on the halt path. -/
private def MessageOp.Outcome.ofExceptCached (cache : Option CalldataCache)
    (ec : Except (ExceptionalHalt × Frame.State) (MessageOp.Outcome × Option CalldataCache)) :
    MessageOp.Outcome × Option CalldataCache :=
  match ec with
  | .error e => (.done (.error e), cache)
  | .ok result => result

private theorem MessageOp.Outcome.ofExceptCached_fst (cache : Option CalldataCache)
    {ec : Except (ExceptionalHalt × Frame.State) (MessageOp.Outcome × Option CalldataCache)}
    {eu : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (h : Except.map Prod.fst ec = eu) :
    (MessageOp.Outcome.ofExceptCached cache ec).1 = MessageOp.Outcome.ofExcept eu := by
  subst h; cases ec <;> rfl

/-- `Except.map` commutes with `bind`, so a cached arm and its ordinary arm compare leaf by
leaf: the two `do` blocks are the same chain and differ only in what they return. -/
private theorem Except.map_bind' {ε α β γ : Type} (m : Except ε α)
    (k : α → Except ε β) (f : β → γ) :
    Except.map f (m >>= k) = m >>= fun a => Except.map f (k a) := by
  cases m <;> rfl

private theorem Except.map_pure' {ε α β : Type} (f : α → β) (a : α) :
    Except.map f (pure a : Except ε α) = pure (f a) := rfl

/-- Cache-threaded specialization of `Checked.MessageOp.step`. The four call opcodes' arms without
state gas are reproduced verbatim with `genericCall.stepCached` in place of `genericCall.step` and
the cache threaded through the early returns; every other arm is the ordinary definition. -/
private def MessageOp.stepCached (ctx : CallContext) (s : Frame.State)
    (cache : Option CalldataCache) : MessageOp → MessageOp.Outcome × Option CalldataCache
  | .call =>
    match ctx.block.rules.stateGas with
    | some _ => (MessageOp.step ctx s .call, cache)
    | none =>
      MessageOp.Outcome.ofExceptCached cache (do
        let ⟨gas, s⟩ ← s.pop
        let ⟨callee, s⟩ ← s.popToAddress
        let ⟨value, s⟩ ← s.pop
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost callee s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress callee
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s callee
        let accessCost := preAccessCost + delegatedAccessGasCost
        let createCost := if (¬ (s.account callee).isEmpty) ∨ value = 0 then 0 else Gas.newAccount
        let transferCost := if value = 0 then 0 else gasRules.callValue
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat s.gasLeft extendCost
            (accessCost + createCost + transferCost)
        let s ← s.chargeGas (msgCallCost + extendCost)
        Except.assert (!ctx.isStatic ∨ value = 0) (.writeInStaticContext .none, s)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (s.account ctx.recipient).balance
        if senderBal < value then
          let s ← s.push 0
          return (.done (.ok ((s.withReturnData []).withGasLeft (s.gasLeft + msgCallStipend))), cache)
        else
          return genericCall.stepCached ctx s msgCallStipend value ctx.recipient callee newCodeAddress
            true false inputIndex inputSize outputIndex outputSize code disablePrecompiles cache :
        Except (ExceptionalHalt × Frame.State) (MessageOp.Outcome × Option CalldataCache))
  | .callcode =>
    match ctx.block.rules.stateGas with
    | some _ => (MessageOp.step ctx s .callcode, cache)
    | none =>
      MessageOp.Outcome.ofExceptCached cache (do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨value, s⟩ ← s.pop
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost codeAddress s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress codeAddress
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s codeAddress
        let accessCost := preAccessCost + delegatedAccessGasCost
        let transferCost := if value = 0 then 0 else gasRules.callValue
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat s.gasLeft extendCost (accessCost + transferCost)
        let s ← s.chargeGas (msgCallCost + extendCost)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (s.account ctx.recipient).balance
        if senderBal < value then
          let s ← s.push 0
          return (.done (.ok ((s.withGasLeft (s.gasLeft + msgCallStipend)).withReturnData [])), cache)
        else
          return genericCall.stepCached ctx s msgCallStipend value ctx.recipient ctx.recipient
            newCodeAddress true false inputIndex inputSize outputIndex outputSize code
            disablePrecompiles cache :
        Except (ExceptionalHalt × Frame.State) (MessageOp.Outcome × Option CalldataCache))
  | .delegatecall =>
    match ctx.block.rules.stateGas with
    | some _ => (MessageOp.step ctx s .delegatecall, cache)
    | none =>
      MessageOp.Outcome.ofExceptCached cache (do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost codeAddress s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress codeAddress
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s codeAddress
        let accessCost := preAccessCost + delegatedAccessGasCost
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat s.gasLeft extendCost accessCost
        let s ← s.chargeGas (msgCallCost + extendCost)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCall.stepCached ctx s msgCallStipend ctx.value ctx.caller ctx.recipient
          newCodeAddress false false inputIndex inputSize outputIndex outputSize code
          disablePrecompiles cache :
        Except (ExceptionalHalt × Frame.State) (MessageOp.Outcome × Option CalldataCache))
  | .staticcall =>
    match ctx.block.rules.stateGas with
    | some _ => (MessageOp.step ctx s .staticcall, cache)
    | none =>
      MessageOp.Outcome.ofExceptCached cache (do
        let ⟨gas, s⟩ ← s.pop
        let ⟨target, s⟩ ← s.popToAddress
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost target s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress target
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s target
        let accessCost := preAccessCost + delegatedAccessGasCost
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat s.gasLeft extendCost accessCost
        let s ← s.chargeGas (msgCallCost + extendCost)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCall.stepCached ctx s msgCallStipend 0 ctx.recipient target newCodeAddress true
          true inputIndex inputSize outputIndex outputSize code disablePrecompiles cache :
        Except (ExceptionalHalt × Frame.State) (MessageOp.Outcome × Option CalldataCache))
  | x => (MessageOp.step ctx s x, cache)

private theorem MessageOp.stepCached_fst (ctx : CallContext) (s : Frame.State)
    (cache : Option CalldataCache) (x : MessageOp) :
    (MessageOp.stepCached ctx s cache x).1 = MessageOp.step ctx s x := by
  cases x <;> simp only [MessageOp.stepCached, MessageOp.step]
  case call =>
    rcases hs : ctx.block.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure', apply_ite (Except.map Prod.fst),
        genericCall.stepCached_fst]
      all_goals rfl
    · rfl
  case callcode =>
    rcases hs : ctx.block.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure', apply_ite (Except.map Prod.fst),
        genericCall.stepCached_fst]
      all_goals rfl
    · rfl
  case delegatecall =>
    rcases hs : ctx.block.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure', genericCall.stepCached_fst]
      all_goals rfl
    · rfl
  case staticcall =>
    rcases hs : ctx.block.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure', genericCall.stepCached_fst]
      all_goals rfl
    · rfl

private def NextOp.stepCached (r : Frame.Running) (cache : Option CalldataCache) (n : NextOp) :
    Step × Option CalldataCache :=
  let pc := r.pc + n.size
  match n with
  | .message x =>
    let result := MessageOp.stepCached r.context r.state cache x
    (MessageOp.Outcome.toStep pc result.1, result.2)
  | _ => (NextOp.step r n, cache)

private theorem NextOp.stepCached_fst (r : Frame.Running) (cache : Option CalldataCache)
    (n : NextOp) : (NextOp.stepCached r cache n).1 = NextOp.step r n := by
  cases n <;> simp [NextOp.stepCached, NextOp.step, MessageOp.stepCached_fst]

private def stepCached (r : Frame.Running) (cache : Option CalldataCache) :
    Except Fault Step × Option CalldataCache :=
  match r.getOp with
  | some (.next n) =>
    let result := NextOp.stepCached r cache n
    (.ok result.1, result.2)
  | _ => (step r, cache)

private theorem stepCached_fst (r : Frame.Running) (cache : Option CalldataCache) :
    (stepCached r cache).1 = step r := by
  unfold stepCached step
  cases h : r.getOp with
  | none => rfl
  | some op =>
    cases op with
    | next n => simp only [NextOp.stepCached_fst]
    | jump j => rfl
    | halt l => rfl

/-- Cache-threaded driver. Its semantic component is proved below to be exactly
`Checked.execFueled`; the extra component only retains a shareable physical representative of an
exact calldata slice, threaded through a child's run into its caller's continuation. -/
private def execFueledCachedCore :
    Frame.Running → Nat → Option CalldataCache → Fueled Fault Frame.Exit × Option CalldataCache
  | _, 0, cache => (Fueled.exhausted, cache)
  | r, fuel + 1, cache =>
    let ⟨step, cache⟩ := stepCached r cache
    match step with
    | .error fault => (Fueled.ofExcept (.error fault), cache)
    | .ok (.exit e) => (Fueled.ofExcept (.ok e), cache)
    | .ok (.next pc s) => execFueledCachedCore ⟨pc, r.context, s⟩ fuel cache
    | .ok (.spawn child pending pc) =>
      let ⟨settled, cache⟩ : Option (Except Fault Frame.Result) × Option CalldataCache :=
        match enter child with
        | .done result => (some result, cache)
        | .run childRunning =>
          let ⟨childResult, cache⟩ := execFueledCachedCore childRunning fuel cache
          ((childResult.run).map (· >>= settle child), cache)
      match settled with
      | none => (Fueled.exhausted, cache)
      | some (.error fault) => (Fueled.ofExcept (.error fault), cache)
      | some (.ok result) =>
        match resume r.context.block.rules pending child.checkpoint result with
        | .error fault => (Fueled.ofExcept (.error fault), cache)
        | .ok (.error (reason, s)) => (Fueled.ofExcept (.ok (.halted reason s)), cache)
        | .ok (.ok s) => execFueledCachedCore ⟨pc, r.context, s⟩ fuel cache

private theorem execFueledCachedCore_fst :
    ∀ fuel r cache, (execFueledCachedCore r fuel cache).1 = execFueled r fuel := by
  intro fuel
  induction fuel with
  | zero => intro r cache; rfl
  | succ fuel ih =>
    intro r cache
    rcases hstep : stepCached r cache with ⟨st, cache'⟩
    have hs : st = step r := by simpa [hstep] using stepCached_fst r cache
    simp only [execFueledCachedCore, hstep, execFueled, ← hs]
    rcases st with fault | (e | ⟨pc, s⟩ | ⟨child, pending, pc⟩)
    · rfl
    · rfl
    · exact ih ⟨pc, r.context, s⟩ cache'
    · dsimp only
      cases hentry : enter child with
      | done res =>
        dsimp only
        rcases res with fault | result
        · rfl
        · dsimp only
          rcases hr : resume r.context.block.rules pending child.checkpoint result with
            fault | (⟨reason, s⟩ | s)
          · rfl
          · rfl
          · exact ih _ cache'
      | run childRunning =>
        dsimp only
        rcases hchild : execFueledCachedCore childRunning fuel cache' with ⟨childResult, cache''⟩
        have hc : childResult = execFueled childRunning fuel := by
          simpa [hchild] using ih childRunning cache'
        subst hc
        dsimp only
        cases (execFueled childRunning fuel).run with
        | none => rfl
        | some raw =>
          simp only [Option.map]
          rcases hset : raw >>= settle child with fault | result
          · rfl
          · dsimp only
            rcases hr : resume r.context.block.rules pending child.checkpoint result with
              fault | (⟨reason, s⟩ | s)
            · rfl
            · rfl
            · exact ih _ cache''

/-- The cached driver. -/
def execFueledCached (r : Frame.Running) (fuel : Nat) : Fueled Fault Frame.Exit :=
  (execFueledCachedCore r fuel none).1

/-- The driver is its cached twin, and the compiled-code substitution: code compiled with this
in scope runs `execFueledCached` wherever it calls `execFueled`. -/
@[csimp] theorem execFueled_eq_cached :
    execFueled = execFueledCached := by
  funext r fuel
  symm
  exact execFueledCachedCore_fst fuel r none

end Jaune.Checked
