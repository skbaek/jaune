import Jaune.MessageCall.Driver

/-!
# The cached twin of the staged driver (goal `jaune-shape-and-names-v1`, W1 unit H)

Implementation module (see `scripts/layering.json`). `execFueledCached` is a second
implementation of the staged driver `execFueled`, kept for speed: it threads a cache
that shares one physical copy of an identical calldata slice across a deep call path. Its
semantic component is proved equal to `execFueled` (`execFueledCachedCore_fst`), and
the compiled-code substitution theorem `execFueled_eq_cached` makes the compiled code run it in
place of `execFueled`.

This is today's `Jaune.Impl.CachedExec` over the staged `Step`: the same cache, the same
coverage (the four legacy call arms cached; the Amsterdam arms and the creation opcodes take
the ordinary definition), and `genericCall.stepCached` is the fifth producer of a spawn, proved
equal to the staged `genericCall.step`.

A substitution theorem rewrites only code compiled after it is in scope, so
`Jaune.MessageCall.Exec`, which defines the staged total `exec`, imports this module. Both this
module and today's `Jaune.Impl.CachedExec` stand until the delete commit removes the old
chain.
-/

namespace Jaune

open Jaune

/-! The cache: one exact calldata slice kept available for structural sharing. The key is the
compact backing array plus the requested range; the padded `Bytes` value is allocated once and
reused when a later call asks for the identical slice. The proof field is erased by code
generation and makes every hit definitionally accountable to the ordinary `Array.sliceD`
result. A private copy of today's (`Jaune.Impl.CachedExec`), which is private there and is
deleted with the old chain. -/

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

/-- The fifth producer of a spawn: the staged `genericCall.step` with the calldata slice taken
through the cache. -/
private def genericCall.stepCached
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool)
    (cache : Option CalldataCache) : MessageOp.Outcome × Option CalldataCache :=
  let evm1 := devm.withReturnData []
  if sevm.depth = 0 then
    (MessageOp.Outcome.ofExcept do
      let devm ← (evm1.withGasLeft (evm1.gasLeft + gas)).push 0
      return .done (.ok devm), cache)
  else
    let (calldata, cache) :=
      CalldataCache.get cache evm1.memory.data inputIndex inputSize
    let message :=
      callMessage sevm gas value caller target codeAddress
        shouldTransferValue isStaticcall calldata code disablePrecompiles
    (.spawn ⟨message, Frame.State.ofDevm evm1⟩
      ⟨.call outputIndex outputSize, false, evm1.output, evm1.error⟩, cache)

private theorem genericCall.stepCached_fst
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address)
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

/-- The cache-threaded counterpart of `MessageOp.Outcome.ofExcept`: an `Except` whose value
already carries the threaded cache, with the untouched cache restored on the error path. -/
private def MessageOp.Outcome.ofExceptCached
    (cache : Option CalldataCache)
    (ec : Except (EvmError × Devm) (MessageOp.Outcome × Option CalldataCache)) :
    MessageOp.Outcome × Option CalldataCache :=
  match ec with
  | .error e => (.done (.error e), cache)
  | .ok result => result

private theorem MessageOp.Outcome.ofExceptCached_fst
    (cache : Option CalldataCache)
    {ec : Except (EvmError × Devm) (MessageOp.Outcome × Option CalldataCache)}
    {eu : Except (EvmError × Devm) MessageOp.Outcome}
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

/-- Cache-threaded specialization of the staged `MessageOp.step`. The four call opcodes'
legacy (`stateGas = none`) arms are reproduced verbatim with `genericCall.stepCached` in place
of `genericCall.step` and the cache threaded through the early returns; every other arm is the
ordinary definition. Coverage is today's (`Jaune.Impl.CachedExec`). -/
private def MessageOp.stepCached
    (sevm : Sevm) (devm : Devm) (cache : Option CalldataCache) :
    MessageOp → MessageOp.Outcome × Option CalldataCache
  | .call =>
    match sevm.benvStat.rules.stateGas with
    | some _ => (MessageOp.step sevm devm .call, cache)
    | none =>
    MessageOp.Outcome.ofExceptCached cache (do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨callee, devm⟩ ← devm.popToAdr
      let ⟨value, devm⟩ ← devm.pop
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let gasRules := sevm.benvStat.rules.gas
      -- Before EIP-2929 the base is flat and the accessed set is untouched.
      let preAccessCost :=
        match sevm.benvStat.rules.access with
        | .eip2929 => gasRules.accessCost callee devm.accessedAddresses
        | .flat g => g.call
      let devm :=
        match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress devm callee
        | .flat _ => devm
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        sevm.benvStat.rules.accessDelegation devm callee
      let accessCost := preAccessCost + delegatedAccessGasCost
      let createCost :=
        if (¬ (devm.getAcct callee).isEmpty) ∨ value = 0 then 0 else Gas.newAccount
      let transferCost := if value = 0 then 0 else gasRules.callValue
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
          (accessCost + createCost + transferCost)
      let devm ← chargeGas (msgCallCost + extendCost) devm
      Except.assert (!sevm.isStatic ∨ value = 0) ⟨.halt (.writeInStaticContext .none), devm⟩
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal := (devm.getAcct sevm.currentTarget).balance
      if senderBal < value then
        let devm ← devm.push 0
        return (.done
          (.ok
            ((devm.withReturnData []).withGasLeft
              (devm.gasLeft + msgCallStipend))), cache)
      else
        return genericCall.stepCached
          sevm devm msgCallStipend value sevm.currentTarget callee
          newCodeAddress true false inputIndex inputSize outputIndex outputSize
          code disablePrecompiles cache :
      Except (EvmError × Devm) (MessageOp.Outcome × Option CalldataCache))
  | .callcode =>
    match sevm.benvStat.rules.stateGas with
    | some _ => (MessageOp.step sevm devm .callcode, cache)
    | none =>
    MessageOp.Outcome.ofExceptCached cache (do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨codeAddress, devm⟩ ← devm.popToAdr
      let ⟨value, devm⟩ ← devm.pop
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let gasRules := sevm.benvStat.rules.gas
      -- Before EIP-2929 the base is flat and the accessed set is untouched.
      let preAccessCost :=
        match sevm.benvStat.rules.access with
        | .eip2929 => gasRules.accessCost codeAddress devm.accessedAddresses
        | .flat g => g.call
      let devm :=
        match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress devm codeAddress
        | .flat _ => devm
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        sevm.benvStat.rules.accessDelegation devm codeAddress
      let accessCost := preAccessCost + delegatedAccessGasCost
      let transferCost := if value = 0 then 0 else gasRules.callValue
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
          (accessCost + transferCost)
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal := (devm.getAcct sevm.currentTarget).balance
      if senderBal < value then
        let devm ← devm.push 0
        return (.done
          (.ok
            ((devm.withGasLeft (devm.gasLeft + msgCallStipend)).withReturnData [])),
          cache)
      else
        return genericCall.stepCached
          sevm devm msgCallStipend value sevm.currentTarget
          sevm.currentTarget newCodeAddress true false
          inputIndex inputSize outputIndex outputSize code disablePrecompiles
          cache :
      Except (EvmError × Devm) (MessageOp.Outcome × Option CalldataCache))
  | .delegatecall =>
    match sevm.benvStat.rules.stateGas with
    | some _ => (MessageOp.step sevm devm .delegatecall, cache)
    | none =>
    MessageOp.Outcome.ofExceptCached cache (do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨codeAddress, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let gasRules := sevm.benvStat.rules.gas
      -- Before EIP-2929 the base is flat and the accessed set is untouched.
      let preAccessCost :=
        match sevm.benvStat.rules.access with
        | .eip2929 => gasRules.accessCost codeAddress devm.accessedAddresses
        | .flat g => g.call
      let devm :=
        match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress devm codeAddress
        | .flat _ => devm
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        sevm.benvStat.rules.accessDelegation devm codeAddress
      let accessCost := preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ :=
        calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost accessCost
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm :=
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      return genericCall.stepCached
        sevm devm msgCallStipend sevm.value sevm.caller
        sevm.currentTarget newCodeAddress false false
        inputIndex inputSize outputIndex outputSize code disablePrecompiles
        cache :
      Except (EvmError × Devm) (MessageOp.Outcome × Option CalldataCache))
  | .staticcall =>
    match sevm.benvStat.rules.stateGas with
    | some _ => (MessageOp.step sevm devm .staticcall, cache)
    | none =>
    MessageOp.Outcome.ofExceptCached cache (do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨target, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost :=
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let gasRules := sevm.benvStat.rules.gas
      -- Before EIP-2929 the base is flat and the accessed set is untouched.
      let preAccessCost :=
        match sevm.benvStat.rules.access with
        | .eip2929 => gasRules.accessCost target devm.accessedAddresses
        | .flat g => g.call
      let devm :=
        match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress devm target
        | .flat _ => devm
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
        sevm.benvStat.rules.accessDelegation devm target
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
      Except (EvmError × Devm) (MessageOp.Outcome × Option CalldataCache))
  | x => (MessageOp.step sevm devm x, cache)

private theorem MessageOp.stepCached_fst
    (sevm : Sevm) (devm : Devm) (cache : Option CalldataCache) (x : MessageOp) :
    (MessageOp.stepCached sevm devm cache x).1 = MessageOp.step sevm devm x := by
  cases x <;> simp only [MessageOp.stepCached, MessageOp.step]
  case call =>
    rcases hs : sevm.benvStat.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure',
        apply_ite (Except.map Prod.fst),
        genericCall.stepCached_fst]
      all_goals rfl
    · rfl
  case callcode =>
    rcases hs : sevm.benvStat.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure',
        apply_ite (Except.map Prod.fst),
        genericCall.stepCached_fst]
      all_goals rfl
    · rfl
  case delegatecall =>
    rcases hs : sevm.benvStat.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure',
        genericCall.stepCached_fst]
      all_goals rfl
    · rfl
  case staticcall =>
    rcases hs : sevm.benvStat.rules.stateGas with _ | state
    · refine MessageOp.Outcome.ofExceptCached_fst cache ?_
      simp only [Except.map_bind', Except.map_pure',
        genericCall.stepCached_fst]
      all_goals rfl
    · rfl

private def NextOp.stepCached
    (evm : Evm) (cache : Option CalldataCache) (n : NextOp) :
    Step × Option CalldataCache :=
  let pc := evm.pc + n.size
  match n with
  | .message x =>
    let result := MessageOp.stepCached evm.sta evm.dyna cache x
    (MessageOp.Outcome.toStep pc result.1, result.2)
  | _ => (NextOp.step evm n, cache)

private theorem NextOp.stepCached_fst
    (evm : Evm) (cache : Option CalldataCache) (n : NextOp) :
    (NextOp.stepCached evm cache n).1 = NextOp.step evm n := by
  cases n <;>
    simp [NextOp.stepCached, NextOp.step, MessageOp.stepCached_fst]

private def Evm.stepCached
    (evm : Evm) (cache : Option CalldataCache) :
    Step × Option CalldataCache :=
  match evm.getInst with
  | .none =>
    (.halt (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩), cache)
  | .some (.next n) => NextOp.stepCached evm cache n
  | .some (.jump j) => (Step.ofJump (j.run evm), cache)
  | .some (.halt l) => (.halt (l.run evm.sta evm.dyna), cache)

private theorem Evm.stepCached_fst
    (evm : Evm) (cache : Option CalldataCache) :
    (Evm.stepCached evm cache).1 = Evm.step evm := by
  unfold Evm.stepCached Evm.step
  cases h : evm.getInst with
  | none => rfl
  | some inst =>
    cases inst with
    | next n => exact NextOp.stepCached_fst evm cache n
    | jump j => rfl
    | halt l => rfl

/-- Cache-threaded staged driver. Its semantic component is proved below to be exactly
`execFueled`; the extra component only retains a shareable physical representative of
an exact calldata slice, threaded through a child's run into its caller's continuation. -/
private def execFueledCachedCore :
    Evm → Nat → Option CalldataCache →
      Fueled (EvmError × Devm) Devm × Option CalldataCache
  | _, 0, cache => (Fueled.exhausted, cache)
  | evm, fuel + 1, cache =>
    let ⟨step, cache⟩ := Evm.stepCached evm cache
    match step with
    | .halt ex => (Fueled.ofExcept ex, cache)
    | .next pc devm => execFueledCachedCore ⟨pc, evm.sta, devm⟩ fuel cache
    | .spawn child pending pc =>
      let ⟨settled, cache⟩ : Option (Except Fault Frame.Result) × Option CalldataCache :=
        match enter child with
        | .done result => (some result, cache)
        | .run childEvm =>
          let ⟨childResult, cache⟩ := execFueledCachedCore childEvm fuel cache
          ((childResult.run).map (settle child), cache)
      match settled with
      | none => (Fueled.exhausted, cache)
      | some (.error fault) =>
        (Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm)), cache)
      | some (.ok result) =>
        match resume evm.sta.benvStat.rules pending child.checkpoint result with
        | .error fault =>
          (Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm)), cache)
        | .ok (.error (reason, devm)) => (Fueled.ofExcept (.error (.halt reason, devm)), cache)
        | .ok (.ok devm) => execFueledCachedCore ⟨pc, evm.sta, devm⟩ fuel cache

private theorem execFueledCachedCore_fst :
    ∀ fuel evm cache,
      (execFueledCachedCore evm fuel cache).1 = execFueled evm fuel := by
  intro fuel
  induction fuel with
  | zero => intro evm cache; rfl
  | succ fuel ih =>
    intro evm cache
    rcases hstep : Evm.stepCached evm cache with ⟨step, cache'⟩
    have hs : step = Evm.step evm := by
      simpa [hstep] using Evm.stepCached_fst evm cache
    simp only [execFueledCachedCore, hstep, execFueled, ← hs]
    cases step with
    | halt ex => rfl
    | next pc devm => exact ih ⟨pc, evm.sta, devm⟩ cache'
    | spawn child pending pc =>
      dsimp only
      cases hentry : enter child with
      | done r =>
        dsimp only
        rcases r with fault | result
        · rfl
        · dsimp only
          rcases hr : resume evm.sta.benvStat.rules pending child.checkpoint result with
            fault | (⟨reason, devm⟩ | devm)
          · rfl
          · rfl
          · exact ih _ cache'
      | run childEvm =>
        dsimp only
        rcases hchild : execFueledCachedCore childEvm fuel cache' with ⟨childResult, cache''⟩
        have hc : childResult = execFueled childEvm fuel := by
          simpa [hchild] using ih childEvm cache'
        subst hc
        dsimp only
        cases (execFueled childEvm fuel).run with
        | none => rfl
        | some raw =>
          simp only [Option.map]
          rcases hset : settle child raw with fault | result
          · rfl
          · dsimp only
            rcases hr : resume evm.sta.benvStat.rules pending child.checkpoint result with
              fault | (⟨reason, devm⟩ | devm)
            · rfl
            · rfl
            · exact ih _ cache''

private def execFueledCached
    (evm : Evm) (fuel : Nat) : Fueled (EvmError × Devm) Devm :=
  (execFueledCachedCore evm fuel none).1

@[csimp] private theorem execFueled_eq_cached :
    execFueled = execFueledCached := by
  funext evm fuel
  symm
  exact execFueledCachedCore_fst fuel evm none

end Jaune

