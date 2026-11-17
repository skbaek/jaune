import Jaune.Transaction

/-!
# What a spawn and a top-level frame carry (goal `jaune-shape-and-names-v1`, W1; Blanc ledger rows 5
and 8)

* **Creation is the message's kind.** A child message built by a create tail has kind `.create`
  and no code address; one built by a call tail has kind `.call` and a code address. So every
  message `Evm.step` spawns satisfies `Message.KindCoherent`: `kind = .create ↔ codeAddress = none`
  (`Evm.step_spawn_kindCoherent`). A top-level frame's message is coherent exactly when its
  creation flag agrees with its `Msg`'s code address (`Message.ofLegacy_kindCoherent_iff`);
  `prepareMessage` builds a `Msg` whose code address is absent exactly when its target is
  (`prepareMessage_codeAddress_eq_none_iff`), and the creation flag `processMessageCall` passes is
  `msg.target.isNone`; top-level delegation resolution only ever sets a code address
  (`Msg.resolveCodeDelegation_codeAddress_eq_none`).
* **The spawn checkpoint.** A spawned child's checkpoint is its caller after the opcode's own
  effects, warming included (`genericCall.step_spawn_checkpoint` and its three siblings); a
  created address is warm in its checkpoint (`Evm.step_spawn_create_warm`).
-/

namespace Jaune

/-- A message's kind and code address agree: a creation has no code address, a call has one. -/
def Message.KindCoherent (m : Message) : Prop :=
  m.kind = .create ↔ m.codeAddress = none

theorem Message.kindCoherent_call {m : Message} (hk : m.kind = .call) (a : Address)
    (ha : m.codeAddress = some a) : m.KindCoherent := by
  unfold Message.KindCoherent; rw [hk, ha]; simp

theorem Message.kindCoherent_create {m : Message} (hk : m.kind = .create)
    (ha : m.codeAddress = none) : m.KindCoherent := by
  unfold Message.KindCoherent; rw [hk, ha]; simp

/-! ### The spawn checkpoint, tail by tail -/

/-- A CALL-family spawn: the child calls `codeAddress`, its checkpoint is the caller as the
opcode left it with the return data cleared, and the result goes to the output window. -/
theorem genericCall.step_spawn_checkpoint
    {sevm : Sevm} {devm : Devm} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (hs : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn child pending) :
    child.checkpoint = Frame.State.ofDevm (devm.withReturnData []) ∧
      pending.target = .call outputIndex outputSize ∧
      child.message.kind = .call ∧ child.message.codeAddress = some codeAddress := by
  simp only [genericCall.step, Bind.bind, Except.bind, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq,
    reduceCtorEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- An Amsterdam CALL-family spawn: as `genericCall.step_spawn_checkpoint`. -/
theorem genericCallAmsterdam.step_spawn_checkpoint
    {sevm : Sevm} {state : StateGasRules} {devm : Devm}
    {gas reservoir : Nat} {value : U256}
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles newAccountCharged insufficientBalance : Bool}
    {child : Frame} {pending : Pending}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value
      caller target codeAddress shouldTransferValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles
      newAccountCharged insufficientBalance = .spawn child pending) :
    child.checkpoint = Frame.State.ofDevm (devm.withReturnData []) ∧
      pending.target = .call outputIndex outputSize ∧
      child.message.kind = .call ∧ child.message.codeAddress = some codeAddress := by
  simp only [genericCallAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq,
    reduceCtorEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A CREATE-family spawn: the checkpoint is the caller after the gas withheld for the child, the
cleared return data, the creator's nonce increment and the new address's warming; the child
creates at `newAddress`. -/
theorem genericCreate.step_spawn_checkpoint
    {sevm : Sevm} {devm : Devm} {endowment : U256} {newAddress : Address}
    {memoryIndex memorySize : Nat} {child : Frame} {pending : Pending}
    (hs : genericCreate.step sevm devm endowment newAddress memoryIndex memorySize
      = .spawn child pending) :
    child.checkpoint = Frame.State.ofDevm (addAccessedAddress
        (((devm.withGasLeft (devm.gasLeft - except64th devm.gasLeft)).withReturnData []).incrNonce
          sevm.currentTarget) newAddress) ∧
      pending.target = .create newAddress ∧
      child.message.kind = .create ∧ child.message.codeAddress = none ∧
      child.message.context.recipient = newAddress := by
  simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
    assertDynamic, Pure.pure, Except.pure] at hs
  repeat' split at hs
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq,
    reduceCtorEq] at hs
  all_goals obtain ⟨rfl, rfl⟩ := hs
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem chargeStateGas_accessedAddresses {amount : Nat} {d d' : Devm}
    (h : chargeStateGas amount d = .ok d') : d'.accessedAddresses = d.accessedAddresses := by
  unfold chargeStateGas liftMachExecution liftMach Footprint.toExecution Footprint.liftOutcome at h
  rcases hc : Mach.chargeStateGas amount d.mach with ⟨err, view⟩ | ⟨u, mach'⟩ <;>
    simp only [hc] at h
  · cases h
  · cases h; rfl

private theorem create_tail_accessedAddresses (d : Devm) (a : Address) :
    (d.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce a).accessedAddresses =
      d.accessedAddresses := rfl

/-- An Amsterdam CREATE-family spawn: the checkpoint is the caller after the opcode's effects, in
which the new address is warm; the child creates at `newAddress`. -/
theorem genericCreateAmsterdam.step_spawn_checkpoint
    {sevm : Sevm} {state : StateGasRules} {devm : Devm} {endowment : U256}
    {newAddress : Address} {memoryIndex memorySize : Nat} {child : Frame} {pending : Pending}
    (hs : genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize = .spawn child pending) :
    (∃ evm1 : Devm, child.checkpoint = Frame.State.ofDevm evm1 ∧
        newAddress ∈ evm1.accessedAddresses) ∧
      pending.target = .create newAddress ∧
      child.message.kind = .create ∧ child.message.codeAddress = none ∧
      child.message.context.recipient = newAddress := by
  simp only [genericCreateAmsterdam.step, Bind.bind, Except.bind, Pure.pure,
    Except.pure] at hs
  repeat' split at hs
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq,
    reduceCtorEq] at hs
  all_goals obtain ⟨rfl, rfl⟩ := hs
  all_goals refine ⟨⟨_, rfl, ?_⟩, rfl, rfl, rfl, rfl⟩
  all_goals rw [create_tail_accessedAddresses]
  all_goals try rw [chargeStateGas_accessedAddresses ‹chargeStateGas _ _ = _›]
  all_goals
    rw [Devm.balReadAccount_accessedAddresses]
    exact (Std.HashSet.mem_insert_self : newAddress ∈ (_ : AdrSet).insert newAddress)

/-! ### Every spawn -/

/-- What a spawn carries: a call, with a code address; or a creation, without one, whose new
address is warm in the child's checkpoint. -/
private def SpawnShape (child : Frame) : Prop :=
  (child.message.kind = .call ∧ ∃ a, child.message.codeAddress = some a) ∨
    (child.message.kind = .create ∧ child.message.codeAddress = none ∧
      child.message.context.recipient ∈ child.checkpoint.substate.accessedAddresses)

private theorem SpawnShape.ofCall {child : Frame} (hk : child.message.kind = .call) {a : Address}
    (ha : child.message.codeAddress = some a) : SpawnShape child :=
  .inl ⟨hk, a, ha⟩

private theorem shape_call {sevm devm gas value caller target codeAddress transfer static ii is oi os
    code disable child pending}
    (hs : genericCall.step sevm devm gas value caller target codeAddress transfer static ii is oi
      os code disable = .spawn child pending) : SpawnShape child :=
  SpawnShape.ofCall (genericCall.step_spawn_checkpoint hs).2.2.1
    (genericCall.step_spawn_checkpoint hs).2.2.2

private theorem shape_callA {sevm state devm gas reservoir value caller target codeAddress transfer
    static ii is oi os code disable charged insufficient child pending}
    (hs : genericCallAmsterdam.step sevm state devm gas reservoir value caller target codeAddress
      transfer static ii is oi os code disable charged insufficient = .spawn child pending) :
    SpawnShape child :=
  SpawnShape.ofCall (genericCallAmsterdam.step_spawn_checkpoint hs).2.2.1
    (genericCallAmsterdam.step_spawn_checkpoint hs).2.2.2

private theorem shape_create {sevm devm endowment newAddress mi ms child pending}
    (hs : genericCreate.step sevm devm endowment newAddress mi ms = .spawn child pending) :
    SpawnShape child := by
  obtain ⟨h1, -, h3, h4, h5⟩ := genericCreate.step_spawn_checkpoint hs
  refine .inr ⟨h3, h4, ?_⟩
  rw [h5, h1]
  exact (Std.HashSet.mem_insert_self : _ ∈ (_ : AdrSet).insert _)

private theorem shape_createA {sevm state devm endowment newAddress mi ms child pending}
    (hs : genericCreateAmsterdam.step sevm state devm endowment newAddress mi ms
      = .spawn child pending) : SpawnShape child := by
  obtain ⟨⟨evm1, h1, hm⟩, -, h3, h4, h5⟩ := genericCreateAmsterdam.step_spawn_checkpoint hs
  refine .inr ⟨h3, h4, ?_⟩
  rw [h5, h1]
  exact hm

/-- What a message opcode spawns: a call, with a code address; or a creation, without one, whose
new address is warm in the child's checkpoint. -/
theorem MessageOp.step_spawn_cases {sevm : Sevm} {devm : Devm} {x : MessageOp}
    {child : Frame} {pending : Pending} (hs : MessageOp.step sevm devm x = .spawn child pending) :
    (child.message.kind = .call ∧ ∃ a, child.message.codeAddress = some a) ∨
      (child.message.kind = .create ∧ child.message.codeAddress = none ∧
        child.message.context.recipient ∈ child.checkpoint.substate.accessedAddresses) := by
  show SpawnShape child
  cases x <;>
    simp only [MessageOp.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [MessageOp.Outcome.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact shape_call hs
      | exact shape_callA hs
      | exact shape_create hs
      | exact shape_createA hs

private theorem toStep_eq_spawn {o : MessageOp.Outcome} {pc pc' : Nat} {child : Frame}
    {pending : Pending} (h : o.toStep pc = .spawn child pending pc') :
    o = .spawn child pending := by
  cases o with
  | done ex => cases ex <;> cases h
  | spawn c p => cases h; rfl

/-- Every spawn of a step comes from a message opcode. -/
theorem Evm.step_spawn_message {evm : Evm} {child : Frame} {pending : Pending} {pc : Nat}
    (h : Evm.step evm = .spawn child pending pc) :
    ∃ x, MessageOp.step evm.sta evm.dyna x = .spawn child pending := by
  unfold Evm.step at h
  split at h
  · cases h
  · rename_i n _
    cases n with
    | message x => exact ⟨x, toStep_eq_spawn h⟩
    | _ =>
      exfalso
      simp only [NextOp.step] at h
      repeat' split at h
      all_goals first
        | cases h
        | (simp only [Step.ofExecution] at h; split at h <;> cases h)
  · simp only [Step.ofJump] at h; split at h <;> cases h
  · cases h

/-- **Creation is the message's kind.** Every message `Evm.step` spawns has kind `.create` exactly
when it has no code address. -/
theorem Evm.step_spawn_kindCoherent {evm : Evm} {child : Frame} {pending : Pending} {pc : Nat}
    (h : Evm.step evm = .spawn child pending pc) : child.message.KindCoherent := by
  obtain ⟨x, hx⟩ := Evm.step_spawn_message h
  rcases MessageOp.step_spawn_cases hx with ⟨hk, a, ha⟩ | ⟨hk, ha, -⟩
  · exact Message.kindCoherent_call hk a ha
  · exact Message.kindCoherent_create hk ha

/-- **Warmth of a created address.** A creation `Evm.step` spawns starts from a checkpoint in which
its new address is warm. -/
theorem Evm.step_spawn_create_warm {evm : Evm} {child : Frame} {pending : Pending} {pc : Nat}
    (h : Evm.step evm = .spawn child pending pc) (hk : child.message.kind = .create) :
    child.message.context.recipient ∈ child.checkpoint.substate.accessedAddresses := by
  obtain ⟨x, hx⟩ := Evm.step_spawn_message h
  rcases MessageOp.step_spawn_cases hx with ⟨hk', -⟩ | ⟨-, -, hw⟩
  · rw [hk] at hk'; cases hk'
  · exact hw

/-- **A call's checkpoint is its caller's.** A call `Evm.step` spawns starts from the caller as the
opcode left it, return data cleared: every address warm there is warm in the child's checkpoint. -/
theorem MessageOp.step_spawn_call_checkpoint {sevm : Sevm} {devm : Devm} {x : MessageOp}
    {child : Frame} {pending : Pending} (hs : MessageOp.step sevm devm x = .spawn child pending)
    (hk : child.message.kind = .call) :
    ∃ evm1 : Devm, child.checkpoint = Frame.State.ofDevm (evm1.withReturnData []) := by
  cases x <;>
    simp only [MessageOp.step, Bind.bind, Except.bind, Except.assert,
      Pure.pure, Except.pure] at hs <;>
    repeat' split at hs
  all_goals simp only [MessageOp.Outcome.ofExcept, reduceCtorEq] at hs
  all_goals
    first
      | exact ⟨_, (genericCall.step_spawn_checkpoint hs).1⟩
      | exact ⟨_, (genericCallAmsterdam.step_spawn_checkpoint hs).1⟩
      | exact absurd ((genericCreate.step_spawn_checkpoint hs).2.2.1.symm.trans hk)
          (by simp)
      | exact absurd ((genericCreateAmsterdam.step_spawn_checkpoint hs).2.2.1.symm.trans hk)
          (by simp)

/-! ### The top level -/

/-- A top-level frame's message is coherent exactly when its creation flag agrees with its
`Msg`'s code address. -/
theorem Message.ofLegacy_kindCoherent_iff (msg : Msg) (isCreate : Bool) :
    (Message.ofLegacy msg isCreate).KindCoherent ↔ (isCreate = true ↔ msg.codeAddress = none) := by
  unfold Message.KindCoherent Message.ofLegacy
  cases isCreate <;> simp

/-- `prepareMessage` gives a creation (no target) exactly no code address. -/
theorem prepareMessage_codeAddress_eq_none_iff {benv : Benv} {tenv : Tenv} {tx : Transaction}
    {msg : Msg} (h : prepareMessage benv tenv tx = .ok msg) :
    msg.codeAddress = none ↔ msg.target = none := by
  unfold prepareMessage at h
  rcases hto : tx.type.to? with _ | t <;>
    simp only [hto, Except.ok.injEq] at h <;> subst h <;> simp

/-- Top-level delegation resolution only ever sets a code address. -/
theorem Msg.resolveCodeDelegation_codeAddress_eq_none {msg : Msg}
    (h : msg.resolveCodeDelegation.codeAddress = none) : msg.codeAddress = none := by
  unfold Msg.resolveCodeDelegation at h
  split at h
  · exact h
  · cases h

/-- The top-level creation frame `processMessageCall.create` runs on a prepared message is
coherent. -/
theorem prepareMessage_create_kindCoherent {benv : Benv} {tenv : Tenv} {tx : Transaction}
    {msg : Msg} (h : prepareMessage benv tenv tx = .ok msg) (hc : msg.target = none) :
    (Frame.ofTop msg true).message.KindCoherent := by
  refine (Message.ofLegacy_kindCoherent_iff msg true).mpr ?_
  exact iff_of_true rfl ((prepareMessage_codeAddress_eq_none_iff h).mpr hc)

/-- The top-level call frame `processMessageCall.call` runs (pre-Amsterdam, on a message with a
target and after delegation resolution) is coherent. -/
theorem resolveCodeDelegation_call_kindCoherent {msg : Msg} (h : msg.codeAddress ≠ none) :
    (Frame.ofTop msg.resolveCodeDelegation false).message.KindCoherent := by
  refine (Message.ofLegacy_kindCoherent_iff _ false).mpr ?_
  exact iff_of_false (by simp) (fun e => h (Msg.resolveCodeDelegation_codeAddress_eq_none e))

end Jaune
