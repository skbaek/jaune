import Jaune.Execution

/-!
Generic frame and step relations used by complete execution derivations.
This module depends only on Jaune and its ordinary Lean dependencies.
Compiler stack-prefix relations remain owned by Blanc.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

def JumpOp.Run (evm : Evm) :
    JumpOp → Except (EvmError × Devm) (Nat × Devm) → Prop :=
  λ j ex => j.run evm = ex

def HaltOp.Run (sevm : Sevm) (devm : Devm) : HaltOp → Execution → Prop :=
  λ l ex => l.run sevm devm = ex

@[implicit_reducible] def Xlot : Type := Option (Evm × Execution)

/-- Fieldwise relations used to assemble the canonical `Devm.Rel` frames. -/
structure Devm.Rels : Type where
  (stack : List U256 → List U256 → Prop)
  (memory : Mem → Mem → Prop)
  (gasLeft : Nat → Nat → Prop)
  (logs : List Log → List Log → Prop)
  (refundCounter : Int → Int → Prop)
  (output : Bytes → Bytes → Prop)
  (accountsToDelete : AdrSet → AdrSet → Prop)
  (returnData : Bytes → Bytes → Prop)
  (error : Option SettledHalt → Option SettledHalt → Prop)
  (accessedAddresses : AdrSet → AdrSet → Prop)
  (accessedStorageKeys : KeySet → KeySet → Prop)
  (state : State → State → Prop)
  (createdAccounts : AdrSet → AdrSet → Prop)
  (transientStorage : TransientStorage → TransientStorage → Prop)
  (stateGas : StateGasMeter → StateGasMeter → Prop)
  (accountReads : AdrSet → AdrSet → Prop)
  (storageReads : KeySet → KeySet → Prop)
  (storageWrites : KeySet → KeySet → Prop)
  (touchedAccounts : AdrSet → AdrSet → Prop)

/-- Canonical relation between dynamic EVM states, assembled field by field. -/
structure Devm.Rel (rels : Devm.Rels) (devm devm' : Devm) : Prop where
  (stack : rels.stack devm.stack devm'.stack)
  (memory : rels.memory devm.memory devm'.memory)
  (gasLeft : rels.gasLeft devm.gasLeft devm'.gasLeft)
  (logs : rels.logs devm.logs devm'.logs)
  (refundCounter : rels.refundCounter devm.refundCounter devm'.refundCounter)
  (output : rels.output devm.output devm'.output)
  ( accountsToDelete :
    rels.accountsToDelete devm.accountsToDelete devm'.accountsToDelete)
  (returnData : rels.returnData devm.returnData devm'.returnData)
  (error : rels.error devm.error devm'.error)
  ( accessedAddresses :
    rels.accessedAddresses devm.accessedAddresses devm'.accessedAddresses )
  ( accessedStorageKeys :
    rels.accessedStorageKeys devm.accessedStorageKeys devm'.accessedStorageKeys )
  (state : rels.state devm.state devm'.state)
  ( createdAccounts :
    rels.createdAccounts devm.createdAccounts devm'.createdAccounts )
  ( transientStorage :
    rels.transientStorage devm.transientStorage devm'.transientStorage )
  (stateGas : rels.stateGas devm.stateGas devm'.stateGas)
  ( accountReads :
    rels.accountReads devm.meta.accountReads devm'.meta.accountReads )
  ( storageReads :
    rels.storageReads devm.meta.storageReads devm'.meta.storageReads )
  ( storageWrites :
    rels.storageWrites devm.world.storageWrites devm'.world.storageWrites )
  ( touchedAccounts :
    rels.touchedAccounts devm.meta.touchedAccounts devm'.meta.touchedAccounts )

def Devm.Rels.eq : Devm.Rels :=
  {
    stack := _root_.Eq,
    memory := _root_.Eq,
    gasLeft := _root_.Eq,
    logs := _root_.Eq,
    refundCounter := _root_.Eq,
    output := _root_.Eq,
    accountsToDelete := _root_.Eq,
    returnData := _root_.Eq,
    error := _root_.Eq,
    accessedAddresses := _root_.Eq,
    accessedStorageKeys := _root_.Eq,
    state := _root_.Eq,
    createdAccounts := _root_.Eq,
    transientStorage := _root_.Eq,
    stateGas := _root_.Eq,
    accountReads := _root_.Eq,
    storageReads := _root_.Eq
    storageWrites := _root_.Eq
    touchedAccounts := _root_.Eq
  }

def Devm.Burn : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := (· ≥ · )
  }

/-! ### Fieldwise laws of `Devm.Rel`

Names and statements are the ones Blanc carried; Jaune now owns them, so a new
`Devm.Rels` field is repaired here, once. -/

/-- Functional compatibility form of reflexivity, avoiding the deprecated root alias. -/
abbrev ReflexiveRel {α : Sort _} (r : α → α → Prop) : Prop := ∀ x, r x x

/-- Functional compatibility form of transitivity, avoiding the deprecated root alias. -/
abbrev TransitiveRel {α : Sort _} (r : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, r x y → r y z → r x z

def Devm.Rels.Refl (r : Devm.Rels) : Prop :=
  ReflexiveRel r.stack ∧ ReflexiveRel r.memory ∧ ReflexiveRel r.gasLeft ∧
  ReflexiveRel r.logs ∧ ReflexiveRel r.refundCounter ∧ ReflexiveRel r.output ∧
  ReflexiveRel r.accountsToDelete ∧ ReflexiveRel r.returnData ∧ ReflexiveRel r.error ∧
  ReflexiveRel r.accessedAddresses ∧ ReflexiveRel r.accessedStorageKeys ∧
  ReflexiveRel r.state ∧ ReflexiveRel r.createdAccounts ∧
  ReflexiveRel r.transientStorage ∧ ReflexiveRel r.stateGas ∧
  ReflexiveRel r.accountReads ∧ ReflexiveRel r.storageReads ∧ ReflexiveRel r.storageWrites ∧
  ReflexiveRel r.touchedAccounts

def Devm.Rels.Trans (r : Devm.Rels) : Prop :=
  TransitiveRel r.stack ∧ TransitiveRel r.memory ∧ TransitiveRel r.gasLeft ∧
  TransitiveRel r.logs ∧ TransitiveRel r.refundCounter ∧ TransitiveRel r.output ∧
  TransitiveRel r.accountsToDelete ∧ TransitiveRel r.returnData ∧ TransitiveRel r.error ∧
  TransitiveRel r.accessedAddresses ∧ TransitiveRel r.accessedStorageKeys ∧
  TransitiveRel r.state ∧ TransitiveRel r.createdAccounts ∧
  TransitiveRel r.transientStorage ∧ TransitiveRel r.stateGas ∧
  TransitiveRel r.accountReads ∧ TransitiveRel r.storageReads ∧ TransitiveRel r.storageWrites ∧
  TransitiveRel r.touchedAccounts

theorem Devm.rel_refl {r : Devm.Rels} (hr : Devm.Rels.Refl r) :
    ReflexiveRel (Devm.Rel r) := by
  intro d
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hr
  exact ⟨h1 _, h2 _, h3 _, h4 _, h5 _, h6 _, h7 _, h8 _, h9 _, h10 _, h11 _, h12 _,
    h13 _, h14 _, h15 _, h16 _, h17 _, h18 _, h19 _⟩

theorem Devm.rel_trans {r : Devm.Rels} (hr : Devm.Rels.Trans r) :
    TransitiveRel (Devm.Rel r) := by
  intro a b c hab hbc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hr
  exact ⟨h1 hab.stack hbc.stack, h2 hab.memory hbc.memory, h3 hab.gasLeft hbc.gasLeft,
    h4 hab.logs hbc.logs, h5 hab.refundCounter hbc.refundCounter,
    h6 hab.output hbc.output, h7 hab.accountsToDelete hbc.accountsToDelete,
    h8 hab.returnData hbc.returnData, h9 hab.error hbc.error,
    h10 hab.accessedAddresses hbc.accessedAddresses,
    h11 hab.accessedStorageKeys hbc.accessedStorageKeys, h12 hab.state hbc.state,
    h13 hab.createdAccounts hbc.createdAccounts,
    h14 hab.transientStorage hbc.transientStorage, h15 hab.stateGas hbc.stateGas,
    h16 hab.accountReads hbc.accountReads, h17 hab.storageReads hbc.storageReads,
    h18 hab.storageWrites hbc.storageWrites,
    h19 hab.touchedAccounts hbc.touchedAccounts⟩

/-- A relation that is equality off the machine fields relates `d` only to
`d` with a new `Mach`. Consumers read the equation instead of unpacking the
fields positionally. -/
theorem Devm.Rel.eq_setMach {stack : List U256 → List U256 → Prop}
    {memory : Mem → Mem → Prop} {gasLeft : Nat → Nat → Prop}
    {stateGas : StateGasMeter → StateGasMeter → Prop} {d d' : Devm}
    (h : Devm.Rel {Devm.Rels.eq with
      stack := stack, memory := memory, gasLeft := gasLeft, stateGas := stateGas} d d') :
    d' = d.setMach d'.mach := by
  obtain ⟨_, _, _, hlogs, hrefund, houtput, hdel, hret, herr, haddr, hkeys, hstate,
    hcreated, htra, _, hreads, hsreads, hwrites, htouched⟩ := h
  rcases d with ⟨mach, ⟨logs, refund, output, toDelete, returnData, err, addr, keys, created,
    reads, sreads, touched⟩, ⟨state, tra, writes⟩⟩
  rcases d' with ⟨mach', ⟨logs', refund', output', toDelete', returnData', err', addr', keys',
    created', reads', sreads', touched'⟩, ⟨state', tra', writes'⟩⟩
  simp only [Devm.Rels.eq] at *
  cases hlogs; cases hrefund; cases houtput; cases hdel; cases hret; cases herr
  cases haddr; cases hkeys; cases hstate; cases hcreated; cases htra; cases hreads
  cases hsreads; cases hwrites; cases htouched
  rfl

/-- `Devm.Burn` changes only the machine. -/
theorem Devm.Burn.eq_setMach {d d' : Devm} (h : Devm.Burn d d') :
    d' = d.setMach d'.mach :=
  Devm.Rel.eq_setMach h


def HaltOp.At (code : ByteArray) (pc : Nat) (l : HaltOp) : Prop := code.getOp pc = some (.halt l)
def NextOp.At (code : ByteArray) (pc : Nat) (n : NextOp) : Prop := code.getOp pc = some (.next n)
def JumpOp.At (code : ByteArray) (pc : Nat) (j : JumpOp) : Prop := code.getOp pc = some (.jump j)
def PlainOp.At (code : ByteArray) (pc : Nat) (r : PlainOp) : Prop := code.getOp pc = some (.next (.plain r))
def MessageOp.At (code : ByteArray) (pc : Nat) (x : MessageOp) : Prop := code.getOp pc = some (.next (.message x))

/-! ### The recursion-facing relational layer.

Each former hand-maintained mirror is now a thin, non-recursive wrapper: an
equation about the flattened frame/step functions of Jaune.  `RunFrame` is the
generic frame relation; the named mirrors specialize it so that the statements
consumed by `Common.lean` and `Solvent.lean` keep their current shape. -/

def RunFrame (f : Legacy.Frame) (xl : Xlot)
    (r : Except (EvmError × State × AdrSet × TransientStorage) Devm) : Prop :=
  match f.enter with
  | .done r' => xl = .none ∧ r = r'
  | .run evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ r = f.settle raw

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (EvmError × State × AdrSet × TransientStorage) Devm) : Prop :=
  match executeCode.enter msg with
  | .inl evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧
    ex = executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw
  | .inr raw => xl = .none ∧
    ex = executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (EvmError × State × AdrSet × TransientStorage) Devm) : Prop :=
  RunFrame (Legacy.Frame.ofCall msg) xl ex

def ProcessCreateMessage (msg : Msg) (xl : Xlot)
    (ex : Except (EvmError × State × AdrSet × TransientStorage) Devm) : Prop :=
  RunFrame (Legacy.Frame.ofCreate msg) xl ex

def XStep.Run (s : XStep) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .done ex' => xl = .none ∧ ex = ex'
  | .spawn f rsm => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def GenericCreate (sevm : Sevm) (devm : Devm) (endowment : U256) (newAddress : Address)
    (memoryIndex memorySize : Nat) (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (Legacy.genericCreate.step sevm devm endowment newAddress memoryIndex memorySize)
    xl ex

def GenericCall
    (sevm: Sevm)
    (devm: Devm)
    (gas: Nat)
    (value: U256)
    (caller: Address)
    (target: Address)
    (codeAddress: Address)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool)
    (xl : Xlot)
    (ex : Execution) : Prop :=
  XStep.Run
    (Legacy.genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall input_index input_size
      output_index output_size code disablePrecompiles)
    xl ex

def GenericCreateAmsterdam (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat)
    (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (Legacy.genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize)
    xl ex

def GenericCallAmsterdam (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (input_index input_size output_index output_size : Nat) (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool)
    (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (Legacy.genericCallAmsterdam.step sevm state devm gas reservoir value caller
      target codeAddress shouldTransferValue isStaticcall input_index
      input_size output_index output_size code disablePrecompiles
      newAccountCharged insufficientBalance)
    xl ex

def MessageOp.Run (sevm : Sevm) (devm : Devm) :
    MessageOp → Xlot → Execution → Prop :=
  fun x xl ex => XStep.Run (Legacy.MessageOp.step sevm devm x) xl ex

def Legacy.Step.Run (s : Legacy.Step) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .halt ex' => xl = .none ∧ ex = ex'
  | .cont _ devm => xl = .none ∧ ex = .ok devm
  | .spawn f rsm _ => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def NextOp.StepRun (pc : Nat) (sevm : Sevm) (devm : Devm)
    (n : NextOp) (xl : Xlot) (ex : Execution) : Prop :=
  Legacy.Step.Run (Legacy.NextOp.step ⟨pc, sevm, devm⟩ n) xl ex

/-- A childless step outcome built from a plain `Execution` carries exactly
that result.  This is the workhorse for the non-spawning instruction kinds. -/
lemma Legacy.Step.run_ofExecution {pc : Nat} {e ex : Execution} {xl : Xlot} :
    Legacy.Step.Run (Legacy.Step.ofExecution pc e) xl ex ↔ (xl = .none ∧ ex = e) := by
  unfold Legacy.Step.ofExecution
  split <;> simp [Legacy.Step.Run]

lemma Legacy.Step.ofExecution_ne_spawn {pc : Nat} {ex : Execution}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat} :
    Legacy.Step.ofExecution pc ex ≠ .spawn f rsm pc' := by
  cases ex <;> simp [Legacy.Step.ofExecution]

lemma Legacy.Step.ofJump_ne_spawn {j : Except (EvmError × Devm) (Nat × Devm)}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat} :
    Legacy.Step.ofJump j ≠ .spawn f rsm pc' := by
  cases j <;> simp [Legacy.Step.ofJump]

lemma XStep.toStep_spawn {pc : Nat} {s : XStep}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat}
    (h : XStep.toStep pc s = .spawn f rsm pc') : s = .spawn f rsm := by
  cases s
  · cases Legacy.Step.ofExecution_ne_spawn h
  · cases h; rfl

/-- Wrapping a call-type step outcome for the driver does not change what it
relates: the program counter it records is only consulted after the child
returns. -/
lemma XStep.run_toStep {pc : Nat} {s : XStep} {xl : Xlot} {ex : Execution} :
    Legacy.Step.Run (XStep.toStep pc s) xl ex ↔ XStep.Run s xl ex := by
  cases s with
  | done e => simp only [XStep.toStep, XStep.Run, Legacy.Step.run_ofExecution]
  | spawn f rsm => exact Iff.rfl

/-- A jump's step outcome carries the jump's own result, whichever branch it
took, and never suspends. -/
lemma Legacy.Step.run_ofJump {j : Except (EvmError × Devm) (Nat × Devm)} {xl : Xlot}
    {ex : Execution} (h : Legacy.Step.Run (Legacy.Step.ofJump j) xl ex) :
    xl = .none ∧
      ((∃ e, j = .error e ∧ ex = .error e) ∨
        (∃ pc' d, j = .ok ⟨pc', d⟩ ∧ ex = .ok d)) := by
  rcases j with e | ⟨pc', devm'⟩ <;> simp only [Legacy.Step.ofJump, Legacy.Step.Run] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨rfl, Or.inl ⟨e, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inr ⟨pc', devm', rfl, rfl⟩⟩

lemma Legacy.Step.ofExecution_cont {pc pc' : Nat} {e : Execution} {devm' : Devm}
    (h : Legacy.Step.ofExecution pc e = .cont pc' devm') : pc' = pc ∧ e = .ok devm' := by
  unfold Legacy.Step.ofExecution at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

lemma Legacy.Step.ofExecution_ne_halt_ok {pc : Nat} {e : Execution} {devm' : Devm} :
    Legacy.Step.ofExecution pc e ≠ .halt (.ok devm') := by
  unfold Legacy.Step.ofExecution
  split <;> simp

lemma Legacy.Step.ofJump_cont {j : Except (EvmError × Devm) (Nat × Devm)}
    {pc' : Nat} {devm' : Devm} (h : Legacy.Step.ofJump j = .cont pc' devm') :
    j = .ok ⟨pc', devm'⟩ := by
  unfold Legacy.Step.ofJump at h
  split at h <;> cases h
  rfl

lemma Legacy.Step.ofJump_ne_halt_ok {j : Except (EvmError × Devm) (Nat × Devm)}
    {devm' : Devm} : Legacy.Step.ofJump j ≠ .halt (.ok devm') := by
  unfold Legacy.Step.ofJump
  split <;> simp

/-- Every step outcome of an ordinary instruction resumes at `pc + n.size`;
the program-counter arithmetic that used to live in `exec` now lives in
`Ninst.step`, so it is recovered here once. -/
lemma Legacy.NextOp.step_cont_pc {evm : Evm} {n : NextOp} {pc' : Nat} {devm' : Devm}
    (h : Legacy.NextOp.step evm n = .cont pc' devm') : pc' = evm.pc + n.size := by
  unfold Legacy.NextOp.step at h
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [] at h
  · exact (Legacy.Step.ofExecution_cont h).1
  · unfold XStep.toStep at h
    split at h
    · exact (Legacy.Step.ofExecution_cont h).1
    · cases h
  · split at h <;> exact (Legacy.Step.ofExecution_cont h).1
  · exact (Legacy.Step.ofExecution_cont h).1
  · exact (Legacy.Step.ofExecution_cont h).1
  · exact (Legacy.Step.ofExecution_cont h).1

lemma Legacy.NextOp.step_spawn_pc {evm : Evm} {n : NextOp}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat}
    (h : Legacy.NextOp.step evm n = .spawn f rsm pc') : pc' = evm.pc + n.size := by
  unfold Legacy.NextOp.step at h
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [] at h
  · cases Legacy.Step.ofExecution_ne_spawn h
  · unfold XStep.toStep at h
    split at h
    · cases Legacy.Step.ofExecution_ne_spawn h
    · cases h; rfl
  · split at h <;> cases Legacy.Step.ofExecution_ne_spawn h
  · cases Legacy.Step.ofExecution_ne_spawn h
  · cases Legacy.Step.ofExecution_ne_spawn h
  · cases Legacy.Step.ofExecution_ne_spawn h

lemma Legacy.NextOp.step_ne_halt_ok {evm : Evm} {n : NextOp} {devm' : Devm} :
    Legacy.NextOp.step evm n ≠ .halt (.ok devm') := by
  unfold Legacy.NextOp.step
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only []
  · exact Legacy.Step.ofExecution_ne_halt_ok
  · unfold XStep.toStep
    split
    · exact Legacy.Step.ofExecution_ne_halt_ok
    · simp
  · split <;> exact Legacy.Step.ofExecution_ne_halt_ok
  · exact Legacy.Step.ofExecution_ne_halt_ok
  · exact Legacy.Step.ofExecution_ne_halt_ok
  · exact Legacy.Step.ofExecution_ne_halt_ok

/-! ### The six branches of `Ninst.step`, made explicit. -/

lemma Legacy.NextOp.step_reg {evm : Evm} {r : PlainOp} :
    Legacy.NextOp.step evm (.plain r) = Legacy.Step.ofExecution (evm.pc + 1) (r.run evm) := rfl

lemma Legacy.NextOp.step_push {evm : Evm} {xs : Bytes} {le : xs.length ≤ 32} :
    Legacy.NextOp.step evm (.push xs le) =
      if xs = [] && !evm.sta.benvStat.rules.opcodes.push0 then
        Legacy.Step.ofExecution (evm.pc + xs.length + 1)
          (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩)
      else
        Legacy.Step.ofExecution (evm.pc + xs.length + 1)
          (do let d ← chargeGas (if xs = [] then Gas.base else Gas.veryLow) evm.dyna
              d.push xs.toU256) := rfl

lemma Legacy.NextOp.step_exec {evm : Evm} {x : MessageOp} :
    Legacy.NextOp.step evm (.message x) =
      XStep.toStep (evm.pc + 1) (Legacy.MessageOp.step evm.sta evm.dyna x) := rfl

lemma Legacy.NextOp.step_dupn {evm : Evm} {imm : UInt8} :
    Legacy.NextOp.step evm (.dupn imm) =
      Legacy.Step.ofExecution (evm.pc + 2)
        (do if evm.sta.benvStat.rules.opcodes.stackAccess then
              let devm ← chargeGas Gas.veryLow evm.dyna
              match decodeSingle imm with
              | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
              | some n =>
                  match devm.stack[n - 1]? with
                  | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
                  | some word => devm.push word
            else
              .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩) := rfl

lemma Legacy.NextOp.step_swapn {evm : Evm} {imm : UInt8} :
    Legacy.NextOp.step evm (.swapn imm) =
      Legacy.Step.ofExecution (evm.pc + 2)
        (do if evm.sta.benvStat.rules.opcodes.stackAccess then
              let devm ← chargeGas Gas.veryLow evm.dyna
              match decodeSingle imm with
              | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
              | some n =>
                  match Jaune.List.swap devm.stack (n - 1) with
                  | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
                  | some stack => .ok (devm.withStack stack)
            else
              .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩) := rfl

lemma Legacy.NextOp.step_exchange {evm : Evm} {imm : UInt8} :
    Legacy.NextOp.step evm (.exchange imm) =
      Legacy.Step.ofExecution (evm.pc + 2)
        (do if evm.sta.benvStat.rules.opcodes.stackAccess then
              let devm ← chargeGas Gas.veryLow evm.dyna
              match decodePair imm with
              | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
              | some (n, m) =>
                  match Jaune.List.exchange devm.stack n m with
                  | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
                  | some stack => .ok (devm.withStack stack)
            else
              .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩) := rfl

/-! ### Introducing frame relations from the frame-entry equation. -/

lemma RunFrame.of_done {f : Legacy.Frame} {r} (h : f.enter = .done r) :
    RunFrame f .none r := by
  unfold RunFrame; rw [h]; exact ⟨rfl, rfl⟩

lemma RunFrame.of_run {f : Legacy.Frame} {cevm : Evm} {raw : Execution}
    (h : f.enter = .run cevm) :
    RunFrame f (.some ⟨cevm, raw⟩) (f.settle raw) := by
  unfold RunFrame; rw [h]; exact ⟨raw, rfl, rfl⟩

/-- Entering a frame preserves the frame's own depth. -/
lemma Legacy.Frame.enter_run_depth {f : Legacy.Frame} {cevm : Evm}
    (h : f.enter = .run cevm) : cevm.sta.depth = f.inner.depth := by
  unfold Legacy.Frame.enter at h
  split at h
  · cases h
  · rename_i benv hbenv
    split at h
    · cases h
      rename_i heq
      unfold executeCode.enter at heq
      simp only [] at heq
      split at heq
      · cases heq; rfl
      · split at heq
        · cases heq
        · cases heq; rfl
    · cases h

/-- Moving the call value preserves the block environment's static part.

`benvAfterTransfer` either returns the environment untouched or rebuilds it
through `Benv.withState`, which replaces the state and nothing else.

Lives here, below every consumer, because it had been proved three times:
in `Blanc/DeploymentMessage.lean` for four deployment-message families, again
privately in `Blanc/Weth10AllowanceArmsPermit.lean`, and once more for
`Frame.enter_run_benvStat` just below. Both copies are gone and every caller
resolves to this one unchanged. -/
lemma benvAfterTransfer_stat {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) : benv.stat = msg.benv.stat := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · rcases Except.bind_eq_ok h with ⟨b, hb, hok⟩
    cases hok
    unfold Option.toExcept at hb
    split at hb
    · cases hb
    · cases hb
      rename_i w hw
      unfold Benv.subBal at hw
      rcases Option.bind_eq_some_iff.mp hw with ⟨st, hst, hb2⟩
      cases hb2
      rfl
  · cases h; rfl

/-- `benvAfterTransfer` without a value transfer returns the environment. -/
lemma of_benvAfterTransfer_no {msg : Msg} {benv' : Benv}
    (h_stv : ¬ msg.shouldTransferValue = true)
    (h : msg.benvAfterTransfer = .ok benv') : benv' = msg.benv := by
  unfold Msg.benvAfterTransfer at h
  simp only [h_stv] at h
  exact (Except.ok.inj h).symm

/-- `benvAfterTransfer` with a nonzero value transfer is a debit then a credit. -/
lemma of_benvAfterTransfer {msg : Msg} {benv' : Benv}
    (h_stv : msg.shouldTransferValue = true)
    (h_nonzero : msg.value ≠ 0)
    (h : msg.benvAfterTransfer = .ok benv') :
    ∃ st_mid, msg.benv.state.subBal msg.caller msg.value = some st_mid ∧
      benv' = ((msg.benv.withState st_mid).clearStorageWritesIfEmpty msg.caller).addBal
        msg.currentTarget msg.value := by
  unfold Msg.benvAfterTransfer at h
  rw [ite_eq_left ⟨h_stv, h_nonzero⟩] at h
  unfold Benv.subBal at h
  rcases hq : msg.benv.state.subBal msg.caller msg.value with _ | st_mid <;>
    rw [hq] at h <;>
    simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
  · cases h
  · injection h with h
    exact ⟨st_mid, rfl, h.symm⟩

/-- Value transfer changes balances but preserves code. -/
lemma benvAfterTransfer_ok_getCode {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Address) :
    benv.state.getCode a = msg.benv.state.getCode a := by
  by_cases hzero : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero hzero] at h
    cases h
    rfl
  by_cases h_stv : msg.shouldTransferValue = true
  · obtain ⟨st_mid, h_sub, rfl⟩ := of_benvAfterTransfer h_stv hzero h
    exact (State.addBal_getCode _ _ _ _).trans (State.subBal_getCode h_sub)
  · rw [of_benvAfterTransfer_no h_stv h]

/-- Zero-value entry preserves storage everywhere. Nonzero value transfer preserves
storage at an account protected by a nonzero nonce or nonempty code. -/
lemma benvAfterTransfer_ok_getStor {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Address)
    (hpreserved : msg.value = 0 ∨ (msg.benv.state.get a).nonce ≠ 0 ∨
      (msg.benv.state.get a).code.size ≠ 0) :
    benv.state.getStor a = msg.benv.state.getStor a := by
  by_cases hzero : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero hzero] at h
    cases h
    rfl
  have hprotected := hpreserved.resolve_left hzero
  have preserve {st : State} {b : Address} {v : U256}
      (hp : (st.get a).nonce ≠ 0 ∨ (st.get a).code.size ≠ 0) :
      ((st.setBal b v).get a).storage = (st.get a).storage := by
    rw [State.setBal_get_stor]
    split
    · rename_i he
      rcases he with ⟨rfl, he⟩
      rcases hp with hn | hc
      · exact (hn he.2.1).elim
      · exact (hc he.1).elim
    · rfl
  by_cases h_stv : msg.shouldTransferValue = true
  · obtain ⟨st_mid, h_sub, rfl⟩ := of_benvAfterTransfer h_stv hzero h
    have hmid : (st_mid.get a).nonce ≠ 0 ∨ (st_mid.get a).code.size ≠ 0 := by
      rw [(State.of_subBal h_sub).2]
      by_cases ha : msg.caller = a
      · rw [ha, State.setBal_get_self]
        simpa only [Account.clearIfEmpty_nonce, Account.clearIfEmpty_code, Account.withBalance]
          using hprotected
      · rw [State.setBal_get_ne ha]
        exact hprotected
    apply (preserve hmid).trans
    rw [(State.of_subBal h_sub).2]
    exact preserve hprotected
  · rw [of_benvAfterTransfer_no h_stv h]

/-- A zero-value message entry preserves the complete balance map, including
the self-call case where caller and callee coincide. -/
lemma benvAfterTransfer_bal_of_value_zero {msg : Msg} {post : Benv}
    (hzero : msg.value = 0)
    (hrun : msg.benvAfterTransfer = .ok post) :
    post.state.bal = msg.benv.state.bal := by
  rw [Msg.benvAfterTransfer_of_value_zero hzero] at hrun
  cases hrun
  rfl

/-- A zero-value message entry always succeeds. -/
lemma benvAfterTransfer_exists_of_value_zero {msg : Msg} (hzero : msg.value = 0) :
    ∃ post, msg.benvAfterTransfer = .ok post := by
  exact ⟨msg.benv, Msg.benvAfterTransfer_of_value_zero hzero⟩

/-- `initSevm` copies the message's block context. -/
lemma initSevm_benvStat (msg : Msg) : (initSevm msg).benvStat = msg.benv.stat :=
  rfl

/-- `Msg.withBenv` replaces the whole block context. -/
lemma Msg.withBenv_benvStat (msg : Msg) (benv : Benv) :
    (msg.withBenv benv).benv.stat = benv.stat :=
  rfl

/-- Entering a frame preserves the block environment's static part.

`Frame.enter` routes through `benvAfterTransfer`, which moves balances, and
installs the result; neither touches `BenvStat` — the chain rules, chain id and
the rest are fixed for the block. A multi-contract frame invariant that names
another account's status under those rules needs exactly this to cross a call
boundary, which `Frame.enter_run_depth` alone cannot supply. -/
lemma Legacy.Frame.enter_run_benvStat {f : Legacy.Frame} {cevm : Evm}
    (h : f.enter = .run cevm) : cevm.sta.benvStat = f.inner.benv.stat := by
  unfold Legacy.Frame.enter at h
  split at h
  · cases h
  · rename_i benv hbenv
    rw [← benvAfterTransfer_stat hbenv]
    split at h
    · cases h
      rename_i heq
      unfold executeCode.enter at heq
      simp only [] at heq
      split at heq
      · cases heq; rfl
      · split at heq
        · cases heq
        · cases heq; rfl
    · cases h

/-- A filled slot means the frame was actually entered, and the suspended
machine is exactly the one `Frame.enter` produced. -/
lemma RunFrame.some_inv {f : Legacy.Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    f.enter = .run evm_ ∧ r = f.settle exn_ := by
  unfold RunFrame at run
  rcases henter : f.enter with r' | cevm <;> rw [henter] at run
  · cases run.1
  · rcases run with ⟨raw, hxl, hr⟩
    cases hxl
    exact ⟨rfl, hr⟩

/-- The depth of a suspended child frame, read off the slot. -/
lemma RunFrame.depth_eq {f : Legacy.Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    evm_.sta.depth = f.inner.depth :=
  Legacy.Frame.enter_run_depth (RunFrame.some_inv run).1

/-- The block statics of a suspended child frame, read off the slot. The
`RunFrame` form of `Frame.enter_run_benvStat`, shaped like `depth_eq` so the
two read the same way at a call site. -/
lemma RunFrame.benvStat_eq {f : Legacy.Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    evm_.sta.benvStat = f.inner.benv.stat :=
  Legacy.Frame.enter_run_benvStat (RunFrame.some_inv run).1

/-- A filled slot on a call-type instruction means the step spawned, and the
slot holds that spawn's child frame. -/
lemma XStep.Run.some_inv {s : XStep} {evm_ : Evm} {exn_ : Execution} {ex : Execution}
    (run : XStep.Run s (.some ⟨evm_, exn_⟩) ex) :
    ∃ f rsm, s = .spawn f rsm ∧ f.enter = .run evm_ ∧ ex = rsm.run (f.settle exn_) := by
  unfold XStep.Run at run
  cases s with
  | done ex' => cases run.1
  | spawn f rsm =>
    rcases run with ⟨r, hframe, hex⟩
    obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
    exact ⟨f, rsm, rfl, henter, by rw [hex, hr]⟩

lemma Legacy.Step.Run.some_inv {s : Legacy.Step} {evm_ : Evm} {exn_ : Execution} {ex : Execution}
    (run : Legacy.Step.Run s (.some ⟨evm_, exn_⟩) ex) :
    ∃ f rsm pc', s = .spawn f rsm pc' ∧ f.enter = .run evm_ ∧
      ex = rsm.run (f.settle exn_) := by
  unfold Legacy.Step.Run at run
  cases s with
  | halt ex' => cases run.1
  | cont pc devm => cases run.1
  | spawn f rsm pc' =>
    rcases run with ⟨r, hframe, hex⟩
    obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
    exact ⟨f, rsm, pc', rfl, henter, by rw [hex, hr]⟩

/-- Only a call-type instruction spawns, and it delegates to `Xinst.step`. -/
lemma Legacy.NextOp.step_spawn_inv {evm : Evm} {n : NextOp}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat}
    (h : Legacy.NextOp.step evm n = .spawn f rsm pc') :
    ∃ x, n = .message x ∧ Legacy.MessageOp.step evm.sta evm.dyna x = .spawn f rsm := by
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a
  · rw [Legacy.NextOp.step_reg] at h; cases Legacy.Step.ofExecution_ne_spawn h
  · rw [Legacy.NextOp.step_exec] at h; exact ⟨x, rfl, XStep.toStep_spawn h⟩
  · rw [Legacy.NextOp.step_push] at h
    split at h <;> cases Legacy.Step.ofExecution_ne_spawn h
  · unfold Legacy.NextOp.step at h; simp only [] at h; cases Legacy.Step.ofExecution_ne_spawn h
  · unfold Legacy.NextOp.step at h; simp only [] at h; cases Legacy.Step.ofExecution_ne_spawn h
  · unfold Legacy.NextOp.step at h; simp only [] at h; cases Legacy.Step.ofExecution_ne_spawn h

/-- The initial machine of an entered code frame is `initEvm` of the message,
whichever decode branch `executeCode.enter` took. -/
lemma executeCode.enter_inl {msg : Msg} {evm : Evm}
    (h : executeCode.enter msg = .inl evm) : evm = initEvm msg := by
  unfold executeCode.enter at h
  split at h
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl

/-- Frame entry, inverted: an entered frame transferred value successfully and
then suspends on the initial machine of the transferred message.  This is the
single fact every downstream "what does the child start from?" argument needs. -/
lemma Legacy.Frame.enter_run_inv {f : Legacy.Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    ∃ benv, f.inner.benvAfterTransfer = .ok benv ∧
      cevm = initEvm (f.inner.withBenv benv) := by
  unfold Legacy.Frame.enter at h
  rcases hbenv : f.inner.benvAfterTransfer with e | benv <;> simp only [hbenv] at h
  · cases h
  · refine ⟨benv, rfl, ?_⟩
    rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [henter] at h
    · cases h; exact executeCode.enter_inl henter
    · cases h

lemma ExecuteCode.some_inv {msg : Msg} {evm_ : Evm} {exn_ : Execution}
    {ex : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    (run : ExecuteCode msg (.some ⟨evm_, exn_⟩) ex) :
    evm_ = initEvm msg ∧
      ex = executeCode.handleErrorWith msg.benv.stat.rules.stateGas exn_ := by
  unfold ExecuteCode at run
  rcases henter : executeCode.enter msg with evm | raw <;> rw [henter] at run
  · rcases run with ⟨raw, hxl, hex⟩
    cases hxl
    exact ⟨executeCode.enter_inl henter, hex⟩
  · cases run.1

/-- The precompile branch of frame entry runs `executePrecomp` on the initial
machine and produces no child derivation. -/
lemma executeCode.enter_inr {msg : Msg} {raw : Execution}
    (h : executeCode.enter msg = .inr raw) :
    ∃ adr, raw = executePrecompile (initEvm msg) adr := by
  unfold executeCode.enter at h
  split at h
  · cases h
  · rename_i adr _
    split at h
    · cases h; exact ⟨adr, rfl⟩
    · cases h

/-- Under `stateGas = none` the selected handler is `handleError`, textually;
on the covered forks this bridge is `rfl`-transparent. -/
lemma executeCode.handleErrorWith_none {raw : Execution} :
    executeCode.handleErrorWith none raw = executeCode.handleError raw := rfl

/-- Under `stateGas = some` the selected handler is `handleErrorAmsterdam`. -/
lemma executeCode.handleErrorWith_some {s : StateGasRules} {raw : Execution} :
    executeCode.handleErrorWith (some s) raw =
      executeCode.handleErrorAmsterdam raw := rfl

/-- The selected handler is the identity on clean results, whichever branch
the rules select. -/
lemma executeCode.handleErrorWith_ok {sg : Option StateGasRules}
    {evm : Devm} :
    executeCode.handleErrorWith sg (.ok evm) = .ok evm := by
  cases sg <;> rfl

/-- `Frame.settle` is `settleMsg` after the rules-selected handler. -/
lemma Legacy.Frame.settle_eq_settleMsg_handleErrorWith {f : Legacy.Frame} {raw : Execution} :
    f.settle raw =
      f.settleMsg
        (executeCode.handleErrorWith f.inner.benv.stat.rules.stateGas raw) := rfl

/-- The frame-independent part of a frame relation: value transfer followed by
code execution, before the frame's own settlement is applied.  Splitting
`RunFrame` into `FrameBody` plus `Frame.settleMsg` is what lets the former
`ProcessMessage`/`ProcessCreateMessage` arguments be phrased once and reused
for both frame kinds. -/
def FrameBody (m : Msg) (xl : Xlot)
    (r : Except (EvmError × State × AdrSet × TransientStorage) Devm) : Prop :=
  match m.benvAfterTransfer with
  | .error e => xl = .none ∧ r = .error e
  | .ok benv => ExecuteCode (m.withBenv benv) xl r

/-- Frame entry is `benvAfterTransfer` followed by `executeCode.enter`, so a
frame relation decomposes into a transfer failure or a code-execution relation
on the transferred message.  This is the bridge that lets every former
`ProcessMessage`/`ProcessCreateMessage` argument be phrased once. -/
lemma RunFrame.decompose {f : Legacy.Frame} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    (run : RunFrame f xl r) :
    (∃ e, f.inner.benvAfterTransfer = .error e ∧ xl = .none ∧
        r = f.settleMsg (.error e)) ∨
    (∃ benv r', f.inner.benvAfterTransfer = .ok benv ∧
        ExecuteCode (f.inner.withBenv benv) xl r' ∧ r = f.settleMsg r') := by
  unfold RunFrame Legacy.Frame.enter at run
  rcases hbenv : f.inner.benvAfterTransfer with e | benv <;>
    simp only [hbenv] at run
  · exact Or.inl ⟨e, rfl, run.1, run.2⟩
  · have hsg : benv.stat.rules.stateGas = f.inner.benv.stat.rules.stateGas :=
      Msg.benvAfterTransfer_ok_stateGas hbenv
    rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [henter] at run
    · rcases run with ⟨raw, hxl, hr⟩
      refine Or.inr ⟨benv,
        executeCode.handleErrorWith benv.stat.rules.stateGas raw, rfl,
        by unfold ExecuteCode; rw [henter]; exact ⟨raw, hxl, rfl⟩, ?_⟩
      rw [hsg]
      exact hr
    · refine Or.inr ⟨benv,
        executeCode.handleErrorWith benv.stat.rules.stateGas raw, rfl,
        by unfold ExecuteCode; rw [henter]; exact ⟨run.1, rfl⟩, ?_⟩
      rw [hsg]
      exact run.2

/-- `RunFrame` is exactly `FrameBody` composed with the frame's settlement. -/
lemma RunFrame.iff_settleMsg {f : Legacy.Frame} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × TransientStorage) Devm} :
    RunFrame f xl r ↔ ∃ r0, FrameBody f.inner xl r0 ∧ r = f.settleMsg r0 := by
  constructor
  · intro run
    rcases RunFrame.decompose run with ⟨e, hbenv, hxl, hr⟩ | ⟨benv, r0, hbenv, hec, hr⟩
    · exact ⟨.error e, by unfold FrameBody; rw [hbenv]; exact ⟨hxl, rfl⟩, hr⟩
    · exact ⟨r0, by unfold FrameBody; rw [hbenv]; exact hec, hr⟩
  · rintro ⟨r0, hbody, rfl⟩
    unfold FrameBody at hbody
    unfold RunFrame Legacy.Frame.enter
    rcases hbenv : f.inner.benvAfterTransfer with e | benv <;>
      simp only [hbenv] at hbody ⊢
    · exact ⟨hbody.1, by rw [hbody.2]⟩
    · unfold ExecuteCode at hbody
      rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
        simp only [henter] at hbody ⊢
      · rcases hbody with ⟨raw, hxl, hr0⟩
        refine ⟨raw, hxl, ?_⟩
        rw [hr0]
        show f.settleMsg (executeCode.handleErrorWith benv.stat.rules.stateGas raw)
          = f.settle raw
        rw [Msg.benvAfterTransfer_ok_stateGas hbenv]
        exact Legacy.Frame.settle_eq_settleMsg_handleErrorWith.symm
      · refine ⟨hbody.1, ?_⟩
        rw [hbody.2]
        show f.settleMsg (executeCode.handleErrorWith benv.stat.rules.stateGas raw)
          = f.settle raw
        rw [Msg.benvAfterTransfer_ok_stateGas hbenv]
        exact Legacy.Frame.settle_eq_settleMsg_handleErrorWith.symm

lemma ProcessMessage.iff_body {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × TransientStorage) Devm} :
    ProcessMessage msg xl r ↔
      ∃ r0, FrameBody msg xl r0 ∧ r = processMessage.settle msg r0 :=
  RunFrame.iff_settleMsg

lemma ProcessCreateMessage.iff_processMessage {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × TransientStorage) Devm} :
    ProcessCreateMessage msg xl r ↔
      ∃ r', ProcessMessage (processCreateMessage.msg msg) xl r' ∧
        r = processCreateMessage.settle msg r' := by
  rw [ProcessCreateMessage, RunFrame.iff_settleMsg]
  constructor
  · rintro ⟨r0, hbody, rfl⟩
    exact ⟨_, ProcessMessage.iff_body.mpr ⟨r0, hbody, rfl⟩, rfl⟩
  · rintro ⟨r', hpm, rfl⟩
    obtain ⟨r0, hbody, rfl⟩ := ProcessMessage.iff_body.mp hpm
    exact ⟨r0, hbody, rfl⟩


/-! ### Decode bridge.

`Evm.step` dispatches on the instruction at the program counter, so each of the
four `*.At` decode predicates pins the driver's step outcome.  These four
equations are what let the former per-instruction relational reasoning survive
against the single step function. -/

lemma Legacy.Evm.step_invOp {pc : Nat} {sevm : Sevm} {devm : Devm}
    (h : sevm.code.getOp pc = none) :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .halt (.error ⟨.halt (.invalidOpcode .none), devm⟩) := by
  unfold Legacy.Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = none from h]

lemma Legacy.Evm.step_next {pc : Nat} {sevm : Sevm} {devm : Devm} {n : NextOp}
    (h : NextOp.At sevm.code pc n) :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = Legacy.NextOp.step ⟨pc, sevm, devm⟩ n := by
  unfold Legacy.Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.next n) from h]

lemma Legacy.Evm.step_jump {pc : Nat} {sevm : Sevm} {devm : Devm} {j : JumpOp}
    (h : JumpOp.At sevm.code pc j) :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = Legacy.Step.ofJump (j.run ⟨pc, sevm, devm⟩) := by
  unfold Legacy.Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.jump j) from h]

lemma Legacy.Evm.step_last {pc : Nat} {sevm : Sevm} {devm : Devm} {l : HaltOp}
    (h : HaltOp.At sevm.code pc l) :
    Legacy.Evm.step ⟨pc, sevm, devm⟩ = .halt (l.run sevm devm) := by
  unfold Legacy.Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.halt l) from h]

/-- Only a call-type instruction spawns a child frame. -/
lemma Legacy.Evm.step_spawn_inv {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Legacy.Frame} {rsm : Resume} {pc' : Nat}
    (hs : Legacy.Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    ∃ x : MessageOp, MessageOp.At sevm.code pc x ∧
      Legacy.MessageOp.step sevm devm x = .spawn f rsm ∧ pc' = pc + 1 := by
  unfold Legacy.Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [Legacy.NextOp.step] at hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
    · refine ⟨x, hgi, XStep.toStep_spawn hs, ?_⟩
      unfold XStep.toStep at hs
      split at hs
      · cases Legacy.Step.ofExecution_ne_spawn hs
      · cases hs; rfl
    · split at hs <;> cases Legacy.Step.ofExecution_ne_spawn hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
    · cases Legacy.Step.ofExecution_ne_spawn hs
  · cases Legacy.Step.ofJump_ne_spawn hs
  · cases hs


end Jaune
