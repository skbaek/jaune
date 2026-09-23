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

def Jinst.Run (evm : Evm) :
    Jinst → Except (EvmError × Devm) (Nat × Devm) → Prop :=
  λ j ex => j.run evm = ex

def Linst.Run (sevm : Sevm) (devm : Devm) : Linst → Execution → Prop :=
  λ l ex => l.run sevm devm = ex

@[implicit_reducible] def Xlot : Type := Option (Evm × Execution)

/-- Fieldwise relations used to assemble the canonical `Devm.Rel` frames. -/
structure Devm.Rels : Type where
  (stack : List B256 → List B256 → Prop)
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
  (transientStorage : Tra → Tra → Prop)
  (stateGas : StateGasMeter → StateGasMeter → Prop)
  (accountReads : AdrSet → AdrSet → Prop)
  (storageReads : KeySet → KeySet → Prop)

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
  }

def Devm.Burn : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := (· ≥ · )
  }


def Linst.At (code : ByteArray) (pc : Nat) (l : Linst) : Prop := code.getInst pc = some (.last l)
def Ninst.At (code : ByteArray) (pc : Nat) (n : Ninst) : Prop := code.getInst pc = some (.next n)
def Jinst.At (code : ByteArray) (pc : Nat) (j : Jinst) : Prop := code.getInst pc = some (.jump j)
def Rinst.At (code : ByteArray) (pc : Nat) (r : Rinst) : Prop := code.getInst pc = some (.next (.reg r))
def Xinst.At (code : ByteArray) (pc : Nat) (x : Xinst) : Prop := code.getInst pc = some (.next (.exec x))

/-! ### The recursion-facing relational layer.

Each former hand-maintained mirror is now a thin, non-recursive wrapper: an
equation about the flattened frame/step functions of Jaune.  `RunFrame` is the
generic frame relation; the named mirrors specialize it so that the statements
consumed by `Common.lean` and `Solvent.lean` keep their current shape. -/

def RunFrame (f : Frame) (xl : Xlot)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  match f.enter with
  | .done r' => xl = .none ∧ r = r'
  | .run evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧ r = f.settle raw

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  match executeCode.enter msg with
  | .inl evm => ∃ raw, xl = .some ⟨evm, raw⟩ ∧
    ex = executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw
  | .inr raw => xl = .none ∧
    ex = executeCode.handleErrorWith msg.benv.stat.rules.stateGas raw

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  RunFrame (Frame.ofCall msg) xl ex

def ProcessCreateMessage (msg : Msg) (xl : Xlot)
    (ex : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  RunFrame (Frame.ofCreate msg) xl ex

def XStep.Run (s : XStep) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .done ex' => xl = .none ∧ ex = ex'
  | .spawn f rsm => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def GenericCreate (sevm : Sevm) (devm : Devm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize)
    xl ex

def GenericCall
    (sevm: Sevm)
    (devm: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
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
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall input_index input_size
      output_index output_size code disablePrecompiles)
    xl ex

def GenericCreateAmsterdam (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (endowment : B256) (newAddress : Adr) (memoryIndex memorySize : Nat)
    (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize)
    xl ex

def GenericCallAmsterdam (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (input_index input_size output_index output_size : Nat) (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool)
    (xl : Xlot) (ex : Execution) : Prop :=
  XStep.Run
    (genericCallAmsterdam.step sevm state devm gas reservoir value caller
      target codeAddress shouldTransferValue isStaticcall input_index
      input_size output_index output_size code disablePrecompiles
      newAccountCharged insufficientBalance)
    xl ex

def Xinst.Run (sevm : Sevm) (devm : Devm) :
    Xinst → Xlot → Execution → Prop :=
  fun x xl ex => XStep.Run (Xinst.step sevm devm x) xl ex

def Step.Run (s : Step) (xl : Xlot) (ex : Execution) : Prop :=
  match s with
  | .halt ex' => xl = .none ∧ ex = ex'
  | .cont _ devm => xl = .none ∧ ex = .ok devm
  | .spawn f rsm _ => ∃ r, RunFrame f xl r ∧ ex = rsm.run r

def Ninst.StepRun (pc : Nat) (sevm : Sevm) (devm : Devm)
    (n : Ninst) (xl : Xlot) (ex : Execution) : Prop :=
  Step.Run (Ninst.step ⟨pc, sevm, devm⟩ n) xl ex

/-- A childless step outcome built from a plain `Execution` carries exactly
that result.  This is the workhorse for the non-spawning instruction kinds. -/
lemma Step.run_ofExecution {pc : Nat} {e ex : Execution} {xl : Xlot} :
    Step.Run (Step.ofExecution pc e) xl ex ↔ (xl = .none ∧ ex = e) := by
  unfold Step.ofExecution
  split <;> simp [Step.Run]

lemma Step.ofExecution_ne_spawn {pc : Nat} {ex : Execution}
    {f : Frame} {rsm : Resume} {pc' : Nat} :
    Step.ofExecution pc ex ≠ .spawn f rsm pc' := by
  cases ex <;> simp [Step.ofExecution]

lemma Step.ofJump_ne_spawn {j : Except (EvmError × Devm) (Nat × Devm)}
    {f : Frame} {rsm : Resume} {pc' : Nat} :
    Step.ofJump j ≠ .spawn f rsm pc' := by
  cases j <;> simp [Step.ofJump]

lemma XStep.toStep_spawn {pc : Nat} {s : XStep}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : XStep.toStep pc s = .spawn f rsm pc') : s = .spawn f rsm := by
  cases s
  · cases Step.ofExecution_ne_spawn h
  · cases h; rfl

/-- Wrapping a call-type step outcome for the driver does not change what it
relates: the program counter it records is only consulted after the child
returns. -/
lemma XStep.run_toStep {pc : Nat} {s : XStep} {xl : Xlot} {ex : Execution} :
    Step.Run (XStep.toStep pc s) xl ex ↔ XStep.Run s xl ex := by
  cases s with
  | done e => simp only [XStep.toStep, XStep.Run, Step.run_ofExecution]
  | spawn f rsm => exact Iff.rfl

/-- A jump's step outcome carries the jump's own result, whichever branch it
took, and never suspends. -/
lemma Step.run_ofJump {j : Except (EvmError × Devm) (Nat × Devm)} {xl : Xlot}
    {ex : Execution} (h : Step.Run (Step.ofJump j) xl ex) :
    xl = .none ∧
      ((∃ e, j = .error e ∧ ex = .error e) ∨
        (∃ pc' d, j = .ok ⟨pc', d⟩ ∧ ex = .ok d)) := by
  rcases j with e | ⟨pc', devm'⟩ <;> simp only [Step.ofJump, Step.Run] at h <;>
    obtain ⟨rfl, rfl⟩ := h
  · exact ⟨rfl, Or.inl ⟨e, rfl, rfl⟩⟩
  · exact ⟨rfl, Or.inr ⟨pc', devm', rfl, rfl⟩⟩

lemma Step.ofExecution_cont {pc pc' : Nat} {e : Execution} {devm' : Devm}
    (h : Step.ofExecution pc e = .cont pc' devm') : pc' = pc ∧ e = .ok devm' := by
  unfold Step.ofExecution at h
  split at h <;> cases h
  exact ⟨rfl, rfl⟩

lemma Step.ofExecution_ne_halt_ok {pc : Nat} {e : Execution} {devm' : Devm} :
    Step.ofExecution pc e ≠ .halt (.ok devm') := by
  unfold Step.ofExecution
  split <;> simp

lemma Step.ofJump_cont {j : Except (EvmError × Devm) (Nat × Devm)}
    {pc' : Nat} {devm' : Devm} (h : Step.ofJump j = .cont pc' devm') :
    j = .ok ⟨pc', devm'⟩ := by
  unfold Step.ofJump at h
  split at h <;> cases h
  rfl

lemma Step.ofJump_ne_halt_ok {j : Except (EvmError × Devm) (Nat × Devm)}
    {devm' : Devm} : Step.ofJump j ≠ .halt (.ok devm') := by
  unfold Step.ofJump
  split <;> simp

/-- Every step outcome of an ordinary instruction resumes at `pc + n.size`;
the program-counter arithmetic that used to live in `exec` now lives in
`Ninst.step`, so it is recovered here once. -/
lemma Ninst.step_cont_pc {evm : Evm} {n : Ninst} {pc' : Nat} {devm' : Devm}
    (h : Ninst.step evm n = .cont pc' devm') : pc' = evm.pc + n.size := by
  unfold Ninst.step at h
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [] at h
  · exact (Step.ofExecution_cont h).1
  · unfold XStep.toStep at h
    split at h
    · exact (Step.ofExecution_cont h).1
    · cases h
  · exact (Step.ofExecution_cont h).1
  · exact (Step.ofExecution_cont h).1
  · exact (Step.ofExecution_cont h).1
  · exact (Step.ofExecution_cont h).1

lemma Ninst.step_spawn_pc {evm : Evm} {n : Ninst}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : Ninst.step evm n = .spawn f rsm pc') : pc' = evm.pc + n.size := by
  unfold Ninst.step at h
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [] at h
  · cases Step.ofExecution_ne_spawn h
  · unfold XStep.toStep at h
    split at h
    · cases Step.ofExecution_ne_spawn h
    · cases h; rfl
  · cases Step.ofExecution_ne_spawn h
  · cases Step.ofExecution_ne_spawn h
  · cases Step.ofExecution_ne_spawn h
  · cases Step.ofExecution_ne_spawn h

lemma Ninst.step_ne_halt_ok {evm : Evm} {n : Ninst} {devm' : Devm} :
    Ninst.step evm n ≠ .halt (.ok devm') := by
  unfold Ninst.step
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only []
  · exact Step.ofExecution_ne_halt_ok
  · unfold XStep.toStep
    split
    · exact Step.ofExecution_ne_halt_ok
    · simp
  · exact Step.ofExecution_ne_halt_ok
  · exact Step.ofExecution_ne_halt_ok
  · exact Step.ofExecution_ne_halt_ok
  · exact Step.ofExecution_ne_halt_ok

/-! ### The six branches of `Ninst.step`, made explicit. -/

lemma Ninst.step_reg {evm : Evm} {r : Rinst} :
    Ninst.step evm (.reg r) = Step.ofExecution (evm.pc + 1) (r.run evm) := rfl

lemma Ninst.step_push {evm : Evm} {xs : Bytes} {le : xs.length ≤ 32} :
    Ninst.step evm (.push xs le) =
      Step.ofExecution (evm.pc + xs.length + 1)
        (do let d ← chargeGas (if xs = [] then gBase else gVerylow) evm.dyna
            d.push xs.toB256) := rfl

lemma Ninst.step_exec {evm : Evm} {x : Xinst} :
    Ninst.step evm (.exec x) =
      XStep.toStep (evm.pc + 1) (Xinst.step evm.sta evm.dyna x) := rfl

lemma Ninst.step_dupn {evm : Evm} {imm : UInt8} :
    Ninst.step evm (.dupn imm) =
      Step.ofExecution (evm.pc + 2)
        (do if evm.sta.benvStat.rules.op.stackAccess then
              let devm ← chargeGas gVerylow evm.dyna
              match decodeSingle imm with
              | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
              | some n =>
                  match devm.stack[n - 1]? with
                  | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
                  | some word => devm.push word
            else
              .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩) := rfl

lemma Ninst.step_swapn {evm : Evm} {imm : UInt8} :
    Ninst.step evm (.swapn imm) =
      Step.ofExecution (evm.pc + 2)
        (do if evm.sta.benvStat.rules.op.stackAccess then
              let devm ← chargeGas gVerylow evm.dyna
              match decodeSingle imm with
              | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
              | some n =>
                  match Jaune.List.swap devm.stack (n - 1) with
                  | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
                  | some stack => .ok (devm.withStack stack)
            else
              .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩) := rfl

lemma Ninst.step_exchange {evm : Evm} {imm : UInt8} :
    Ninst.step evm (.exchange imm) =
      Step.ofExecution (evm.pc + 2)
        (do if evm.sta.benvStat.rules.op.stackAccess then
              let devm ← chargeGas gVerylow evm.dyna
              match decodePair imm with
              | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
              | some (n, m) =>
                  match Jaune.List.exchange devm.stack n m with
                  | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
                  | some stack => .ok (devm.withStack stack)
            else
              .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩) := rfl

/-! ### Introducing frame relations from the frame-entry equation. -/

lemma RunFrame.of_done {f : Frame} {r} (h : f.enter = .done r) :
    RunFrame f .none r := by
  unfold RunFrame; rw [h]; exact ⟨rfl, rfl⟩

lemma RunFrame.of_run {f : Frame} {cevm : Evm} {raw : Execution}
    (h : f.enter = .run cevm) :
    RunFrame f (.some ⟨cevm, raw⟩) (f.settle raw) := by
  unfold RunFrame; rw [h]; exact ⟨raw, rfl, rfl⟩

/-- Entering a frame preserves the frame's own depth. -/
lemma Frame.enter_run_depth {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) : cevm.sta.depth = f.inner.depth := by
  unfold Frame.enter at h
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
lemma Frame.enter_run_benvStat {f : Frame} {cevm : Evm}
    (h : f.enter = .run cevm) : cevm.sta.benvStat = f.inner.benv.stat := by
  unfold Frame.enter at h
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
lemma RunFrame.some_inv {f : Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    f.enter = .run evm_ ∧ r = f.settle exn_ := by
  unfold RunFrame at run
  rcases henter : f.enter with r' | cevm <;> rw [henter] at run
  · cases run.1
  · rcases run with ⟨raw, hxl, hr⟩
    cases hxl
    exact ⟨rfl, hr⟩

/-- The depth of a suspended child frame, read off the slot. -/
lemma RunFrame.depth_eq {f : Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    evm_.sta.depth = f.inner.depth :=
  Frame.enter_run_depth (RunFrame.some_inv run).1

/-- The block statics of a suspended child frame, read off the slot. The
`RunFrame` form of `Frame.enter_run_benvStat`, shaped like `depth_eq` so the
two read the same way at a call site. -/
lemma RunFrame.benvStat_eq {f : Frame} {evm_ : Evm} {exn_ : Execution} {r}
    (run : RunFrame f (.some ⟨evm_, exn_⟩) r) :
    evm_.sta.benvStat = f.inner.benv.stat :=
  Frame.enter_run_benvStat (RunFrame.some_inv run).1

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

lemma Step.Run.some_inv {s : Step} {evm_ : Evm} {exn_ : Execution} {ex : Execution}
    (run : Step.Run s (.some ⟨evm_, exn_⟩) ex) :
    ∃ f rsm pc', s = .spawn f rsm pc' ∧ f.enter = .run evm_ ∧
      ex = rsm.run (f.settle exn_) := by
  unfold Step.Run at run
  cases s with
  | halt ex' => cases run.1
  | cont pc devm => cases run.1
  | spawn f rsm pc' =>
    rcases run with ⟨r, hframe, hex⟩
    obtain ⟨henter, hr⟩ := RunFrame.some_inv hframe
    exact ⟨f, rsm, pc', rfl, henter, by rw [hex, hr]⟩

/-- Only a call-type instruction spawns, and it delegates to `Xinst.step`. -/
lemma Ninst.step_spawn_inv {evm : Evm} {n : Ninst}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (h : Ninst.step evm n = .spawn f rsm pc') :
    ∃ x, n = .exec x ∧ Xinst.step evm.sta evm.dyna x = .spawn f rsm := by
  rcases n with r | x | ⟨xs, hxs⟩ | a | a | a
  · rw [Ninst.step_reg] at h; cases Step.ofExecution_ne_spawn h
  · rw [Ninst.step_exec] at h; exact ⟨x, rfl, XStep.toStep_spawn h⟩
  · rw [Ninst.step_push] at h; cases Step.ofExecution_ne_spawn h
  · unfold Ninst.step at h; simp only [] at h; cases Step.ofExecution_ne_spawn h
  · unfold Ninst.step at h; simp only [] at h; cases Step.ofExecution_ne_spawn h
  · unfold Ninst.step at h; simp only [] at h; cases Step.ofExecution_ne_spawn h

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
lemma Frame.enter_run_inv {f : Frame} {cevm : Evm} (h : f.enter = .run cevm) :
    ∃ benv, f.inner.benvAfterTransfer = .ok benv ∧
      cevm = initEvm (f.inner.withBenv benv) := by
  unfold Frame.enter at h
  rcases hbenv : f.inner.benvAfterTransfer with e | benv <;> simp only [hbenv] at h
  · cases h
  · refine ⟨benv, rfl, ?_⟩
    rcases henter : executeCode.enter (f.inner.withBenv benv) with evm | raw <;>
      simp only [henter] at h
    · cases h; exact executeCode.enter_inl henter
    · cases h

lemma ExecuteCode.some_inv {msg : Msg} {evm_ : Evm} {exn_ : Execution}
    {ex : Except (EvmError × State × AdrSet × Tra) Devm}
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
    ∃ adr, raw = executePrecomp (initEvm msg) adr := by
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
lemma Frame.settle_eq_settleMsg_handleErrorWith {f : Frame} {raw : Execution} :
    f.settle raw =
      f.settleMsg
        (executeCode.handleErrorWith f.inner.benv.stat.rules.stateGas raw) := rfl

/-- The frame-independent part of a frame relation: value transfer followed by
code execution, before the frame's own settlement is applied.  Splitting
`RunFrame` into `FrameBody` plus `Frame.settleMsg` is what lets the former
`ProcessMessage`/`ProcessCreateMessage` arguments be phrased once and reused
for both frame kinds. -/
def FrameBody (m : Msg) (xl : Xlot)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) : Prop :=
  match m.benvAfterTransfer with
  | .error e => xl = .none ∧ r = .error e
  | .ok benv => ExecuteCode (m.withBenv benv) xl r

/-- Frame entry is `benvAfterTransfer` followed by `executeCode.enter`, so a
frame relation decomposes into a transfer failure or a code-execution relation
on the transferred message.  This is the bridge that lets every former
`ProcessMessage`/`ProcessCreateMessage` argument be phrased once. -/
lemma RunFrame.decompose {f : Frame} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × Tra) Devm}
    (run : RunFrame f xl r) :
    (∃ e, f.inner.benvAfterTransfer = .error e ∧ xl = .none ∧
        r = f.settleMsg (.error e)) ∨
    (∃ benv r', f.inner.benvAfterTransfer = .ok benv ∧
        ExecuteCode (f.inner.withBenv benv) xl r' ∧ r = f.settleMsg r') := by
  unfold RunFrame Frame.enter at run
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
lemma RunFrame.iff_settleMsg {f : Frame} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} :
    RunFrame f xl r ↔ ∃ r0, FrameBody f.inner xl r0 ∧ r = f.settleMsg r0 := by
  constructor
  · intro run
    rcases RunFrame.decompose run with ⟨e, hbenv, hxl, hr⟩ | ⟨benv, r0, hbenv, hec, hr⟩
    · exact ⟨.error e, by unfold FrameBody; rw [hbenv]; exact ⟨hxl, rfl⟩, hr⟩
    · exact ⟨r0, by unfold FrameBody; rw [hbenv]; exact hec, hr⟩
  · rintro ⟨r0, hbody, rfl⟩
    unfold FrameBody at hbody
    unfold RunFrame Frame.enter
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
        exact Frame.settle_eq_settleMsg_handleErrorWith.symm
      · refine ⟨hbody.1, ?_⟩
        rw [hbody.2]
        show f.settleMsg (executeCode.handleErrorWith benv.stat.rules.stateGas raw)
          = f.settle raw
        rw [Msg.benvAfterTransfer_ok_stateGas hbenv]
        exact Frame.settle_eq_settleMsg_handleErrorWith.symm

lemma ProcessMessage.iff_body {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} :
    ProcessMessage msg xl r ↔
      ∃ r0, FrameBody msg xl r0 ∧ r = processMessage.settle msg r0 :=
  RunFrame.iff_settleMsg

lemma ProcessCreateMessage.iff_processMessage {msg : Msg} {xl : Xlot}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} :
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

lemma Evm.step_invOp {pc : Nat} {sevm : Sevm} {devm : Devm}
    (h : sevm.code.getInst pc = none) :
    Evm.step ⟨pc, sevm, devm⟩ = .halt (.error ⟨.halt (.invalidOpcode .none), devm⟩) := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = none from h]

lemma Evm.step_next {pc : Nat} {sevm : Sevm} {devm : Devm} {n : Ninst}
    (h : Ninst.At sevm.code pc n) :
    Evm.step ⟨pc, sevm, devm⟩ = Ninst.step ⟨pc, sevm, devm⟩ n := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.next n) from h]

lemma Evm.step_jump {pc : Nat} {sevm : Sevm} {devm : Devm} {j : Jinst}
    (h : Jinst.At sevm.code pc j) :
    Evm.step ⟨pc, sevm, devm⟩ = Step.ofJump (j.run ⟨pc, sevm, devm⟩) := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.jump j) from h]

lemma Evm.step_last {pc : Nat} {sevm : Sevm} {devm : Devm} {l : Linst}
    (h : Linst.At sevm.code pc l) :
    Evm.step ⟨pc, sevm, devm⟩ = .halt (l.run sevm devm) := by
  unfold Evm.step
  rw [show (Evm.getInst ⟨pc, sevm, devm⟩) = some (.last l) from h]

/-- Only a call-type instruction spawns a child frame. -/
lemma Evm.step_spawn_inv {pc : Nat} {sevm : Sevm} {devm : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hs : Evm.step ⟨pc, sevm, devm⟩ = .spawn f rsm pc') :
    ∃ x : Xinst, Xinst.At sevm.code pc x ∧
      Xinst.step sevm devm x = .spawn f rsm ∧ pc' = pc + 1 := by
  unfold Evm.step at hs
  split at hs
  · cases hs
  · rename_i n hgi
    rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> simp only [Ninst.step] at hs
    · cases Step.ofExecution_ne_spawn hs
    · refine ⟨x, hgi, XStep.toStep_spawn hs, ?_⟩
      unfold XStep.toStep at hs
      split at hs
      · cases Step.ofExecution_ne_spawn hs
      · cases hs; rfl
    · cases Step.ofExecution_ne_spawn hs
    · cases Step.ofExecution_ne_spawn hs
    · cases Step.ofExecution_ne_spawn hs
    · cases Step.ofExecution_ne_spawn hs
  · cases Step.ofJump_ne_spawn hs
  · cases hs


end Jaune
