import Jaune.MessageCall.Plain
import Jaune.Bridge.G2b.State

/-!
# Bridge: plain instructions over `Frame.State` against `PlainOp.runCore` (G2b, unit W3-2a)

Old side: `Jaune.PlainOp.runCore` at `86934d92` (`Jaune/Machine.lean`), unedited. New side:
`Jaune.Staging.PlainOp.runCore` (`Jaune.MessageCall.Plain`). One square per opcode arm, and the
square for the whole function, each of the form

  `Frame.State.ofExecution (PlainOp.runCore pc d sevm op) =
    Except.ofHalt (Staging.PlainOp.runCore pc (CallContext.ofSevm sevm) (Frame.State.ofDevm d) op)`

for every program counter, every `Devm`, every `Sevm` (so every fork) and, for `DUP`, `SWAP` and
`LOG`, every immediate. The squares observe both channels in full: the halt reason and the
partial state on the error channel, the whole state on the success channel, up to what
`Frame.State.ofDevm` forgets (output, stored error), which no plain instruction reads or writes.

The squares are composed from W3-1's commuting lemmas (`Jaune.Bridge.G2b.State`) through the
bind lemmas below; a machine-level arm is first distributed over its binds
(`liftMachine_bind`, `liftMachine_bindValue`). Everything here goes with `Devm` after G2b's tag.
-/

namespace Jaune.Bridge.G2b

open Jaune Frame.State

/-! ### Distributing `liftMachine` over a machine step's binds -/

theorem liftMachine_bindValue {ε α : Type} (s : Frame.State)
    (c : Machine → Except (ε × Machine) (α × Machine))
    (f : α × Machine → Except (ε × Machine) Machine) :
    s.liftMachine (fun m => c m >>= f) =
      s.liftMachineValue c >>= fun p => p.2.liftMachine (fun m => f (p.1, m)) := by
  unfold liftMachine liftMachineValue
  dsimp only
  rcases c s.machine with ⟨e, m⟩ | ⟨a, m⟩ <;> rfl

theorem liftMachine_bind {ε : Type} (s : Frame.State) (c : Machine → Except (ε × Machine) Machine)
    (f : Machine → Except (ε × Machine) Machine) :
    s.liftMachine (fun m => c m >>= f) = s.liftMachine c >>= fun s' => s'.liftMachine f := by
  unfold liftMachine
  dsimp only
  rcases c s.machine with ⟨e, m⟩ | m <;> rfl

theorem liftMachine_ite {ε : Type} (s : Frame.State) (c : Machine → Prop) [∀ m, Decidable (c m)]
    (f g : Machine → Except (ε × Machine) Machine) :
    s.liftMachine (fun m => if c m then f m else g m) =
      if c s.machine then s.liftMachine f else s.liftMachine g := by
  by_cases h : c s.machine
  · simp only [h, ↓reduceIte]; unfold liftMachine; simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte]; unfold liftMachine; simp only [h, ↓reduceIte]

/-- A push whose word and machine are read off the machine, against a `Devm` push. -/
theorem sq_push_lift {d d' : Devm} {x : U256} {f : Machine → U256} {g : Machine → Machine}
    (hx : f (ofDevm d).machine = x) (hg : (ofDevm d).withMachine (g (ofDevm d).machine) = ofDevm d') :
    ofExecution (d'.push x) =
      Except.ofHalt ((ofDevm d).liftMachine (fun m => Machine.push (f m) (g m))) := by
  rw [ofExecution_push, ← hx, ← hg]
  unfold push liftMachine
  rfl

/-! ### Distributing `liftLog` -/

theorem liftLog_bindValue {α : Type} (s : Frame.State)
    (c : Machine → Except (ExceptionalHalt × Machine) (α × Machine))
    (f : α × Machine → Except (ExceptionalHalt × Machine) (Machine × Log)) :
    Staging.PlainOp.liftLog (fun m => c m >>= f) s =
      s.liftMachineValue c >>= fun p => Staging.PlainOp.liftLog (fun m => f (p.1, m)) p.2 := by
  unfold Staging.PlainOp.liftLog liftMachineValue
  dsimp only
  rcases c s.machine with ⟨e, m⟩ | ⟨a, m⟩ <;> rfl

theorem liftLog_bind (s : Frame.State) (c : Machine → Except (ExceptionalHalt × Machine) Machine)
    (f : Machine → Except (ExceptionalHalt × Machine) (Machine × Log)) :
    Staging.PlainOp.liftLog (fun m => c m >>= f) s =
      s.liftMachine c >>= fun s' => Staging.PlainOp.liftLog f s' := by
  unfold Staging.PlainOp.liftLog liftMachine
  dsimp only
  rcases c s.machine with ⟨e, m⟩ | m <;> rfl

/-! ### Bind lemmas for squares -/

/-- A bind on a value-returning step, when the step and every continuation commute. -/
theorem sq_bindValue {α : Type} {x : Except (EvmError × Devm) (α × Devm)}
    {y : Except (ExceptionalHalt × Frame.State) (α × Frame.State)}
    {f : α × Devm → Execution}
    {g : α × Frame.State → Except (ExceptionalHalt × Frame.State) Frame.State}
    (hx : ofOutcome x = Except.ofHalt y)
    (hf : ∀ a d, ofExecution (f (a, d)) = Except.ofHalt (g (a, ofDevm d))) :
    ofExecution (x >>= f) = Except.ofHalt (y >>= g) := by
  rcases x with ⟨e, d⟩ | ⟨a, d⟩ <;> rcases y with ⟨h, s⟩ | ⟨b, s⟩ <;>
    simp only [ofOutcome, Except.mapState, Except.ofHalt, reduceCtorEq, Except.error.injEq,
      Except.ok.injEq, Prod.mk.injEq] at hx
  · obtain ⟨rfl, rfl⟩ := hx; rfl
  · obtain ⟨rfl, rfl⟩ := hx; exact hf a d

/-- A bind on a step without a value. -/
theorem sq_bind {x : Execution} {y : Except (ExceptionalHalt × Frame.State) Frame.State}
    {f : Devm → Execution} {g : Frame.State → Except (ExceptionalHalt × Frame.State) Frame.State}
    (hx : ofExecution x = Except.ofHalt y)
    (hf : ∀ d, ofExecution (f d) = Except.ofHalt (g (ofDevm d))) :
    ofExecution (x >>= f) = Except.ofHalt (y >>= g) := by
  rcases x with ⟨e, d⟩ | d <;> rcases y with ⟨h, s⟩ | s <;>
    simp only [ofExecution, Except.mapResultState, Except.ofHalt, reduceCtorEq,
      Except.error.injEq, Except.ok.injEq, Prod.mk.injEq] at hx
  · obtain ⟨rfl, rfl⟩ := hx; rfl
  · subst hx; exact hf d

/-- A check that halts with the current state. -/
theorem sq_assert {p : Prop} [Decidable p] {h : ExceptionalHalt} {d : Devm} {f : Unit → Execution}
    {g : Unit → Except (ExceptionalHalt × Frame.State) Frame.State}
    (hf : p → ofExecution (f ()) = Except.ofHalt (g ())) :
    ofExecution (Except.assert p (EvmError.halt h, d) >>= f) =
      Except.ofHalt (Except.assert p (h, ofDevm d) >>= g) := by
  unfold Except.assert
  by_cases hp : p
  · simp only [hp, ↓reduceIte]; exact hf hp
  · simp only [hp, ↓reduceIte]; rfl

/-- The static check. -/
theorem sq_assertDynamic {sevm : Sevm} {d : Devm} {f : Unit → Execution}
    {g : Unit → Except (ExceptionalHalt × Frame.State) Frame.State}
    (hf : sevm.isStatic = false → ofExecution (f ()) = Except.ofHalt (g ())) :
    ofExecution (assertDynamic sevm d >>= f) =
      Except.ofHalt ((ofDevm d).assertDynamic (.ofSevm sevm) >>= g) :=
  sq_assert (p := (!sevm.isStatic) = true) fun hp => hf (by simpa using hp)

/-- A branch on the same condition on both sides. -/
theorem sq_ite {c : Prop} [Decidable c] {a b : Execution}
    {a' b' : Except (ExceptionalHalt × Frame.State) Frame.State}
    (ha : c → ofExecution a = Except.ofHalt a') (hb : ¬c → ofExecution b = Except.ofHalt b') :
    ofExecution (if c then a else b) = Except.ofHalt (if c then a' else b') := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

/-- A branch on the same condition, the new side inside a machine lift. -/
theorem sq_ite_lift {c : Prop} [Decidable c] {a b : Execution} {s : Frame.State}
    {f g : Machine → Except (ExceptionalHalt × Machine) Machine}
    (ha : c → ofExecution a = Except.ofHalt (s.liftMachine f))
    (hb : ¬c → ofExecution b = Except.ofHalt (s.liftMachine g)) :
    ofExecution (if c then a else b) =
      Except.ofHalt (s.liftMachine fun m => if c then f m else g m) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

/-- A memory read on the grouped machine, against the `Devm` one. -/
theorem machine_memRead_ofDevm (d : Devm) (i n : Nat) :
    ((ofDevm d).machine.memRead i n).1 = (d.memRead i n).1 ∧
      (ofDevm d).withMachine ((ofDevm d).machine.memRead i n).2 = ofDevm (d.memRead i n).2 := by
  have h := ofDevm_memRead d i n
  simp only [memRead] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

/-- A halt. -/
theorem sq_error (h : ExceptionalHalt) (d : Devm) :
    ofExecution (.error (EvmError.halt h, d)) = Except.ofHalt (.error (h, ofDevm d)) := rfl

/-- Success. -/
theorem sq_ok (d : Devm) : ofExecution (.ok d) = Except.ofHalt (.ok (ofDevm d)) := rfl

/-- The square at one opcode. -/
abbrev PlainOp.Square (pc : Nat) (d : Devm) (sevm : Sevm) (op : Jaune.PlainOp) : Prop :=
  ofExecution (Jaune.PlainOp.runCore pc d sevm op) =
    Except.ofHalt (Staging.PlainOp.runCore pc (.ofSevm sevm) (ofDevm d) op)

/-- Closes a square goal by walking the binds of both sides in step. -/
macro "square_walk" : tactic => `(tactic| (
  repeat' (first
    | simp only [liftMachine_bindValue, liftMachine_bind, liftMachine_ite,
        ← ofDevm_addAccessedAddress, ← ofDevm_addAccessedStorageKey, ← ofDevm_balReadAccount,
        ← ofDevm_balReadStorage, ← ofDevm_memWrite, ← ofDevm_setStorVal, ← ofDevm_setTransVal,
        ← ofDevm_withRefundCounter, ← ofDevm_addLog, ← ofDevm_creditStateGasRefund,
        ofDevm_originalStorageValue, ofDevm_storageValue, ofDevm_refund, ofDevm_transientValue,
        ofDevm_gasLeft, ofDevm_accessedStorageKeys, ofDevm_accessedAddresses]
    | refine sq_bindValue (ofOutcome_pop _) fun _ _ => ?_
    | refine sq_bindValue (ofOutcome_popToNat _) fun _ _ => ?_
    | refine sq_bindValue (ofOutcome_popToAdr _) fun _ _ => ?_
    | refine sq_bindValue (ofOutcome_popN _ _) fun _ _ => ?_
    | refine sq_bind (ofExecution_chargeGas _ _) fun _ => ?_
    | refine sq_bind (ofExecution_chargeStateGas _ _) fun _ => ?_
    | refine sq_assertDynamic fun _ => ?_
    | refine sq_assert fun _ => ?_
    | refine sq_ite (fun _ => ?_) (fun _ => ?_)
    | refine sq_ite_lift (fun _ => ?_) (fun _ => ?_))
  all_goals first
    | exact ofExecution_push _ _
    | exact ofExecution_pushItem _ _ _
    | exact ofExecution_applyUnary _ _ _
    | exact ofExecution_applyBinary _ _ _
    | exact ofExecution_applyTernary _ _ _
    | exact ofExecution_chargeGas _ _
    | exact sq_push_lift rfl rfl
    | rfl))

/-- Unfold both sides of an arm and distribute the machine lifts. -/
macro "square_open" : tactic => `(tactic| (
  dsimp only [Jaune.Bridge.G2b.PlainOp.Square, Jaune.PlainOp.runCore, Staging.PlainOp.runCore,
    CallContext.ofSevm]
  try simp only [liftMachine_bindValue, liftMachine_bind, liftMachine_ite]))

/-! ### Per-arm squares -/

namespace PlainOp

variable (pc : Nat) (d : Devm) (sevm : Sevm)

/-! #### Word: environment pushes -/

theorem runCore_address : Square pc d sevm .address := ofExecution_pushItem _ _ _
theorem runCore_origin : Square pc d sevm .origin := ofExecution_pushItem _ _ _
theorem runCore_caller : Square pc d sevm .caller := ofExecution_pushItem _ _ _
theorem runCore_callvalue : Square pc d sevm .callvalue := ofExecution_pushItem _ _ _
theorem runCore_calldatasize : Square pc d sevm .calldatasize := ofExecution_pushItem _ _ _
theorem runCore_codesize : Square pc d sevm .codesize := ofExecution_pushItem _ _ _
theorem runCore_gasprice : Square pc d sevm .gasprice := ofExecution_pushItem _ _ _
theorem runCore_returndatasize : Square pc d sevm .returndatasize := ofExecution_pushItem _ _ _
theorem runCore_number : Square pc d sevm .number := ofExecution_pushItem _ _ _
theorem runCore_timestamp : Square pc d sevm .timestamp := ofExecution_pushItem _ _ _
theorem runCore_gaslimit : Square pc d sevm .gaslimit := ofExecution_pushItem _ _ _
theorem runCore_prevrandao : Square pc d sevm .prevrandao := ofExecution_pushItem _ _ _
theorem runCore_coinbase : Square pc d sevm .coinbase := ofExecution_pushItem _ _ _
theorem runCore_msize : Square pc d sevm .msize := ofExecution_pushItem _ _ _
theorem runCore_pc : Square pc d sevm .pc := ofExecution_pushItem _ _ _
theorem runCore_basefee : Square pc d sevm .basefee := by square_open; square_walk
theorem runCore_blobbasefee : Square pc d sevm .blobbasefee := by square_open; square_walk
theorem runCore_chainid : Square pc d sevm .chainid := by square_open; square_walk
theorem runCore_slotnum : Square pc d sevm .slotnum := by square_open; square_walk
theorem runCore_gas : Square pc d sevm .gas := by
  square_open
  exact sq_bind (ofExecution_chargeGas _ _) fun d => sq_push_lift rfl rfl

/-! #### Word: reads of a popped operand -/

theorem runCore_blobhash : Square pc d sevm .blobhash := by square_open; square_walk
theorem runCore_calldataload : Square pc d sevm .calldataload := by square_open; square_walk
theorem runCore_blockhash : Square pc d sevm .blockhash := by square_open; square_walk

/-! #### Word: arithmetic, comparison, bitwise -/

theorem runCore_eq : Square pc d sevm .eq := ofExecution_applyBinary _ _ _
theorem runCore_lt : Square pc d sevm .lt := ofExecution_applyBinary _ _ _
theorem runCore_gt : Square pc d sevm .gt := ofExecution_applyBinary _ _ _
theorem runCore_slt : Square pc d sevm .slt := ofExecution_applyBinary _ _ _
theorem runCore_sgt : Square pc d sevm .sgt := ofExecution_applyBinary _ _ _
theorem runCore_iszero : Square pc d sevm .iszero := ofExecution_applyUnary _ _ _
theorem runCore_not : Square pc d sevm .not := ofExecution_applyUnary _ _ _
theorem runCore_and : Square pc d sevm .and := ofExecution_applyBinary _ _ _
theorem runCore_or : Square pc d sevm .or := ofExecution_applyBinary _ _ _
theorem runCore_xor : Square pc d sevm .xor := ofExecution_applyBinary _ _ _
theorem runCore_signextend : Square pc d sevm .signextend := ofExecution_applyBinary _ _ _
theorem runCore_byte : Square pc d sevm .byte := ofExecution_applyBinary _ _ _
theorem runCore_shl : Square pc d sevm .shl := by square_open; square_walk
theorem runCore_shr : Square pc d sevm .shr := by square_open; square_walk
theorem runCore_sar : Square pc d sevm .sar := by square_open; square_walk
theorem runCore_clz : Square pc d sevm .clz := by square_open; square_walk
theorem runCore_add : Square pc d sevm .add := ofExecution_applyBinary _ _ _
theorem runCore_sub : Square pc d sevm .sub := ofExecution_applyBinary _ _ _
theorem runCore_mul : Square pc d sevm .mul := ofExecution_applyBinary _ _ _
theorem runCore_div : Square pc d sevm .div := ofExecution_applyBinary _ _ _
theorem runCore_sdiv : Square pc d sevm .sdiv := ofExecution_applyBinary _ _ _
theorem runCore_mod : Square pc d sevm .mod := ofExecution_applyBinary _ _ _
theorem runCore_smod : Square pc d sevm .smod := ofExecution_applyBinary _ _ _
theorem runCore_addmod : Square pc d sevm .addmod := ofExecution_applyTernary _ _ _
theorem runCore_mulmod : Square pc d sevm .mulmod := ofExecution_applyTernary _ _ _
theorem runCore_exp : Square pc d sevm .exp := by square_open; square_walk
theorem runCore_pop : Square pc d sevm .pop := by
  square_open
  have h : (d.pop <&> Prod.snd >>= Jaune.chargeGas Gas.base) =
      (d.pop >>= fun p => Jaune.chargeGas Gas.base p.2) := by
    cases d.pop <;> rfl
  rw [h]; square_walk

/-! #### Shuffle -/

theorem runCore_swap (n : Fin 16) : Square pc d sevm (.swap n) := by
  square_open
  refine sq_bind (ofExecution_chargeGas _ _) fun d => ?_
  unfold liftMachine
  dsimp only
  rw [show (ofDevm d).machine.stack = d.stack from rfl]
  cases List.swap d.stack n <;> rfl

theorem runCore_dup (n : Fin 16) : Square pc d sevm (.dup n) := by
  square_open
  refine sq_bind (ofExecution_chargeGas _ _) fun d => ?_
  unfold liftMachine
  dsimp only
  rw [show (ofDevm d).machine.stack = d.stack from rfl]
  cases h : d.stack[n]?
  · rfl
  · simp only
    exact (ofExecution_push _ _).trans (by unfold push liftMachine; rfl)

/-! #### Memory -/

theorem runCore_mload : Square pc d sevm .mload := by
  square_open
  refine sq_bindValue (ofOutcome_popToNat _) fun i d => ?_
  refine sq_bind (ofExecution_chargeGas _ _) fun d => ?_
  exact sq_push_lift (congrArg Bytes.toU256 (machine_memRead_ofDevm d i 32).1)
    (machine_memRead_ofDevm d i 32).2
theorem runCore_mstore : Square pc d sevm .mstore := by square_open; square_walk
theorem runCore_mstore8 : Square pc d sevm .mstore8 := by square_open; square_walk
theorem runCore_calldatacopy : Square pc d sevm .calldatacopy := by square_open; square_walk
theorem runCore_codecopy : Square pc d sevm .codecopy := by square_open; square_walk
theorem runCore_returndatacopy : Square pc d sevm .returndatacopy := by square_open; square_walk
theorem runCore_mcopy : Square pc d sevm .mcopy := by square_open; square_walk
theorem runCore_keccak256 : Square pc d sevm .keccak256 := by square_open; square_walk

/-! #### Log -/

theorem runCore_log (n : Fin 5) : Square pc d sevm (.log n) := by
  show _ = Except.ofHalt (Staging.PlainOp.liftLog
    (fun m => Staging.PlainOp.logStep n (.ofSevm sevm) m) (ofDevm d))
  simp only [Jaune.PlainOp.runCore, Staging.PlainOp.logStep, CallContext.ofSevm,
    liftLog_bindValue, liftLog_bind]
  refine sq_bindValue (ofOutcome_popToNat _) fun i d => ?_
  refine sq_bindValue (ofOutcome_popToNat _) fun k d => ?_
  refine sq_bindValue (ofOutcome_popN _ _) fun ts d => ?_
  refine sq_bind (ofExecution_chargeGas _ _) fun d => ?_
  unfold Staging.PlainOp.liftLog assertDynamic Except.assert
  rcases Bool.eq_false_or_eq_true sevm.isStatic with hs | hs <;>
    simp only [hs, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
  · rfl
  · change Except.ofHalt (.ok ((ofDevm (d.memRead i k).2).addLog
        ⟨sevm.currentTarget, ts, (d.memRead i k).1⟩)) =
      Except.ofHalt (.ok (((ofDevm d).withMachine ((ofDevm d).machine.memRead i k).2).addLog
        ⟨sevm.currentTarget, ts, ((ofDevm d).machine.memRead i k).1⟩))
    rw [(machine_memRead_ofDevm d i k).2, (machine_memRead_ofDevm d i k).1]

/-! #### Read -/

theorem runCore_balance : Square pc d sevm .balance := by
  rcases d with ⟨⟨stack, mem, gas, sg⟩, v, w⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
    dsimp only [Square, Jaune.PlainOp.runCore, Staging.PlainOp.runCore, CallContext.ofSevm]
    simp only [liftMachMetaWorldExecution, liftMachMetaExecution, liftMachMeta, Footprint.liftOutcome,
      Footprint.toExecution, PlainOp.balanceCore, Mach.pop, Mach.chargeGas, Mach.push,
      popToAddress, liftMachineValue, Machine.popToAddress, Machine.pop, liftMachine,
      Machine.chargeGas, push, Machine.push, Frame.State.chargeGas, ofDevm, withMachine,
      bind, Except.bind, Devm.stack, Devm.memory, Devm.gasLeft, Devm.stateGas, Devm.returnData,
      Devm.logs, Devm.refundCounter, Devm.accountsToDelete, Devm.accessedAddresses,
      Devm.accessedStorageKeys, Devm.createdAccounts, recordAccountRead, Frame.State.addAccessedAddress,
      withSubstate, withTrail, Frame.State.balance, Frame.State.account, Frame.State.state,
      Frame.State.accessedAddresses, Substate.addAccessedAddress, Meta.addAccessedAddress,
      Meta.readAccount, Trail.readAccount]
    try dsimp only
    cases sevm.benvStat.rules.access with
    | eip2929 =>
      by_cases hw : x.toAddress ∈ v.accessedAddresses <;> simp only [hw, ↓reduceIte] <;>
        (try dsimp only)
      · rcases hs : safeSub gas (Gas.warmStorageReadCost) with _ | g' <;> simp only [hs] <;> (try dsimp only) <;>
          (try (by_cases hl : xs.length < 1024 <;> simp only [hl, ↓reduceIte])) <;>
          (try (by_cases hb : sevm.benvStat.rules.blockAccessListRules.isSome = true <;>
            simp only [hb, ↓reduceIte, Bool.false_eq_true])) <;> rfl
      · rcases hs : safeSub gas (sevm.benvStat.rules.gas.coldAccountAccess) with _ | g' <;> simp only [hs] <;> (try dsimp only) <;>
          (try (by_cases hl : xs.length < 1024 <;> simp only [hl, ↓reduceIte])) <;>
          (try (by_cases hb : sevm.benvStat.rules.blockAccessListRules.isSome = true <;>
            simp only [hb, ↓reduceIte, Bool.false_eq_true])) <;> rfl
    | flat g =>
      try dsimp only
      rcases hs : safeSub gas (g.balance) with _ | g' <;> simp only [hs] <;> (try dsimp only) <;>
          (try (by_cases hl : xs.length < 1024 <;> simp only [hl, ↓reduceIte])) <;>
          (try (by_cases hb : sevm.benvStat.rules.blockAccessListRules.isSome = true <;>
            simp only [hb, ↓reduceIte, Bool.false_eq_true])) <;> rfl

theorem runCore_extcodesize : Square pc d sevm .extcodesize := by
  square_open; cases sevm.benvStat.rules.access <;> square_walk
theorem runCore_extcodecopy : Square pc d sevm .extcodecopy := by
  square_open; cases sevm.benvStat.rules.access <;> square_walk
theorem runCore_extcodehash : Square pc d sevm .extcodehash := by
  square_open; cases sevm.benvStat.rules.access <;> square_walk
theorem runCore_selfbalance : Square pc d sevm .selfbalance := by square_open; square_walk
theorem runCore_sload : Square pc d sevm .sload := by
  square_open; cases sevm.benvStat.rules.access <;> square_walk
theorem runCore_tload : Square pc d sevm .tload := by square_open; square_walk

/-! #### Store -/

theorem runCore_sstore : Square pc d sevm .sstore := by
  dsimp only [Square, Jaune.PlainOp.runCore, Staging.PlainOp.runCore, CallContext.ofSevm,
    Staging.PlainOp.sstoreBerlin, Staging.PlainOp.sstoreLegacy, Staging.PlainOp.sstoreAmsterdam]
  rcases hsg : sevm.benvStat.rules.stateGas with _ | st
  · rcases sevm.benvStat.rules.sstore with ⟨a, b⟩
    cases a <;> cases b <;> cases sevm.benvStat.rules.access <;> dsimp only <;>
      refine sq_bindValue (ofOutcome_pop _) fun key d => ?_ <;>
      refine sq_bindValue (ofOutcome_pop _) fun nv d => ?_ <;>
      refine sq_assert fun _ => ?_ <;> dsimp only
    all_goals
      simp only [ok_bind, ← ofDevm_balReadStorage, ofDevm_accessedStorageKeys,
        ofDevm_originalStorageValue, ofDevm_storageValue]
      try (by_cases hc : (sevm.currentTarget, key) ∉
          (Devm.balReadStorage sevm.benvStat.rules sevm.currentTarget key d).accessedStorageKeys <;>
        simp only [hc, ↓reduceIte, not_false_eq_true, not_true_eq_false, ite_true, ite_false])
      all_goals
        simp only [← ofDevm_addAccessedStorageKey, ← ofDevm_withRefundCounter, ofDevm_refund]
        refine sq_bind (ofExecution_chargeGas _ _) fun d => ?_
        refine sq_assertDynamic fun _ => ?_
        simp only [← ofDevm_balReadAccount, ← ofDevm_setStorVal]
        rfl
  · refine sq_assertDynamic fun _ => ?_
    refine sq_bindValue (ofOutcome_pop _) fun key d => ?_
    refine sq_bindValue (ofOutcome_pop _) fun nv d => ?_
    refine sq_assert fun _ => ?_
    dsimp only
    by_cases hc : (sevm.currentTarget, key) ∉ d.accessedStorageKeys <;>
      simp only [hc, ofDevm_accessedStorageKeys, ↓reduceIte, decide_true, decide_false,
        not_false_eq_true, not_true_eq_false, ite_true, ite_false] <;>
      simp only [← ofDevm_addAccessedStorageKey, ← ofDevm_balReadStorage, ← ofDevm_withRefundCounter,
        ← ofDevm_creditStateGasRefund, ofDevm_originalStorageValue, ofDevm_storageValue,
        ofDevm_refund] <;>
      refine sq_bind (ofExecution_chargeGas _ _) fun d => ?_ <;>
      refine sq_bind (ofExecution_chargeStateGas _ _) fun d => ?_ <;>
      simp only [← ofDevm_balReadAccount, ← ofDevm_setStorVal] <;> rfl

theorem runCore_tstore : Square pc d sevm .tstore := by
  square_open; cases sevm.benvStat.rules.stateGas <;> square_walk


/-! ### The whole function -/

/-- **The square for `PlainOp.runCore`.** For every program counter, every `Devm`, every `Sevm`
(so every fork) and every plain instruction, the successor over `Frame.State` and `CallContext`
is the old body mapped through `Frame.State.ofDevm` on both channels, its halts embedded in
`EvmError` by `Except.ofHalt`. -/
theorem runCore_square (pc : Nat) (d : Devm) (sevm : Sevm) (op : Jaune.PlainOp) :
    Frame.State.ofExecution (Jaune.PlainOp.runCore pc d sevm op) =
      Except.ofHalt (Staging.PlainOp.runCore pc (CallContext.ofSevm sevm) (Frame.State.ofDevm d) op) :=
  match op with
  | .address => runCore_address pc d sevm
  | .origin => runCore_origin pc d sevm
  | .caller => runCore_caller pc d sevm
  | .callvalue => runCore_callvalue pc d sevm
  | .calldatasize => runCore_calldatasize pc d sevm
  | .codesize => runCore_codesize pc d sevm
  | .gasprice => runCore_gasprice pc d sevm
  | .returndatasize => runCore_returndatasize pc d sevm
  | .number => runCore_number pc d sevm
  | .timestamp => runCore_timestamp pc d sevm
  | .gaslimit => runCore_gaslimit pc d sevm
  | .prevrandao => runCore_prevrandao pc d sevm
  | .coinbase => runCore_coinbase pc d sevm
  | .msize => runCore_msize pc d sevm
  | .pc => runCore_pc pc d sevm
  | .basefee => runCore_basefee pc d sevm
  | .blobbasefee => runCore_blobbasefee pc d sevm
  | .chainid => runCore_chainid pc d sevm
  | .slotnum => runCore_slotnum pc d sevm
  | .gas => runCore_gas pc d sevm
  | .blobhash => runCore_blobhash pc d sevm
  | .calldataload => runCore_calldataload pc d sevm
  | .blockhash => runCore_blockhash pc d sevm
  | .eq => runCore_eq pc d sevm
  | .lt => runCore_lt pc d sevm
  | .gt => runCore_gt pc d sevm
  | .slt => runCore_slt pc d sevm
  | .sgt => runCore_sgt pc d sevm
  | .iszero => runCore_iszero pc d sevm
  | .not => runCore_not pc d sevm
  | .and => runCore_and pc d sevm
  | .or => runCore_or pc d sevm
  | .xor => runCore_xor pc d sevm
  | .signextend => runCore_signextend pc d sevm
  | .byte => runCore_byte pc d sevm
  | .shl => runCore_shl pc d sevm
  | .shr => runCore_shr pc d sevm
  | .sar => runCore_sar pc d sevm
  | .clz => runCore_clz pc d sevm
  | .add => runCore_add pc d sevm
  | .sub => runCore_sub pc d sevm
  | .mul => runCore_mul pc d sevm
  | .div => runCore_div pc d sevm
  | .sdiv => runCore_sdiv pc d sevm
  | .mod => runCore_mod pc d sevm
  | .smod => runCore_smod pc d sevm
  | .addmod => runCore_addmod pc d sevm
  | .mulmod => runCore_mulmod pc d sevm
  | .exp => runCore_exp pc d sevm
  | .pop => runCore_pop pc d sevm
  | .swap k => runCore_swap pc d sevm k
  | .dup k => runCore_dup pc d sevm k
  | .mload => runCore_mload pc d sevm
  | .mstore => runCore_mstore pc d sevm
  | .mstore8 => runCore_mstore8 pc d sevm
  | .calldatacopy => runCore_calldatacopy pc d sevm
  | .codecopy => runCore_codecopy pc d sevm
  | .returndatacopy => runCore_returndatacopy pc d sevm
  | .mcopy => runCore_mcopy pc d sevm
  | .keccak256 => runCore_keccak256 pc d sevm
  | .log k => runCore_log pc d sevm k
  | .balance => runCore_balance pc d sevm
  | .extcodesize => runCore_extcodesize pc d sevm
  | .extcodecopy => runCore_extcodecopy pc d sevm
  | .extcodehash => runCore_extcodehash pc d sevm
  | .selfbalance => runCore_selfbalance pc d sevm
  | .sload => runCore_sload pc d sevm
  | .tload => runCore_tload pc d sevm
  | .sstore => runCore_sstore pc d sevm
  | .tstore => runCore_tstore pc d sevm

/-- The same square at the running-frame level: `Staging.PlainOp.run` against `PlainOp.run`. -/
theorem run_square (evm : Evm) (op : Jaune.PlainOp) :
    Frame.State.ofExecution (Jaune.PlainOp.run evm op) =
      Except.ofHalt (Staging.PlainOp.run (Frame.Running.ofEvm evm) op) :=
  runCore_square evm.pc evm.dyna evm.sta op

end PlainOp

end Jaune.Bridge.G2b
