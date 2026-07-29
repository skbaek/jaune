import Jaune.Execution

/-!
# A sufficient fuel bound for the interpreter driver

`Jaune.Execution` defines the interpreter driver structurally recursive on a
fuel parameter, so it must report exhaustion as a possible outcome. This module
proves that fuel seeded from the frame's remaining gas is always sufficient, and
uses that proof to give the driver and its frame wrappers a total type.

It sits between `Jaune.Execution` (the driver) and `Jaune.Transaction` (its
first consumer) so that the consumers can be stated against the total API.

## The measure

The measure is the single field `Devm.gasLeft`. It is deliberately *not*
Blanc's `Devm.Burn`: that relation is non-strict and bundles thirteen further
field equalities, neither of which this argument wants. Everything here is
stated about `gasLeft` alone.

## The obligations

Sufficiency reduces to four facts about one step of the driver, all measured
against the frame's gas at the *start* of the step:

* `.cont` — a continuing step leaves strictly less gas;
* spawn/child — a spawned child starts with strictly less gas than its parent;
* spawn/done — a spawn that resolves without running a child resumes the parent
  with strictly less gas;
* spawn/settle — a spawn whose child ran, and whose child did not gain gas,
  resumes the parent with strictly less gas.

The last one is why the driver also needs a monotonicity theorem: the resumed
parent's gas is `parent.gasLeft + child.gasLeft`, so the child's own budget has
to be known not to have grown.
-/

/-- The remaining gas carried by a raw frame result, in either branch. The
error branch retains its `Devm` precisely so that gas can still be read off it,
and the driver's monotonicity theorem has to cover both branches because
`Frame.settle` consumes both. -/
def Execution.gasLeft : Execution → Nat
  | .ok devm => devm.gasLeft
  | .error e => e.2.gasLeft

@[simp] theorem Execution.gasLeft_ok (devm : Devm) :
    Execution.gasLeft (.ok devm) = devm.gasLeft := rfl

@[simp] theorem Execution.gasLeft_error (e : String × Devm) :
    Execution.gasLeft (.error e) = e.2.gasLeft := rfl

/-! ## Gas-preserving state updates

Every `Devm → Devm` update used by an instruction body other than
`Devm.withGasLeft` leaves `gasLeft` alone. Stating that once as a `simp` set is
what keeps the per-instruction proofs to a single `omega` at the end. -/

namespace Devm

@[simp] theorem setMach_gasLeft (devm : Devm) (mach : Mach) :
    (devm.setMach mach).gasLeft = mach.gasLeft := rfl

@[simp] theorem setMeta_gasLeft (devm : Devm) (view : Meta) :
    (devm.setMeta view).gasLeft = devm.gasLeft := rfl

@[simp] theorem setWorld_gasLeft (devm : Devm) (world : World) :
    (devm.setWorld world).gasLeft = devm.gasLeft := rfl

@[simp] theorem withGasLeft_gasLeft (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).gasLeft = n := rfl

@[simp] theorem withStack_gasLeft (devm : Devm) (stack : List B256) :
    (devm.withStack stack).gasLeft = devm.gasLeft := rfl

@[simp] theorem withMemory_gasLeft (devm : Devm) (memory : Mem) :
    (devm.withMemory memory).gasLeft = devm.gasLeft := rfl

@[simp] theorem withLogs_gasLeft (devm : Devm) (logs : List Log) :
    (devm.withLogs logs).gasLeft = devm.gasLeft := rfl

@[simp] theorem withRefundCounter_gasLeft (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).gasLeft = devm.gasLeft := rfl

@[simp] theorem withReturnData_gasLeft (devm : Devm) (returnData : Bytes) :
    (devm.withReturnData returnData).gasLeft = devm.gasLeft := rfl

@[simp] theorem withError_gasLeft (devm : Devm) (error : Option String) :
    (devm.withError error).gasLeft = devm.gasLeft := rfl

@[simp] theorem withCreatedAccounts_gasLeft (devm : Devm) (as : AdrSet) :
    (devm.withCreatedAccounts as).gasLeft = devm.gasLeft := rfl

@[simp] theorem withState_gasLeft (devm : Devm) (state : State) :
    (devm.withState state).gasLeft = devm.gasLeft := rfl

@[simp] theorem memWrite_gasLeft (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).gasLeft = devm.gasLeft := rfl

@[simp] theorem memExtends_gasLeft (devm : Devm) (pairs : List (Nat × Nat)) :
    (devm.memExtends pairs).gasLeft = devm.gasLeft := rfl

@[simp] theorem memRead_gasLeft (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.gasLeft = devm.gasLeft := rfl

@[simp] theorem addLog_gasLeft (devm : Devm) (log : Log) :
    (devm.addLog log).gasLeft = devm.gasLeft := rfl

@[simp] theorem setStorVal_gasLeft (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setStorVal adr key val).gasLeft = devm.gasLeft := rfl

@[simp] theorem setTransVal_gasLeft (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setTransVal adr key val).gasLeft = devm.gasLeft := rfl

@[simp] theorem incrNonce_gasLeft (devm : Devm) (adr : Adr) :
    (devm.incrNonce adr).gasLeft = devm.gasLeft := rfl

@[simp] theorem setCode_gasLeft (devm : Devm) (adr : Adr) (code : ByteArray) :
    (devm.setCode adr code).gasLeft = devm.gasLeft := rfl

@[simp] theorem rollback_gasLeft (devm : Devm) (wor : State) (tra : Tra) :
    (devm.rollback wor tra).gasLeft = devm.gasLeft := rfl

end Devm

@[simp] theorem addAccessedAddress_gasLeft (devm : Devm) (a : Adr) :
    (addAccessedAddress devm a).gasLeft = devm.gasLeft := rfl

@[simp] theorem addAccessedStorageKey_gasLeft (devm : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey devm a k).gasLeft = devm.gasLeft := rfl

/-! ## The charging primitive

`chargeGas` is the only place an instruction body loses gas, and it loses
exactly the cost it was asked for. Every strict-decrease proof in the corpus
bottoms out in `chargeGas_gasLeft`, so it is stated as an exact equation rather
than an inequality: the arithmetic of the call/create families needs to add the
charge back. -/

theorem chargeGas_gasLeft {c : Nat} {devm devm' : Devm}
    (h : chargeGas c devm = .ok devm') : devm'.gasLeft + c = devm.gasLeft := by
  rw [chargeGas_def] at h
  by_cases hle : c ≤ devm.gasLeft
  · simp only [safeSub, if_pos hle, Except.ok.injEq] at h
    subst h
    simp only [Devm.setMach_gasLeft]
    omega
  · exact absurd h (by simp [safeSub, if_neg hle])

/-! ## Stack primitives

Pushing and popping never touch `gasLeft`. These are the inversion forms the
instruction walks need: the hypothesis is the `.ok` equation that survives a
`split`, and the conclusion feeds `omega`. -/

theorem Devm.push_gasLeft {x : B256} {devm devm' : Devm}
    (h : Devm.push x devm = .ok devm') : devm'.gasLeft = devm.gasLeft := by
  rw [Devm.push_def] at h
  unfold Except.assert at h
  split at h
  · simp only [bind, Except.bind, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp [bind, Except.bind])

theorem Devm.pop_gasLeft {devm : Devm} {x : B256} {devm' : Devm}
    (h : devm.pop = .ok (x, devm')) : devm'.gasLeft = devm.gasLeft := by
  rw [Devm.pop_def] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; rfl

theorem Devm.popToNat_gasLeft {devm : Devm} {n : Nat} {devm' : Devm}
    (h : devm.popToNat = .ok (n, devm')) : devm'.gasLeft = devm.gasLeft := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack with
  | nil =>
    exact absurd h (by
      simp [Devm.popToNat, liftMach, Mach.popToNat, Mach.pop, Footprint.liftOutcome])
  | cons x xs =>
    simp only [Devm.popToNat, liftMach, Mach.popToNat, Mach.pop,
      Footprint.liftOutcome, Devm.setMach, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl

theorem Devm.popToAdr_gasLeft {devm : Devm} {a : Adr} {devm' : Devm}
    (h : devm.popToAdr = .ok (a, devm')) : devm'.gasLeft = devm.gasLeft := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack with
  | nil =>
    exact absurd h (by
      simp [Devm.popToAdr, liftMach, Mach.popToAdr, Mach.pop, Footprint.liftOutcome])
  | cons x xs =>
    simp only [Devm.popToAdr, liftMach, Mach.popToAdr, Mach.pop,
      Footprint.liftOutcome, Devm.setMach, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl

theorem Devm.popN_gasLeft {devm : Devm} {n : Nat} {xs : List B256} {devm' : Devm}
    (h : devm.popN n = .ok (xs, devm')) : devm'.gasLeft = devm.gasLeft := by
  induction n generalizing devm xs devm' with
  | zero =>
    rw [Devm.popN_def] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  | succ n ih =>
    rw [Devm.popN_def] at h
    cases hp : devm.pop with
    | error e => rw [hp] at h; exact absurd h (by simp [bind, Except.bind])
    | ok p =>
      rw [hp] at h
      simp only [bind, Except.bind] at h
      cases hq : p.2.popN n with
      | error e => rw [hq] at h; exact absurd h (by simp)
      | ok q =>
        rw [hq] at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        rw [← h.2, ih (by rw [hq]), Devm.pop_gasLeft (x := p.1) (by rw [hp])]

/-! ## Lifting a footprint-restricted core

`liftMachExecution` and its `Meta`/`World` variants only ever reattach the
core's own `Mach` to the original `Devm`, so a gas fact proved once about the
core transfers verbatim. These inversion lemmas are what let the `apply*`
family — and, in the corpus, `Rinst.balanceCore` — be handled at the `Mach`
level, where there is no `Devm` scaffolding in the way. -/

theorem liftMachExecution_ok {core : Mach → Footprint.Outcome Mach Unit}
    {devm devm' : Devm} (h : liftMachExecution core devm = .ok devm') :
    ∃ u mach', core devm.mach = .ok (u, mach') ∧ devm'.gasLeft = mach'.gasLeft := by
  unfold liftMachExecution liftMach Footprint.toExecution Footprint.liftOutcome at h
  rcases hc : core devm.mach with ⟨err, view⟩ | ⟨u, mach'⟩ <;> simp only [hc] at h
  · exact absurd h (by simp)
  · refine ⟨u, mach', rfl, ?_⟩
    simp only [Except.ok.injEq] at h
    rw [← h]
    rfl

theorem liftMachMetaExecution_ok
    {core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit}
    {devm devm' : Devm} (h : liftMachMetaExecution core devm = .ok devm') :
    ∃ u view', core devm.mach devm.meta = .ok (u, view') ∧
      devm'.gasLeft = view'.1.gasLeft := by
  unfold liftMachMetaExecution liftMachMeta Footprint.toExecution
    Footprint.liftOutcome at h
  rcases hc : core devm.mach devm.meta with ⟨err, view⟩ | ⟨u, view'⟩ <;>
    simp only [hc] at h
  · exact absurd h (by simp)
  · refine ⟨u, view', rfl, ?_⟩
    simp only [Except.ok.injEq] at h
    rw [← h]
    rfl

theorem liftMachMetaWorldExecution_ok
    {core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit}
    {devm devm' : Devm} (h : liftMachMetaWorldExecution core devm = .ok devm') :
    ∃ u view', core devm.world devm.mach devm.meta = .ok (u, view') ∧
      devm'.gasLeft = view'.1.gasLeft :=
  liftMachMetaExecution_ok h

/-! ## The `Mach`-level charging and stack layer

The `apply*` family is defined by `liftMachExecution` over a `Mach`-only core
with no intervening `_def` lemma for the ternary case, so its gas accounting is
proved here rather than at `Devm` level. -/

namespace Mach

theorem chargeGas_gasLeft {c : Nat} {mach mach' : Mach} {u : Unit}
    (h : Mach.chargeGas c mach = .ok (u, mach')) :
    mach'.gasLeft + c = mach.gasLeft := by
  unfold Mach.chargeGas safeSub at h
  by_cases hle : c ≤ mach.gasLeft
  · simp only [if_pos hle, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    dsimp only
    omega
  · exact absurd h (by simp [if_neg hle])

theorem pop_gasLeft {mach mach' : Mach} {x : B256}
    (h : mach.pop = .ok (x, mach')) : mach'.gasLeft = mach.gasLeft := by
  unfold Mach.pop at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]

theorem push_gasLeft {x : B256} {mach mach' : Mach} {u : Unit}
    (h : Mach.push x mach = .ok (u, mach')) : mach'.gasLeft = mach.gasLeft := by
  unfold Mach.push at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
  · exact absurd h (by simp)

theorem pushItem_gasLeft {x : B256} {c : Nat} {mach mach' : Mach} {u : Unit}
    (h : Mach.pushItem x c mach = .ok (u, mach')) :
    mach'.gasLeft + c = mach.gasLeft := by
  unfold Mach.pushItem at h
  rcases hc : Mach.chargeGas c mach with ⟨err, m⟩ | ⟨uc, m1⟩ <;> simp only [hc] at h
  · exact absurd h (by simp)
  · rw [push_gasLeft h, ← chargeGas_gasLeft hc]

theorem applyUnary_gasLeft {f : B256 → B256} {c : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.applyUnary f c mach = .ok (u, mach')) :
    mach'.gasLeft + c = mach.gasLeft := by
  unfold Mach.applyUnary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rw [pushItem_gasLeft h, pop_gasLeft hp]

theorem applyBinary_gasLeft {f : B256 → B256 → B256} {c : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.applyBinary f c mach = .ok (u, mach')) :
    mach'.gasLeft + c = mach.gasLeft := by
  unfold Mach.applyBinary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rcases hq : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> simp only [hq] at h
    · exact absurd h (by simp)
    · rw [pushItem_gasLeft h, pop_gasLeft hq, pop_gasLeft hp]

theorem applyTernary_gasLeft {f : B256 → B256 → B256 → B256} {c : Nat}
    {mach mach' : Mach} {u : Unit}
    (h : Mach.applyTernary f c mach = .ok (u, mach')) :
    mach'.gasLeft + c = mach.gasLeft := by
  unfold Mach.applyTernary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rcases hq : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> simp only [hq] at h
    · exact absurd h (by simp)
    · rcases hr : m2.pop with ⟨err, m⟩ | ⟨z, m3⟩ <;> simp only [hr] at h
      · exact absurd h (by simp)
      · rw [pushItem_gasLeft h, pop_gasLeft hr, pop_gasLeft hq, pop_gasLeft hp]

end Mach

/-! ## The instruction-level combinators

These four cover every `Rinst` constructor whose body is a bare
`pushItem`/`apply*` call, and they are the last step of the walk for many of
the rest. Each is stated as an exact equation in the charge, so a caller that
needs strictness supplies `0 < c` and finishes with `omega`. -/

theorem pushItem_gasLeft {x : B256} {c : Nat} {devm devm' : Devm}
    (h : pushItem x c devm = .ok devm') : devm'.gasLeft + c = devm.gasLeft := by
  obtain ⟨_, mach', hcore, hgas⟩ := liftMachExecution_ok h
  rw [hgas, Mach.pushItem_gasLeft hcore]
  rfl

theorem applyUnary_gasLeft {f : B256 → B256} {c : Nat} {devm devm' : Devm}
    (h : applyUnary f c devm = .ok devm') : devm'.gasLeft + c = devm.gasLeft := by
  obtain ⟨_, mach', hcore, hgas⟩ := liftMachExecution_ok h
  rw [hgas, Mach.applyUnary_gasLeft hcore]
  rfl

theorem applyBinary_gasLeft {f : B256 → B256 → B256} {c : Nat} {devm devm' : Devm}
    (h : applyBinary f c devm = .ok devm') : devm'.gasLeft + c = devm.gasLeft := by
  obtain ⟨_, mach', hcore, hgas⟩ := liftMachExecution_ok h
  rw [hgas, Mach.applyBinary_gasLeft hcore]
  rfl

theorem applyTernary_gasLeft {f : B256 → B256 → B256 → B256} {c : Nat}
    {devm devm' : Devm} (h : applyTernary f c devm = .ok devm') :
    devm'.gasLeft + c = devm.gasLeft := by
  obtain ⟨_, mach', hcore, hgas⟩ := liftMachExecution_ok h
  rw [hgas, Mach.applyTernary_gasLeft hcore]
  rfl

/-! ## Walking an instruction body

Every instruction body is a `do` chain in `Except (String × Devm)`. Peeling one
`bind` at a time with this lemma is what keeps the walks free of the fragile
`split`-and-`rename_i` idiom: the scrutinee never has to be written out, so a
cost expression can be arbitrarily large without the proof mentioning it. -/

theorem Except.bind_eq_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β}
    {b : β} (h : e >>= f = .ok b) : ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e with
  | error err => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

theorem Except.assert_eq_ok {p : Prop} [Decidable p] {ε : Type} {e : ε} {u : Unit}
    (h : Except.assert p e = .ok u) : p := by
  unfold Except.assert at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-! ## Resume accounting

A `Resume` succeeds only by incorporating a child that itself succeeded, and it
always hands the parent back exactly `parent.gasLeft + child.gasLeft`. Isolating
that here is what collapses the three spawn-shaped obligations of the driver
into the single arithmetic fact `frame.inner.gas + rsm.parentGas < gasLeft`:
the child's own budget is `frame.inner.gas` and never grows, and the parent's
retained gas is `rsm.parentGas`. -/

/-- The gas a `Resume` retains for the parent, before the child's leftover is
added back. -/
def Resume.parentGas : Resume → Nat
  | .create parent _ => parent.gasLeft
  | .call parent _ _ => parent.gasLeft

theorem Resume.run_ok_gasLeft {rsm : Resume}
    {r : Except (String × State × AdrSet × Tra) Devm} {devm' : Devm}
    (h : rsm.run r = .ok devm') :
    ∃ child : Devm, r = .ok child ∧
      devm'.gasLeft = rsm.parentGas + child.gasLeft := by
  cases rsm with
  | create parent newAddress =>
    cases r with
    | error e => exact absurd h (by simp [Resume.run, liftToExecution, bind, Except.bind])
    | ok child =>
      refine ⟨child, rfl, ?_⟩
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      split at h
      · rw [Devm.push_gasLeft h]; rfl
      · rw [Devm.push_gasLeft h]; rfl
  | call parent outputIndex outputSize =>
    cases r with
    | error e => exact absurd h (by simp [Resume.run, liftToExecution, bind, Except.bind])
    | ok child =>
      refine ⟨child, rfl, ?_⟩
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      split at h
      · rcases hp : (incorporateChildOnError parent child child.output).push 0 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.memWrite_gasLeft, Devm.push_gasLeft hp]
          rfl
      · rcases hp : (incorporateChildOnSuccess parent child child.output).push 1 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.memWrite_gasLeft, Devm.push_gasLeft hp]
          rfl

/-! ## Call-family accounting

The whole call family reduces to one inequality: whatever `calculateMsgCallGas`
hands the child as a stipend is strictly less than what it charges the parent
for the call. That holds in *both* of its branches and needs no hypothesis about
the parent's remaining gas — the only side condition is that the instruction's
`extra_gas` strictly covers the stipend, which every call-type opcode satisfies
because a warm access alone costs 100 and a value-bearing call pays
`gasCallValue = 9000` against a `gCallStipend = 2300` stipend.

This single lemma discharges all three call outcomes: the depth-0 refund, the
insufficient-balance refund, and the spawn itself. -/

theorem access_cost_pos (x : Adr) (a : AdrSet) : 0 < accessCost x a := by
  unfold accessCost gasWarmAccess gasColdAccountAccess
  split <;> omega

theorem gasWarmAccess_le_access_cost (x : Adr) (a : AdrSet) :
    gasWarmAccess ≤ accessCost x a := by
  unfold accessCost gasWarmAccess gasColdAccountAccess
  split <;> omega

theorem calculateMsgCallGas_stipend_lt
    {value gas gasLeft memoryCost extraGas cs : Nat}
    (hstip : (if value = 0 then 0 else cs) < extraGas + memoryCost) :
    (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).2 <
      (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).1 + memoryCost := by
  unfold calculateMsgCallGas
  split <;> split <;> simp_all <;> omega

/-! ## Pilot

Step 1 discharges a representative slice of the corpus rather than all of it:
one instruction from each shape Step 2 will meet, so that the cost of the grind
can be estimated honestly and the combinator layer is known to be the right one.

The slice is `.add` (the `apply*` family, 25 constructors), `.mstore` (a
memory-extending body, 7 constructors), `.extcodesize` (a warm/cold access body
with the charge inside an `if`, 4 constructors), `Jinst.jumpdest` (the smallest
charge in the machine, `gJumpdest = 1`), and `Xinst.step .call` — the hard case,
covering a spawn and both of its refund branches. -/

@[simp] theorem accessDelegation_gasLeft (devm : Devm) (adr : Adr) :
    (accessDelegation devm adr).2.2.2.2.gasLeft = devm.gasLeft := by
  unfold accessDelegation
  by_cases hd : isValidDelegation (devm.state.getCode adr) <;>
    simp only [hd, if_pos, if_neg, not_false_iff, addAccessedAddress_gasLeft]

/-- The step-level obligation for a call-type instruction, measured against the
frame's gas at the start of the step.

The spawn case is the design decision that keeps the corpus small: rather than
three separate obligations (child budget, resume-after-`done`,
resume-after-child) it asserts the single arithmetic fact
`frame.inner.gas + rsm.parentGas < n`. The other three follow from it
generically, because `Frame.enter` hands the child exactly `frame.inner.gas`,
neither the child nor `Frame.settle` can increase that, and `Resume.run`
returns `rsm.parentGas + child.gasLeft` (`Resume.run_ok_gasLeft`). -/
def XStep.GasDecreasing (n : Nat) : XStep → Prop
  | .done ex => ∀ devm', ex = .ok devm' → devm'.gasLeft < n
  | .spawn frame rsm => frame.inner.gas + rsm.parentGas < n

theorem XStep.ofExcept_gasDecreasing {n : Nat} {x : Except (String × Devm) XStep}
    (h : ∀ step, x = .ok step → step.GasDecreasing n) :
    (XStep.ofExcept x).GasDecreasing n := by
  cases x with
  | error e => intro devm' hd; exact absurd hd (by simp)
  | ok step => exact h step rfl

/-- The call-family spawn, stated once for all six dispatch sites. The single
hypothesis is what each `Xinst` constructor has to establish: the gas the parent
keeps, plus the whole budget handed to the child, is still strictly less than
what the parent had when the step began. The depth-0 refund branch hands the
budget straight back, so it needs exactly the same inequality. -/
theorem genericCall.step_gasDecreasing
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) {n : Nat}
    (hn : devm.gasLeft + gas < n) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).GasDecreasing n := by
  unfold genericCall.step
  split
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨d1, p1, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasLeft p1, Devm.withGasLeft_gasLeft,
      Devm.withReturnData_gasLeft]
    exact hn
  · show (Frame.ofCall _).inner.gas + Resume.parentGas _ < n
    simp only [Frame.ofCall, callMsg, Resume.parentGas, Devm.withReturnData_gasLeft]
    omega

/-- The shared tail of every call-type instruction. Once the parent has been
charged `cost + memoryCost` for a call whose stipend that charge strictly
covers, whatever the parent keeps plus the stipend it hands over is still
strictly below where the parent started. Both refund branches and the spawn
itself consume exactly this. -/
theorem call_charge_stipend_lt
    {value gas gasLeft memoryCost extraGas cs : Nat} {devm d d' : Devm}
    (hstip : (if value = 0 then 0 else cs) < extraGas + memoryCost)
    (hd : d.gasLeft = devm.gasLeft)
    (hcharge : chargeGas
        ((calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).1 + memoryCost)
        d = .ok d') :
    d'.gasLeft + (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).2
      < devm.gasLeft := by
  have e := chargeGas_gasLeft hcharge
  have s := calculateMsgCallGas_stipend_lt (value := value) (gas := gas)
    (gasLeft := gasLeft) (memoryCost := memoryCost) (extraGas := extraGas)
    (cs := cs) hstip
  omega

theorem Xinst.step_call_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (Xinst.step sevm devm .call).GasDecreasing devm.gasLeft := by
  simp only [Xinst.step]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨callee, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  have e1 := Devm.pop_gasLeft p1
  have e2 := Devm.popToAdr_gasLeft p2
  have e3 := Devm.pop_gasLeft p3
  have e4 := Devm.popToNat_gasLeft p4
  have e5 := Devm.popToNat_gasLeft p5
  have e6 := Devm.popToNat_gasLeft p6
  have e7 := Devm.popToNat_gasLeft p7
  dsimp only at e2 e3 e4 e5 e6 e7
  -- The delegation lookup can warm one more address but never touches gas.
  have eA : (accessDelegation (addAccessedAddress d7 callee) callee).2.2.2.2.gasLeft
      = devm.gasLeft := by
    rw [accessDelegation_gasLeft, addAccessedAddress_gasLeft]; omega
  -- `extra_gas` strictly covers the stipend: a warm access alone costs 100, and
  -- a value-bearing call pays `gasCallValue` against a `gCallStipend` stipend.
  have hstip :
      (if value.toNat = 0 then 0 else gCallStipend) <
        ((accessCost callee d7.accessedAddresses +
              (accessDelegation (addAccessedAddress d7 callee) callee).2.2.2.1 +
            if ¬((accessDelegation (addAccessedAddress d7 callee) callee).2.2.2.2.getAcct
                    callee).Empty ∨ value = 0 then 0 else gNewAccount) +
          if value = 0 then 0 else gasCallValue) +
        d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    have hac := gasWarmAccess_le_access_cost callee d7.accessedAddresses
    by_cases hv : value = 0
    · have : value.toNat = 0 := by rw [hv]; rfl
      rw [if_pos this]
      unfold gasWarmAccess at hac
      omega
    · rw [if_neg hv]
      unfold gCallStipend gasCallValue at *
      split <;> omega
  obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨-, -, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  split at hstep
  · -- Insufficient sender balance: the stipend is refunded, nothing is spawned.
    obtain ⟨d9, ppush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.withGasLeft_gasLeft, Devm.push_gasLeft ppush,
      Devm.memExtends_gasLeft]
    exact key
  · -- The spawn: the child's whole budget is the stipend.
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCall.step_gasDecreasing
    rw [Devm.memExtends_gasLeft]
    exact key

theorem Rinst.runCore_mstore_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm} (h : Rinst.runCore pc devm sevm .mstore = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  simp only [Rinst.runCore] at h
  obtain ⟨⟨start_index, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
  dsimp only at h h1 h2 h3
  simp only [Except.ok.injEq] at h
  have e1 := Devm.popToNat_gasLeft h1
  have e2 := Devm.pop_gasLeft h2
  have e3 := chargeGas_gasLeft h3
  rw [← h, Devm.memWrite_gasLeft]
  unfold gVerylow at e3
  omega

theorem Rinst.runCore_extcodesize_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm} (h : Rinst.runCore pc devm sevm .extcodesize = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  simp only [Rinst.runCore] at h
  obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  dsimp only at h h1
  have e1 := Devm.popToAdr_gasLeft h1
  -- The charge sits inside the warm/cold `if`, and the elaborator pushed the
  -- continuation into both arms; both charge a positive constant, and the cold
  -- arm's `addAccessedAddress` preserves gas.
  split at h
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasLeft h2
    have e3 := Devm.push_gasLeft h3
    unfold gasWarmAccess at e2
    omega
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasLeft h2
    rw [addAccessedAddress_gasLeft] at e2
    have e3 := Devm.push_gasLeft h3
    unfold gasColdAccountAccess at e2
    omega

theorem Jinst.runCore_jumpdest_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {pc' : Nat} {devm' : Devm}
    (h : Jinst.runCore pc devm sevm .jumpdest = .ok (pc', devm')) :
    devm'.gasLeft < devm.gasLeft := by
  simp only [Jinst.runCore] at h
  obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  have e1 := chargeGas_gasLeft h1
  unfold gJumpdest at e1
  rw [← h.2]
  omega

/-! ## Strict-decrease corpus: reusable short walks -/

theorem pushItem_gasLt {x : B256} {c : Nat} {devm devm' : Devm}
    (hc : 0 < c) (h : pushItem x c devm = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  have e := pushItem_gasLeft h
  omega

theorem applyUnary_gasLt {f : B256 → B256} {c : Nat} {devm devm' : Devm}
    (hc : 0 < c) (h : applyUnary f c devm = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  have e := applyUnary_gasLeft h
  omega

theorem applyBinary_gasLt {f : B256 → B256 → B256} {c : Nat}
    {devm devm' : Devm} (hc : 0 < c)
    (h : applyBinary f c devm = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  have e := applyBinary_gasLeft h
  omega

theorem applyTernary_gasLt {f : B256 → B256 → B256 → B256} {c : Nat}
    {devm devm' : Devm} (hc : 0 < c)
    (h : applyTernary f c devm = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  have e := applyTernary_gasLeft h
  omega

theorem popChargePush_gasLt (pre : Devm)
    (cost : B256 → Devm → Nat) (value : B256 → Devm → B256)
    (hpos : ∀ x d, 0 < cost x d) {post : Devm}
    (h : (do
      let ⟨x, d⟩ ← pre.pop
      let d' ← chargeGas (cost x d) d
      d'.push (value x d')) = .ok post) :
    post.gasLeft < pre.gasLeft := by
  obtain ⟨⟨x, d⟩, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨d', hc, hpush⟩ := Except.bind_eq_ok h
  have ep := Devm.pop_gasLeft hp
  have ec := chargeGas_gasLeft hc
  have eq := Devm.push_gasLeft hpush
  have hcpos := hpos x d
  omega

theorem pop2ChargePush_gasLt (pre : Devm)
    (cost : B256 → B256 → Devm → Nat)
    (value : B256 → B256 → Devm → B256)
    (hpos : ∀ x y d, 0 < cost x y d) {post : Devm}
    (h : (do
      let ⟨x, d⟩ ← pre.pop
      let ⟨y, d⟩ ← d.pop
      let d' ← chargeGas (cost x y d) d
      d'.push (value x y d')) = .ok post) :
    post.gasLeft < pre.gasLeft := by
  obtain ⟨⟨x, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨y, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  have e1 := Devm.pop_gasLeft h1
  have e2 := Devm.pop_gasLeft h2
  have e3 := chargeGas_gasLeft h3
  have e4 := Devm.push_gasLeft h4
  have hp := hpos x y d2
  omega

theorem popNat3ChargePure_gasLt (pre : Devm)
    (cost : Nat → Nat → Nat → Devm → Nat)
    (next : Nat → Nat → Nat → Devm → Devm)
    (hpos : ∀ x y z d, 0 < cost x y z d) {post : Devm}
    (hnext : ∀ x y z d, (next x y z d).gasLeft = d.gasLeft)
    (h : (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d' ← chargeGas (cost x y z d) d
      .ok (next x y z d')) = .ok post) :
    post.gasLeft < pre.gasLeft := by
  obtain ⟨⟨x, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨y, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨z, d3⟩, h3, h⟩ := Except.bind_eq_ok h
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq] at h5
  have e1 := Devm.popToNat_gasLeft h1
  have e2 := Devm.popToNat_gasLeft h2
  have e3 := Devm.popToNat_gasLeft h3
  have e4 := chargeGas_gasLeft h4
  have ep := hpos x y z d3
  rw [← h5, hnext]
  omega

theorem popNatPopChargePure_gasLt (pre : Devm)
    (cost : Nat → B256 → Devm → Nat)
    (next : Nat → B256 → Devm → Devm)
    (hpos : ∀ x y d, 0 < cost x y d) {post : Devm}
    (hnext : ∀ x y d, (next x y d).gasLeft = d.gasLeft)
    (h : (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.pop
      let d' ← chargeGas (cost x y d) d
      .ok (next x y d')) = .ok post) :
    post.gasLeft < pre.gasLeft := by
  obtain ⟨⟨x, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨y, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq] at h4
  have e1 := Devm.popToNat_gasLeft h1
  have e2 := Devm.pop_gasLeft h2
  have e3 := chargeGas_gasLeft h3
  have ep := hpos x y d2
  rw [← h4, hnext]
  omega

theorem Rinst.balance_runCore_gasLt {pc : Nat} {devm devm' : Devm}
    {sevm : Sevm}
    (h : Rinst.runCore pc devm sevm .balance = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  simp only [Rinst.runCore] at h
  obtain ⟨u, view', hcore, hout⟩ := liftMachMetaWorldExecution_ok h
  unfold Rinst.balanceCore at hcore
  cases hp : devm.mach.pop with
  | error e => simp [hp] at hcore
  | ok p =>
    rcases p with ⟨x, mach1⟩
    simp only [hp] at hcore
    by_cases hw : x.toAdr ∈ devm.meta.accessedAddresses
    · simp only [hw, if_pos] at hcore
      cases hc : Mach.chargeGas gasWarmAccess mach1 with
      | error e => simp [hc] at hcore
      | ok p =>
        rcases p with ⟨u2, mach2⟩
        simp only [hc] at hcore
        cases hpush : Mach.push (devm.world.state.get x.toAdr).bal mach2 with
        | error e => simp [hpush] at hcore
        | ok p =>
          rcases p with ⟨u3, mach3⟩
          simp only [hpush, Except.ok.injEq, Prod.mk.injEq] at hcore
          have ep := Mach.pop_gasLeft hp
          have ec := Mach.chargeGas_gasLeft hc
          have eq := Mach.push_gasLeft hpush
          have hv : view'.1.gasLeft = mach3.gasLeft :=
            congrArg Mach.gasLeft (congrArg Prod.fst hcore.2).symm
          rw [hout, hv]
          change mach3.gasLeft < devm.mach.gasLeft
          unfold gasWarmAccess at ec
          omega
    · simp only [hw, if_false] at hcore
      cases hc : Mach.chargeGas gasColdAccountAccess mach1 with
      | error e => simp [hc] at hcore
      | ok p =>
        rcases p with ⟨u2, mach2⟩
        simp only [hc] at hcore
        cases hpush : Mach.push (devm.world.state.get x.toAdr).bal mach2 with
        | error e => simp [hpush] at hcore
        | ok p =>
          rcases p with ⟨u3, mach3⟩
          simp only [hpush, Except.ok.injEq, Prod.mk.injEq] at hcore
          have ep := Mach.pop_gasLeft hp
          have ec := Mach.chargeGas_gasLeft hc
          have eq := Mach.push_gasLeft hpush
          have hv : view'.1.gasLeft = mach3.gasLeft :=
            congrArg Mach.gasLeft (congrArg Prod.fst hcore.2).symm
          rw [hout, hv]
          change mach3.gasLeft < devm.mach.gasLeft
          unfold gasColdAccountAccess at ec
          omega

theorem popAdrAccessChargePush_gasLt (pre : Devm)
    (value : Adr → Devm → B256) {post : Devm}
    (h : (do
      let ⟨adr, d⟩ ← pre.popToAdr
      let d' ←
        if adr ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gasColdAccountAccess (addAccessedAddress d adr)
      d'.push (value adr d')) = .ok post) :
    post.gasLeft < pre.gasLeft := by
  obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  have e1 := Devm.popToAdr_gasLeft h1
  dsimp only at h e1
  split at h
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasLeft h2
    have e3 := Devm.push_gasLeft h3
    unfold gasWarmAccess at e2
    omega
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasLeft h2
    rw [addAccessedAddress_gasLeft] at e2
    have e3 := Devm.push_gasLeft h3
    unfold gasColdAccountAccess at e2
    omega

theorem Rinst.runCore_gasLt (pc : Nat) (devm : Devm) (sevm : Sevm)
    (r : Rinst) {devm' : Devm}
    (h : Rinst.runCore pc devm sevm r = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  cases r <;> simp only [Rinst.runCore] at h
  all_goals first
    | exact applyBinary_gasLt (by decide) h
    | exact applyUnary_gasLt (by decide) h
    | exact applyTernary_gasLt (by decide) h
    | exact pushItem_gasLt (by decide) h
    | skip
  case exp =>
    exact pop2ChargePush_gasLt devm
      (fun _ exponent _ => gExp + gExpbyte * exponent.bytecount)
      (fun base exponent _ => B256.bexp base exponent)
      (by intros; unfold gExp; omega) h
  case clz =>
    split at h
    · exact applyUnary_gasLt (by decide) h
    · simp at h
  case kec =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasLeft h1
    have e2 := Devm.popToNat_gasLeft h2
    have e3 := chargeGas_gasLeft h3
    have e4 := Devm.push_gasLeft h4
    dsimp only at e1 e2 e3 e4
    rw [Devm.memRead_gasLeft] at e4
    unfold gKeccak256 at e3
    omega
  case balance =>
    apply Rinst.balance_runCore_gasLt (pc := pc) (sevm := sevm)
    simpa only [Rinst.runCore] using h
  case calldataload =>
    exact popChargePush_gasLt devm
      (fun _ _ => gVerylow)
      (fun start _ => Bytes.toB256 <| sevm.data.sliceD start.toNat 32 0)
      (by intros; decide) h
  case calldatacopy =>
    exact popNat3ChargePure_gasLt devm
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart dataStart size d =>
        d.memWrite memoryStart (sevm.data.sliceD dataStart size 0))
      (by intros; unfold gVerylow; omega)
      (by intros; simp only [Devm.memWrite_gasLeft]) h
  case retdatacopy =>
    obtain ⟨⟨memoryStart, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨returnStart, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d3⟩, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasLeft h1
    have e2 := Devm.popToNat_gasLeft h2
    have e3 := Devm.popToNat_gasLeft h3
    have e4 := chargeGas_gasLeft h4
    dsimp only at h e1 e2 e3 e4
    split at h
    · nomatch h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.memWrite_gasLeft]
      unfold gVerylow at e4
      omega
  case extcodecopy =>
    obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨memoryStart, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨codeStart, d3⟩, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d4⟩, h4, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToAdr_gasLeft h1
    have e2 := Devm.popToNat_gasLeft h2
    have e3 := Devm.popToNat_gasLeft h3
    have e4 := Devm.popToNat_gasLeft h4
    dsimp only at h e1 e2 e3 e4
    split at h
    · obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h6
      have e5 := chargeGas_gasLeft h5
      rw [← h6, Devm.memWrite_gasLeft]
      unfold gasWarmAccess at e5
      omega
    · obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h6
      have e5 := chargeGas_gasLeft h5
      rw [addAccessedAddress_gasLeft] at e5
      rw [← h6, Devm.memWrite_gasLeft]
      unfold gasColdAccountAccess at e5
      omega
  case extcodesize =>
    apply Rinst.runCore_extcodesize_gasLt (pc := pc) (sevm := sevm)
    simpa only [Rinst.runCore] using h
  case extcodehash =>
    exact popAdrAccessChargePush_gasLt devm
      (fun adr d =>
        let account := d.getAcct adr
        if account.Empty then 0
        else ByteArray.keccak 0 account.code.size account.code) h
  case blockhash =>
    exact popChargePush_gasLt devm
      (fun _ _ => gBlockhash)
      (fun blockNumberWord _ =>
        if sevm.benvStat.number ≤ blockNumberWord.toNat ∨
            blockNumberWord.toNat + 256 < sevm.benvStat.number then 0
        else sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length -
            (sevm.benvStat.number - blockNumberWord.toNat)) 0)
      (by intros; unfold gBlockhash; omega) h
  case blobhash =>
    exact popChargePush_gasLt devm
      (fun _ _ => gHashopcode)
      (fun index _ => sevm.tenvStat.blobVersionedHashes.getD index.toNat 0)
      (by intros; unfold gHashopcode; omega) h
  case pop =>
    cases hp : devm.pop with
    | error e =>
      change Except.bind (Except.map Prod.snd devm.pop) (chargeGas gBase) =
        .ok devm' at h
      simp only [hp, Except.map, Except.bind] at h
      nomatch h
    | ok p =>
      have e1 := Devm.pop_gasLeft hp
      change Except.bind (Except.map Prod.snd devm.pop) (chargeGas gBase) =
        .ok devm' at h
      simp only [hp, Except.map, Except.bind] at h
      have e2 := chargeGas_gasLeft h
      unfold gBase at e2
      omega
  case mload =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasLeft h1
    have e2 := chargeGas_gasLeft h2
    have e3 := Devm.push_gasLeft h3
    dsimp only at e1 e2 e3
    rw [Devm.memRead_gasLeft] at e3
    unfold gVerylow at e2
    omega
  case mstore =>
    apply Rinst.runCore_mstore_gasLt (pc := pc) (sevm := sevm)
    simpa only [Rinst.runCore] using h
  case mstore8 =>
    exact popNatPopChargePure_gasLt devm
      (fun start _ d => gVerylow + d.extCost [(start, 1)])
      (fun start value d => d.memWrite start [value.2.2.toUInt8])
      (by intros; unfold gVerylow; omega)
      (by intros; simp only [Devm.memWrite_gasLeft]) h
  case mcopy =>
    exact popNat3ChargePure_gasLt devm
      (fun destinationStart sourceStart size d =>
        gVerylow + gasCopy * ceilDiv size 32 +
          d.extCost [(sourceStart, size), (destinationStart, size)])
      (fun destinationStart sourceStart size d =>
        (d.memRead sourceStart size).2.memWrite destinationStart
          (d.memRead sourceStart size).1)
      (by intros; unfold gVerylow; omega)
      (by intros; simp only [Devm.memWrite_gasLeft, Devm.memRead_gasLeft]) h
  case sstore =>
    obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, hStipend, h⟩ := Except.bind_eq_ok h
    have _hStipend := Except.assert_eq_ok hStipend
    obtain ⟨gasPair, hPair, h⟩ := Except.bind_eq_ok h
    obtain ⟨cost, hCost, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, hRefund, h⟩ := Except.bind_eq_ok h
    obtain ⟨d4, hCharge, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hDynamic, hFinal⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at hPair hCost hRefund hFinal
    have e1 := Devm.pop_gasLeft h1
    have e2 := Devm.pop_gasLeft h2
    have e3 := chargeGas_gasLeft hCharge
    have hPairGas : gasPair.1.gasLeft = d2.gasLeft := by
      rw [← hPair]
      split <;> simp only [addAccessedStorageKey_gasLeft]
    have hRefundGas : d3.gasLeft = d2.gasLeft := by
      rw [← hRefund, Devm.withRefundCounter_gasLeft, hPairGas]
    have hCostPos : 0 < cost := by
      rw [← hCost]
      split
      · split
        · unfold gasStorageSet
          omega
        · unfold gasStorageUpdate gasColdSload
          omega
      · unfold gasWarmAccess
        omega
    dsimp only at e1 e2 hFinal
    rw [← hFinal, Devm.setStorVal_gasLeft]
    omega
  case sload =>
    obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasLeft h1
    dsimp only at h e1
    split at h
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasLeft h2
      have e3 := Devm.push_gasLeft h3
      unfold gasWarmAccess at e2
      omega
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasLeft h2
      rw [addAccessedStorageKey_gasLeft] at e2
      have e3 := Devm.push_gasLeft h3
      unfold gasColdSload at e2
      omega
  case tload =>
    obtain ⟨⟨key, d1⟩, h1, h2⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasLeft h1
    have e2 := pushItem_gasLt (by unfold gasWarmAccess; omega) h2
    dsimp only at e1 e2
    omega
  case tstore =>
    obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hassert, h4⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h4
    have e1 := Devm.pop_gasLeft h1
    have e2 := Devm.pop_gasLeft h2
    have e3 := chargeGas_gasLeft h3
    dsimp only at e1 e2 e3
    rw [← h4, Devm.setTransVal_gasLeft]
    unfold gasWarmAccess at e3
    omega
  case gas =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasLeft h1
    have e2 := Devm.push_gasLeft h2
    unfold gBase at e1
    omega
  case dup i =>
    obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasLeft h1
    split at h
    · nomatch h
    · have e2 := Devm.push_gasLeft h
      unfold gVerylow at e1
      omega
  case swap i =>
    obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasLeft h1
    split at h
    · nomatch h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.withStack_gasLeft]
      unfold gVerylow at e1
      omega
  case log topicCount =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨topics, d3⟩, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hassert, h5⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h5
    have e1 := Devm.popToNat_gasLeft h1
    have e2 := Devm.popToNat_gasLeft h2
    have e3 := Devm.popN_gasLeft h3
    have e4 := chargeGas_gasLeft h4
    dsimp only at e1 e2 e3 e4 h5
    rw [← h5, Devm.addLog_gasLeft, Devm.memRead_gasLeft]
    unfold gLog at e4
    omega
  case codecopy =>
    exact popNat3ChargePure_gasLt devm
      (fun memoryStart _ size d =>
        gVerylow + gasCopy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart codeStart size d =>
        d.memWrite memoryStart
          (sevm.code.sliceD codeStart size (Linst.toUInt8 .stop)))
      (by intros; unfold gVerylow; omega)
      (by intros; simp only [Devm.memWrite_gasLeft]) h

theorem Jinst.runCore_gasLt (pc : Nat) (devm : Devm) (sevm : Sevm)
    (j : Jinst) {pc' : Nat} {devm' : Devm}
    (h : Jinst.runCore pc devm sevm j = .ok (pc', devm')) :
    devm'.gasLeft < devm.gasLeft := by
  cases j
  case jumpdest =>
    exact Jinst.runCore_jumpdest_gasLt h
  case jump =>
    simp only [Jinst.runCore] at h
    obtain ⟨⟨destination, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hassert, h3⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    have e1 := Devm.pop_gasLeft h1
    have e2 := chargeGas_gasLeft h2
    dsimp only at e1 e2
    rw [← h3.2]
    unfold gMid at e2
    omega
  case jumpi =>
    simp only [Jinst.runCore] at h
    obtain ⟨⟨destination, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨condition, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasLeft h1
    have e2 := Devm.pop_gasLeft h2
    have e3 := chargeGas_gasLeft h3
    dsimp only at h e1 e2 e3
    split at h
    · obtain ⟨nextPc, _hpc, h4⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h4
      rw [← h4.2]
      unfold gHigh at e3
      omega
    · obtain ⟨_, _hassert, h⟩ := Except.bind_eq_ok h
      obtain ⟨nextPc, _hpc, h4⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h4
      rw [← h4.2]
      unfold gHigh at e3
      omega

theorem except64th_le (n : Nat) : except64th n ≤ n := by
  unfold except64th
  omega

@[simp] theorem processCreateMessage.msg_gas (msg : Msg) :
    (processCreateMessage.msg msg).gas = msg.gas := rfl

theorem genericCreate.step_gasDecreasing
    (sevm : Sevm) (devm : Devm) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) {n : Nat}
    (hn : devm.gasLeft < n) :
    XStep.GasDecreasing n
      (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨_, _hsize, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  obtain ⟨_, _hdynamic, hstep⟩ := Except.bind_eq_ok hstep
  split at hstep
  · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasLeft hpush, Devm.withGasLeft_gasLeft,
      Devm.withReturnData_gasLeft, Devm.withGasLeft_gasLeft]
    have hle := except64th_le devm.gasLeft
    omega
  · split at hstep
    · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      intro devm' hd
      simp only [Except.ok.injEq] at hd
      rw [← hd, Devm.push_gasLeft hpush, addAccessedAddress_gasLeft,
        Devm.incrNonce_gasLeft, Devm.withReturnData_gasLeft,
        Devm.withGasLeft_gasLeft]
      omega
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      show (Frame.ofCreate _).inner.gas + Resume.parentGas _ < n
      simp only [Frame.ofCreate, processCreateMessage.msg_gas, createMsg,
        Resume.parentGas, addAccessedAddress_gasLeft,
        Devm.incrNonce_gasLeft, Devm.withReturnData_gasLeft,
        Devm.withGasLeft_gasLeft]
      have hle := except64th_le devm.gasLeft
      omega

theorem Xinst.step_create_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (Xinst.step sevm devm .create).GasDecreasing devm.gasLeft := by
  simp only [Xinst.step]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨d4, h4, hstep⟩ := Except.bind_eq_ok hstep
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
  rw [← hstep]
  apply genericCreate.step_gasDecreasing
  have e1 := Devm.pop_gasLeft h1
  have e2 := Devm.popToNat_gasLeft h2
  have e3 := Devm.popToNat_gasLeft h3
  have e4 := chargeGas_gasLeft h4
  dsimp only at e1 e2 e3 e4
  rw [Devm.memExtends_gasLeft]
  unfold gasCreate at e4
  omega

theorem Xinst.step_create2_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (Xinst.step sevm devm .create2).GasDecreasing devm.gasLeft := by
  simp only [Xinst.step]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨salt, d4⟩, h4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨d5, h5, hstep⟩ := Except.bind_eq_ok hstep
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
  rw [← hstep]
  apply genericCreate.step_gasDecreasing
  have e1 := Devm.pop_gasLeft h1
  have e2 := Devm.popToNat_gasLeft h2
  have e3 := Devm.popToNat_gasLeft h3
  have e4 := Devm.pop_gasLeft h4
  have e5 := chargeGas_gasLeft h5
  dsimp only at e1 e2 e3 e4 e5
  rw [Devm.memExtends_gasLeft]
  unfold gasCreate at e5
  omega

theorem Xinst.step_callcode_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (Xinst.step sevm devm .callcode).GasDecreasing devm.gasLeft := by
  simp only [Xinst.step]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  have e1 := Devm.pop_gasLeft p1
  have e2 := Devm.popToAdr_gasLeft p2
  have e3 := Devm.pop_gasLeft p3
  have e4 := Devm.popToNat_gasLeft p4
  have e5 := Devm.popToNat_gasLeft p5
  have e6 := Devm.popToNat_gasLeft p6
  have e7 := Devm.popToNat_gasLeft p7
  dsimp only at e2 e3 e4 e5 e6 e7
  have eA :
      (accessDelegation (addAccessedAddress d7 codeAddress) codeAddress).2.2.2.2.gasLeft
        = devm.gasLeft := by
    rw [accessDelegation_gasLeft, addAccessedAddress_gasLeft]
    omega
  have hstip :
      (if value.toNat = 0 then 0 else gCallStipend) <
        ((accessCost codeAddress d7.accessedAddresses +
            (accessDelegation (addAccessedAddress d7 codeAddress)
              codeAddress).2.2.2.1) +
          if value = 0 then 0 else gasCallValue) +
        d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    have hac := gasWarmAccess_le_access_cost codeAddress d7.accessedAddresses
    by_cases hv : value = 0
    · have : value.toNat = 0 := by rw [hv]; rfl
      rw [if_pos this]
      unfold gasWarmAccess at hac
      omega
    · rw [if_neg hv]
      unfold gCallStipend gasCallValue at *
      split <;> omega
  obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  split at hstep
  · obtain ⟨d9, ppush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.withReturnData_gasLeft, Devm.withGasLeft_gasLeft,
      Devm.push_gasLeft ppush, Devm.memExtends_gasLeft]
    exact key
  · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCall.step_gasDecreasing
    rw [Devm.memExtends_gasLeft]
    exact key

theorem Xinst.step_delcall_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (Xinst.step sevm devm .delcall).GasDecreasing devm.gasLeft := by
  simp only [Xinst.step]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  have e1 := Devm.pop_gasLeft p1
  have e2 := Devm.popToAdr_gasLeft p2
  have e3 := Devm.popToNat_gasLeft p3
  have e4 := Devm.popToNat_gasLeft p4
  have e5 := Devm.popToNat_gasLeft p5
  have e6 := Devm.popToNat_gasLeft p6
  dsimp only at e2 e3 e4 e5 e6
  have eA :
      (accessDelegation (addAccessedAddress d6 codeAddress) codeAddress).2.2.2.2.gasLeft
        = devm.gasLeft := by
    rw [accessDelegation_gasLeft, addAccessedAddress_gasLeft]
    omega
  have hstip :
      (if (0 : Nat) = 0 then 0 else gCallStipend) <
        (accessCost codeAddress d6.accessedAddresses +
          (accessDelegation (addAccessedAddress d6 codeAddress)
            codeAddress).2.2.2.1) +
        d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    simp only [if_pos]
    have hac := access_cost_pos codeAddress d6.accessedAddresses
    omega
  obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
  rw [← hstep]
  apply genericCall.step_gasDecreasing
  rw [Devm.memExtends_gasLeft]
  exact key

theorem Xinst.step_statcall_gasDecreasing (sevm : Sevm) (devm : Devm) :
    (Xinst.step sevm devm .statcall).GasDecreasing devm.gasLeft := by
  simp only [Xinst.step]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨target, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  have e1 := Devm.pop_gasLeft p1
  have e2 := Devm.popToAdr_gasLeft p2
  have e3 := Devm.popToNat_gasLeft p3
  have e4 := Devm.popToNat_gasLeft p4
  have e5 := Devm.popToNat_gasLeft p5
  have e6 := Devm.popToNat_gasLeft p6
  dsimp only at e2 e3 e4 e5 e6
  have eA :
      (accessDelegation (addAccessedAddress d6 target) target).2.2.2.2.gasLeft
        = devm.gasLeft := by
    rw [accessDelegation_gasLeft, addAccessedAddress_gasLeft]
    omega
  have hstip :
      (if (0 : Nat) = 0 then 0 else gCallStipend) <
        (accessCost target d6.accessedAddresses +
          (accessDelegation (addAccessedAddress d6 target) target).2.2.2.1) +
        d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    simp only [if_pos]
    have hac := access_cost_pos target d6.accessedAddresses
    omega
  obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
  rw [← hstep]
  apply genericCall.step_gasDecreasing
  rw [Devm.memExtends_gasLeft]
  exact key

theorem Xinst.step_gasDecreasing (sevm : Sevm) (devm : Devm) (x : Xinst) :
    (Xinst.step sevm devm x).GasDecreasing devm.gasLeft := by
  cases x
  case create => exact Xinst.step_create_gasDecreasing sevm devm
  case create2 => exact Xinst.step_create2_gasDecreasing sevm devm
  case call => exact Xinst.step_call_gasDecreasing sevm devm
  case callcode => exact Xinst.step_callcode_gasDecreasing sevm devm
  case delcall => exact Xinst.step_delcall_gasDecreasing sevm devm
  case statcall => exact Xinst.step_statcall_gasDecreasing sevm devm

theorem executePrecomp_gasLe (evm : Evm) (adr : Adr) :
    (executePrecomp evm adr).gasLeft ≤ evm.dyna.gasLeft := by
  unfold executePrecomp applyPrecompResult
  cases precompileRun evm adr with
  | error msg cost =>
    simp only [Execution.gasLeft_error, Devm.withGasLeft_gasLeft]
    omega
  | ok cost output =>
    simp only [Execution.gasLeft_ok]
    simp only [Devm.withOutput, Devm.setMeta_gasLeft,
      Devm.withGasLeft_gasLeft]
    omega

theorem executeCode.handleError_ok_gasLe {raw : Execution} {devm : Devm}
    (h : executeCode.handleError raw = .ok devm) :
    devm.gasLeft ≤ raw.gasLeft := by
  cases raw with
  | ok d =>
    simp only [executeCode.handleError, Except.ok.injEq] at h
    rw [← h]
    simp only [Execution.gasLeft_ok]
    omega
  | error e =>
    simp only [executeCode.handleError] at h
    split at h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.setMeta_gasLeft, Devm.withGasLeft_gasLeft]
      omega
    · split at h
      · simp only [Except.ok.injEq] at h
        rw [← h, Devm.withError_gasLeft]
        simp only [Execution.gasLeft_error]
        omega
      · nomatch h

@[simp] theorem chargeGas_result_gasLe (cost : Nat) (devm : Devm) :
    (chargeGas cost devm).gasLeft ≤ devm.gasLeft := by
  rw [chargeGas_def]
  by_cases hc : cost ≤ devm.gasLeft
  · simp only [safeSub, hc, if_pos, Execution.gasLeft_ok,
      Devm.setMach_gasLeft]
    omega
  · simp [safeSub, hc, Execution.gasLeft]

/-! ## Gas non-increase

The corpus above constrains successful results only, but the driver hands a
child's *whole* result back to its parent. `executeCode.handleError` turns a
`"Revert"` error into a *successful* frame result carrying the reverting frame's
leftover gas, and `Resume.run` adds that back to the parent, so driver
monotonicity has to bound the error branch too. (The other two error shapes are
free: an exceptional halt is rewritten to zero gas, and any remaining tag stays
an `.error`, which `Resume.run` cannot turn into a resumed parent.)

The device is one compositional bind lemma. `resultGas proj e` reads the gas out
of whichever branch `e` takes, and the bind lemmas peel a single `bind`, leaving
the tail as an *unconditional* obligation measured against the intermediate
`Devm`. Walks therefore chain without threading equations through hypotheses,
which is what keeps this second corpus to a fraction of the size of the first.
-/

/-- The gas reported by a `Devm`-threading step, in whichever branch it takes.
`proj` reads the `Devm` out of a successful payload. -/
def resultGas {α : Type} (proj : α → Devm) : Except (String × Devm) α → Nat
  | .error p => p.2.gasLeft
  | .ok a => (proj a).gasLeft

@[simp] theorem resultGas_error {α : Type} (proj : α → Devm) (p : String × Devm) :
    resultGas proj (.error p) = p.2.gasLeft := rfl

@[simp] theorem resultGas_ok {α : Type} (proj : α → Devm) (a : α) :
    resultGas proj (.ok a) = (proj a).gasLeft := rfl

@[simp] theorem resultGas_id (ex : Execution) : resultGas id ex = ex.gasLeft := by
  cases ex <;> rfl

/-- Peel one `bind` whose payload is a `_ × Devm` pair. The tail obligation is
measured against the intermediate `Devm`, so it is this lemma again one level
down. -/
theorem gasLe_bind_snd {α : Type} {n : Nat}
    {e : Except (String × Devm) (α × Devm)} {f : α × Devm → Execution}
    (he : resultGas Prod.snd e ≤ n)
    (hf : ∀ a : α × Devm, Execution.gasLeft (f a) ≤ a.2.gasLeft) :
    Execution.gasLeft (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

/-- Peel one `bind` whose payload is a bare `Devm`. -/
theorem gasLe_bind_id {n : Nat} {e : Execution} {f : Devm → Execution}
    (he : e.gasLeft ≤ n) (hf : ∀ d : Devm, Execution.gasLeft (f d) ≤ d.gasLeft) :
    Execution.gasLeft (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok d => exact Nat.le_trans (hf d) he

/-- Peel a `bind` whose payload carries no `Devm` at all — an `Except.assert`
guard, or an `.ok` of a pure value. The current `Devm` simply survives it. -/
theorem gasLe_bind_const {α : Type} {n : Nat} {devm : Devm}
    {e : Except (String × Devm) α} {f : α → Execution}
    (he : resultGas (fun _ => devm) e ≤ n)
    (hf : ∀ a : α, Execution.gasLeft (f a) ≤ devm.gasLeft) :
    Execution.gasLeft (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

@[simp] theorem resultGas_assert {p : Prop} [Decidable p] {devm : Devm}
    (msg : String) :
    resultGas (fun _ => devm) (Except.assert p ⟨msg, devm⟩) = devm.gasLeft := by
  unfold Except.assert
  split <;> rfl

/-! ### The `Mach` layer of the non-increase corpus -/

/-- The `Mach`-level analogue of `resultGas`, for the primitives defined by a
footprint lift. -/
def machResultGas {α : Type} : Footprint.Outcome Mach α → Nat
  | .error p => p.2.gasLeft
  | .ok p => p.2.gasLeft

theorem liftMach_resultGas {α : Type} (core : Mach → Footprint.Outcome Mach α)
    (devm : Devm) :
    resultGas Prod.snd (liftMach core devm) = machResultGas (core devm.mach) := by
  unfold liftMach Footprint.liftOutcome
  cases core devm.mach <;> rfl

theorem liftMachExecution_resultGas (core : Mach → Footprint.Outcome Mach Unit)
    (devm : Devm) :
    (liftMachExecution core devm).gasLeft = machResultGas (core devm.mach) := by
  unfold liftMachExecution Footprint.toExecution liftMach Footprint.liftOutcome
  cases core devm.mach <;> rfl

namespace Mach

@[simp] theorem pop_machResultGas (mach : Mach) :
    machResultGas mach.pop = mach.gasLeft := by
  rcases mach with ⟨stack, memory, gasLeft⟩
  cases stack <;> rfl

@[simp] theorem popToNat_machResultGas (mach : Mach) :
    machResultGas mach.popToNat = mach.gasLeft := by
  rcases mach with ⟨stack, memory, gasLeft⟩
  cases stack <;> rfl

@[simp] theorem popToAdr_machResultGas (mach : Mach) :
    machResultGas mach.popToAdr = mach.gasLeft := by
  rcases mach with ⟨stack, memory, gasLeft⟩
  cases stack <;> rfl

@[simp] theorem popN_machResultGas (n : Nat) (mach : Mach) :
    machResultGas (mach.popN n) = mach.gasLeft := by
  induction n generalizing mach with
  | zero => rfl
  | succ n ih =>
    rcases mach with ⟨stack, memory, gasLeft⟩
    cases stack with
    | nil => rfl
    | cons x xs =>
      have ih' := ih ⟨xs, memory, gasLeft⟩
      rcases hp : Mach.popN ⟨xs, memory, gasLeft⟩ n with ⟨err, m⟩ | ⟨ys, m⟩ <;>
        rw [hp] at ih' <;>
        simpa only [Mach.popN, Mach.pop, hp, machResultGas] using ih'

@[simp] theorem push_machResultGas (x : B256) (mach : Mach) :
    machResultGas (Mach.push x mach) = mach.gasLeft := by
  unfold Mach.push
  split <;> rfl

@[simp] theorem chargeGas_machResultGas (c : Nat) (mach : Mach) :
    machResultGas (Mach.chargeGas c mach) ≤ mach.gasLeft := by
  unfold Mach.chargeGas safeSub
  by_cases hc : c ≤ mach.gasLeft
  · simp only [if_pos hc, machResultGas]
    omega
  · simp only [if_neg hc, machResultGas]
    omega

@[simp] theorem pushItem_machResultGas (x : B256) (c : Nat) (mach : Mach) :
    machResultGas (Mach.pushItem x c mach) ≤ mach.gasLeft := by
  unfold Mach.pushItem
  have hc := Mach.chargeGas_machResultGas c mach
  rcases hg : Mach.chargeGas c mach with ⟨err, m⟩ | ⟨u, m⟩ <;> rw [hg] at hc <;>
    simp only [machResultGas] at hc
  · exact hc
  · exact Nat.le_trans (Nat.le_of_eq (push_machResultGas x m)) hc

@[simp] theorem applyUnary_machResultGas (f : B256 → B256) (c : Nat) (mach : Mach) :
    machResultGas (Mach.applyUnary f c mach) ≤ mach.gasLeft := by
  unfold Mach.applyUnary
  have hp := Mach.pop_machResultGas mach
  rcases hg : mach.pop with ⟨err, m⟩ | ⟨x, m⟩ <;> rw [hg] at hp <;>
    simp only [machResultGas] at hp ⊢
  · exact Nat.le_of_eq hp
  · exact Nat.le_trans (pushItem_machResultGas _ _ m) (Nat.le_of_eq hp)

@[simp] theorem applyBinary_machResultGas (f : B256 → B256 → B256) (c : Nat)
    (mach : Mach) :
    machResultGas (Mach.applyBinary f c mach) ≤ mach.gasLeft := by
  unfold Mach.applyBinary
  have hp := Mach.pop_machResultGas mach
  rcases hg : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> rw [hg] at hp <;>
    simp only [machResultGas] at hp ⊢
  · exact Nat.le_of_eq hp
  · have hq := Mach.pop_machResultGas m1
    rcases hg1 : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> rw [hg1] at hq <;>
      simp only [machResultGas] at hq ⊢
    · omega
    · exact Nat.le_trans (pushItem_machResultGas _ _ m2) (by omega)

@[simp] theorem applyTernary_machResultGas (f : B256 → B256 → B256 → B256) (c : Nat)
    (mach : Mach) :
    machResultGas (Mach.applyTernary f c mach) ≤ mach.gasLeft := by
  unfold Mach.applyTernary
  have hp := Mach.pop_machResultGas mach
  rcases hg : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> rw [hg] at hp <;>
    simp only [machResultGas] at hp ⊢
  · exact Nat.le_of_eq hp
  · have hq := Mach.pop_machResultGas m1
    rcases hg1 : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> rw [hg1] at hq <;>
      simp only [machResultGas] at hq ⊢
    · omega
    · have hr := Mach.pop_machResultGas m2
      rcases hg2 : m2.pop with ⟨err, m⟩ | ⟨z, m3⟩ <;> rw [hg2] at hr <;>
        simp only [machResultGas] at hr ⊢
      · omega
      · exact Nat.le_trans (pushItem_machResultGas _ _ m3) (by omega)

end Mach

/-! ### The `Devm` layer of the non-increase corpus -/

@[simp] theorem Devm.pop_resultGas (devm : Devm) :
    resultGas Prod.snd devm.pop = devm.gasLeft := by
  rw [Devm.pop, liftMach_resultGas, Mach.pop_machResultGas]
  rfl

@[simp] theorem Devm.popToNat_resultGas (devm : Devm) :
    resultGas Prod.snd devm.popToNat = devm.gasLeft := by
  rw [Devm.popToNat, liftMach_resultGas, Mach.popToNat_machResultGas]
  rfl

@[simp] theorem Devm.popToAdr_resultGas (devm : Devm) :
    resultGas Prod.snd devm.popToAdr = devm.gasLeft := by
  rw [Devm.popToAdr, liftMach_resultGas, Mach.popToAdr_machResultGas]
  rfl

@[simp] theorem Devm.popN_resultGas (devm : Devm) (n : Nat) :
    resultGas Prod.snd (devm.popN n) = devm.gasLeft := by
  rw [Devm.popN, liftMach_resultGas, Mach.popN_machResultGas]
  rfl

@[simp] theorem Devm.push_gasLe (x : B256) (devm : Devm) :
    (devm.push x).gasLeft = devm.gasLeft := by
  rw [Devm.push, liftMachExecution_resultGas, Mach.push_machResultGas]
  rfl

@[simp] theorem pushItem_gasLe (x : B256) (c : Nat) (devm : Devm) :
    (pushItem x c devm).gasLeft ≤ devm.gasLeft := by
  rw [pushItem, liftMachExecution_resultGas]
  exact Mach.pushItem_machResultGas x c devm.mach

@[simp] theorem applyUnary_gasLe (f : B256 → B256) (c : Nat) (devm : Devm) :
    (applyUnary f c devm).gasLeft ≤ devm.gasLeft := by
  rw [applyUnary, liftMachExecution_resultGas]
  exact Mach.applyUnary_machResultGas f c devm.mach

@[simp] theorem applyBinary_gasLe (f : B256 → B256 → B256) (c : Nat) (devm : Devm) :
    (applyBinary f c devm).gasLeft ≤ devm.gasLeft := by
  rw [applyBinary, liftMachExecution_resultGas]
  exact Mach.applyBinary_machResultGas f c devm.mach

@[simp] theorem applyTernary_gasLe (f : B256 → B256 → B256 → B256) (c : Nat)
    (devm : Devm) :
    (applyTernary f c devm).gasLeft ≤ devm.gasLeft := by
  rw [applyTernary, liftMachExecution_resultGas]
  exact Mach.applyTernary_machResultGas f c devm.mach

@[simp] theorem Devm.pop_map_snd_gasLe (devm : Devm) :
    Execution.gasLeft (devm.pop <&> Prod.snd) = devm.gasLeft := by
  have h := Devm.pop_resultGas devm
  rcases hp : devm.pop with ⟨err, d⟩ | ⟨x, d⟩ <;> rw [hp] at h <;>
    simp only [resultGas_error, resultGas_ok] at h
  · exact h
  · exact h

/-- The general form of the peeling lemma, for the bodies whose payload carries
its `Devm` somewhere other than the second component. -/
theorem gasLe_bind {α : Type} {n : Nat} {proj : α → Devm}
    {e : Except (String × Devm) α} {f : α → Execution}
    (he : resultGas proj e ≤ n)
    (hf : ∀ a : α, Execution.gasLeft (f a) ≤ (proj a).gasLeft) :
    Execution.gasLeft (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

/-- The fully general peeling lemma, for bodies that do not end in a bare
`Devm` — `Jinst.runCore` returns a `Nat × Devm` jump target. -/
theorem gasLe_bind_gen {α β : Type} {n : Nat} {proj : α → Devm} {proj' : β → Devm}
    {e : Except (String × Devm) α} {f : α → Except (String × Devm) β}
    (he : resultGas proj e ≤ n)
    (hf : ∀ a : α, resultGas proj' (f a) ≤ (proj a).gasLeft) :
    resultGas proj' (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

@[simp] theorem assertDynamic_resultGas (sevm : Sevm) (devm : Devm) :
    resultGas (fun _ => devm) (assertDynamic sevm devm) = devm.gasLeft :=
  resultGas_assert _

/-- The `Mach × Meta` analogue of `machResultGas`, for `Rinst.balanceCore`. -/
def machMetaResultGas {α : Type} : Footprint.Outcome (Mach × Meta) α → Nat
  | .error p => p.2.1.gasLeft
  | .ok p => p.2.1.gasLeft

theorem liftMachMetaExecution_resultGas
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit) (devm : Devm) :
    (liftMachMetaExecution core devm).gasLeft =
      machMetaResultGas (core devm.mach devm.meta) := by
  rcases h : core devm.mach devm.meta with ⟨err, view⟩ | ⟨u, view⟩ <;>
    simp only [liftMachMetaExecution, Footprint.toExecution, liftMachMeta,
      Footprint.liftOutcome, h, machMetaResultGas] <;> rfl

theorem Rinst.balanceCore_machMetaResultGas (world : World) (mach : Mach) (view : Meta) :
    machMetaResultGas (Rinst.balanceCore world mach view) ≤ mach.gasLeft := by
  have hp := Mach.pop_machResultGas mach
  have hc : ∀ (c : Nat) (m : Mach), machResultGas (Mach.chargeGas c m) ≤ m.gasLeft :=
    Mach.chargeGas_machResultGas
  have hs : ∀ (x : B256) (m : Mach), machResultGas (Mach.push x m) = m.gasLeft :=
    Mach.push_machResultGas
  unfold Rinst.balanceCore
  split
  · rename_i err m heq
    rw [heq] at hp
    simpa only [machResultGas, machMetaResultGas] using Nat.le_of_eq hp
  · rename_i x m1 heq
    rw [heq] at hp
    simp only [machResultGas] at hp
    dsimp only
    split
    · rename_i err m2 heq2
      have := hc (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
        else gasColdAccountAccess) m1
      rw [heq2] at this
      simp only [machResultGas] at this
      simp only [machMetaResultGas]
      omega
    · rename_i u m2 heq2
      have h2 := hc (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
        else gasColdAccountAccess) m1
      rw [heq2] at h2
      simp only [machResultGas] at h2
      split
      · rename_i err m3 heq3
        have h3 := hs (world.state.get x.toAdr).bal m2
        rw [heq3] at h3
        simp only [machResultGas] at h3
        simp only [machMetaResultGas]
        omega
      · rename_i u2 m3 heq3
        have h3 := hs (world.state.get x.toAdr).bal m2
        rw [heq3] at h3
        simp only [machResultGas] at h3
        simp only [machMetaResultGas]
        omega

/-- Every `Rinst` body leaves at most the gas it started with, in *either*
branch. The successful branch is already covered strictly by
`Rinst.runCore_gasLt`; this is the error branch the `"Revert"` path needs. -/
theorem Rinst.runCore_gasLe (pc : Nat) (devm : Devm) (sevm : Sevm) (r : Rinst) :
    (Rinst.runCore pc devm sevm r).gasLeft ≤ devm.gasLeft := by
  cases r <;> simp only [Rinst.runCore]
  all_goals first
    | exact pushItem_gasLe _ _ _
    | exact applyUnary_gasLe _ _ _
    | exact applyBinary_gasLe _ _ _
    | exact applyTernary_gasLe _ _ _
    | skip
  case balance =>
    rw [liftMachMetaWorldExecution, liftMachMetaExecution_resultGas]
    exact Rinst.balanceCore_machMetaResultGas _ _ _
  case clz =>
    split
    · exact applyUnary_gasLe _ _ _
    · simp
  case pop =>
    exact gasLe_bind_id (Nat.le_of_eq (Devm.pop_map_snd_gasLe devm))
      (fun d => chargeGas_result_gasLe _ d)
  case blobhash =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case calldataload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case blockhash =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case gas =>
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case exp =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case tload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    exact pushItem_gasLe _ _ _
  case mload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d2
    simp
  case kec =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case mstore =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case mstore8 =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case calldatacopy | codecopy | mcopy =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨z, d3⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d4
    simp
  case retdatacopy =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨z, d3⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d4
    split
    · exact gasLe_bind_const (devm := d4) (by simp) (fun _ => by simp)
    · simp
  case extcodesize | extcodehash =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨adr, d1⟩
    split
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
    · exact gasLe_bind_id
        (Nat.le_trans (chargeGas_result_gasLe _ _)
          (Nat.le_of_eq (addAccessedAddress_gasLeft _ _)))
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case sload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨key, d1⟩
    split
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
    · exact gasLe_bind_id
        (Nat.le_trans (chargeGas_result_gasLe _ _)
          (Nat.le_of_eq (addAccessedStorageKey_gasLeft _ _ _)))
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case extcodecopy =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨adr, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d2⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d3⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨z, d4⟩
    split
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _) (fun d => by simp)
    · exact gasLe_bind_id
        (Nat.le_trans (chargeGas_result_gasLe _ _)
          (Nat.le_of_eq (addAccessedAddress_gasLeft _ _)))
        (fun d => by simp)
  case swap n =>
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d1
    split <;> simp
  case dup n =>
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d1
    split
    · simp
    · exact Nat.le_of_eq (Devm.push_gasLe _ _)
  case tstore =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨key, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨val, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    refine gasLe_bind_const (devm := d3) (by simp) ?_
    intro _
    simp
  case log n =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨topics, d3⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d4
    refine gasLe_bind_const (devm := d4) (by simp) ?_
    intro _
    simp
  case sstore =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨key, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨val, d2⟩
    refine gasLe_bind_const (devm := d2) (by simp) ?_
    intro _
    refine gasLe_bind (proj := Prod.fst) ?_ ?_
    · simp only [resultGas_ok]
      split <;> simp
    · rintro ⟨d3, cost2⟩
      refine gasLe_bind_const (devm := d3) (by simp) ?_
      intro _
      refine gasLe_bind_id (by simp) ?_
      intro d4
      refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
      intro d5
      refine gasLe_bind_const (devm := d5) (by simp) ?_
      intro _
      simp

theorem Jinst.runCore_gasLe (pc : Nat) (devm : Devm) (sevm : Sevm) (j : Jinst) :
    resultGas Prod.snd (Jinst.runCore pc devm sevm j) ≤ devm.gasLeft := by
  cases j <;> simp only [Jinst.runCore]
  case jumpdest =>
    exact gasLe_bind_gen (proj := id) (by simp) (fun d => by simp)
  case jump =>
    refine gasLe_bind_gen (proj := Prod.snd) (by simp) ?_
    rintro ⟨dest, d1⟩
    refine gasLe_bind_gen (proj := id) (by simp) ?_
    intro d2
    refine gasLe_bind_gen (proj := fun _ : Unit => d2) (by simp) ?_
    intro _
    simp
  case jumpi =>
    refine gasLe_bind_gen (proj := Prod.snd) (by simp) ?_
    rintro ⟨dest, d1⟩
    refine gasLe_bind_gen (proj := Prod.snd) (by simp) ?_
    rintro ⟨cond, d2⟩
    refine gasLe_bind_gen (proj := id) (by simp) ?_
    intro d3
    split
    · exact gasLe_bind_gen (proj := fun _ : Nat => d3) (by simp) (fun _ => by simp)
    · refine gasLe_bind_gen (proj := fun _ : Unit => d3) (by simp) ?_
      intro _
      exact gasLe_bind_gen (proj := fun _ : Nat => d3) (by simp) (fun _ => by simp)

@[simp] theorem Devm.subBal_gasLeft {devm devm' : Devm} {a : Adr} {v : B256}
    (h : devm.subBal a v = some devm') : devm'.gasLeft = devm.gasLeft := by
  unfold Devm.subBal at h
  rcases hs : devm.state.subBal a v with _ | state <;> rw [hs] at h <;>
    simp only [bind, Option.bind, Option.some.injEq] at h
  · nomatch h
  · rw [← h, Devm.withState_gasLeft]

@[simp] theorem Devm.setBal_gasLeft (devm : Devm) (a : Adr) (v : B256) :
    (devm.setBal a v).gasLeft = devm.gasLeft := rfl

@[simp] theorem addAccountToDelete_gasLeft (devm : Devm) (a : Adr) :
    (addAccountToDelete devm a).gasLeft = devm.gasLeft := rfl

@[simp] theorem Devm.addBal_gasLeft (devm : Devm) (a : Adr) (v : B256) :
    (devm.addBal a v).gasLeft = devm.gasLeft := rfl

@[simp] theorem Devm.withOutput_gasLeft (devm : Devm) (output : Bytes) :
    (devm.withOutput output).gasLeft = devm.gasLeft := rfl

/-- The halting instructions. `.rev` is the reason this whole layer exists: it
is the sole producer of the `"Revert"` tag, the one error `handleError` turns
back into a successful frame result carrying live gas. -/
theorem Linst.run_gasLe (sevm : Sevm) (devm : Devm) (l : Linst) :
    Execution.gasLeft (Linst.run sevm devm l) ≤ devm.gasLeft := by
  cases l <;> simp only [Linst.run]
  case stop => simp
  case ret =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case rev =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case dest =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨donee, d1⟩
    refine gasLe_bind_const (devm := d1) (by simp) ?_
    intro donorBal
    refine gasLe_bind (proj := Prod.fst) ?_ ?_
    · simp only [resultGas_ok]
      split <;> simp
    · rintro ⟨d2, cost2⟩
      refine gasLe_bind_const (devm := d2) (by simp) ?_
      intro cost3
      refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
      intro d3
      refine gasLe_bind_const (devm := d3) (by simp) ?_
      intro _
      refine gasLe_bind_id ?_ ?_
      · rcases hb : d3.subBal sevm.currentTarget donorBal with _ | d4
        · simp [Option.toExcept]
        · simp [Option.toExcept, Devm.subBal_gasLeft hb]
      · intro d4
        refine gasLe_bind_id (by simp) ?_
        intro d5
        split <;> simp

/-! ## The `Xinst` halt branch

`Xinst` is the one family whose error branch resists the `resultGas` walk. A
call-type instruction that short-circuits at depth 0 hands the stipend *back*,
so the `Devm` in `(evm1.withGasLeft (evm1.gasLeft + gas)).push 0` carries more
gas than the intermediate it came from; the bound is recoverable only from the
charge equation the compositional device deliberately discards.

What the driver actually needs is weaker than a gas bound. `handleError`
manufactures a live-gas frame result out of exactly one tag, `"Revert"`, and
every error an `Xinst` can raise is a stack or gas fault — `"Revert"` is
produced at a single site in the whole interpreter, `Linst.run .rev`. So the
`Xinst` family discharges the settlement obligation by tag rather than by
arithmetic, which is a walk with no arithmetic in it at all. -/

/-- No branch of this outcome reports the `"Revert"` tag. -/
def NoRevertOut {α : Type} : Except (String × Devm) α → Prop
  | .error p => p.1 ≠ "Revert"
  | .ok _ => True

/-- The `Mach`-level analogue, for the footprint-lifted primitives. -/
def MachNoRevert {α : Type} : Footprint.Outcome Mach α → Prop
  | .error q => q.1 ≠ "Revert"
  | .ok _ => True

theorem liftMach_noRevert {α : Type} {core : Mach → Footprint.Outcome Mach α}
    {devm : Devm} (h : MachNoRevert (core devm.mach)) :
    NoRevertOut (liftMach core devm) := by
  unfold liftMach Footprint.liftOutcome
  rcases hc : core devm.mach with ⟨err, m⟩ | ⟨v, m⟩ <;> rw [hc] at h
  · exact h
  · trivial

theorem liftMachExecution_noRevert {core : Mach → Footprint.Outcome Mach Unit}
    {devm : Devm} (h : MachNoRevert (core devm.mach)) :
    NoRevertOut (liftMachExecution core devm) := by
  unfold liftMachExecution Footprint.toExecution liftMach Footprint.liftOutcome
  rcases hc : core devm.mach with ⟨err, m⟩ | ⟨v, m⟩ <;> rw [hc] at h
  · exact h
  · trivial

theorem Mach.pop_noRevert (mach : Mach) : MachNoRevert mach.pop := by
  unfold Mach.pop
  split
  · show ("StackUnderflowError" : String) ≠ "Revert"
    decide
  · trivial

theorem Mach.popToNat_noRevert (mach : Mach) : MachNoRevert mach.popToNat := by
  have h := Mach.pop_noRevert mach
  unfold Mach.popToNat
  rcases hp : mach.pop with ⟨e⟩ | ⟨x, m⟩ <;> rw [hp] at h
  · exact h
  · trivial

theorem Mach.popToAdr_noRevert (mach : Mach) : MachNoRevert mach.popToAdr := by
  have h := Mach.pop_noRevert mach
  unfold Mach.popToAdr
  rcases hp : mach.pop with ⟨e⟩ | ⟨x, m⟩ <;> rw [hp] at h
  · exact h
  · trivial

theorem Mach.push_noRevert (x : B256) (mach : Mach) :
    MachNoRevert (Mach.push x mach) := by
  unfold Mach.push
  split
  · trivial
  · show ("StackOverflowError" : String) ≠ "Revert"
    decide

theorem Mach.chargeGas_noRevert (c : Nat) (mach : Mach) :
    MachNoRevert (Mach.chargeGas c mach) := by
  unfold Mach.chargeGas
  split
  · show ("OutOfGasError" : String) ≠ "Revert"
    decide
  · trivial

theorem Devm.pop_noRevert (devm : Devm) : NoRevertOut devm.pop :=
  liftMach_noRevert (Mach.pop_noRevert devm.mach)

theorem Devm.popToNat_noRevert (devm : Devm) : NoRevertOut devm.popToNat :=
  liftMach_noRevert (Mach.popToNat_noRevert devm.mach)

theorem Devm.popToAdr_noRevert (devm : Devm) : NoRevertOut devm.popToAdr :=
  liftMach_noRevert (Mach.popToAdr_noRevert devm.mach)

theorem Devm.push_noRevert (x : B256) (devm : Devm) : NoRevertOut (devm.push x) :=
  liftMachExecution_noRevert (Mach.push_noRevert x devm.mach)

theorem chargeGas_noRevert (c : Nat) (devm : Devm) : NoRevertOut (chargeGas c devm) :=
  liftMachExecution_noRevert (Mach.chargeGas_noRevert c devm.mach)

theorem assert_noRevert {p : Prop} [Decidable p] {msg : String} {devm : Devm}
    (h : msg ≠ "Revert") :
    NoRevertOut (Except.assert p (⟨msg, devm⟩ : String × Devm)) := by
  unfold Except.assert
  split
  · trivial
  · exact h

theorem assertDynamic_noRevert (sevm : Sevm) (devm : Devm) :
    NoRevertOut (assertDynamic sevm devm) := by
  unfold assertDynamic
  exact assert_noRevert (by decide)

/-- The `XStep` form of the tag obligation. A spawn carries no outcome of its
own, so it owes nothing. -/
def XStep.NoRevert : XStep → Prop
  | .done ex => NoRevertOut ex
  | .spawn _ _ => True

/-- The obligation on an `XStep`-valued body, before `XStep.ofExcept` collapses
its error branch into a `.done`. -/
def xstepNoRevert : Except (String × Devm) XStep → Prop
  | .error p => p.1 ≠ "Revert"
  | .ok step => step.NoRevert

theorem XStep.ofExcept_noRevert {x : Except (String × Devm) XStep}
    (h : xstepNoRevert x) : (XStep.ofExcept x).NoRevert := by
  cases x with
  | error p => exact h
  | ok step => exact h

theorem xstepNoRevert_bind {α : Type} {e : Except (String × Devm) α}
    {f : α → Except (String × Devm) XStep}
    (he : NoRevertOut e) (hf : ∀ a, xstepNoRevert (f a)) :
    xstepNoRevert (e >>= f) := by
  cases e with
  | error p => exact he
  | ok a => exact hf a

theorem genericCall.step_noRevert
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).NoRevert := by
  unfold genericCall.step
  split
  · exact XStep.ofExcept_noRevert
      (xstepNoRevert_bind (Devm.push_noRevert _ _) (fun _ => trivial))
  · trivial

theorem genericCreate.step_noRevert
    (sevm : Sevm) (devm : Devm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) :
    (genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize).NoRevert := by
  unfold genericCreate.step
  apply XStep.ofExcept_noRevert
  refine xstepNoRevert_bind (assert_noRevert (by decide)) ?_
  intro _
  refine xstepNoRevert_bind (assertDynamic_noRevert _ _) ?_
  intro _
  dsimp only
  split
  · exact xstepNoRevert_bind (Devm.push_noRevert _ _) (fun _ => trivial)
  · split
    · exact xstepNoRevert_bind (Devm.push_noRevert _ _) (fun _ => trivial)
    · trivial

theorem Xinst.step_noRevert (sevm : Sevm) (devm : Devm) (x : Xinst) :
    (Xinst.step sevm devm x).NoRevert := by
  cases x <;> simp only [Xinst.step] <;> apply XStep.ofExcept_noRevert
  case create =>
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨endowment, d1⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨memoryIndex, d2⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨memorySize, d3⟩
    refine xstepNoRevert_bind (chargeGas_noRevert _ _) ?_
    intro d4
    exact genericCreate.step_noRevert _ _ _ _ _ _
  case create2 =>
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨endowment, d1⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨memoryIndex, d2⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨memorySize, d3⟩
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨salt, d4⟩
    refine xstepNoRevert_bind (chargeGas_noRevert _ _) ?_
    intro d5
    exact genericCreate.step_noRevert _ _ _ _ _ _
  case call =>
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨gas, d1⟩
    refine xstepNoRevert_bind (Devm.popToAdr_noRevert _) ?_
    rintro ⟨callee, d2⟩
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨value, d3⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputIndex, d4⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputSize, d5⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputIndex, d6⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputSize, d7⟩
    refine xstepNoRevert_bind (chargeGas_noRevert _ _) ?_
    intro d8
    refine xstepNoRevert_bind (assert_noRevert (by decide)) ?_
    intro _
    split
    · exact xstepNoRevert_bind (Devm.push_noRevert _ _) (fun _ => trivial)
    · exact genericCall.step_noRevert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case callcode =>
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨gas, d1⟩
    refine xstepNoRevert_bind (Devm.popToAdr_noRevert _) ?_
    rintro ⟨codeAddress, d2⟩
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨value, d3⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputIndex, d4⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputSize, d5⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputIndex, d6⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputSize, d7⟩
    refine xstepNoRevert_bind (chargeGas_noRevert _ _) ?_
    intro d8
    split
    · exact xstepNoRevert_bind (Devm.push_noRevert _ _) (fun _ => trivial)
    · exact genericCall.step_noRevert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case delcall =>
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨gas, d1⟩
    refine xstepNoRevert_bind (Devm.popToAdr_noRevert _) ?_
    rintro ⟨codeAddress, d2⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputIndex, d3⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputSize, d4⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputIndex, d5⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputSize, d6⟩
    refine xstepNoRevert_bind (chargeGas_noRevert _ _) ?_
    intro d7
    exact genericCall.step_noRevert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  case statcall =>
    refine xstepNoRevert_bind (Devm.pop_noRevert _) ?_
    rintro ⟨gas, d1⟩
    refine xstepNoRevert_bind (Devm.popToAdr_noRevert _) ?_
    rintro ⟨target, d2⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputIndex, d3⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨inputSize, d4⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputIndex, d5⟩
    refine xstepNoRevert_bind (Devm.popToNat_noRevert _) ?_
    rintro ⟨outputSize, d6⟩
    refine xstepNoRevert_bind (chargeGas_noRevert _ _) ?_
    intro d7
    exact genericCall.step_noRevert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## Settling a finished frame

`Frame.settle` turns a child's raw result into the value its parent resumes
from, and it is where the two halting routes above are consumed. Stating the
obligation once, as `Execution.SettledGasLe`, is what lets the driver stay
ignorant of which route a given instruction family took. -/

/-- What a halting outcome owes the parent frame: whatever
`executeCode.handleError` can turn into a *successful* frame result reports at
most `n` gas. An exceptional halt is rewritten to zero gas, and every remaining
tag stays an `.error`, which `Resume.run` cannot turn into a resumed parent. -/
def Execution.SettledGasLe (n : Nat) (ex : Execution) : Prop :=
  ∀ d : Devm, executeCode.handleError ex = .ok d → d.gasLeft ≤ n

theorem Execution.SettledGasLe.mono {m n : Nat} {ex : Execution} (h : m ≤ n)
    (hs : ex.SettledGasLe m) : ex.SettledGasLe n :=
  fun d hd => Nat.le_trans (hs d hd) h

/-- The route the `Rinst`/`Jinst`/`Linst` corpus takes. -/
theorem Execution.settledGasLe_of_gasLe {n : Nat} {ex : Execution}
    (h : ex.gasLeft ≤ n) : ex.SettledGasLe n :=
  fun _ hd => Nat.le_trans (executeCode.handleError_ok_gasLe hd) h

/-- The route the `Xinst` family takes: bound the successful branch, and rule
out the one tag that would let an error carry live gas through. -/
theorem Execution.settledGasLe_of_noRevert {n : Nat} {ex : Execution}
    (hok : ∀ d, ex = .ok d → d.gasLeft ≤ n) (hnr : NoRevertOut ex) :
    ex.SettledGasLe n := by
  intro d hd
  cases ex with
  | ok d0 =>
    simp only [executeCode.handleError, Except.ok.injEq] at hd
    rw [← hd]
    exact hok d0 rfl
  | error p =>
    obtain ⟨err, evm⟩ := p
    simp only [executeCode.handleError] at hd
    split at hd
    · simp only [Except.ok.injEq] at hd
      rw [← hd, Devm.setMeta_gasLeft, Devm.withGasLeft_gasLeft]
      omega
    · split at hd
      · rename_i hrev
        exact absurd hrev hnr
      · nomatch hd

theorem processCreateMessage.chargeCodeGas_gasLe (rules : ForkRules) (devm : Devm) :
    (processCreateMessage.chargeCodeGas rules devm).gasLeft ≤ devm.gasLeft := by
  unfold processCreateMessage.chargeCodeGas
  dsimp only
  split
  · simp
  · refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d
    split <;> simp

theorem processMessage.settle_ok_gasLe {msg : Msg}
    {r : Except (String × State × AdrSet × Tra) Devm} {d : Devm}
    (h : processMessage.settle msg r = .ok d) :
    ∃ d0, r = .ok d0 ∧ d.gasLeft ≤ d0.gasLeft := by
  cases r with
  | error e =>
    exact absurd h (by simp [processMessage.settle, bind, Except.bind])
  | ok d0 =>
    refine ⟨d0, rfl, ?_⟩
    simp only [processMessage.settle, bind, Except.bind] at h
    split at h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.rollback_gasLeft]
    · simp only [Except.ok.injEq] at h
      rw [← h]

theorem processCreateMessage.settle_ok_gasLe {msg : Msg}
    {r : Except (String × State × AdrSet × Tra) Devm} {d : Devm}
    (h : processCreateMessage.settle msg r = .ok d) :
    ∃ d0, r = .ok d0 ∧ d.gasLeft ≤ d0.gasLeft := by
  cases r with
  | error e =>
    exact absurd h (by simp [processCreateMessage.settle, bind, Except.bind])
  | ok d0 =>
    refine ⟨d0, rfl, ?_⟩
    simp only [processCreateMessage.settle, bind, Except.bind] at h
    split at h
    · have hc := processCreateMessage.chargeCodeGas_gasLe msg.benv.stat.rules d0
      rcases hcc : processCreateMessage.chargeCodeGas msg.benv.stat.rules d0 with
          ⟨err, d1⟩ | d1 <;> rw [hcc] at hc h <;>
        simp only [Execution.gasLeft_error, Execution.gasLeft_ok] at hc <;>
        dsimp only at h
      · split at h
        · simp only [Except.ok.injEq] at h
          rw [← h]
          unfold processCreateMessage.exceptionalHalt
          rw [Devm.setMeta_gasLeft, Devm.withGasLeft_gasLeft]
          omega
        · nomatch h
      · simp only [Except.ok.injEq] at h
        rw [← h, Devm.setCode_gasLeft]
        exact hc
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.rollback_gasLeft]

theorem Frame.settleMsg_ok_gasLe {f : Frame}
    {r : Except (String × State × AdrSet × Tra) Devm} {d : Devm}
    (h : f.settleMsg r = .ok d) : ∃ d0, r = .ok d0 ∧ d.gasLeft ≤ d0.gasLeft := by
  unfold Frame.settleMsg at h
  dsimp only at h
  split at h
  · obtain ⟨d1, h1, hle1⟩ := processCreateMessage.settle_ok_gasLe h
    obtain ⟨d0, h0, hle0⟩ := processMessage.settle_ok_gasLe h1
    exact ⟨d0, h0, Nat.le_trans hle1 hle0⟩
  · exact processMessage.settle_ok_gasLe h

theorem Frame.settle_gasLe {f : Frame} {raw : Execution} {n : Nat} {d : Devm}
    (hraw : raw.SettledGasLe n) (h : f.settle raw = .ok d) : d.gasLeft ≤ n := by
  unfold Frame.settle at h
  obtain ⟨d0, h0, hle⟩ := Frame.settleMsg_ok_gasLe h
  exact Nat.le_trans hle (hraw d0 h0)

/-! ## Entering a frame

A frame either hands the child exactly the inner message's gas, or resolves
without running a child at all — and in that case its result is a settled
precompile outcome, which the settlement bound already covers. -/

@[simp] theorem Msg.withBenv_gas (msg : Msg) (benv : Benv) :
    (msg.withBenv benv).gas = msg.gas := rfl

@[simp] theorem initEvm_gasLeft (msg : Msg) :
    (initEvm msg).dyna.gasLeft = msg.gas := rfl

theorem executeCode.enter_inl_gasLeft {msg : Msg} {evm : Evm}
    (h : executeCode.enter msg = .inl evm) : evm.dyna.gasLeft = msg.gas := by
  unfold executeCode.enter at h
  dsimp only at h
  split at h
  · simp only [Sum.inl.injEq] at h
    rw [← h, initEvm_gasLeft]
  · split at h
    · nomatch h
    · simp only [Sum.inl.injEq] at h
      rw [← h, initEvm_gasLeft]

theorem executeCode.enter_inr_gasLe {msg : Msg} {raw : Execution}
    (h : executeCode.enter msg = .inr raw) : raw.gasLeft ≤ msg.gas := by
  unfold executeCode.enter at h
  dsimp only at h
  split at h
  · nomatch h
  · split at h
    · simp only [Sum.inr.injEq] at h
      rw [← h]
      exact executePrecomp_gasLe _ _
    · nomatch h

theorem Frame.enter_run_gasLeft {f : Frame} {child : Evm}
    (h : f.enter = .run child) : child.dyna.gasLeft = f.inner.gas := by
  unfold Frame.enter at h
  split at h
  · nomatch h
  · split at h
    · rename_i evm henter
      simp only [FrameEntry.run.injEq] at h
      rw [← h, executeCode.enter_inl_gasLeft henter, Msg.withBenv_gas]
    · nomatch h

theorem Frame.enter_done_gasLe {f : Frame}
    {r : Except (String × State × AdrSet × Tra) Devm} {d : Devm}
    (h : f.enter = .done r) (hd : r = .ok d) : d.gasLeft ≤ f.inner.gas := by
  unfold Frame.enter at h
  split at h
  · simp only [FrameEntry.done.injEq] at h
    rw [← h] at hd
    obtain ⟨d0, h0, -⟩ := Frame.settleMsg_ok_gasLe hd
    nomatch h0
  · split at h
    · nomatch h
    · rename_i raw henter
      simp only [FrameEntry.done.injEq] at h
      rw [← h] at hd
      exact Frame.settle_gasLe
        (Execution.settledGasLe_of_gasLe
          (Nat.le_trans (executeCode.enter_inr_gasLe henter)
            (Nat.le_of_eq (Msg.withBenv_gas _ _)))) hd

/-! ## Resuming a parent

`Resume.run_ok_gasLeft` already pins the successful result at
`rsm.parentGas + child.gasLeft`. The bound below covers the error branch as
well, which the driver needs because a resume that overflows the parent's stack
still produces a raw result the *grandparent* has to settle. -/

@[simp] theorem incorporateChildOnError_gasLeft (parent child : Devm) (rd : Bytes) :
    (incorporateChildOnError parent child rd).gasLeft =
      parent.gasLeft + child.gasLeft := rfl

@[simp] theorem incorporateChildOnSuccess_gasLeft (parent child : Devm) (rd : Bytes) :
    (incorporateChildOnSuccess parent child rd).gasLeft =
      parent.gasLeft + child.gasLeft := rfl

theorem Resume.run_gasLe {rsm : Resume}
    {r : Except (String × State × AdrSet × Tra) Devm} {m : Nat}
    (hr : ∀ d, r = .ok d → d.gasLeft ≤ m) :
    Execution.gasLeft (rsm.run r) ≤ rsm.parentGas + m := by
  cases rsm with
  | create parent newAddress =>
    cases r with
    | error e =>
      simp only [Resume.run, liftToExecution, bind, Except.bind,
        Execution.gasLeft_error, Resume.parentGas, Devm.setWorld_gasLeft,
        Devm.withCreatedAccounts_gasLeft]
      omega
    | ok child =>
      have hc := hr child rfl
      simp only [Resume.run, liftToExecution, bind, Except.bind, Resume.parentGas]
      split <;> simp only [Devm.push_gasLe, incorporateChildOnError_gasLeft,
        incorporateChildOnSuccess_gasLeft] <;> omega
  | call parent outputIndex outputSize =>
    cases r with
    | error e =>
      simp only [Resume.run, liftToExecution, bind, Except.bind,
        Execution.gasLeft_error, Resume.parentGas, Devm.setWorld_gasLeft,
        Devm.withCreatedAccounts_gasLeft]
      omega
    | ok child =>
      have hc := hr child rfl
      simp only [Resume.run, liftToExecution, bind, Except.bind, Resume.parentGas]
      split <;>
        refine gasLe_bind_id ?_ (fun d => by simp) <;>
        simp only [Devm.push_gasLe, incorporateChildOnError_gasLeft,
          incorporateChildOnSuccess_gasLeft] <;> omega

/-! ## The step-level obligation

One statement covering all three outcomes of `Evm.step`, so that the driver
induction has a single hypothesis to consume. -/

/-- What one step of the driver owes, measured against the frame's gas at the
start of the step. -/
def Step.GasBound (n : Nat) : Step → Prop
  | .halt ex => ex.SettledGasLe n
  | .cont _ devm => devm.gasLeft < n
  | .spawn frame rsm _ => frame.inner.gas + rsm.parentGas < n

theorem Step.ofExecution_gasBound {pc n : Nat} {ex : Execution}
    (hok : ∀ d, ex = .ok d → d.gasLeft < n) (hset : ex.SettledGasLe n) :
    (Step.ofExecution pc ex).GasBound n := by
  cases ex with
  | error e => exact hset
  | ok d => exact hok d rfl

theorem Step.ofJump_gasBound {n : Nat} {x : Except (String × Devm) (Nat × Devm)}
    (hok : ∀ p, x = .ok p → p.2.gasLeft < n) (hle : resultGas Prod.snd x ≤ n) :
    (Step.ofJump x).GasBound n := by
  cases x with
  | error e => exact Execution.settledGasLe_of_gasLe hle
  | ok p => exact hok p rfl

theorem XStep.toStep_gasBound {pc n : Nat} {step : XStep}
    (hdec : step.GasDecreasing n) (hnr : step.NoRevert) :
    (XStep.toStep pc step).GasBound n := by
  cases step with
  | done ex =>
    refine Step.ofExecution_gasBound hdec ?_
    exact Execution.settledGasLe_of_noRevert
      (fun d hd => Nat.le_of_lt (hdec d hd)) hnr
  | spawn frame rsm => exact hdec

theorem Ninst.step_push_gasLt {xs : Bytes} {evm : Evm} {devm : Devm}
    (h : (chargeGas (if xs = [] then gBase else gVerylow) evm.dyna >>=
      Devm.push xs.toB256) = .ok devm) : devm.gasLeft < evm.dyna.gasLeft := by
  obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
  have e1 := chargeGas_gasLeft h1
  have e2 := Devm.push_gasLeft h2
  have hpos : 0 < (if xs = [] then gBase else gVerylow) := by
    split <;> decide
  omega

theorem Ninst.step_gasBound (evm : Evm) (n : Ninst) :
    (Ninst.step evm n).GasBound evm.dyna.gasLeft := by
  cases n with
  | push xs b =>
    refine Step.ofExecution_gasBound (fun d hd => Ninst.step_push_gasLt hd) ?_
    refine Execution.settledGasLe_of_gasLe ?_
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  | reg r =>
    refine Step.ofExecution_gasBound
      (fun d hd => Rinst.runCore_gasLt evm.pc evm.dyna evm.sta r hd) ?_
    exact Execution.settledGasLe_of_gasLe
      (Rinst.runCore_gasLe evm.pc evm.dyna evm.sta r)
  | exec x =>
    exact XStep.toStep_gasBound (Xinst.step_gasDecreasing evm.sta evm.dyna x)
      (Xinst.step_noRevert evm.sta evm.dyna x)

theorem Evm.step_gasBound (evm : Evm) : evm.step.GasBound evm.dyna.gasLeft := by
  unfold Evm.step
  split
  · exact Execution.settledGasLe_of_gasLe (Nat.le_of_eq rfl)
  · exact Ninst.step_gasBound evm _
  · rename_i j _
    exact Step.ofJump_gasBound
      (fun p hp => Jinst.runCore_gasLt evm.pc evm.dyna evm.sta j hp)
      (Jinst.runCore_gasLe evm.pc evm.dyna evm.sta j)
  · rename_i l _
    exact Execution.settledGasLe_of_gasLe (Linst.run_gasLe evm.sta evm.dyna l)

/-! ## The driver

Both theorems go by structural induction on the fuel, and monotonicity has to
come first: sufficiency needs to know that a child which ran to completion did
not hand its parent back more gas than it was given. -/

/-- Driver monotonicity. Stated over the settlement obligation rather than over
raw gas, because that is the only thing a parent can extract from a child's
result and it is what both routes of the halting corpus establish. -/
theorem execFueled_settledGasLe : ∀ (fuel : Nat) (evm : Evm) {raw : Execution},
    (execFueled evm fuel).run = some raw → raw.SettledGasLe evm.dyna.gasLeft := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm raw h
    rw [execFueled] at h
    simp only [Fueled.exhausted_run] at h
    nomatch h
  | succ fuel ih =>
    intro evm raw h
    have hstep := Evm.step_gasBound evm
    rw [execFueled] at h
    rcases hs : evm.step with ⟨ex⟩ | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩
    · rw [hs] at h hstep
      simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      rw [← h]
      exact hstep
    · rw [hs] at h hstep
      simp only [Step.GasBound] at hstep
      exact (ih _ h).mono (Nat.le_of_lt hstep)
    · rw [hs] at h hstep
      simp only [Step.GasBound] at hstep
      dsimp only at h
      rcases he : frame.enter with r | child
      · rw [he] at h
        dsimp only at h
        have hres := Resume.run_gasLe (rsm := rsm) (m := frame.inner.gas)
          (fun d hd => Frame.enter_done_gasLe he hd)
        rcases hrun : rsm.run r with ⟨e⟩ | d1
        · rw [hrun] at h hres
          simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          simp only [Execution.gasLeft_error] at hres
          rw [← h]
          refine Execution.settledGasLe_of_gasLe ?_
          simp only [Execution.gasLeft_error]
          omega
        · rw [hrun] at h hres
          simp only [Execution.gasLeft_ok] at hres
          exact (ih _ h).mono (show d1.gasLeft ≤ evm.dyna.gasLeft by omega)
      · rw [he] at h
        dsimp only at h
        rcases hc : (execFueled child fuel).run with _ | raw'
        · rw [hc] at h
          simp only [Fueled.exhausted_run] at h
          nomatch h
        · rw [hc] at h
          dsimp only at h
          have hchild := ih child hc
          rw [Frame.enter_run_gasLeft he] at hchild
          have hres := Resume.run_gasLe (rsm := rsm) (r := frame.settle raw')
            (m := frame.inner.gas) (fun d hd => Frame.settle_gasLe hchild hd)
          rcases hrun : rsm.run (frame.settle raw') with ⟨e⟩ | d1
          · rw [hrun] at h hres
            simp only [Fueled.ofExcept_run, Option.some.injEq] at h
            simp only [Execution.gasLeft_error] at hres
            rw [← h]
            refine Execution.settledGasLe_of_gasLe ?_
            simp only [Execution.gasLeft_error]
            omega
          · rw [hrun] at h hres
            simp only [Execution.gasLeft_ok] at hres
            exact (ih _ h).mono (show d1.gasLeft ≤ evm.dyna.gasLeft by omega)

/-- **Sufficiency.** Fuel strictly greater than the frame's remaining gas always
carries the driver to a result. The base case is vacuous: the hypothesis forces
`fuel > 0`. -/
theorem execFueled_run_isSome : ∀ (fuel : Nat) (evm : Evm),
    evm.dyna.gasLeft < fuel → ∃ raw : Execution, (execFueled evm fuel).run = some raw := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm h
    omega
  | succ fuel ih =>
    intro evm h
    have hstep := Evm.step_gasBound evm
    rw [execFueled]
    rcases hs : evm.step with ⟨ex⟩ | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩ <;>
      rw [hs] at hstep <;> simp only [Step.GasBound] at hstep <;> dsimp only
    · exact ⟨ex, rfl⟩
    · have hlt : devm.gasLeft < fuel := by omega
      exact ih _ hlt
    · rcases he : frame.enter with r | child <;> dsimp only
      · rcases hrun : rsm.run r with ⟨e⟩ | d1 <;> dsimp only
        · exact ⟨.error e, rfl⟩
        · obtain ⟨d0, hd0, hgas⟩ := Resume.run_ok_gasLeft hrun
          have hle : d0.gasLeft ≤ frame.inner.gas := Frame.enter_done_gasLe he hd0
          have hlt : d1.gasLeft < fuel := by omega
          exact ih _ hlt
      · have hgas : child.dyna.gasLeft = frame.inner.gas := Frame.enter_run_gasLeft he
        have hchildlt : child.dyna.gasLeft < fuel := by omega
        obtain ⟨raw', hraw'⟩ := ih child hchildlt
        rw [hraw']
        dsimp only
        rcases hrun : rsm.run (frame.settle raw') with ⟨e⟩ | d1 <;> dsimp only
        · exact ⟨.error e, rfl⟩
        · obtain ⟨d0, hd0, hgas2⟩ := Resume.run_ok_gasLeft hrun
          have hsettled := execFueled_settledGasLe fuel child hraw'
          rw [hgas] at hsettled
          have hle : d0.gasLeft ≤ frame.inner.gas := Frame.settle_gasLe hsettled hd0
          have hlt : d1.gasLeft < fuel := by omega
          exact ih _ hlt

theorem execFueled_ne_exhausted (evm : Evm) (fuel : Nat) (h : evm.dyna.gasLeft < fuel) :
    execFueled evm fuel ≠ Fueled.exhausted := by
  obtain ⟨raw, hraw⟩ := execFueled_run_isSome fuel evm h
  intro hcon
  rw [hcon] at hraw
  simp only [Fueled.exhausted_run] at hraw
  nomatch hraw

/-- The form the total `exec` consumes. The additive constant is **1**: seeding
the driver with `gasLeft + 1` is always enough, so the total wrapper can
discharge the `Option` with this witness. -/
theorem execFueled_succ_ne_exhausted (evm : Evm) :
    execFueled evm (evm.dyna.gasLeft + 1) ≠ Fueled.exhausted :=
  execFueled_ne_exhausted evm (evm.dyna.gasLeft + 1) (Nat.lt_succ_self _)

/-! ## The total interpreter

Everything below is fuel-free. `execFueled` survives as the structurally
recursive definition downstream proofs reason over, but no consumer has to
thread a fuel parameter or handle an exhaustion outcome any more. -/

/-- The fuel budget seeded from a frame's remaining gas. The additive constant
is the one `execFueled_succ_ne_exhausted` proves sufficient: **1**. -/
def sufficientFuel (gas : Nat) : Nat := gas + 1

theorem execFueled_run_sufficientFuel_isSome (evm : Evm) :
    ((execFueled evm (sufficientFuel evm.dyna.gasLeft)).run).isSome := by
  obtain ⟨raw, hraw⟩ :=
    execFueled_run_isSome (sufficientFuel evm.dyna.gasLeft) evm (Nat.lt_succ_self _)
  rw [hraw]
  rfl

/-- **The total interpreter.** Fuel is an implementation detail: the driver is
seeded from the frame's own remaining gas and `execFueled_run_sufficientFuel_isSome`
discharges the resulting `Option` at the definition site. -/
def exec (evm : Evm) : Except (String × Devm) Devm :=
  ((execFueled evm (sufficientFuel evm.dyna.gasLeft)).run).get
    (execFueled_run_sufficientFuel_isSome evm)

/-- **Bridge equation.** The driver at the seeded budget returns exactly the
total result, so no downstream proof has to manipulate `Option.get`. -/
theorem execFueled_run_sufficientFuel (evm : Evm) :
    (execFueled evm (sufficientFuel evm.dyna.gasLeft)).run = some (exec evm) :=
  (Option.some_get _).symm

/-- More fuel never changes a result the driver already reached. This is what
makes the seeded budget an implementation detail rather than a semantic choice:
every budget past the frame's gas gives the same answer, so replacing the old
`gas + 50` seeding by `sufficientFuel gas` is observationally neutral. -/
theorem execFueled_run_mono :
    ∀ (fuel : Nat) (evm : Evm) {fuel' : Nat} {raw : Execution}, fuel ≤ fuel' →
      (execFueled evm fuel).run = some raw → (execFueled evm fuel').run = some raw := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm fuel' raw _ h
    rw [execFueled] at h
    simp only [Fueled.exhausted_run] at h
    nomatch h
  | succ fuel ih =>
    intro evm fuel' raw hle h
    obtain ⟨m, rfl⟩ : ∃ m, fuel' = m + 1 := by
      cases fuel' with
      | zero => omega
      | succ m => exact ⟨m, rfl⟩
    have hle' : fuel ≤ m := by omega
    rw [execFueled] at h
    rw [execFueled]
    rcases hs : evm.step with ⟨ex⟩ | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩ <;>
      rw [hs] at h <;> dsimp only at h ⊢
    · exact h
    · exact ih _ hle' h
    · rcases he : frame.enter with r | child <;> rw [he] at h <;>
        dsimp only at h ⊢
      · rcases hrun : rsm.run r with ⟨e⟩ | d1 <;> rw [hrun] at h <;>
          dsimp only at h ⊢
        · exact h
        · exact ih _ hle' h
      · rcases hc : (execFueled child fuel).run with _ | raw'
        · rw [hc] at h
          simp only [Fueled.exhausted_run] at h
          nomatch h
        · rw [hc] at h
          rw [ih _ hle' hc]
          dsimp only at h ⊢
          rcases hrun : rsm.run (frame.settle raw') with ⟨e⟩ | d1 <;>
            rw [hrun] at h <;> dsimp only at h ⊢
          · exact h
          · exact ih _ hle' h

/-- The downstream bridge at an arbitrary sufficient budget. -/
theorem execFueled_run_of_lt {evm : Evm} {fuel : Nat} (h : evm.dyna.gasLeft < fuel) :
    (execFueled evm fuel).run = some (exec evm) :=
  execFueled_run_mono _ evm h (execFueled_run_sufficientFuel evm)

/-- Reading a fueled result off as the total one: the shape a proof stated over
`execFueled` uses to transfer to `exec`. -/
theorem exec_eq_of_run {evm : Evm} {fuel : Nat} {raw : Execution}
    (hlt : evm.dyna.gasLeft < fuel) (h : (execFueled evm fuel).run = some raw) :
    exec evm = raw := by
  rw [execFueled_run_of_lt hlt] at h
  exact Option.some.inj h

/-! ## The total frame wrappers

These are the public entry points. They lost their `fuel` parameter and their
`Fueled` result type together: a frame is entered, the driver runs to a
definite result, and the frame settles it. -/

def runFrame (frame : Frame) : Except (String × State × AdrSet × Tra) Devm :=
  match frame.enter with
  | .done r => r
  | .run evm => frame.settle (exec evm)

def executeCode (msg : Msg) : Except (String × State × AdrSet × Tra) Devm :=
  match executeCode.enter msg with
  | .inl evm => executeCode.handleError (exec evm)
  | .inr raw => executeCode.handleError raw

def processMessage (msg : Msg) : Except (String × State × AdrSet × Tra) Devm :=
  runFrame (Frame.ofCall msg)

def processCreateMessage (msg : Msg) :
    Except (String × State × AdrSet × Tra) Devm :=
  runFrame (Frame.ofCreate msg)

/-! ## Focused executable checks for the total entry points

These mirror the flatten arc's representative states — arithmetic loop, nested
CALL, CREATE collision, precompile under both dispatch paths, depth-zero
short-circuit, out-of-gas halt, REVERT with output — but drive them through the
fuel-free API. `Jaune.Execution` keeps the checks that pin `execFueled` itself,
including the one that shows fuel really can run out when it is not seeded from
the frame's gas.

`private` declarations do not cross module boundaries, so the two helpers this
block shares with `Jaune.Execution` are restated here. Keep them in step with
their counterparts at `Jaune/Execution.lean:4203`. -/

private def totalGuardCode (bytes : Bytes) : ByteArray := .mk <| .mk bytes

private def totalGuardMsg (bytes : Bytes) (gas depth : Nat) : Msg :=
  {
    (default : Msg) with
    gas := gas
    code := totalGuardCode bytes
    depth := depth
  }

private def totalGuardSummary
    (r : Except (String × State × AdrSet × Tra) Devm) :
    Option (Option String × List B256 × Bytes × Nat) :=
  match r with
  | .ok devm => some ⟨devm.error, devm.stack, devm.output, devm.gasLeft⟩
  | .error _ => none

-- Arithmetic loop: the state that exhausted `execFueled` at fuel 20 now runs to a
-- definite out-of-gas result, because the seeded budget is provably sufficient.
private def totalGuardArithmeticLoop : Bool :=
  let msg := totalGuardMsg [0x5B, 0x60, 0x00, 0x56] 1000 8
  match exec (initEvm msg), processMessage msg with
  | .error ⟨err, _⟩, .ok devm =>
    err == "OutOfGasError" &&
      devm.error == some "OutOfGasError" &&
      devm.gasLeft == 0
  | _, _ => false

#guard totalGuardArithmeticLoop

-- Nested CALL: run a parent that calls address 0x20, whose code is STOP.
private def totalGuardNestedCallMsg : Msg :=
  let child : Adr := 0x20
  let state := State.setCode .empty child (totalGuardCode [0x00])
  let benv := {(default : Benv) with state := state}
  {
    (totalGuardMsg
      [ 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00,
        0x60, 0x00, 0x60, 0x20, 0x61, 0x03, 0xE8, 0xF1, 0x00 ]
      100000 8) with
    benv := benv
  }

private def totalGuardNestedCallDirect :=
  totalGuardSummary (runFrame (Frame.ofCall totalGuardNestedCallMsg))

private def totalGuardNestedCallPublic :=
  totalGuardSummary (processMessage totalGuardNestedCallMsg)

#guard totalGuardNestedCallDirect = totalGuardNestedCallPublic
#guard totalGuardNestedCallDirect.map
    (fun x => ((x.2.1.head?, x.2.2.2) : Option B256 × Nat)) =
  some (some 1, 97379)

-- CREATE collision, reached the way a transaction reaches it: a frame executes
-- CREATE at an address that already carries code, so the child is never
-- spawned, the reserved `createGas` is not returned, and 0 is pushed.
private def totalGuardCreateCollisionCreator : Adr := 0x30

private def totalGuardCreateCollisionMsg : Msg :=
  let created := computeContractAddress totalGuardCreateCollisionCreator 0
  let state := State.setCode .empty created (totalGuardCode [0x00])
  {
    (totalGuardMsg [0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xF0, 0x00] 100000 8) with
    benv := {(default : Benv) with state := state}
    currentTarget := totalGuardCreateCollisionCreator
  }

private def totalGuardCreateCollision : Bool :=
  match processMessage totalGuardCreateCollisionMsg with
  | .ok devm =>
    devm.error == none && devm.stack.head? == some 0 && devm.gasLeft == 1062
  | .error _ => false

#guard totalGuardCreateCollision

-- Precompile dispatch is taken normally and bypassed when explicitly disabled:
-- the enabled path pays ecrecover's 3,000 gas without ever entering the driver.
private def totalGuardPrecompileMsg (disabled : Bool) : Msg :=
  {
    (totalGuardMsg [] 10000 8) with
    target := some 1
    currentTarget := 1
    codeAddress := some 1
    disablePrecompiles := disabled
  }

private def totalGuardPrecompileDispatch : Bool :=
  match
      processMessage (totalGuardPrecompileMsg false),
      processMessage (totalGuardPrecompileMsg true) with
  | .ok viaPrecomp, .ok viaCode => viaPrecomp.gasLeft == 7000 && viaCode.gasLeft == 10000
  | _, _ => false

#guard totalGuardPrecompileDispatch

-- Depth zero prevents spawning: the same parent that gets failure word 1 at
-- depth 8 gets 0 at depth 0, with the call never reaching the driver.
private def totalGuardDepthZero : Bool :=
  match processMessage {totalGuardNestedCallMsg with depth := 0} with
  | .ok devm => devm.stack.head? == some 0 && devm.gasLeft == 97379
  | .error _ => false

#guard totalGuardDepthZero

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def totalGuardOog : Bool :=
  let msg := totalGuardMsg [0x60, 0x01, 0x00] 0 8
  match exec (initEvm msg) with
  | .error ⟨err, _⟩ => err == "OutOfGasError"
  | .ok _ => false

#guard totalGuardOog

-- REVERT retains the 32-byte memory slice and becomes a settled frame result.
private def totalGuardRevert : Bool :=
  let msg :=
    totalGuardMsg
      [ 0x60, 0x2A, 0x60, 0x00, 0x52,
        0x60, 0x20, 0x60, 0x00, 0xFD ]
      1000 8
  match runFrame (Frame.ofCall msg) with
  | .ok devm =>
    devm.error == some "Revert" &&
      devm.output.length == 32 &&
      devm.output.getLast? == some 0x2A &&
      devm.gasLeft == 982
  | .error _ => false

#guard totalGuardRevert
