import Elevm.Execution

/-!
# A sufficient fuel bound for the interpreter driver

`Elevm.Execution` defines the interpreter driver structurally recursive on a
fuel parameter, so it must report exhaustion as a possible outcome. This module
proves that fuel seeded from the frame's remaining gas is always sufficient, and
uses that proof to give the driver and its frame wrappers a total type.

It sits between `Elevm.Execution` (the driver) and `Elevm.Transaction` (its
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

@[simp] theorem withReturnData_gasLeft (devm : Devm) (returnData : B8L) :
    (devm.withReturnData returnData).gasLeft = devm.gasLeft := rfl

@[simp] theorem withError_gasLeft (devm : Devm) (error : Option String) :
    (devm.withError error).gasLeft = devm.gasLeft := rfl

@[simp] theorem withCreatedAccounts_gasLeft (devm : Devm) (as : AdrSet) :
    (devm.withCreatedAccounts as).gasLeft = devm.gasLeft := rfl

@[simp] theorem withState_gasLeft (devm : Devm) (state : State) :
    (devm.withState state).gasLeft = devm.gasLeft := rfl

@[simp] theorem memWrite_gasLeft (devm : Devm) (idx : Nat) (val : B8L) :
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

theorem chargeGas_gasLt {c : Nat} {devm devm' : Devm} (hc : 0 < c)
    (h : chargeGas c devm = .ok devm') : devm'.gasLeft < devm.gasLeft := by
  have := chargeGas_gasLeft h; omega

theorem chargeGas_gasLe {c : Nat} {devm devm' : Devm}
    (h : chargeGas c devm = .ok devm') : devm'.gasLeft ≤ devm.gasLeft := by
  have := chargeGas_gasLeft h; omega

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

theorem access_cost_pos (x : Adr) (a : AdrSet) : 0 < access_cost x a := by
  unfold access_cost gasWarmAccess gasColdAccountAccess
  split <;> omega

theorem gasWarmAccess_le_access_cost (x : Adr) (a : AdrSet) :
    gasWarmAccess ≤ access_cost x a := by
  unfold access_cost gasWarmAccess gasColdAccountAccess
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
        ((access_cost callee d7.accessedAddresses +
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

theorem Rinst.runCore_add_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm} (h : Rinst.runCore pc devm sevm .add = .ok devm') :
    devm'.gasLeft < devm.gasLeft := by
  simp only [Rinst.runCore] at h
  have hg := applyBinary_gasLeft h
  unfold gVerylow at hg
  omega

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
      (fun start _ => B8L.toB256 <| sevm.data.sliceD start.toNat 32 0)
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
          (sevm.code.sliceD codeStart size (Linst.toB8 .stop)))
      (by intros; unfold gVerylow; omega)
      (by intros; simp only [Devm.memWrite_gasLeft]) h
