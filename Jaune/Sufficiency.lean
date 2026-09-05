import Jaune.Execution

namespace Jaune

open Jaune

/-!
# A sufficient fuel bound for the interpreter driver

`Jaune.Execution` defines the interpreter driver structurally recursive on a
fuel parameter, so it must report exhaustion as a possible outcome. This module
proves that fuel seeded from the frame's gas measure is always sufficient, and
uses that proof to give the driver and its frame wrappers a total type.

It sits between `Jaune.Execution` (the driver) and `Jaune.Transaction` (its
first consumer) so that the consumers can be stated against the total API.

## The measure

The measure is `Devm.gasMeasure`: execution gas plus the outstanding and the
committed spill of EIP-8037's state-gas meter, `gasLeft + spilled +
committedSpill` (`Jaune/Machine.lean`, beside the meter). Under
`rules.stateGas = none` the meter is zero and the measure *is* `gasLeft`, so
every Prague-stated fact below is the fact it always was; under `some _` it is
what still decreases when a state-gas refund raises `gasLeft`
(`DualGasProbe.executionGas_alone_can_increase` is the standing witness that
`gasLeft` alone cannot serve, and the Amsterdam `SSTORE` arm is where that
witness is met at a real site). It is deliberately *not* Blanc's `Devm.Burn`:
that relation is non-strict and bundles thirteen further field equalities,
neither of which this argument wants. Everything here is stated about the
measure alone, and treats it as one atom: the `simp` sets below say which
updates leave it alone, `chargeGas_gasMeasure` says how much a charge takes,
and every site proof ends in one `omega`.

## The obligations

Sufficiency reduces to four facts about one step of the driver, all measured
against the frame's gas at the *start* of the step:

* `.cont` — a continuing step leaves a strictly smaller measure;
* spawn/child — a spawned child starts with a strictly smaller measure than its
  parent;
* spawn/done — a spawn that resolves without running a child resumes the parent
  with a strictly smaller measure;
* spawn/settle — a spawn whose child ran, and whose child's measure did not
  grow, resumes the parent with a strictly smaller measure.

The last one is why the driver also needs a monotonicity theorem: the resumed
parent's measure is at most `parent.gasMeasure + child.gasMeasure`, so the
child's own budget has to be known not to have grown.
-/

/-- The measure carried by a raw frame result, in either branch. The error
branch retains its `Devm` precisely so that the measure can still be read off
it, and the driver's monotonicity theorem has to cover both branches because
`Frame.settle` consumes both. -/
def Execution.gasMeasure : Execution → Nat
  | .ok devm => devm.gasMeasure
  | .error e => e.2.gasMeasure

@[simp] theorem Execution.gasMeasure_ok (devm : Devm) :
    Execution.gasMeasure (.ok devm) = devm.gasMeasure := rfl

@[simp] theorem Execution.gasMeasure_error (e : EvmError × Devm) :
    Execution.gasMeasure (.error e) = e.2.gasMeasure := rfl

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

@[simp] theorem withError_gasLeft (devm : Devm) (error : Option SettledHalt) :
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

/-! ### The same set, for the state-gas meter

Every update above leaves the meter alone as well, and for the same reason: it
reaches `Mach` through `setMach` with a `with`-update that does not name
`stateGas`. Stating it as a second `simp` set is what lets a goal about
`Devm.gasMeasure` -- which unfolds to `gasLeft` plus two meter fields -- be
closed by the same single `omega` as the goals about `gasLeft` were.

Two operations are deliberately absent, because they are the two that move the
meter: `chargeStateGas` and `creditStateGasRefund`. Their measure lemmas are
below, and they are the content of the migration. -/

namespace Devm

@[simp] theorem setMach_stateGas (devm : Devm) (mach : Mach) :
    (devm.setMach mach).mach.stateGas = mach.stateGas := rfl

@[simp] theorem setMeta_stateGas (devm : Devm) (view : Meta) :
    (devm.setMeta view).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem setWorld_stateGas (devm : Devm) (world : World) :
    (devm.setWorld world).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withGasLeft_stateGas (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withStack_stateGas (devm : Devm) (stack : List B256) :
    (devm.withStack stack).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withMemory_stateGas (devm : Devm) (memory : Mem) :
    (devm.withMemory memory).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withLogs_stateGas (devm : Devm) (logs : List Log) :
    (devm.withLogs logs).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withRefundCounter_stateGas (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withReturnData_stateGas (devm : Devm) (returnData : Bytes) :
    (devm.withReturnData returnData).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withError_stateGas (devm : Devm) (error : Option SettledHalt) :
    (devm.withError error).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withCreatedAccounts_stateGas (devm : Devm) (as : AdrSet) :
    (devm.withCreatedAccounts as).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem withState_stateGas (devm : Devm) (state : State) :
    (devm.withState state).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem memWrite_stateGas (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem memExtends_stateGas (devm : Devm) (pairs : List (Nat × Nat)) :
    (devm.memExtends pairs).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem memRead_stateGas (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem addLog_stateGas (devm : Devm) (log : Log) :
    (devm.addLog log).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem setStorVal_stateGas (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setStorVal adr key val).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem setTransVal_stateGas (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setTransVal adr key val).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem incrNonce_stateGas (devm : Devm) (adr : Adr) :
    (devm.incrNonce adr).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem setCode_stateGas (devm : Devm) (adr : Adr) (code : ByteArray) :
    (devm.setCode adr code).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem rollback_stateGas (devm : Devm) (wor : State) (tra : Tra) :
    (devm.rollback wor tra).mach.stateGas = devm.mach.stateGas := rfl

end Devm

@[simp] theorem addAccessedAddress_stateGas (devm : Devm) (a : Adr) :
    (addAccessedAddress devm a).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem addAccessedStorageKey_stateGas (devm : Devm) (a : Adr)
    (k : B256) :
    (addAccessedStorageKey devm a k).mach.stateGas = devm.mach.stateGas := rfl

/-! ### The same set, for the measure

`Devm.gasMeasure` is `gasLeft + spilled + committedSpill`, so an update that
leaves both `gasLeft` and `stateGas` alone leaves the measure alone, and the two
sets above compose into this one. It is stated as its own `simp` set -- rather
than unfolding the measure at every site -- so that a proof about the measure
treats it as the single atom `gasLeft` used to be: every `omega` below sees one
number per `Devm`, not three.

`withGasLeft` is the one plain update that moves the measure, and it moves it
by exactly the change in `gasLeft`: the meter's two spill fields ride along.
That pair is named, as `Devm.spill`, because it is also what an exceptional
halt keeps -- `handleError` zeroes `gasLeft` and leaves the meter alone -- so
the same name is what the halt obligation below is stated against. -/

namespace Devm

/-- The part of the measure that is not execution gas: the meter's outstanding
and committed spill. `gasMeasure = gasLeft + spill`, and a halted frame settles
at exactly `spill`. -/
def spill (devm : Devm) : Nat :=
  devm.mach.stateGas.spilled + devm.mach.stateGas.committedSpill

theorem gasMeasure_eq (devm : Devm) : devm.gasMeasure = devm.gasLeft + devm.spill := by
  simp only [Devm.gasMeasure, Mach.gasMeasure, Devm.gasLeft, Devm.spill]
  omega

theorem gasLeft_le_gasMeasure (devm : Devm) : devm.gasLeft ≤ devm.gasMeasure := by
  rw [Devm.gasMeasure_eq]
  exact Nat.le_add_right _ _

theorem spill_le_gasMeasure (devm : Devm) : devm.spill ≤ devm.gasMeasure := by
  rw [Devm.gasMeasure_eq]
  exact Nat.le_add_left _ _

@[simp] theorem setMeta_spill (devm : Devm) (view : Meta) :
    (devm.setMeta view).spill = devm.spill := rfl

@[simp] theorem setWorld_spill (devm : Devm) (world : World) :
    (devm.setWorld world).spill = devm.spill := rfl

@[simp] theorem withGasLeft_spill (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).spill = devm.spill := rfl

@[simp] theorem withReturnData_spill (devm : Devm) (returnData : Bytes) :
    (devm.withReturnData returnData).spill = devm.spill := rfl

@[simp] theorem rollback_spill (devm : Devm) (wor : State) (tra : Tra) :
    (devm.rollback wor tra).spill = devm.spill := rfl

@[simp] theorem setMach_gasMeasure (devm : Devm) (mach : Mach) :
    (devm.setMach mach).gasMeasure = mach.gasMeasure := rfl

@[simp] theorem setMeta_gasMeasure (devm : Devm) (view : Meta) :
    (devm.setMeta view).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setWorld_gasMeasure (devm : Devm) (world : World) :
    (devm.setWorld world).gasMeasure = devm.gasMeasure := rfl

theorem withGasLeft_gasMeasure (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).gasMeasure = n + devm.spill := by
  simp only [Devm.withGasLeft, Devm.setMach, Devm.gasMeasure, Mach.gasMeasure,
    Devm.spill]
  omega

@[simp] theorem withStack_gasMeasure (devm : Devm) (stack : List B256) :
    (devm.withStack stack).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withMemory_gasMeasure (devm : Devm) (memory : Mem) :
    (devm.withMemory memory).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withLogs_gasMeasure (devm : Devm) (logs : List Log) :
    (devm.withLogs logs).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withRefundCounter_gasMeasure (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withReturnData_gasMeasure (devm : Devm) (returnData : Bytes) :
    (devm.withReturnData returnData).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withError_gasMeasure (devm : Devm) (error : Option SettledHalt) :
    (devm.withError error).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withCreatedAccounts_gasMeasure (devm : Devm) (as : AdrSet) :
    (devm.withCreatedAccounts as).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withState_gasMeasure (devm : Devm) (state : State) :
    (devm.withState state).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem memWrite_gasMeasure (devm : Devm) (idx : Nat) (val : Bytes) :
    (devm.memWrite idx val).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem memExtends_gasMeasure (devm : Devm) (pairs : List (Nat × Nat)) :
    (devm.memExtends pairs).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem memRead_gasMeasure (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.gasMeasure = devm.gasMeasure := rfl

@[simp] theorem addLog_gasMeasure (devm : Devm) (log : Log) :
    (devm.addLog log).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setStorVal_gasMeasure (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setStorVal adr key val).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setTransVal_gasMeasure (devm : Devm) (adr : Adr) (key val : B256) :
    (devm.setTransVal adr key val).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem incrNonce_gasMeasure (devm : Devm) (adr : Adr) :
    (devm.incrNonce adr).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setCode_gasMeasure (devm : Devm) (adr : Adr) (code : ByteArray) :
    (devm.setCode adr code).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem rollback_gasMeasure (devm : Devm) (wor : State) (tra : Tra) :
    (devm.rollback wor tra).gasMeasure = devm.gasMeasure := rfl

end Devm

@[simp] theorem addAccessedAddress_gasMeasure (devm : Devm) (a : Adr) :
    (addAccessedAddress devm a).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem addAccessedStorageKey_gasMeasure (devm : Devm) (a : Adr) (k : B256) :
    (addAccessedStorageKey devm a k).gasMeasure = devm.gasMeasure := rfl

/-! ### Child incorporation, on the measure

Prague's incorporation adds the child's execution gas to the parent's and leaves
the parent's meter alone, so the parent's measure grows by exactly
`child.gasLeft` -- which is at most `child.gasMeasure`. The driver only ever
needs the bound, and stating the bound is what lets the Amsterdam siblings
(`incorporateChildAmsterdam*_gasMeasure`, which conserve the pair's measure up
to a committed spill a child cannot carry) satisfy the same obligation. -/

theorem incorporateChildOnError_gasMeasure (parent child : Devm) (rd : Bytes) :
    (incorporateChildOnError parent child rd).gasMeasure =
      parent.gasMeasure + child.gasLeft := by
  simp only [incorporateChildOnError, Devm.setMach, Devm.setMeta, Devm.setWorld,
    Devm.gasMeasure, Mach.gasMeasure, Devm.gasLeft]
  omega

theorem incorporateChildOnSuccess_gasMeasure (parent child : Devm) (rd : Bytes) :
    (incorporateChildOnSuccess parent child rd).gasMeasure =
      parent.gasMeasure + child.gasLeft := by
  simp only [incorporateChildOnSuccess, Devm.setMach, Devm.setMeta, Devm.setWorld,
    Devm.gasMeasure, Mach.gasMeasure, Devm.gasLeft]
  omega

/-! ## The charging primitive

`chargeGas` is the only place an instruction body loses execution gas, and it
loses exactly the cost it was asked for; the meter is untouched, so the measure
drops by exactly that cost too. Every strict-decrease proof in the corpus
bottoms out in `chargeGas_gasMeasure`, so it is stated as an exact equation
rather than an inequality: the arithmetic of the call/create families needs to
add the charge back. -/

theorem chargeGas_gasMeasure {c : Nat} {devm devm' : Devm}
    (h : chargeGas c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  rw [chargeGas_def] at h
  by_cases hle : c ≤ devm.gasLeft
  · simp only [safeSub, if_pos hle, Except.ok.injEq] at h
    subst h
    simp only [Devm.setMach, Mach.gasMeasure, Devm.gasMeasure, Devm.gasLeft] at hle ⊢
    omega
  · exact absurd h (by simp [safeSub, if_neg hle])

/-! ## Stack primitives

Pushing and popping never touch `gasLeft` or the meter. These are the inversion
forms the instruction walks need: the hypothesis is the `.ok` equation that
survives a `split`, and the conclusion feeds `omega`. -/

theorem Devm.push_gasMeasure {x : B256} {devm devm' : Devm}
    (h : Devm.push x devm = .ok devm') : devm'.gasMeasure = devm.gasMeasure := by
  rw [Devm.push_def] at h
  unfold Except.assert at h
  split at h
  · simp only [bind, Except.bind, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp [bind, Except.bind])

theorem Devm.pop_gasMeasure {devm : Devm} {x : B256} {devm' : Devm}
    (h : devm.pop = .ok (x, devm')) : devm'.gasMeasure = devm.gasMeasure := by
  rw [Devm.pop_def] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]; rfl

theorem Devm.popToNat_gasMeasure {devm : Devm} {n : Nat} {devm' : Devm}
    (h : devm.popToNat = .ok (n, devm')) : devm'.gasMeasure = devm.gasMeasure := by
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

theorem Devm.popToAdr_gasMeasure {devm : Devm} {a : Adr} {devm' : Devm}
    (h : devm.popToAdr = .ok (a, devm')) : devm'.gasMeasure = devm.gasMeasure := by
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

theorem Devm.popN_gasMeasure {devm : Devm} {n : Nat} {xs : List B256} {devm' : Devm}
    (h : devm.popN n = .ok (xs, devm')) : devm'.gasMeasure = devm.gasMeasure := by
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
        rw [← h.2, ih (by rw [hq]), Devm.pop_gasMeasure (x := p.1) (by rw [hp])]

/-! ## Lifting a footprint-restricted core

`liftMachExecution` and its `Meta`/`World` variants only ever reattach the
core's own `Mach` to the original `Devm`, so a fact proved once about the core's
`Mach` transfers verbatim. These inversion lemmas are what let the `apply*`
family — and, in the corpus, `Rinst.balanceCore` — be handled at the `Mach`
level, where there is no `Devm` scaffolding in the way. They return the whole
`Mach` rather than one field of it, so that both the measure and, where a site
needs it, the meter can be read off the same witness. -/

theorem liftMachExecution_ok {core : Mach → Footprint.Outcome Mach Unit}
    {devm devm' : Devm} (h : liftMachExecution core devm = .ok devm') :
    ∃ u mach', core devm.mach = .ok (u, mach') ∧ devm'.mach = mach' := by
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
      devm'.mach = view'.1 := by
  unfold liftMachMetaExecution liftMachMeta Footprint.toExecution
    Footprint.liftOutcome at h
  rcases hc : core devm.mach devm.meta with ⟨err, view⟩ | ⟨u, view'⟩ <;>
    simp only [hc] at h
  · exact absurd h (by simp)
  · refine ⟨u, view', rfl, ?_⟩
    simp only [Except.ok.injEq] at h
    rw [← h]

theorem liftMachMetaWorldExecution_ok
    {core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit}
    {devm devm' : Devm} (h : liftMachMetaWorldExecution core devm = .ok devm') :
    ∃ u view', core devm.world devm.mach devm.meta = .ok (u, view') ∧
      devm'.mach = view'.1 :=
  liftMachMetaExecution_ok h

/-! ## The `Mach`-level charging and stack layer

The `apply*` family is defined by `liftMachExecution` over a `Mach`-only core
with no intervening `_def` lemma for the ternary case, so its accounting is
proved here rather than at `Devm` level. The charge itself is
`Mach.chargeGas_gasMeasure`, stated beside the meter in `Jaune/Machine.lean`
with the rest of the meter operations' measure lemmas. -/

namespace Mach

theorem pop_gasMeasure {mach mach' : Mach} {x : B256}
    (h : mach.pop = .ok (x, mach')) : mach'.gasMeasure = mach.gasMeasure := by
  unfold Mach.pop at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl

theorem push_gasMeasure {x : B256} {mach mach' : Mach} {u : Unit}
    (h : Mach.push x mach = .ok (u, mach')) : mach'.gasMeasure = mach.gasMeasure := by
  unfold Mach.push at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl
  · exact absurd h (by simp)

theorem pushItem_gasMeasure {x : B256} {c : Nat} {mach mach' : Mach} {u : Unit}
    (h : Mach.pushItem x c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.pushItem at h
  rcases hc : Mach.chargeGas c mach with ⟨err, m⟩ | ⟨uc, m1⟩ <;> simp only [hc] at h
  · exact absurd h (by simp)
  · rw [push_gasMeasure h, ← Mach.chargeGas_gasMeasure hc]

theorem applyUnary_gasMeasure {f : B256 → B256} {c : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.applyUnary f c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.applyUnary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rw [pushItem_gasMeasure h, pop_gasMeasure hp]

theorem applyBinary_gasMeasure {f : B256 → B256 → B256} {c : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.applyBinary f c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.applyBinary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rcases hq : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> simp only [hq] at h
    · exact absurd h (by simp)
    · rw [pushItem_gasMeasure h, pop_gasMeasure hq, pop_gasMeasure hp]

theorem applyTernary_gasMeasure {f : B256 → B256 → B256 → B256} {c : Nat}
    {mach mach' : Mach} {u : Unit}
    (h : Mach.applyTernary f c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.applyTernary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rcases hq : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> simp only [hq] at h
    · exact absurd h (by simp)
    · rcases hr : m2.pop with ⟨err, m⟩ | ⟨z, m3⟩ <;> simp only [hr] at h
      · exact absurd h (by simp)
      · rw [pushItem_gasMeasure h, pop_gasMeasure hr, pop_gasMeasure hq, pop_gasMeasure hp]

end Mach

/-! ## The instruction-level combinators

These four cover every `Rinst` constructor whose body is a bare
`pushItem`/`apply*` call, and they are the last step of the walk for many of
the rest. Each is stated as an exact equation in the charge, so a caller that
needs strictness supplies `0 < c` and finishes with `omega`. -/

theorem pushItem_gasMeasure {x : B256} {c : Nat} {devm devm' : Devm}
    (h : pushItem x c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.pushItem_gasMeasure hcore]

theorem applyUnary_gasMeasure {f : B256 → B256} {c : Nat} {devm devm' : Devm}
    (h : applyUnary f c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.applyUnary_gasMeasure hcore]

theorem applyBinary_gasMeasure {f : B256 → B256 → B256} {c : Nat} {devm devm' : Devm}
    (h : applyBinary f c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.applyBinary_gasMeasure hcore]

theorem applyTernary_gasMeasure {f : B256 → B256 → B256 → B256} {c : Nat}
    {devm devm' : Devm} (h : applyTernary f c devm = .ok devm') :
    devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.applyTernary_gasMeasure hcore]

/-! ## The meter operations, at the frame

The Amsterdam `SSTORE` arm is the first site that touches the meter: it credits
a refund and charges state gas beside its execution charge. Both are
measure-neutral (`Jaune/Machine.lean` proves it on `Mach`); these are the
`Devm`-level forms the walks consume, in the same shapes as the primitives
above. -/

theorem chargeGas_gasMeasure_lt {c : Nat} {devm devm' : Devm} (hc : 0 < c)
    (h : chargeGas c devm = .ok devm') : devm'.gasMeasure < devm.gasMeasure := by
  have e := chargeGas_gasMeasure h
  omega

theorem chargeStateGas_gasMeasure {amount : Nat} {devm devm' : Devm}
    (h : chargeStateGas amount devm = .ok devm') :
    devm'.gasMeasure = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure = devm.mach.gasMeasure
  rw [hmach, Mach.chargeStateGas_gasMeasure hcore]

@[simp] theorem Devm.creditStateGasRefund_gasMeasure (amount : Nat) (devm : Devm) :
    (devm.creditStateGasRefund amount).gasMeasure = devm.gasMeasure :=
  Mach.creditStateGasRefund_gasMeasure amount devm.mach

@[simp] theorem Devm.withholdCreateGas_gasMeasure (devm : Devm) :
    devm.withholdCreateGas.2.gasMeasure + devm.withholdCreateGas.1 =
      devm.gasMeasure := by
  change devm.mach.withholdCreateGas.2.gasMeasure +
      devm.mach.withholdCreateGas.1 = devm.mach.gasMeasure
  exact Mach.withholdCreateGas_gasMeasure devm.mach

@[simp] theorem Devm.drainStateGasReservoir_gasMeasure (devm : Devm) :
    devm.drainStateGasReservoir.2.gasMeasure = devm.gasMeasure := by
  change devm.mach.drainStateGasReservoir.2.gasMeasure = devm.mach.gasMeasure
  exact Mach.drainStateGasReservoir_gasMeasure devm.mach

@[simp] theorem Devm.restoreChildGas_gasMeasure (gas reservoir : Nat)
    (devm : Devm) :
    (devm.restoreChildGas gas reservoir).gasMeasure = devm.gasMeasure + gas := by
  change (devm.mach.restoreChildGas gas reservoir).gasMeasure =
    devm.mach.gasMeasure + gas
  exact Mach.restoreChildGas_gasMeasure gas reservoir devm.mach

@[simp] theorem Devm.restoreStateGas_gasMeasure (devm : Devm) :
    devm.restoreStateGas.gasMeasure = devm.gasMeasure := by
  change devm.mach.restoreStateGas.gasMeasure = devm.mach.gasMeasure
  exact Mach.restoreStateGas_gasMeasure devm.mach

theorem Devm.forfeitRemainingGas_gasMeasure_le (devm : Devm) :
    devm.forfeitRemainingGas.gasMeasure ≤ devm.gasMeasure := by
  change devm.mach.forfeitRemainingGas.gasMeasure ≤ devm.mach.gasMeasure
  exact Mach.forfeitRemainingGas_gasMeasure_le devm.mach

theorem Devm.restoreStateGas_forfeitRemainingGas_gasMeasure_le_spill (devm : Devm) :
    devm.restoreStateGas.forfeitRemainingGas.gasMeasure ≤ devm.spill := by
  simp only [Devm.restoreStateGas, Devm.forfeitRemainingGas, Devm.setMach,
    Devm.withRefundCounter, Devm.setMeta, Devm.gasMeasure, Mach.gasMeasure,
    Mach.restoreStateGas, Mach.forfeitRemainingGas, Devm.spill]
  omega

/-- The `SSTORE` arms warm the slot only when it is cold, and the walks meet
that as an `if` around one `Devm`; either way the measure is untouched. -/
@[simp] theorem Devm.ite_addAccessedStorageKey_gasMeasure {c : Prop} [Decidable c]
    (devm : Devm) (a : Adr) (k : B256) :
    (if c then addAccessedStorageKey devm a k else devm).gasMeasure
      = devm.gasMeasure := by
  split <;> simp

@[simp] theorem Devm.ite_addAccessedStorageKey_gasMeasure' {c : Prop} [Decidable c]
    (devm : Devm) (a : Adr) (k : B256) :
    (if c then devm else addAccessedStorageKey devm a k).gasMeasure
      = devm.gasMeasure := by
  split <;> simp

/-- Amsterdam's `SSTORE` execution charge is at least the warm access, so the
arm still decreases the measure whatever the slot's history. -/
theorem sstoreAmsterdamGasCost_pos (state : StateGasRules)
    (new_value original_value current_value : B256) (cold : Bool) :
    0 < sstoreAmsterdamGasCost state new_value original_value current_value cold := by
  unfold sstoreAmsterdamGasCost gasColdSload gasWarmAccess
  split <;> split <;> omega

/-! ## Walking an instruction body

Every instruction body is a `do` chain in `Except (EvmError × Devm)`. Peeling one
`bind` at a time with `Except.bind_eq_ok` -- declared in `Jaune/Machine.lean`,
where the strict field decoders invert the same way -- is what keeps the walks
free of the fragile `split`-and-`rename_i` idiom: the scrutinee never has to be
written out, so a cost expression can be arbitrarily large without the proof
mentioning it. -/

theorem Except.assert_eq_ok {p : Prop} [Decidable p] {ε : Type} {e : ε} {u : Unit}
    (h : Except.assert p e = .ok u) : p := by
  unfold Except.assert at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-! ## Resume accounting

A `Resume` succeeds only by incorporating a child that itself succeeded, and it
hands the parent back at most `parent.gasMeasure + child.gasMeasure` -- Prague's
incorporation adds exactly the child's `gasLeft`, and Amsterdam's conserves the
pair's measure up to the committed spill a child cannot carry. Isolating that
here is what collapses the three spawn-shaped obligations of the driver into
the single arithmetic fact `frame.inner.gas + rsm.parentGas < gasMeasure`: the
child's own budget is `frame.inner.gas` (a fresh frame carries no spill, so its
measure is its grant) and never grows, and the parent's retained measure is
`rsm.parentGas`. -/

/-- The measure a `Resume` retains for the parent, before the child's leftover
is added back. -/
def Resume.parentGas : Resume → Nat
  | .create parent _ => parent.gasMeasure
  | .call parent _ _ => parent.gasMeasure
  | .createAmsterdam _ parent _ _ => parent.gasMeasure
  | .callAmsterdam _ parent _ _ _ => parent.gasMeasure

theorem Resume.run_ok_gasMeasure {rsm : Resume}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {devm' : Devm}
    (h : rsm.run r = .ok devm') :
    ∃ child : Devm, r = .ok child ∧
      devm'.gasMeasure ≤ rsm.parentGas + child.gasMeasure := by
  cases rsm with
  | create parent newAddress =>
    cases r with
    | error e => exact absurd h (by simp [Resume.run, liftToExecution, bind, Except.bind])
    | ok child =>
      refine ⟨child, rfl, ?_⟩
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      have hc := Devm.gasLeft_le_gasMeasure child
      split at h
      · rw [Devm.push_gasMeasure h, incorporateChildOnError_gasMeasure]
        simp only [Resume.parentGas]
        omega
      · rw [Devm.push_gasMeasure h, incorporateChildOnSuccess_gasMeasure]
        simp only [Resume.parentGas]
        omega
  | call parent outputIndex outputSize =>
    cases r with
    | error e => exact absurd h (by simp [Resume.run, liftToExecution, bind, Except.bind])
    | ok child =>
      refine ⟨child, rfl, ?_⟩
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      have hc := Devm.gasLeft_le_gasMeasure child
      split at h
      · rcases hp : (incorporateChildOnError parent child child.output).push 0 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.memWrite_gasMeasure, Devm.push_gasMeasure hp,
            incorporateChildOnError_gasMeasure]
          simp only [Resume.parentGas]
          omega
      · rcases hp : (incorporateChildOnSuccess parent child child.output).push 1 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.memWrite_gasMeasure, Devm.push_gasMeasure hp,
            incorporateChildOnSuccess_gasMeasure]
          simp only [Resume.parentGas]
          omega
  | createAmsterdam state parent newAddress newAccountCharged =>
    cases r with
    | error e => exact absurd h (by simp [Resume.run, liftToExecution, bind, Except.bind])
    | ok child =>
      refine ⟨child, rfl, ?_⟩
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      split at h
      · have hsettled : child.AmsterdamFailedChildSettled := by
          by_contra hn
          simp [Except.assert, hn] at h
        simp only [Except.assert, if_pos hsettled] at h
        rcases hp :
          (if newAccountCharged then
              (incorporateChildAmsterdamOnError parent child child.output).creditStateGasRefund
                state.newAccount
            else incorporateChildAmsterdamOnError parent child child.output).push 0 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.push_gasMeasure hp]
          simp only [Resume.parentGas]
          have he := incorporateChildAmsterdamOnError_gasMeasure_of_child_settled
            (parent := parent) (child := child) (rd := child.output) hsettled
          split <;> simp_all only [Devm.creditStateGasRefund_gasMeasure] <;> omega
      · have huncommitted : child.AmsterdamChildUncommitted := by
          by_contra hn
          simp [Except.assert, hn] at h
        simp only [Except.assert, if_pos huncommitted] at h
        rw [Devm.push_gasMeasure h]
        simp only [Resume.parentGas]
        have he := incorporateChildAmsterdamOnSuccess_gasMeasure_of_child_uncommitted
          (parent := parent) (child := child) (rd := []) huncommitted
        omega
  | callAmsterdam state parent outputIndex outputSize newAccountCharged =>
    cases r with
    | error e => exact absurd h (by simp [Resume.run, liftToExecution, bind, Except.bind])
    | ok child =>
      refine ⟨child, rfl, ?_⟩
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      split at h
      · have hsettled : child.AmsterdamFailedChildSettled := by
          by_contra hn
          simp [Except.assert, hn] at h
        simp only [Except.assert, if_pos hsettled] at h
        rcases hp :
          (if newAccountCharged then
              (incorporateChildAmsterdamOnError parent child child.output).creditStateGasRefund
                state.newAccount
            else incorporateChildAmsterdamOnError parent child child.output).push 0 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.memWrite_gasMeasure, Devm.push_gasMeasure hp]
          simp only [Resume.parentGas]
          have he := incorporateChildAmsterdamOnError_gasMeasure_of_child_settled
            (parent := parent) (child := child) (rd := child.output) hsettled
          split <;> simp_all only [Devm.creditStateGasRefund_gasMeasure] <;> omega
      · have huncommitted : child.AmsterdamChildUncommitted := by
          by_contra hn
          simp [Except.assert, hn] at h
        simp only [Except.assert, if_pos huncommitted] at h
        rcases hp :
          (incorporateChildAmsterdamOnSuccess parent child child.output).push 1 with
          ⟨e⟩ | ⟨d⟩ <;> simp only [hp] at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq] at h
          rw [← h, Devm.memWrite_gasMeasure, Devm.push_gasMeasure hp]
          simp only [Resume.parentGas]
          have he := incorporateChildAmsterdamOnSuccess_gasMeasure_of_child_uncommitted
            (parent := parent) (child := child) (rd := child.output) huncommitted
          omega

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

/-! ### The same two facts, of the schedule the interpreter reads

The two lemmas above are about `accessCost`, which is Prague's function and
stays exactly that -- Blanc names it 121 times. The interpreter now reads
`rules.gas.accessCost`, whose cold half is whatever the fork's schedule says,
so the same two facts have to be available of an arbitrary schedule. That is
what `GasSchedule.Valid` buys, and it is the only thing the family asks of a
schedule it did not choose. -/

theorem GasSchedule.access_cost_pos {gas : GasSchedule} (hv : gas.Valid)
    (x : Adr) (a : AdrSet) : 0 < gas.accessCost x a :=
  hv.accessCost_pos x a

theorem GasSchedule.gasWarmAccess_le_access_cost {gas : GasSchedule}
    (hv : gas.Valid) (x : Adr) (a : AdrSet) :
    gasWarmAccess ≤ gas.accessCost x a :=
  hv.warmAccess_le_accessCost x a

theorem calculateMsgCallGas_stipend_lt
    {value gas gasLeft memoryCost extraGas cs : Nat}
    (hstip : (if value = 0 then 0 else cs) < extraGas + memoryCost) :
    (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).2 <
      (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).1 + memoryCost := by
  unfold calculateMsgCallGas
  split <;> split <;> simp_all <;> omega

theorem calculateMsgCallGas_zero_cost
    (value gas gasLeft cs : Nat) :
    (calculateMsgCallGas value gas gasLeft 0 0 cs).2 =
      (calculateMsgCallGas value gas gasLeft 0 0 cs).1 +
        (if value = 0 then 0 else cs) := by
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

@[simp] theorem accessDelegation_gasMeasure (devm : Devm) (adr : Adr) :
    (accessDelegation devm adr).2.2.2.2.gasMeasure = devm.gasMeasure := by
  unfold accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_gasMeasure]

@[simp] theorem accessDelegation_stateGas (devm : Devm) (adr : Adr) :
    (accessDelegation devm adr).2.2.2.2.mach.stateGas = devm.mach.stateGas := by
  unfold accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_stateGas]

@[simp] theorem GasSchedule.accessDelegation_gasMeasure
    (gas : GasSchedule) (devm : Devm) (adr : Adr) :
    (gas.accessDelegation devm adr).2.2.2.2.gasMeasure = devm.gasMeasure := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_gasMeasure]

@[simp] theorem GasSchedule.accessDelegation_stateGas
    (gas : GasSchedule) (devm : Devm) (adr : Adr) :
    (gas.accessDelegation devm adr).2.2.2.2.mach.stateGas = devm.mach.stateGas := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_stateGas]

@[simp] theorem completeDelegationAccess_gasMeasure
    (devm : Devm) (delegated : Bool) (adr : Adr) :
    (completeDelegationAccess devm delegated adr).2.gasMeasure =
      devm.gasMeasure := by
  unfold completeDelegationAccess
  dsimp only
  split <;> simp only [addAccessedAddress_gasMeasure]

@[simp] theorem completeDelegationAccess_stateGas
    (devm : Devm) (delegated : Bool) (adr : Adr) :
    (completeDelegationAccess devm delegated adr).2.mach.stateGas =
      devm.mach.stateGas := by
  unfold completeDelegationAccess
  dsimp only
  split <;> simp only [addAccessedAddress_stateGas]

/-- The step-level obligation for a call-type instruction, measured against the
frame's gas at the start of the step.

The spawn case is the design decision that keeps the corpus small: rather than
three separate obligations (child budget, resume-after-`done`,
resume-after-child) it asserts the single arithmetic fact
`frame.inner.gas + rsm.parentGas < n`. The other three follow from it
generically, because `Frame.enter` hands the child exactly `frame.inner.gas`,
neither the child nor `Frame.settle` can increase that, and `Resume.run`
returns `rsm.parentGas + child.gasMeasure` (`Resume.run_ok_gasMeasure`). -/
def XStep.GasDecreasing (sevm : Sevm) (n : Nat) : XStep → Prop
  | .done ex => ∀ devm', ex = .ok devm' → devm'.gasMeasure < n
  | .spawn frame rsm =>
      frame.inner.gas + rsm.parentGas < n ∧
        frame.inner.benv.stat.rules = sevm.benvStat.rules

theorem XStep.ofExcept_gasDecreasing {sevm : Sevm} {n : Nat}
    {x : Except (EvmError × Devm) XStep}
    (h : ∀ step, x = .ok step → step.GasDecreasing sevm n) :
    (XStep.ofExcept x).GasDecreasing sevm n := by
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
    (hn : devm.gasMeasure + gas < n) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).GasDecreasing sevm n := by
  unfold genericCall.step
  split
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨d1, p1, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure p1]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_gasLeft,
      Devm.withReturnData_spill]
    have hm := Devm.gasMeasure_eq devm
    omega
  · -- The spawn owes two things now: the arithmetic, and that the child runs
    -- under the spawning frame's rules -- which holds by construction, since
    -- `callMsg` copies `sevm.benvStat` verbatim.
    refine ⟨?_, rfl⟩
    show (Frame.ofCall _).inner.gas + Resume.parentGas _ < n
    simp only [Frame.ofCall, callMsg, Resume.parentGas, Devm.withReturnData_gasMeasure]
    omega

theorem genericCallAmsterdam.step_gasDecreasing
    (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) {n : Nat}
    (hn : devm.gasMeasure + gas < n) :
    (genericCallAmsterdam.step sevm state devm gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize
      outputIndex outputSize code disablePrecompiles newAccountCharged
      insufficientBalance).GasDecreasing sevm n := by
  unfold genericCallAmsterdam.step
  split
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨d1, p1, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure p1]
    split <;>
      simp only [Devm.withReturnData_gasMeasure, Devm.restoreChildGas_gasMeasure,
        Devm.creditStateGasRefund_gasMeasure] <;>
      omega
  · refine ⟨?_, rfl⟩
    show (Frame.ofCall _).inner.gas + Resume.parentGas _ < n
    simp only [Frame.ofCall, callMsg, Resume.parentGas,
      Devm.withReturnData_gasMeasure]
    omega

/-- The shared tail of every call-type instruction. Once the parent has been
charged `cost + memoryCost` for a call whose stipend that charge strictly
covers, whatever the parent keeps plus the stipend it hands over is still
strictly below where the parent started. Both refund branches and the spawn
itself consume exactly this. -/
theorem call_charge_stipend_lt
    {value gas gasLeft memoryCost extraGas cs : Nat} {devm d d' : Devm}
    (hstip : (if value = 0 then 0 else cs) < extraGas + memoryCost)
    (hd : d.gasMeasure = devm.gasMeasure)
    (hcharge : chargeGas
        ((calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).1 + memoryCost)
        d = .ok d') :
    d'.gasMeasure + (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).2
      < devm.gasMeasure := by
  have e := chargeGas_gasMeasure hcharge
  have s := calculateMsgCallGas_stipend_lt (value := value) (gas := gas)
    (gasLeft := gasLeft) (memoryCost := memoryCost) (extraGas := extraGas)
    (cs := cs) hstip
  omega

theorem Xinst.step_call_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (Xinst.step sevm devm .call).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step, hstate]
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
  have e1 := Devm.pop_gasMeasure p1
  have e2 := Devm.popToAdr_gasMeasure p2
  have e3 := Devm.pop_gasMeasure p3
  have e4 := Devm.popToNat_gasMeasure p4
  have e5 := Devm.popToNat_gasMeasure p5
  have e6 := Devm.popToNat_gasMeasure p6
  have e7 := Devm.popToNat_gasMeasure p7
  dsimp only at e2 e3 e4 e5 e6 e7
  -- The delegation lookup can warm one more address but never touches gas.
  have eA : (sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress d7 callee) callee).2.2.2.2.gasMeasure = devm.gasMeasure := by
    rw [GasSchedule.accessDelegation_gasMeasure, addAccessedAddress_gasMeasure]
    omega
  -- `extra_gas` strictly covers the stipend: a warm access alone costs 100, and
  -- a value-bearing call pays `gasCallValue` against a `gCallStipend` stipend.
  have hstip :
      (if value.toNat = 0 then 0 else gCallStipend) <
        ((sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
              (sevm.benvStat.rules.gas.accessDelegation
                (addAccessedAddress d7 callee) callee).2.2.2.1 +
            if ¬((sevm.benvStat.rules.gas.accessDelegation
                    (addAccessedAddress d7 callee) callee).2.2.2.2.getAcct
                    callee).Empty ∨ value = 0 then 0 else gNewAccount) +
          if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
        d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    have hac := GasSchedule.access_cost_pos hv.gas callee d7.accessedAddresses
    have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
    by_cases hv : value = 0
    · have : value.toNat = 0 := by rw [hv]; rfl
      rw [if_pos this]
      omega
    · rw [if_neg hv]
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
    rw [← hd]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_spill]
    rw [Nat.add_right_comm, ← Devm.gasMeasure_eq, Devm.push_gasMeasure ppush,
      Devm.memExtends_gasMeasure]
    exact key
  · -- The spawn: the child's whole budget is the stipend.
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCall.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure]
    exact key

theorem Xinst.step_call_gasDecreasing (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm .call).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step]
  split
  · simpa only [Xinst.step, *] using
      Xinst.step_call_gasDecreasing_legacy sevm devm hv (by assumption)
  · rename_i state hstate
    apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨callee, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hstatic, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.pop_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    have e7 := Devm.popToNat_gasMeasure p7
    dsimp only at e1 e2 e3 e4 e5 e6 e7
    have eA :
        (completeDelegationAccess (addAccessedAddress d7 callee)
          (sevm.benvStat.rules.gas.delegationCost
            (addAccessedAddress d7 callee) callee).1
          (sevm.benvStat.rules.gas.delegationCost
            (addAccessedAddress d7 callee) callee).2.1).2.gasMeasure =
          devm.gasMeasure := by
      rw [completeDelegationAccess_gasMeasure, addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if value.toNat = 0 then 0 else gCallStipend) <
          (sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
              (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 callee) callee).2.2) +
            d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      have hac := GasSchedule.access_cost_pos hv.gas callee d7.accessedAddresses
      have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
      by_cases hvalue : value = 0
      · have : value.toNat = 0 := by rw [hvalue]; rfl
        rw [if_pos this, if_pos hvalue]
        omega
      · have hto : value.toNat ≠ 0 := by
          intro hz
          exact hvalue (B256.toNat_inj value 0 (by rw [hz, B256.toNat_zero]))
        rw [if_neg hto, if_neg hvalue]
        omega
    have echarge := chargeGas_gasMeasure pcharge
    dsimp only at echarge hstep
    have hchargeCost :
        d8.gasMeasure +
            ((sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
                (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
                (sevm.benvStat.rules.gas.delegationCost
                  (addAccessedAddress d7 callee) callee).2.2) +
              d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) =
          devm.gasMeasure := by
      calc
        _ = (completeDelegationAccess (addAccessedAddress d7 callee)
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 callee) callee).1
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 callee) callee).2.1).2.gasMeasure := echarge
        _ = devm.gasMeasure := eA
    have hpaid :
        d8.gasMeasure + (if value.toNat = 0 then 0 else gCallStipend) <
          devm.gasMeasure := by
      calc
        _ < d8.gasMeasure +
              ((sevm.benvStat.rules.gas.accessCost callee d7.accessedAddresses +
                  (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
                  (sevm.benvStat.rules.gas.delegationCost
                    (addAccessedAddress d7 callee) callee).2.2) +
                d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) :=
            Nat.add_lt_add_left hstip _
        _ = devm.gasMeasure := hchargeCost
    split at hstep
    · obtain ⟨d9, pstate, hstep⟩ := Except.bind_eq_ok hstep
      obtain ⟨d10, pcall, hstep⟩ := Except.bind_eq_ok hstep
      have estate := chargeStateGas_gasMeasure pstate
      have ecall := chargeGas_gasMeasure pcall
      have hcalc := calculateMsgCallGas_zero_cost value.toNat gas.toNat d9.gasLeft
        gCallStipend
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCallAmsterdam.step_gasDecreasing
      rw [Devm.memExtends_gasMeasure,
        Devm.drainStateGasReservoir_gasMeasure]
      omega
    · simp only [bind, Except.bind] at hstep
      obtain ⟨d9, pcall, hstep⟩ := Except.bind_eq_ok hstep
      have ecall := chargeGas_gasMeasure pcall
      have hcalc := calculateMsgCallGas_zero_cost value.toNat gas.toNat d8.gasLeft
        gCallStipend
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      apply genericCallAmsterdam.step_gasDecreasing
      rw [Devm.memExtends_gasMeasure,
        Devm.drainStateGasReservoir_gasMeasure]
      omega

theorem Rinst.runCore_mstore_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm} (h : Rinst.runCore pc devm sevm .mstore = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  simp only [Rinst.runCore] at h
  obtain ⟨⟨start_index, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
  dsimp only at h h1 h2 h3
  simp only [Except.ok.injEq] at h
  have e1 := Devm.popToNat_gasMeasure h1
  have e2 := Devm.pop_gasMeasure h2
  have e3 := chargeGas_gasMeasure h3
  rw [← h, Devm.memWrite_gasMeasure]
  unfold gVerylow at e3
  omega

theorem Rinst.runCore_extcodesize_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm} (hv : sevm.benvStat.rules.Valid)
    (h : Rinst.runCore pc devm sevm .extcodesize = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  simp only [Rinst.runCore] at h
  obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  dsimp only at h h1
  have e1 := Devm.popToAdr_gasMeasure h1
  -- The charge sits inside the warm/cold `if`, and the elaborator pushed the
  -- continuation into both arms; both charge a positive constant, and the cold
  -- arm's `addAccessedAddress` preserves gas.
  split at h
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasMeasure h2
    have e3 := Devm.push_gasMeasure h3
    unfold gasWarmAccess at e2
    omega
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasMeasure h2
    rw [addAccessedAddress_gasMeasure] at e2
    have e3 := Devm.push_gasMeasure h3
    -- The cold half is now whatever the fork's schedule says, so positivity
    -- comes from `Valid` rather than from a literal.
    have hc := hv.gas.warmAccess_le
    unfold gasWarmAccess at hc
    omega

theorem Jinst.runCore_jumpdest_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {pc' : Nat} {devm' : Devm}
    (h : Jinst.runCore pc devm sevm .jumpdest = .ok (pc', devm')) :
    devm'.gasMeasure < devm.gasMeasure := by
  simp only [Jinst.runCore] at h
  obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  have e1 := chargeGas_gasMeasure h1
  unfold gJumpdest at e1
  rw [← h.2]
  omega

/-! ## Strict-decrease corpus: reusable short walks -/

theorem pushItem_gasLt {x : B256} {c : Nat} {devm devm' : Devm}
    (hc : 0 < c) (h : pushItem x c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := pushItem_gasMeasure h
  omega

theorem applyUnary_gasLt {f : B256 → B256} {c : Nat} {devm devm' : Devm}
    (hc : 0 < c) (h : applyUnary f c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := applyUnary_gasMeasure h
  omega

theorem applyBinary_gasLt {f : B256 → B256 → B256} {c : Nat}
    {devm devm' : Devm} (hc : 0 < c)
    (h : applyBinary f c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := applyBinary_gasMeasure h
  omega

theorem applyTernary_gasLt {f : B256 → B256 → B256 → B256} {c : Nat}
    {devm devm' : Devm} (hc : 0 < c)
    (h : applyTernary f c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := applyTernary_gasMeasure h
  omega

theorem popChargePush_gasLt (pre : Devm)
    (cost : B256 → Devm → Nat) (value : B256 → Devm → B256)
    (hpos : ∀ x d, 0 < cost x d) {post : Devm}
    (h : (do
      let ⟨x, d⟩ ← pre.pop
      let d' ← chargeGas (cost x d) d
      d'.push (value x d')) = .ok post) :
    post.gasMeasure < pre.gasMeasure := by
  obtain ⟨⟨x, d⟩, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨d', hc, hpush⟩ := Except.bind_eq_ok h
  have ep := Devm.pop_gasMeasure hp
  have ec := chargeGas_gasMeasure hc
  have eq := Devm.push_gasMeasure hpush
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
    post.gasMeasure < pre.gasMeasure := by
  obtain ⟨⟨x, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨y, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  have e1 := Devm.pop_gasMeasure h1
  have e2 := Devm.pop_gasMeasure h2
  have e3 := chargeGas_gasMeasure h3
  have e4 := Devm.push_gasMeasure h4
  have hp := hpos x y d2
  omega

theorem popNat3ChargePure_gasLt (pre : Devm)
    (cost : Nat → Nat → Nat → Devm → Nat)
    (next : Nat → Nat → Nat → Devm → Devm)
    (hpos : ∀ x y z d, 0 < cost x y z d) {post : Devm}
    (hnext : ∀ x y z d, (next x y z d).gasMeasure = d.gasMeasure)
    (h : (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.popToNat
      let ⟨z, d⟩ ← d.popToNat
      let d' ← chargeGas (cost x y z d) d
      .ok (next x y z d')) = .ok post) :
    post.gasMeasure < pre.gasMeasure := by
  obtain ⟨⟨x, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨y, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨z, d3⟩, h3, h⟩ := Except.bind_eq_ok h
  obtain ⟨d4, h4, h5⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq] at h5
  have e1 := Devm.popToNat_gasMeasure h1
  have e2 := Devm.popToNat_gasMeasure h2
  have e3 := Devm.popToNat_gasMeasure h3
  have e4 := chargeGas_gasMeasure h4
  have ep := hpos x y z d3
  rw [← h5, hnext]
  omega

theorem popNatPopChargePure_gasLt (pre : Devm)
    (cost : Nat → B256 → Devm → Nat)
    (next : Nat → B256 → Devm → Devm)
    (hpos : ∀ x y d, 0 < cost x y d) {post : Devm}
    (hnext : ∀ x y d, (next x y d).gasMeasure = d.gasMeasure)
    (h : (do
      let ⟨x, d⟩ ← pre.popToNat
      let ⟨y, d⟩ ← d.pop
      let d' ← chargeGas (cost x y d) d
      .ok (next x y d')) = .ok post) :
    post.gasMeasure < pre.gasMeasure := by
  obtain ⟨⟨x, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨y, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq] at h4
  have e1 := Devm.popToNat_gasMeasure h1
  have e2 := Devm.pop_gasMeasure h2
  have e3 := chargeGas_gasMeasure h3
  have ep := hpos x y d2
  rw [← h4, hnext]
  omega

theorem Rinst.balance_runCore_gasLt {pc : Nat} {devm devm' : Devm}
    {sevm : Sevm} (hvalid : sevm.benvStat.rules.Valid)
    (h : Rinst.runCore pc devm sevm .balance = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
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
          have ep := Mach.pop_gasMeasure hp
          have ec := Mach.chargeGas_gasMeasure hc
          have eq := Mach.push_gasMeasure hpush
          have hv : view'.1.gasMeasure = mach3.gasMeasure :=
            congrArg Mach.gasMeasure (congrArg Prod.fst hcore.2).symm
          show devm'.mach.gasMeasure < devm.mach.gasMeasure
          rw [hout, hv]
          unfold gasWarmAccess at ec
          omega
    · simp only [hw, if_false] at hcore
      cases hc : Mach.chargeGas sevm.benvStat.rules.gas.coldAccountAccess
          mach1 with
      | error e => simp [hc] at hcore
      | ok p =>
        rcases p with ⟨u2, mach2⟩
        simp only [hc] at hcore
        cases hpush : Mach.push (devm.world.state.get x.toAdr).bal mach2 with
        | error e => simp [hpush] at hcore
        | ok p =>
          rcases p with ⟨u3, mach3⟩
          simp only [hpush, Except.ok.injEq, Prod.mk.injEq] at hcore
          have ep := Mach.pop_gasMeasure hp
          have ec := Mach.chargeGas_gasMeasure hc
          have eq := Mach.push_gasMeasure hpush
          have hv : view'.1.gasMeasure = mach3.gasMeasure :=
            congrArg Mach.gasMeasure (congrArg Prod.fst hcore.2).symm
          show devm'.mach.gasMeasure < devm.mach.gasMeasure
          rw [hout, hv]
          have hcold := hvalid.gas.warmAccess_le
          unfold gasWarmAccess at hcold
          omega

theorem popAdrAccessChargePush_gasLt (pre : Devm) {gas : GasSchedule}
    (hv : gas.Valid)
    (value : Adr → Devm → B256) {post : Devm}
    (h : (do
      let ⟨adr, d⟩ ← pre.popToAdr
      let d' ←
        if adr ∈ d.accessedAddresses then chargeGas gasWarmAccess d
        else chargeGas gas.coldAccountAccess (addAccessedAddress d adr)
      d'.push (value adr d')) = .ok post) :
    post.gasMeasure < pre.gasMeasure := by
  obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  have e1 := Devm.popToAdr_gasMeasure h1
  dsimp only at h e1
  split at h
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasMeasure h2
    have e3 := Devm.push_gasMeasure h3
    unfold gasWarmAccess at e2
    omega
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasMeasure h2
    rw [addAccessedAddress_gasMeasure] at e2
    have e3 := Devm.push_gasMeasure h3
    have hc := hv.warmAccess_le
    unfold gasWarmAccess at hc
    omega

theorem Rinst.runCore_gasLt (pc : Nat) (devm : Devm) (sevm : Sevm)
    (r : Rinst) {devm' : Devm} (hv : sevm.benvStat.rules.Valid)
    (h : Rinst.runCore pc devm sevm r = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
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
  case keccak256 =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := chargeGas_gasMeasure h3
    have e4 := Devm.push_gasMeasure h4
    dsimp only at e1 e2 e3 e4
    rw [Devm.memRead_gasMeasure] at e4
    unfold gKeccak256 at e3
    omega
  case balance =>
    apply Rinst.balance_runCore_gasLt (pc := pc) (sevm := sevm) hv
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
      (by intros; simp only [Devm.memWrite_gasMeasure]) h
  case returndatacopy =>
    obtain ⟨⟨memoryStart, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨returnStart, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d3⟩, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := chargeGas_gasMeasure h4
    dsimp only at h e1 e2 e3 e4
    split at h
    · nomatch h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.memWrite_gasMeasure]
      unfold gVerylow at e4
      omega
  case extcodecopy =>
    obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨memoryStart, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨codeStart, d3⟩, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d4⟩, h4, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToAdr_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := Devm.popToNat_gasMeasure h4
    dsimp only at h e1 e2 e3 e4
    split at h
    · obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h6
      have e5 := chargeGas_gasMeasure h5
      rw [← h6, Devm.memWrite_gasMeasure]
      unfold gasWarmAccess at e5
      omega
    · obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h6
      have e5 := chargeGas_gasMeasure h5
      rw [addAccessedAddress_gasMeasure] at e5
      rw [← h6, Devm.memWrite_gasMeasure]
      have hc := hv.gas.warmAccess_le
      unfold gasWarmAccess at hc
      omega
  case extcodesize =>
    apply Rinst.runCore_extcodesize_gasLt (pc := pc) (sevm := sevm) hv
    simpa only [Rinst.runCore] using h
  case extcodehash =>
    exact popAdrAccessChargePush_gasLt devm hv.gas
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
      have e1 := Devm.pop_gasMeasure hp
      change Except.bind (Except.map Prod.snd devm.pop) (chargeGas gBase) =
        .ok devm' at h
      simp only [hp, Except.map, Except.bind] at h
      have e2 := chargeGas_gasMeasure h
      unfold gBase at e2
      omega
  case mload =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasMeasure h1
    have e2 := chargeGas_gasMeasure h2
    have e3 := Devm.push_gasMeasure h3
    dsimp only at e1 e2 e3
    rw [Devm.memRead_gasMeasure] at e3
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
      (by intros; simp only [Devm.memWrite_gasMeasure]) h
  case mcopy =>
    exact popNat3ChargePure_gasLt devm
      (fun destinationStart sourceStart size d =>
        gVerylow + gasCopy * ceilDiv size 32 +
          d.extCost [(sourceStart, size), (destinationStart, size)])
      (fun destinationStart sourceStart size d =>
        (d.memRead sourceStart size).2.memWrite destinationStart
          (d.memRead sourceStart size).1)
      (by intros; unfold gVerylow; omega)
      (by intros; simp only [Devm.memWrite_gasMeasure, Devm.memRead_gasMeasure]) h
  case sstore =>
    split at h
    · -- Prague: the body it has always been.
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
      have e1 := Devm.pop_gasMeasure h1
      have e2 := Devm.pop_gasMeasure h2
      have e3 := chargeGas_gasMeasure hCharge
      have hPairGas : gasPair.1.gasMeasure = d2.gasMeasure := by
        rw [← hPair]
        split <;> simp only [addAccessedStorageKey_gasMeasure]
      have hRefundGas : d3.gasMeasure = d2.gasMeasure := by
        rw [← hRefund, Devm.withRefundCounter_gasMeasure, hPairGas]
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
      rw [← hFinal, Devm.setStorVal_gasMeasure]
      omega
    · -- Amsterdam: `vm/instructions/storage.py` `sstore`. The credit and the
      -- state charge are measure-neutral; the execution charge is at least a
      -- warm access, and that is the whole decrease.
      obtain ⟨_, _hStatic, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, _hGas, h⟩ := Except.bind_eq_ok h
      obtain ⟨d3, hCharge, h⟩ := Except.bind_eq_ok h
      obtain ⟨d4, hState, hFinal⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at hFinal
      have e1 := Devm.pop_gasMeasure h1
      have e2 := Devm.pop_gasMeasure h2
      have e3 := chargeGas_gasMeasure_lt (sstoreAmsterdamGasCost_pos _ _ _ _ _) hCharge
      have e4 := chargeStateGas_gasMeasure hState
      simp only [Devm.creditStateGasRefund_gasMeasure, Devm.withRefundCounter_gasMeasure,
        Devm.ite_addAccessedStorageKey_gasMeasure] at e3
      dsimp only at e1 e2 hFinal
      rw [← hFinal, Devm.setStorVal_gasMeasure]
      omega
  case sload =>
    obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasMeasure h1
    dsimp only at h e1
    split at h
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasMeasure h2
      have e3 := Devm.push_gasMeasure h3
      unfold gasWarmAccess at e2
      omega
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasMeasure h2
      rw [addAccessedStorageKey_gasMeasure] at e2
      have e3 := Devm.push_gasMeasure h3
      unfold gasColdSload at e2
      omega
  case tload =>
    obtain ⟨⟨key, d1⟩, h1, h2⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasMeasure h1
    have e2 := pushItem_gasLt (by unfold gasWarmAccess; omega) h2
    dsimp only at e1 e2
    omega
  case tstore =>
    split at h
    · obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
      obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, _hassert, h4⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h4
      have e1 := Devm.pop_gasMeasure h1
      have e2 := Devm.pop_gasMeasure h2
      have e3 := chargeGas_gasMeasure h3
      dsimp only at e1 e2 e3
      rw [← h4, Devm.setTransVal_gasMeasure]
      unfold gasWarmAccess at e3
      omega
    · obtain ⟨_, _hassert, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
      obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h4
      have e1 := Devm.pop_gasMeasure h1
      have e2 := Devm.pop_gasMeasure h2
      have e3 := chargeGas_gasMeasure h3
      dsimp only at e1 e2 e3
      rw [← h4, Devm.setTransVal_gasMeasure]
      unfold gasWarmAccess at e3
      omega
  case gas =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasMeasure h1
    have e2 := Devm.push_gasMeasure h2
    unfold gBase at e1
    omega
  case dup i =>
    obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasMeasure h1
    split at h
    · nomatch h
    · have e2 := Devm.push_gasMeasure h
      unfold gVerylow at e1
      omega
  case swap i =>
    obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasMeasure h1
    split at h
    · nomatch h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.withStack_gasMeasure]
      unfold gVerylow at e1
      omega
  case log topicCount =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨topics, d3⟩, h3, h⟩ := Except.bind_eq_ok h
    obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hassert, h5⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h5
    have e1 := Devm.popToNat_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popN_gasMeasure h3
    have e4 := chargeGas_gasMeasure h4
    dsimp only at e1 e2 e3 e4 h5
    rw [← h5, Devm.addLog_gasMeasure, Devm.memRead_gasMeasure]
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
      (by intros; simp only [Devm.memWrite_gasMeasure]) h

theorem Jinst.runCore_gasLt (pc : Nat) (devm : Devm) (sevm : Sevm)
    (j : Jinst) {pc' : Nat} {devm' : Devm}
    (h : Jinst.runCore pc devm sevm j = .ok (pc', devm')) :
    devm'.gasMeasure < devm.gasMeasure := by
  cases j
  case jumpdest =>
    exact Jinst.runCore_jumpdest_gasLt h
  case jump =>
    simp only [Jinst.runCore] at h
    obtain ⟨⟨destination, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hassert, h3⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    have e1 := Devm.pop_gasMeasure h1
    have e2 := chargeGas_gasMeasure h2
    dsimp only at e1 e2
    rw [← h3.2]
    unfold gMid at e2
    omega
  case jumpi =>
    simp only [Jinst.runCore] at h
    obtain ⟨⟨destination, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨condition, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.pop_gasMeasure h2
    have e3 := chargeGas_gasMeasure h3
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
    (hn : devm.gasMeasure < n) :
    XStep.GasDecreasing sevm n
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
    rw [← hd, Devm.push_gasMeasure hpush]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withGasLeft_gasLeft,
      Devm.withReturnData_gasLeft, Devm.withReturnData_spill,
      Devm.withGasLeft_spill]
    have hle := except64th_le devm.gasLeft
    have hm := Devm.gasMeasure_eq devm
    omega
  · split at hstep
    · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      intro devm' hd
      simp only [Except.ok.injEq] at hd
      rw [← hd, Devm.push_gasMeasure hpush, addAccessedAddress_gasMeasure,
        Devm.incrNonce_gasMeasure, Devm.withReturnData_gasMeasure,
        Devm.withGasLeft_gasMeasure]
      have hm := Devm.gasMeasure_eq devm
      omega
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
      rw [← hstep]
      refine ⟨?_, rfl⟩
      show (Frame.ofCreate _).inner.gas + Resume.parentGas _ < n
      simp only [Frame.ofCreate, processCreateMessage.msg_gas, createMsg,
        Resume.parentGas, addAccessedAddress_gasMeasure,
        Devm.incrNonce_gasMeasure, Devm.withReturnData_gasMeasure,
        Devm.withGasLeft_gasMeasure]
      have hle := except64th_le devm.gasLeft
      have hm := Devm.gasMeasure_eq devm
      omega

theorem genericCreateAmsterdam.step_gasDecreasing
    (sevm : Sevm) (state : StateGasRules) (devm : Devm) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) {n : Nat}
    (hn : devm.gasMeasure < n) :
    (genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize).GasDecreasing sevm n := by
  unfold genericCreateAmsterdam.step
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  dsimp only at hstep
  split at hstep
  · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd, Devm.push_gasMeasure hpush, Devm.withReturnData_gasMeasure]
    exact hn
  · have eaccess :
        (addAccessedAddress (devm.withReturnData []) newAddress).gasMeasure =
          devm.gasMeasure := by simp
    split at hstep
    · obtain ⟨d1, hstate, hstep⟩ := Except.bind_eq_ok hstep
      have estate := chargeStateGas_gasMeasure hstate
      have hwith := Devm.withholdCreateGas_gasMeasure d1
      split at hstep
      · obtain ⟨d2, hpush, hstep⟩ := Except.bind_eq_ok hstep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        intro devm' hd
        simp only [Except.ok.injEq] at hd
        rw [← hd, Devm.push_gasMeasure hpush,
          Devm.incrNonce_gasMeasure]
        omega
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, rfl⟩
        show (Frame.ofCreate _).inner.gas + Resume.parentGas _ < n
        simp only [Frame.ofCreate, processCreateMessage.msg_gas, createMsg,
          Resume.parentGas, Devm.incrNonce_gasMeasure,
          Devm.drainStateGasReservoir_gasMeasure,
          Devm.withholdCreateGas_gasMeasure]
        omega
    · simp only [bind, Except.bind] at hstep
      have hwith := Devm.withholdCreateGas_gasMeasure
        (addAccessedAddress (devm.withReturnData []) newAddress)
      split at hstep
      · obtain ⟨d1, hpush, hstep⟩ := Except.bind_eq_ok hstep
        simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        intro devm' hd
        simp only [Except.ok.injEq] at hd
        rw [← hd, Devm.push_gasMeasure hpush,
          Devm.incrNonce_gasMeasure]
        omega
      · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
        rw [← hstep]
        refine ⟨?_, rfl⟩
        show (Frame.ofCreate _).inner.gas + Resume.parentGas _ < n
        simp only [Frame.ofCreate, processCreateMessage.msg_gas, createMsg,
          Resume.parentGas, Devm.incrNonce_gasMeasure,
          Devm.drainStateGasReservoir_gasMeasure,
          Devm.withholdCreateGas_gasMeasure]
        omega
theorem Xinst.step_create_gasDecreasing (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm .create).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step]
  split
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d4, h4, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCreate.step_gasDecreasing
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := chargeGas_gasMeasure h4
    dsimp only at e1 e2 e3 e4
    rw [Devm.memExtends_gasMeasure]
    have hpos := hv.gas.createAccess_pos
    omega
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨_, hstatic, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d4, h4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hsize, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCreateAmsterdam.step_gasDecreasing
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := chargeGas_gasMeasure h4
    have hpos := hv.gas.createAccess_pos
    dsimp only at e1 e2 e3 e4
    rw [Devm.memExtends_gasMeasure]
    omega

theorem Xinst.step_create2_gasDecreasing (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm .create2).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step]
  split
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨salt, d4⟩, h4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d5, h5, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCreate.step_gasDecreasing
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := Devm.pop_gasMeasure h4
    have e5 := chargeGas_gasMeasure h5
    dsimp only at e1 e2 e3 e4 e5
    rw [Devm.memExtends_gasMeasure]
    have hpos := hv.gas.createAccess_pos
    omega
  · apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨_, hstatic, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨endowment, d1⟩, h1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memoryIndex, d2⟩, h2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨memorySize, d3⟩, h3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨salt, d4⟩, h4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d5, h5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hsize, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCreateAmsterdam.step_gasDecreasing
    have e1 := Devm.pop_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := Devm.popToNat_gasMeasure h3
    have e4 := Devm.pop_gasMeasure h4
    have e5 := chargeGas_gasMeasure h5
    have hpos := hv.gas.createAccess_pos
    dsimp only at e1 e2 e3 e4 e5
    rw [Devm.memExtends_gasMeasure]
    omega

theorem Xinst.step_callcode_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (Xinst.step sevm devm .callcode).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step, hstate]
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
  have e1 := Devm.pop_gasMeasure p1
  have e2 := Devm.popToAdr_gasMeasure p2
  have e3 := Devm.pop_gasMeasure p3
  have e4 := Devm.popToNat_gasMeasure p4
  have e5 := Devm.popToNat_gasMeasure p5
  have e6 := Devm.popToNat_gasMeasure p6
  have e7 := Devm.popToNat_gasMeasure p7
  dsimp only at e2 e3 e4 e5 e6 e7
  have eA :
      (sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d7 codeAddress) codeAddress).2.2.2.2.gasMeasure
        = devm.gasMeasure := by
    rw [GasSchedule.accessDelegation_gasMeasure, addAccessedAddress_gasMeasure]
    omega
  have hstip :
      (if value.toNat = 0 then 0 else gCallStipend) <
        ((sevm.benvStat.rules.gas.accessCost codeAddress d7.accessedAddresses +
            (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress d7 codeAddress)
              codeAddress).2.2.2.1) +
          if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
        d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    have hac := GasSchedule.access_cost_pos hv.gas codeAddress d7.accessedAddresses
    have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
    by_cases hv : value = 0
    · have : value.toNat = 0 := by rw [hv]; rfl
      rw [if_pos this]
      omega
    · rw [if_neg hv]
      split <;> omega
  obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  split at hstep
  · obtain ⟨d9, ppush, hstep⟩ := Except.bind_eq_ok hstep
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    intro devm' hd
    simp only [Except.ok.injEq] at hd
    rw [← hd]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_gasMeasure]
    rw [Nat.add_right_comm, ← Devm.gasMeasure_eq, Devm.push_gasMeasure ppush,
      Devm.memExtends_gasMeasure]
    exact key
  · simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCall.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure]
    exact key

theorem Xinst.step_callcode_gasDecreasing (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm .callcode).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step]
  split
  · simpa only [Xinst.step, *] using
      Xinst.step_callcode_gasDecreasing_legacy sevm devm hv (by assumption)
  · rename_i state hstate
    apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨value, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d7⟩, p7, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d8, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.pop_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    have e7 := Devm.popToNat_gasMeasure p7
    dsimp only at e1 e2 e3 e4 e5 e6 e7 hstep
    have eA :
        (sevm.benvStat.rules.gas.accessDelegation
          (addAccessedAddress d7 codeAddress) codeAddress).2.2.2.2.gasMeasure =
          devm.gasMeasure := by
      rw [GasSchedule.accessDelegation_gasMeasure,
        addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if value.toNat = 0 then 0 else gCallStipend) <
          ((sevm.benvStat.rules.gas.accessCost codeAddress d7.accessedAddresses +
              (if value = 0 then 0 else sevm.benvStat.rules.gas.callValue) +
              (sevm.benvStat.rules.gas.accessDelegation
                (addAccessedAddress d7 codeAddress) codeAddress).2.2.2.1) +
            d7.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) := by
      have hac := GasSchedule.access_cost_pos hv.gas codeAddress d7.accessedAddresses
      have hcall := GasSchedule.Valid.stipend_le_callValue hv.gas
      by_cases hvalue : value = 0
      · have hto : value.toNat = 0 := by rw [hvalue]; rfl
        rw [if_pos hto, if_pos hvalue]
        omega
      · have hto : value.toNat ≠ 0 := by
          intro hz
          exact hvalue (B256.toNat_inj value 0 (by rw [hz, B256.toNat_zero]))
        rw [if_neg hto, if_neg hvalue]
        omega
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCallAmsterdam.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure,
      Devm.drainStateGasReservoir_gasMeasure]
    exact key

theorem Xinst.step_delegatecall_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (Xinst.step sevm devm .delegatecall).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step, hstate]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  have e1 := Devm.pop_gasMeasure p1
  have e2 := Devm.popToAdr_gasMeasure p2
  have e3 := Devm.popToNat_gasMeasure p3
  have e4 := Devm.popToNat_gasMeasure p4
  have e5 := Devm.popToNat_gasMeasure p5
  have e6 := Devm.popToNat_gasMeasure p6
  dsimp only at e2 e3 e4 e5 e6
  have eA :
      (sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d6 codeAddress) codeAddress).2.2.2.2.gasMeasure
        = devm.gasMeasure := by
    rw [GasSchedule.accessDelegation_gasMeasure, addAccessedAddress_gasMeasure]
    omega
  have hstip :
      (if (0 : Nat) = 0 then 0 else gCallStipend) <
        (sevm.benvStat.rules.gas.accessCost codeAddress d6.accessedAddresses +
          (sevm.benvStat.rules.gas.accessDelegation (addAccessedAddress d6 codeAddress)
            codeAddress).2.2.2.1) +
        d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    simp only [if_pos]
    have hac := GasSchedule.access_cost_pos hv.gas codeAddress d6.accessedAddresses
    omega
  obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
  rw [← hstep]
  apply genericCall.step_gasDecreasing
  rw [Devm.memExtends_gasMeasure]
  exact key

theorem Xinst.step_delegatecall_gasDecreasing (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm .delegatecall).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step]
  split
  · simpa only [Xinst.step, *] using
      Xinst.step_delegatecall_gasDecreasing_legacy sevm devm hv (by assumption)
  · rename_i state hstate
    apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.popToNat_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    dsimp only at e1 e2 e3 e4 e5 e6 hstep
    have eA :
        (sevm.benvStat.rules.gas.accessDelegation
          (addAccessedAddress d6 codeAddress) codeAddress).2.2.2.2.gasMeasure =
          devm.gasMeasure := by
      rw [GasSchedule.accessDelegation_gasMeasure,
        addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if (0 : Nat) = 0 then 0 else gCallStipend) <
          (sevm.benvStat.rules.gas.accessCost codeAddress d6.accessedAddresses +
              0 +
              (sevm.benvStat.rules.gas.accessDelegation
                (addAccessedAddress d6 codeAddress) codeAddress).2.2.2.1) +
            d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      simp only [if_pos]
      have hac := GasSchedule.access_cost_pos hv.gas codeAddress d6.accessedAddresses
      omega
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCallAmsterdam.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure,
      Devm.drainStateGasReservoir_gasMeasure]
    exact key

theorem Xinst.step_staticcall_gasDecreasing_legacy (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (Xinst.step sevm devm .staticcall).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step, hstate]
  apply XStep.ofExcept_gasDecreasing
  intro step hstep
  obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨target, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
  obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
  dsimp only at hstep
  have e1 := Devm.pop_gasMeasure p1
  have e2 := Devm.popToAdr_gasMeasure p2
  have e3 := Devm.popToNat_gasMeasure p3
  have e4 := Devm.popToNat_gasMeasure p4
  have e5 := Devm.popToNat_gasMeasure p5
  have e6 := Devm.popToNat_gasMeasure p6
  dsimp only at e2 e3 e4 e5 e6
  have eA :
      (sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress d6 target) target).2.2.2.2.gasMeasure
        = devm.gasMeasure := by
    rw [GasSchedule.accessDelegation_gasMeasure, addAccessedAddress_gasMeasure]
    omega
  have hstip :
      (if (0 : Nat) = 0 then 0 else gCallStipend) <
        (sevm.benvStat.rules.gas.accessCost target d6.accessedAddresses +
          (sevm.benvStat.rules.gas.accessDelegation
            (addAccessedAddress d6 target) target).2.2.2.1) +
        d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
    simp only [if_pos]
    have hac := GasSchedule.access_cost_pos hv.gas target d6.accessedAddresses
    omega
  obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
  have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
  simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
  rw [← hstep]
  apply genericCall.step_gasDecreasing
  rw [Devm.memExtends_gasMeasure]
  exact key

theorem Xinst.step_staticcall_gasDecreasing (sevm : Sevm) (devm : Devm)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm .staticcall).GasDecreasing sevm devm.gasMeasure := by
  simp only [Xinst.step]
  split
  · simpa only [Xinst.step, *] using
      Xinst.step_staticcall_gasDecreasing_legacy sevm devm hv (by assumption)
  · rename_i state hstate
    apply XStep.ofExcept_gasDecreasing
    intro step hstep
    obtain ⟨⟨gas, d1⟩, p1, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨codeAddress, d2⟩, p2, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputIndex, d3⟩, p3, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨inputSize, d4⟩, p4, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputIndex, d5⟩, p5, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨⟨outputSize, d6⟩, p6, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hpre, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨_, hfull, hstep⟩ := Except.bind_eq_ok hstep
    obtain ⟨d7, pcharge, hstep⟩ := Except.bind_eq_ok hstep
    have e1 := Devm.pop_gasMeasure p1
    have e2 := Devm.popToAdr_gasMeasure p2
    have e3 := Devm.popToNat_gasMeasure p3
    have e4 := Devm.popToNat_gasMeasure p4
    have e5 := Devm.popToNat_gasMeasure p5
    have e6 := Devm.popToNat_gasMeasure p6
    dsimp only at e1 e2 e3 e4 e5 e6 hstep
    have eA :
        (sevm.benvStat.rules.gas.accessDelegation
          (addAccessedAddress d6 codeAddress) codeAddress).2.2.2.2.gasMeasure =
          devm.gasMeasure := by
      rw [GasSchedule.accessDelegation_gasMeasure,
        addAccessedAddress_gasMeasure]
      omega
    have hstip :
        (if (0 : Nat) = 0 then 0 else gCallStipend) <
          (sevm.benvStat.rules.gas.accessCost codeAddress d6.accessedAddresses +
              0 +
              (sevm.benvStat.rules.gas.accessDelegation
                (addAccessedAddress d6 codeAddress) codeAddress).2.2.2.1) +
            d6.extCost [(inputIndex, inputSize), (outputIndex, outputSize)] := by
      simp only [if_pos]
      have hac := GasSchedule.access_cost_pos hv.gas codeAddress d6.accessedAddresses
      omega
    have key := call_charge_stipend_lt (devm := devm) hstip eA pcharge
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hstep
    rw [← hstep]
    apply genericCallAmsterdam.step_gasDecreasing
    rw [Devm.memExtends_gasMeasure,
      Devm.drainStateGasReservoir_gasMeasure]
    exact key

theorem Xinst.step_gasDecreasing (sevm : Sevm) (devm : Devm) (x : Xinst)
    (hv : sevm.benvStat.rules.Valid) :
    (Xinst.step sevm devm x).GasDecreasing sevm devm.gasMeasure := by
  cases x
  case create => exact Xinst.step_create_gasDecreasing sevm devm hv
  case create2 => exact Xinst.step_create2_gasDecreasing sevm devm hv
  case call => exact Xinst.step_call_gasDecreasing sevm devm hv
  case callcode => exact Xinst.step_callcode_gasDecreasing sevm devm hv
  case delegatecall => exact Xinst.step_delegatecall_gasDecreasing sevm devm hv
  case staticcall => exact Xinst.step_staticcall_gasDecreasing sevm devm hv

theorem executePrecomp_gasLe (evm : Evm) (adr : Adr) :
    (executePrecomp evm adr).gasMeasure ≤ evm.dyna.gasMeasure := by
  unfold executePrecomp applyPrecompResult
  cases precompileRun evm adr with
  | error msg cost =>
    simp only [Execution.gasMeasure_error, Devm.withGasLeft_gasMeasure]
    have hm := Devm.gasMeasure_eq evm.dyna
    omega
  | ok cost output =>
    simp only [Execution.gasMeasure_ok]
    simp only [Devm.withOutput, Devm.setMeta_gasMeasure,
      Devm.withGasLeft_gasMeasure]
    have hm := Devm.gasMeasure_eq evm.dyna
    omega

theorem executeCode.handleError_ok_gasLe {raw : Execution} {devm : Devm}
    (h : executeCode.handleError raw = .ok devm) :
    devm.gasMeasure ≤ raw.gasMeasure := by
  cases raw with
  | ok d =>
    simp only [executeCode.handleError, Except.ok.injEq] at h
    rw [← h]
    simp only [Execution.gasMeasure_ok]
    omega
  | error e =>
    obtain ⟨err, d0⟩ := e
    cases err with
    | halt reason =>
      simp only [executeCode.handleError, Except.ok.injEq] at h
      rw [← h, Devm.setMeta_gasMeasure, Devm.withGasLeft_gasMeasure]
      simp only [Execution.gasMeasure_error]
      have hm := Devm.gasMeasure_eq d0
      omega
    | revert =>
      simp only [executeCode.handleError, Except.ok.injEq] at h
      rw [← h, Devm.withError_gasMeasure]
      simp only [Execution.gasMeasure_error]
      omega
    | crypto reason => exact absurd h (by simp [executeCode.handleError])
    | internal reason => exact absurd h (by simp [executeCode.handleError])

theorem executeCode.handleErrorAmsterdam_ok_gasLe {raw : Execution} {devm : Devm}
    (h : executeCode.handleErrorAmsterdam raw = .ok devm) :
    devm.gasMeasure ≤ raw.gasMeasure := by
  cases raw with
  | ok d =>
    simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
    rw [← h]
    exact Nat.le_refl _
  | error e =>
    obtain ⟨err, d0⟩ := e
    cases err with
    | halt reason =>
      simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
      rw [← h, Devm.setMeta_gasMeasure]
      simp only [Execution.gasMeasure_error]
      exact Nat.le_trans (Devm.forfeitRemainingGas_gasMeasure_le _)
        (Nat.le_of_eq (Devm.restoreStateGas_gasMeasure d0))
    | revert =>
      simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
      rw [← h, Devm.withError_gasMeasure, Devm.restoreStateGas_gasMeasure]
      exact Nat.le_refl _
    | crypto reason => exact absurd h (by simp [executeCode.handleErrorAmsterdam])
    | internal reason => exact absurd h (by simp [executeCode.handleErrorAmsterdam])

theorem executeCode.handleErrorWith_ok_gasLe {stateGas : Option StateGasRules}
    {raw : Execution} {devm : Devm}
    (h : executeCode.handleErrorWith stateGas raw = .ok devm) :
    devm.gasMeasure ≤ raw.gasMeasure := by
  cases stateGas with
  | none => exact executeCode.handleError_ok_gasLe h
  | some state => exact executeCode.handleErrorAmsterdam_ok_gasLe h

@[simp] theorem chargeGas_result_gasLe (cost : Nat) (devm : Devm) :
    (chargeGas cost devm).gasMeasure ≤ devm.gasMeasure := by
  rw [chargeGas_def]
  by_cases hc : cost ≤ devm.gasLeft
  · simp only [safeSub, hc, if_pos, Execution.gasMeasure_ok,
      Devm.setMach_gasMeasure]
    simp only [Mach.gasMeasure, Devm.gasMeasure, Devm.gasLeft]
    omega
  · simp [safeSub, hc, Execution.gasMeasure]

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
def resultGas {α : Type} (proj : α → Devm) : Except (EvmError × Devm) α → Nat
  | .error p => p.2.gasMeasure
  | .ok a => (proj a).gasMeasure

@[simp] theorem resultGas_error {α : Type} (proj : α → Devm) (p : EvmError × Devm) :
    resultGas proj (.error p) = p.2.gasMeasure := rfl

@[simp] theorem resultGas_ok {α : Type} (proj : α → Devm) (a : α) :
    resultGas proj (.ok a) = (proj a).gasMeasure := rfl

@[simp] theorem resultGas_id (ex : Execution) : resultGas id ex = ex.gasMeasure := by
  cases ex <;> rfl

/-- Peel one `bind` whose payload is a `_ × Devm` pair. The tail obligation is
measured against the intermediate `Devm`, so it is this lemma again one level
down. -/
theorem gasLe_bind_snd {α : Type} {n : Nat}
    {e : Except (EvmError × Devm) (α × Devm)} {f : α × Devm → Execution}
    (he : resultGas Prod.snd e ≤ n)
    (hf : ∀ a : α × Devm, Execution.gasMeasure (f a) ≤ a.2.gasMeasure) :
    Execution.gasMeasure (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

/-- Peel one `bind` whose payload is a bare `Devm`. -/
theorem gasLe_bind_id {n : Nat} {e : Execution} {f : Devm → Execution}
    (he : e.gasMeasure ≤ n) (hf : ∀ d : Devm, Execution.gasMeasure (f d) ≤ d.gasMeasure) :
    Execution.gasMeasure (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok d => exact Nat.le_trans (hf d) he

/-- Peel a `bind` whose payload carries no `Devm` at all — an `Except.assert`
guard, or an `.ok` of a pure value. The current `Devm` simply survives it. -/
theorem gasLe_bind_const {α : Type} {n : Nat} {devm : Devm}
    {e : Except (EvmError × Devm) α} {f : α → Execution}
    (he : resultGas (fun _ => devm) e ≤ n)
    (hf : ∀ a : α, Execution.gasMeasure (f a) ≤ devm.gasMeasure) :
    Execution.gasMeasure (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

@[simp] theorem resultGas_assert {p : Prop} [Decidable p] {devm : Devm}
    (msg : EvmError) :
    resultGas (fun _ => devm) (Except.assert p ⟨msg, devm⟩) = devm.gasMeasure := by
  unfold Except.assert
  split <;> rfl

/-! ### The `Mach` layer of the non-increase corpus -/

/-- The `Mach`-level analogue of `resultGas`, for the primitives defined by a
footprint lift. -/
def machResultGas {α : Type} : Footprint.Outcome Mach α → Nat
  | .error p => p.2.gasMeasure
  | .ok p => p.2.gasMeasure

theorem liftMach_resultGas {α : Type} (core : Mach → Footprint.Outcome Mach α)
    (devm : Devm) :
    resultGas Prod.snd (liftMach core devm) = machResultGas (core devm.mach) := by
  unfold liftMach Footprint.liftOutcome
  cases core devm.mach <;> rfl

theorem liftMachExecution_resultGas (core : Mach → Footprint.Outcome Mach Unit)
    (devm : Devm) :
    (liftMachExecution core devm).gasMeasure = machResultGas (core devm.mach) := by
  unfold liftMachExecution Footprint.toExecution liftMach Footprint.liftOutcome
  cases core devm.mach <;> rfl

/-- A state charge never raises the measure in either branch: a reservoir draw
moves nothing the measure counts, a spill moves exactly as much out of
`gasLeft` as it records, and the out-of-gas branch returns the frame it was
given. -/
@[simp] theorem Mach.chargeStateGas_machResultGas (amount : Nat) (mach : Mach) :
    machResultGas (Mach.chargeStateGas amount mach) ≤ mach.gasMeasure := by
  unfold Mach.chargeStateGas
  split_ifs <;> simp only [machResultGas, Mach.gasMeasure] <;> omega

@[simp] theorem chargeStateGas_result_gasLe (amount : Nat) (devm : Devm) :
    (chargeStateGas amount devm).gasMeasure ≤ devm.gasMeasure := by
  rw [chargeStateGas, liftMachExecution_resultGas]
  exact Mach.chargeStateGas_machResultGas amount devm.mach


namespace Mach

@[simp] theorem pop_machResultGas (mach : Mach) :
    machResultGas mach.pop = mach.gasMeasure := by
  rcases mach with ⟨stack, memory, gasLeft, stateGas⟩
  cases stack <;> rfl

@[simp] theorem popToNat_machResultGas (mach : Mach) :
    machResultGas mach.popToNat = mach.gasMeasure := by
  rcases mach with ⟨stack, memory, gasLeft, stateGas⟩
  cases stack <;> rfl

@[simp] theorem popToAdr_machResultGas (mach : Mach) :
    machResultGas mach.popToAdr = mach.gasMeasure := by
  rcases mach with ⟨stack, memory, gasLeft, stateGas⟩
  cases stack <;> rfl

@[simp] theorem popN_machResultGas (n : Nat) (mach : Mach) :
    machResultGas (mach.popN n) = mach.gasMeasure := by
  induction n generalizing mach with
  | zero => rfl
  | succ n ih =>
    rcases mach with ⟨stack, memory, gasLeft, stateGas⟩
    cases stack with
    | nil => rfl
    | cons x xs =>
      have ih' := ih ⟨xs, memory, gasLeft, stateGas⟩
      rcases hp : Mach.popN ⟨xs, memory, gasLeft, stateGas⟩ n with
          ⟨err, m⟩ | ⟨ys, m⟩ <;>
        rw [hp] at ih' <;>
        simpa only [Mach.popN, Mach.pop, hp, machResultGas, Mach.gasMeasure]
          using ih'

@[simp] theorem push_machResultGas (x : B256) (mach : Mach) :
    machResultGas (Mach.push x mach) = mach.gasMeasure := by
  unfold Mach.push
  split <;> rfl

@[simp] theorem chargeGas_machResultGas (c : Nat) (mach : Mach) :
    machResultGas (Mach.chargeGas c mach) ≤ mach.gasMeasure := by
  unfold Mach.chargeGas safeSub
  by_cases hc : c ≤ mach.gasLeft
  · simp only [if_pos hc, machResultGas, Mach.gasMeasure]
    omega
  · simp only [if_neg hc, machResultGas, Mach.gasMeasure]
    omega

@[simp] theorem pushItem_machResultGas (x : B256) (c : Nat) (mach : Mach) :
    machResultGas (Mach.pushItem x c mach) ≤ mach.gasMeasure := by
  unfold Mach.pushItem
  have hc := Mach.chargeGas_machResultGas c mach
  rcases hg : Mach.chargeGas c mach with ⟨err, m⟩ | ⟨u, m⟩ <;> rw [hg] at hc <;>
    simp only [machResultGas] at hc
  · exact hc
  · exact Nat.le_trans (Nat.le_of_eq (push_machResultGas x m)) hc

@[simp] theorem applyUnary_machResultGas (f : B256 → B256) (c : Nat) (mach : Mach) :
    machResultGas (Mach.applyUnary f c mach) ≤ mach.gasMeasure := by
  unfold Mach.applyUnary
  have hp := Mach.pop_machResultGas mach
  rcases hg : mach.pop with ⟨err, m⟩ | ⟨x, m⟩ <;> rw [hg] at hp <;>
    simp only [machResultGas] at hp ⊢
  · exact Nat.le_of_eq hp
  · exact Nat.le_trans (pushItem_machResultGas _ _ m) (Nat.le_of_eq hp)

@[simp] theorem applyBinary_machResultGas (f : B256 → B256 → B256) (c : Nat)
    (mach : Mach) :
    machResultGas (Mach.applyBinary f c mach) ≤ mach.gasMeasure := by
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
    machResultGas (Mach.applyTernary f c mach) ≤ mach.gasMeasure := by
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
    resultGas Prod.snd devm.pop = devm.gasMeasure := by
  rw [Devm.pop, liftMach_resultGas, Mach.pop_machResultGas]
  rfl

@[simp] theorem Devm.popToNat_resultGas (devm : Devm) :
    resultGas Prod.snd devm.popToNat = devm.gasMeasure := by
  rw [Devm.popToNat, liftMach_resultGas, Mach.popToNat_machResultGas]
  rfl

@[simp] theorem Devm.popToAdr_resultGas (devm : Devm) :
    resultGas Prod.snd devm.popToAdr = devm.gasMeasure := by
  rw [Devm.popToAdr, liftMach_resultGas, Mach.popToAdr_machResultGas]
  rfl

@[simp] theorem Devm.popN_resultGas (devm : Devm) (n : Nat) :
    resultGas Prod.snd (devm.popN n) = devm.gasMeasure := by
  rw [Devm.popN, liftMach_resultGas, Mach.popN_machResultGas]
  rfl

@[simp] theorem Devm.push_gasLe (x : B256) (devm : Devm) :
    (devm.push x).gasMeasure = devm.gasMeasure := by
  rw [Devm.push, liftMachExecution_resultGas, Mach.push_machResultGas]
  rfl

@[simp] theorem pushItem_gasLe (x : B256) (c : Nat) (devm : Devm) :
    (pushItem x c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [pushItem, liftMachExecution_resultGas]
  exact Mach.pushItem_machResultGas x c devm.mach

@[simp] theorem applyUnary_gasLe (f : B256 → B256) (c : Nat) (devm : Devm) :
    (applyUnary f c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [applyUnary, liftMachExecution_resultGas]
  exact Mach.applyUnary_machResultGas f c devm.mach

@[simp] theorem applyBinary_gasLe (f : B256 → B256 → B256) (c : Nat) (devm : Devm) :
    (applyBinary f c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [applyBinary, liftMachExecution_resultGas]
  exact Mach.applyBinary_machResultGas f c devm.mach

@[simp] theorem applyTernary_gasLe (f : B256 → B256 → B256 → B256) (c : Nat)
    (devm : Devm) :
    (applyTernary f c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [applyTernary, liftMachExecution_resultGas]
  exact Mach.applyTernary_machResultGas f c devm.mach

@[simp] theorem Devm.pop_map_snd_gasLe (devm : Devm) :
    Execution.gasMeasure (devm.pop <&> Prod.snd) = devm.gasMeasure := by
  have h := Devm.pop_resultGas devm
  rcases hp : devm.pop with ⟨err, d⟩ | ⟨x, d⟩ <;> rw [hp] at h <;>
    simp only [resultGas_error, resultGas_ok] at h
  · exact h
  · exact h

/-- The general form of the peeling lemma, for the bodies whose payload carries
its `Devm` somewhere other than the second component. -/
theorem gasLe_bind {α : Type} {n : Nat} {proj : α → Devm}
    {e : Except (EvmError × Devm) α} {f : α → Execution}
    (he : resultGas proj e ≤ n)
    (hf : ∀ a : α, Execution.gasMeasure (f a) ≤ (proj a).gasMeasure) :
    Execution.gasMeasure (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

/-- The fully general peeling lemma, for bodies that do not end in a bare
`Devm` — `Jinst.runCore` returns a `Nat × Devm` jump target. -/
theorem gasLe_bind_gen {α β : Type} {n : Nat} {proj : α → Devm} {proj' : β → Devm}
    {e : Except (EvmError × Devm) α} {f : α → Except (EvmError × Devm) β}
    (he : resultGas proj e ≤ n)
    (hf : ∀ a : α, resultGas proj' (f a) ≤ (proj a).gasMeasure) :
    resultGas proj' (e >>= f) ≤ n := by
  cases e with
  | error p => exact he
  | ok a => exact Nat.le_trans (hf a) he

@[simp] theorem assertDynamic_resultGas (sevm : Sevm) (devm : Devm) :
    resultGas (fun _ => devm) (assertDynamic sevm devm) = devm.gasMeasure :=
  resultGas_assert _

/-- The `Mach × Meta` analogue of `machResultGas`, for `Rinst.balanceCore`. -/
def machMetaResultGas {α : Type} : Footprint.Outcome (Mach × Meta) α → Nat
  | .error p => p.2.1.gasMeasure
  | .ok p => p.2.1.gasMeasure

theorem liftMachMetaExecution_resultGas
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit) (devm : Devm) :
    (liftMachMetaExecution core devm).gasMeasure =
      machMetaResultGas (core devm.mach devm.meta) := by
  rcases h : core devm.mach devm.meta with ⟨err, view⟩ | ⟨u, view⟩ <;>
    simp only [liftMachMetaExecution, Footprint.toExecution, liftMachMeta,
      Footprint.liftOutcome, h, machMetaResultGas] <;> rfl

theorem Rinst.balanceCore_machMetaResultGas (gas : GasSchedule) (world : World)
    (mach : Mach) (view : Meta) :
    machMetaResultGas (Rinst.balanceCore gas world mach view) ≤ mach.gasMeasure := by
  have hp := Mach.pop_machResultGas mach
  have hc : ∀ (c : Nat) (m : Mach), machResultGas (Mach.chargeGas c m) ≤ m.gasMeasure :=
    Mach.chargeGas_machResultGas
  have hs : ∀ (x : B256) (m : Mach), machResultGas (Mach.push x m) = m.gasMeasure :=
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
        else gas.coldAccountAccess) m1
      rw [heq2] at this
      simp only [machResultGas] at this
      simp only [machMetaResultGas]
      omega
    · rename_i u m2 heq2
      have h2 := hc (if x.toAdr ∈ view.accessedAddresses then gasWarmAccess
        else gas.coldAccountAccess) m1
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
    (Rinst.runCore pc devm sevm r).gasMeasure ≤ devm.gasMeasure := by
  cases r <;> simp only [Rinst.runCore]
  all_goals first
    | exact pushItem_gasLe _ _ _
    | exact applyUnary_gasLe _ _ _
    | exact applyBinary_gasLe _ _ _
    | exact applyTernary_gasLe _ _ _
    | skip
  case balance =>
    rw [liftMachMetaWorldExecution, liftMachMetaExecution_resultGas]
    exact Rinst.balanceCore_machMetaResultGas _ _ _ _
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
  case keccak256 =>
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
  case returndatacopy =>
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
          (Nat.le_of_eq (addAccessedAddress_gasMeasure _ _)))
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  case sload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨key, d1⟩
    split
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
    · exact gasLe_bind_id
        (Nat.le_trans (chargeGas_result_gasLe _ _)
          (Nat.le_of_eq (addAccessedStorageKey_gasMeasure _ _ _)))
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
          (Nat.le_of_eq (addAccessedAddress_gasMeasure _ _)))
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
    split
    · refine gasLe_bind_snd (by simp) ?_
      rintro ⟨key, d1⟩
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨val, d2⟩
      refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
      intro d3
      refine gasLe_bind_const (devm := d3) (by simp) ?_
      intro _
      simp
    · refine gasLe_bind_const (devm := devm) (by simp) ?_
      intro _
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨key, d1⟩
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨val, d2⟩
      refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
      intro d3
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
    split
    · -- Prague.
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
    · -- Amsterdam.
      refine gasLe_bind_const (devm := devm) (by simp) ?_
      intro _
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨key, d1⟩
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨val, d2⟩
      refine gasLe_bind_const (devm := d2) (by simp) ?_
      intro _
      refine gasLe_bind_id (Nat.le_trans (chargeGas_result_gasLe _ _) (by simp)) ?_
      intro d3
      refine gasLe_bind_id (chargeStateGas_result_gasLe _ _) ?_
      intro d4
      simp

theorem Jinst.runCore_gasLe (pc : Nat) (devm : Devm) (sevm : Sevm) (j : Jinst) :
    resultGas Prod.snd (Jinst.runCore pc devm sevm j) ≤ devm.gasMeasure := by
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

@[simp] theorem Devm.subBal_gasMeasure {devm devm' : Devm} {a : Adr} {v : B256}
    (h : devm.subBal a v = some devm') : devm'.gasMeasure = devm.gasMeasure := by
  unfold Devm.subBal at h
  rcases hs : devm.state.subBal a v with _ | state <;> rw [hs] at h <;>
    simp only [bind, Option.bind, Option.some.injEq] at h
  · nomatch h
  · rw [← h, Devm.withState_gasMeasure]

@[simp] theorem Devm.setBal_gasMeasure (devm : Devm) (a : Adr) (v : B256) :
    (devm.setBal a v).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem addAccountToDelete_gasMeasure (devm : Devm) (a : Adr) :
    (addAccountToDelete devm a).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem Devm.addBal_gasMeasure (devm : Devm) (a : Adr) (v : B256) :
    (devm.addBal a v).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem Devm.emitTransferLog_gasMeasure
    (devm : Devm) (sender recipient : Adr) (amount : B256) :
    (devm.emitTransferLog sender recipient amount).gasMeasure = devm.gasMeasure := by
  unfold Devm.emitTransferLog
  split <;> simp

@[simp] theorem Devm.withOutput_gasMeasure (devm : Devm) (output : Bytes) :
    (devm.withOutput output).gasMeasure = devm.gasMeasure := rfl

/-- The halting instructions. `.revert` is the reason this whole layer exists: it
is the sole producer of the `"Revert"` tag, the one error `handleError` turns
back into a successful frame result carrying live gas. -/
theorem Linst.run_gasLe (sevm : Sevm) (devm : Devm) (l : Linst) :
    Execution.gasMeasure (Linst.run sevm devm l) ≤ devm.gasMeasure := by
  cases l <;> simp only [Linst.run]
  case stop => simp
  case return_ =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case revert =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d3
    simp
  case selfdestruct =>
    split
    · refine gasLe_bind_snd (by simp) ?_
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
          · simp [Option.toExcept, Devm.subBal_gasMeasure hb]
        · intro d4
          refine gasLe_bind_id (by simp) ?_
          intro d5
          split <;> simp
    · refine gasLe_bind_const (devm := devm) (by simp) ?_
      intro _
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨donee, d1⟩
      refine gasLe_bind_const (devm := d1) (by simp) ?_
      intro _
      let d2 := if donee ∉ d1.accessedAddresses then addAccessedAddress d1 donee else d1
      have hd2 : d2.gasMeasure = d1.gasMeasure := by
        simp only [d2]
        split <;> simp
      refine gasLe_bind_id ?_ ?_
      · exact Nat.le_trans (chargeGas_result_gasLe _ d2) (Nat.le_of_eq hd2)
      · intro d3
        refine gasLe_bind_id (chargeStateGas_result_gasLe _ d3) ?_
        intro d4
        refine gasLe_bind_id ?_ ?_
        · rcases hb : d4.subBal sevm.currentTarget (d2.getAcct sevm.currentTarget).bal with
            _ | d5
          · simp [Option.toExcept]
          · simp [Option.toExcept, Devm.subBal_gasMeasure hb]
        · intro d5
          simp only [apply_ite, Execution.gasMeasure_ok, addAccountToDelete_gasMeasure,
            Devm.emitTransferLog_gasMeasure, Devm.addBal_gasMeasure, ite_self, Nat.le_refl]

/-! ## The `Xinst` halt branch

`Xinst` is the one family whose error branch resists the `resultGas` walk. A
call-type instruction that short-circuits at depth 0 hands the stipend *back*,
so the `Devm` in `(evm1.withGasLeft (evm1.gasLeft + gas)).push 0` carries more
gas than the intermediate it came from; the bound is recoverable only from the
charge equation the compositional device deliberately discards.

What the driver actually needs is weaker than a measure bound, and it has two
halves. `handleError` manufactures a live-gas frame result out of exactly one
tag, `"Revert"`, and every error an `Xinst` can raise is a stack or gas fault —
`"Revert"` is produced at a single site in the whole interpreter,
`Linst.run .revert`. That is the first half, and it is a walk with no
arithmetic in it at all. The second half is what an exceptional halt *keeps*:
`handleError` zeroes `gasLeft` and leaves the meter alone, so the settled
measure is the halted frame's `spill`, and the driver needs that spill bounded
by the measure the step began with. Along a Prague arm no operation touches the
meter, so the walk carries one more fact -- every branch still holds the meter
the step began with -- and the bound follows because a meter's spill never
exceeds the measure it is part of. The two halves travel together in one walk,
which is the walk the tag obligation alone used to be. -/

/-- Every error branch of this outcome is a halt that is not a `"Revert"` and
still carries the meter `s`; a successful branch carries `s` too, which is what
lets the fact travel across a bind. -/
def HaltOut {α : Type} (proj : α → Devm) (s : StateGasMeter) :
    Except (EvmError × Devm) α → Prop
  | .error p => p.1 ≠ .revert ∧ p.2.mach.stateGas = s
  | .ok a => (proj a).mach.stateGas = s

/-- The `Mach`-level analogue, for the footprint-lifted primitives. -/
def MachHaltOut {α : Type} (s : StateGasMeter) : Footprint.Outcome Mach α → Prop
  | .error q => q.1 ≠ .revert ∧ q.2.stateGas = s
  | .ok p => p.2.stateGas = s

theorem liftMach_haltOut {α : Type} {core : Mach → Footprint.Outcome Mach α}
    {devm : Devm} {s : StateGasMeter} (h : MachHaltOut s (core devm.mach)) :
    HaltOut Prod.snd s (liftMach core devm) := by
  unfold liftMach Footprint.liftOutcome
  rcases hc : core devm.mach with ⟨err, m⟩ | ⟨v, m⟩ <;> rw [hc] at h
  · exact h
  · exact h

theorem liftMachExecution_haltOut {core : Mach → Footprint.Outcome Mach Unit}
    {devm : Devm} {s : StateGasMeter} (h : MachHaltOut s (core devm.mach)) :
    HaltOut id s (liftMachExecution core devm) := by
  unfold liftMachExecution Footprint.toExecution liftMach Footprint.liftOutcome
  rcases hc : core devm.mach with ⟨err, m⟩ | ⟨v, m⟩ <;> rw [hc] at h
  · exact h
  · exact h

theorem Mach.pop_haltOut {mach : Mach} {s : StateGasMeter}
    (hs : mach.stateGas = s) : MachHaltOut s mach.pop := by
  unfold Mach.pop
  split
  · exact And.intro (by simp) hs
  · exact hs

theorem Mach.popToNat_haltOut {mach : Mach} {s : StateGasMeter}
    (hs : mach.stateGas = s) : MachHaltOut s mach.popToNat := by
  have h := Mach.pop_haltOut hs
  unfold Mach.popToNat
  rcases hp : mach.pop with ⟨e⟩ | ⟨x, m⟩ <;> rw [hp] at h
  · exact h
  · exact h

theorem Mach.popToAdr_haltOut {mach : Mach} {s : StateGasMeter}
    (hs : mach.stateGas = s) : MachHaltOut s mach.popToAdr := by
  have h := Mach.pop_haltOut hs
  unfold Mach.popToAdr
  rcases hp : mach.pop with ⟨e⟩ | ⟨x, m⟩ <;> rw [hp] at h
  · exact h
  · exact h

theorem Mach.push_haltOut {x : B256} {mach : Mach} {s : StateGasMeter}
    (hs : mach.stateGas = s) : MachHaltOut s (Mach.push x mach) := by
  unfold Mach.push
  split
  · exact hs
  · exact And.intro (by simp) hs

theorem Mach.chargeGas_haltOut {c : Nat} {mach : Mach} {s : StateGasMeter}
    (hs : mach.stateGas = s) : MachHaltOut s (Mach.chargeGas c mach) := by
  unfold Mach.chargeGas
  split
  · exact And.intro (by simp) hs
  · exact hs

theorem Devm.pop_haltOut {devm : Devm} {s : StateGasMeter}
    (hs : devm.mach.stateGas = s) : HaltOut Prod.snd s devm.pop :=
  liftMach_haltOut (Mach.pop_haltOut hs)

theorem Devm.popToNat_haltOut {devm : Devm} {s : StateGasMeter}
    (hs : devm.mach.stateGas = s) : HaltOut Prod.snd s devm.popToNat :=
  liftMach_haltOut (Mach.popToNat_haltOut hs)

theorem Devm.popToAdr_haltOut {devm : Devm} {s : StateGasMeter}
    (hs : devm.mach.stateGas = s) : HaltOut Prod.snd s devm.popToAdr :=
  liftMach_haltOut (Mach.popToAdr_haltOut hs)

theorem Devm.push_haltOut {x : B256} {devm : Devm} {s : StateGasMeter}
    (hs : devm.mach.stateGas = s) : HaltOut id s (devm.push x) :=
  liftMachExecution_haltOut (Mach.push_haltOut hs)

theorem chargeGas_haltOut {c : Nat} {devm : Devm} {s : StateGasMeter}
    (hs : devm.mach.stateGas = s) : HaltOut id s (chargeGas c devm) :=
  liftMachExecution_haltOut (Mach.chargeGas_haltOut hs)

theorem assert_haltOut {p : Prop} [Decidable p] {msg : EvmError} {devm : Devm}
    {s : StateGasMeter} (h : msg ≠ .revert) (hs : devm.mach.stateGas = s) :
    HaltOut (fun _ => devm) s (Except.assert p (⟨msg, devm⟩ : EvmError × Devm)) := by
  unfold Except.assert
  split
  · exact hs
  · exact And.intro h hs

theorem assertDynamic_haltOut (sevm : Sevm) {devm : Devm} {s : StateGasMeter}
    (hs : devm.mach.stateGas = s) :
    HaltOut (fun _ => devm) s (assertDynamic sevm devm) := by
  unfold assertDynamic
  exact assert_haltOut (by decide) hs

/-- What the `Xinst` route owes on its halt branch, against the measure `n`
the step began with: no `"Revert"` tag, and a spill `n` still covers, because
the spill is what an exceptional halt keeps. A spawn carries no outcome of its
own, so it owes nothing. -/
def XStep.Halt (n : Nat) : XStep → Prop
  | .done ex => ∀ p, ex = .error p → p.1 ≠ .revert ∧ p.2.spill ≤ n
  | .spawn _ _ => True

theorem XStep.done_ok_halt (d : Devm) (n : Nat) : (XStep.done (.ok d)).Halt n := by
  intro p hp
  exact absurd hp (by simp)

/-- The obligation on an `XStep`-valued body, before `XStep.ofExcept` collapses
its error branch into a `.done`: an error is a non-`Revert` halt still carrying
the meter `s`, and a step owes `Halt n`. -/
def xstepHalt (s : StateGasMeter) (n : Nat) : Except (EvmError × Devm) XStep → Prop
  | .error p => p.1 ≠ .revert ∧ p.2.mach.stateGas = s
  | .ok step => step.Halt n

/-- Collapsing the error branch: a halt still holding the meter `s` spills at
most what `s` spills, which is the one arithmetic fact in this corpus. -/
theorem XStep.ofExcept_halt {s : StateGasMeter} {n : Nat}
    {x : Except (EvmError × Devm) XStep}
    (hsn : s.spilled + s.committedSpill ≤ n) (h : xstepHalt s n x) :
    (XStep.ofExcept x).Halt n := by
  cases x with
  | error p =>
    have h' : p.1 ≠ .revert ∧ p.2.mach.stateGas = s := h
    intro q hq
    cases hq
    refine ⟨h'.1, ?_⟩
    unfold Devm.spill
    rw [h'.2]
    exact hsn
  | ok step => exact h

theorem xstepHalt_bind {α : Type} {proj : α → Devm} {s : StateGasMeter} {n : Nat}
    {e : Except (EvmError × Devm) α} {f : α → Except (EvmError × Devm) XStep}
    (he : HaltOut proj s e)
    (hf : ∀ a, (proj a).mach.stateGas = s → xstepHalt s n (f a)) :
    xstepHalt s n (e >>= f) := by
  cases e with
  | error p => exact he
  | ok a => exact hf a he

/-- The Amsterdam halt walk carries the bound it actually needs instead of an
unchanged meter: errors are non-`Revert` and spill-bounded, while successful
payloads satisfy the predicate needed by the remaining tail. -/
def HaltLe {α : Type} (n : Nat) (P : α → Prop) :
    Except (EvmError × Devm) α → Prop
  | .error p => p.1 ≠ .revert ∧ p.2.spill ≤ n
  | .ok a => P a

theorem HaltLe.bind {α β : Type} {n : Nat} {P : α → Prop} {Q : β → Prop}
    {e : Except (EvmError × Devm) α} {f : α → Except (EvmError × Devm) β}
    (he : HaltLe n P e) (hf : ∀ a, P a → HaltLe n Q (f a)) :
    HaltLe n Q (e >>= f) := by
  cases e with
  | error p => exact he
  | ok a => exact hf a he

theorem HaltLe.ofHaltOut {α : Type} {proj : α → Devm} {s : StateGasMeter}
    {n : Nat} {e : Except (EvmError × Devm) α}
    (hh : HaltOut proj s e) (hg : resultGas proj e ≤ n) :
    HaltLe n (fun a => (proj a).gasMeasure ≤ n) e := by
  cases e with
  | error p =>
    exact ⟨hh.1, Nat.le_trans (Devm.spill_le_gasMeasure p.2) hg⟩
  | ok a => exact hg

theorem XStep.ofExcept_haltLe {n : Nat}
    {e : Except (EvmError × Devm) XStep}
    (h : HaltLe n (fun step => step.Halt n) e) :
    (XStep.ofExcept e).Halt n := by
  cases e with
  | error p =>
    intro q hq
    cases hq
    exact h
  | ok step => exact h

theorem Devm.pop_haltLe {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun p : B256 × Devm => p.2.gasMeasure ≤ n) devm.pop :=
  HaltLe.ofHaltOut (Devm.pop_haltOut rfl) (by simpa using hn)

theorem Devm.popToNat_haltLe {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun p : Nat × Devm => p.2.gasMeasure ≤ n) devm.popToNat :=
  HaltLe.ofHaltOut (Devm.popToNat_haltOut rfl) (by simpa using hn)

theorem Devm.popToAdr_haltLe {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun p : Adr × Devm => p.2.gasMeasure ≤ n) devm.popToAdr :=
  HaltLe.ofHaltOut (Devm.popToAdr_haltOut rfl) (by simpa using hn)

theorem Devm.push_haltLe (x : B256) {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun d : Devm => d.gasMeasure ≤ n) (devm.push x) :=
  HaltLe.ofHaltOut (Devm.push_haltOut rfl)
    (by
      change resultGas id (devm.push x) ≤ n
      rw [resultGas_id]
      exact Nat.le_trans (Nat.le_of_eq (Devm.push_gasLe x devm)) hn)

@[simp] theorem Devm.restoreChildGas_spill (gas reservoir : Nat)
    (devm : Devm) :
    (devm.restoreChildGas gas reservoir).spill = devm.spill := rfl

theorem Devm.creditStateGasRefund_spill_le (amount : Nat) (devm : Devm) :
    (devm.creditStateGasRefund amount).spill ≤ devm.spill := by
  simp only [Devm.creditStateGasRefund, Devm.setMach,
    Mach.creditStateGasRefund, Devm.spill]
  omega

theorem Devm.push_haltLe_spill (x : B256) {devm : Devm} {n : Nat}
    (hn : devm.spill ≤ n) :
    HaltLe n (fun _ : Devm => True) (devm.push x) := by
  cases hp : devm.push x with
  | error p =>
    have hh := Devm.push_haltOut (x := x) (s := devm.mach.stateGas) rfl
    rw [hp] at hh
    refine ⟨hh.1, ?_⟩
    unfold Devm.spill
    rw [hh.2]
    exact hn
  | ok d => trivial

theorem chargeGas_haltLe (cost : Nat) {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun d : Devm => d.gasMeasure ≤ n) (chargeGas cost devm) :=
  HaltLe.ofHaltOut (chargeGas_haltOut rfl)
    (by
      change resultGas id (chargeGas cost devm) ≤ n
      rw [resultGas_id]
      exact Nat.le_trans (chargeGas_result_gasLe cost devm) hn)

theorem assert_haltLe {p : Prop} [Decidable p] (msg : EvmError)
    (hmsg : msg ≠ .revert) {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun _ : Unit => devm.gasMeasure ≤ n)
      (Except.assert p ⟨msg, devm⟩) :=
  HaltLe.ofHaltOut (assert_haltOut hmsg rfl) (by simpa using hn)

theorem assertDynamic_haltLe (sevm : Sevm) {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun _ : Unit => devm.gasMeasure ≤ n) (assertDynamic sevm devm) :=
  HaltLe.ofHaltOut (assertDynamic_haltOut sevm rfl) (by simpa using hn)

theorem chargeStateGas_haltLe (amount : Nat) {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun d : Devm => d.gasMeasure ≤ n) (chargeStateGas amount devm) := by
  cases h : chargeStateGas amount devm with
  | error p =>
    refine ⟨?_, ?_⟩
    · rw [chargeStateGas] at h
      unfold liftMachExecution Footprint.toExecution liftMach
        Footprint.liftOutcome at h
      unfold Mach.chargeStateGas at h
      by_cases hleft : amount ≤ devm.mach.stateGas.left
      · simp [hleft] at h
      · by_cases hgas : amount - devm.mach.stateGas.left ≤ devm.mach.gasLeft
        · simp [hleft, hgas] at h
        · simp [hleft, hgas] at h
          rw [← h]
          simp
    · have hg := chargeStateGas_result_gasLe amount devm
      rw [h] at hg
      exact Nat.le_trans (Devm.spill_le_gasMeasure p.2) (Nat.le_trans hg hn)
  | ok d =>
    have hg := chargeStateGas_result_gasLe amount devm
    rw [h] at hg
    exact Nat.le_trans hg hn

theorem genericCall.step_halt
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n) :
    (genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles).Halt n := by
  unfold genericCall.step
  split
  · exact XStep.ofExcept_halt hsn
      (xstepHalt_bind (Devm.push_haltOut (by simpa using hs))
        (fun _ _ => XStep.done_ok_halt _ _))
  · trivial

theorem genericCallAmsterdam.step_halt
    (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) {n : Nat}
    (hn : devm.spill ≤ n) :
    (genericCallAmsterdam.step sevm state devm gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize
      outputIndex outputSize code disablePrecompiles newAccountCharged
      insufficientBalance).Halt n := by
  unfold genericCallAmsterdam.step
  split
  · apply XStep.ofExcept_haltLe
    refine HaltLe.bind (Devm.push_haltLe_spill 0 ?_) ?_
    · split
      · exact Nat.le_trans (Devm.creditStateGasRefund_spill_le _ _) (by simpa using hn)
      · simpa using hn
    · intro d hd
      exact XStep.done_ok_halt d n
  · trivial

theorem genericCreate.step_halt
    (sevm : Sevm) (devm : Devm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n) :
    (genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize).Halt n := by
  unfold genericCreate.step
  apply XStep.ofExcept_halt hsn
  refine xstepHalt_bind (assert_haltOut (by decide) hs) ?_
  intro _ _
  refine xstepHalt_bind (assertDynamic_haltOut _ (by simpa using hs)) ?_
  intro _ _
  dsimp only
  split
  · exact xstepHalt_bind (Devm.push_haltOut (by simpa using hs))
      (fun _ _ => XStep.done_ok_halt _ _)
  · split
    · exact xstepHalt_bind (Devm.push_haltOut (by simpa using hs))
        (fun _ _ => XStep.done_ok_halt _ _)
    · trivial

theorem genericCreateAmsterdam.step_halt
    (sevm : Sevm) (state : StateGasRules) (devm : Devm) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    (genericCreateAmsterdam.step sevm state devm endowment newAddress
      memoryIndex memorySize).Halt n := by
  unfold genericCreateAmsterdam.step
  apply XStep.ofExcept_haltLe
  dsimp only
  split
  · refine HaltLe.bind (Devm.push_haltLe 0 ?_) ?_
    · simpa only [Devm.withReturnData_gasMeasure] using hn
    · intro d hd
      exact XStep.done_ok_halt d n
  · have haccess :
        (addAccessedAddress (devm.withReturnData []) newAddress).gasMeasure ≤ n := by
      simpa only [addAccessedAddress_gasMeasure,
        Devm.withReturnData_gasMeasure] using hn
    split
    · refine HaltLe.bind (chargeStateGas_haltLe state.newAccount haccess) ?_
      intro d1 hd
      have hwith := Devm.withholdCreateGas_gasMeasure d1
      split
      · refine HaltLe.bind (Devm.push_haltLe 0 ?_) ?_
        · simp only [Devm.incrNonce_gasMeasure]
          omega
        · intro d2 hd2
          exact XStep.done_ok_halt d2 n
      · trivial
    · simp only [bind, Except.bind]
      have hwith := Devm.withholdCreateGas_gasMeasure
        (addAccessedAddress (devm.withReturnData []) newAddress)
      split
      · refine HaltLe.bind (Devm.push_haltLe 0 ?_) ?_
        · simp only [Devm.incrNonce_gasMeasure]
          omega
        · intro d2 hd2
          exact XStep.done_ok_halt d2 n
      · trivial

theorem Xinst.step_halt_legacy (sevm : Sevm) (devm : Devm) (x : Xinst)
    {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (Xinst.step sevm devm x).Halt n := by
  cases x <;> simp only [Xinst.step, hstate] <;> apply XStep.ofExcept_halt hsn
  case create =>
    refine xstepHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨endowment, d1⟩ h1
    refine xstepHalt_bind (Devm.popToNat_haltOut h1) ?_
    rintro ⟨memoryIndex, d2⟩ h2
    refine xstepHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨memorySize, d3⟩ h3
    refine xstepHalt_bind (chargeGas_haltOut h3) ?_
    intro d4 h4
    exact genericCreate.step_halt _ _ _ _ _ _ (by simpa using h4) hsn
  case create2 =>
    refine xstepHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨endowment, d1⟩ h1
    refine xstepHalt_bind (Devm.popToNat_haltOut h1) ?_
    rintro ⟨memoryIndex, d2⟩ h2
    refine xstepHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨memorySize, d3⟩ h3
    refine xstepHalt_bind (Devm.pop_haltOut h3) ?_
    rintro ⟨salt, d4⟩ h4
    refine xstepHalt_bind (chargeGas_haltOut h4) ?_
    intro d5 h5
    exact genericCreate.step_halt _ _ _ _ _ _ (by simpa using h5) hsn
  case call =>
    refine xstepHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine xstepHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨callee, d2⟩ h2
    refine xstepHalt_bind (Devm.pop_haltOut h2) ?_
    rintro ⟨value, d3⟩ h3
    refine xstepHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputIndex, d4⟩ h4
    refine xstepHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨inputSize, d5⟩ h5
    refine xstepHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputIndex, d6⟩ h6
    refine xstepHalt_bind (Devm.popToNat_haltOut h6) ?_
    rintro ⟨outputSize, d7⟩ h7
    refine xstepHalt_bind (chargeGas_haltOut (by
      simpa only [GasSchedule.accessDelegation_stateGas,
        addAccessedAddress_stateGas] using h7)) ?_
    intro d8 h8
    refine xstepHalt_bind (assert_haltOut (by decide) h8) ?_
    intro _ _
    split
    · exact xstepHalt_bind (Devm.push_haltOut (by simpa using h8))
        (fun _ _ => XStep.done_ok_halt _ _)
    · exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h8) hsn
  case callcode =>
    refine xstepHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine xstepHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨codeAddress, d2⟩ h2
    refine xstepHalt_bind (Devm.pop_haltOut h2) ?_
    rintro ⟨value, d3⟩ h3
    refine xstepHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputIndex, d4⟩ h4
    refine xstepHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨inputSize, d5⟩ h5
    refine xstepHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputIndex, d6⟩ h6
    refine xstepHalt_bind (Devm.popToNat_haltOut h6) ?_
    rintro ⟨outputSize, d7⟩ h7
    refine xstepHalt_bind (chargeGas_haltOut (by
      simpa only [GasSchedule.accessDelegation_stateGas,
        addAccessedAddress_stateGas] using h7)) ?_
    intro d8 h8
    split
    · exact xstepHalt_bind (Devm.push_haltOut (by simpa using h8))
        (fun _ _ => XStep.done_ok_halt _ _)
    · exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h8) hsn
  case delegatecall =>
    refine xstepHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine xstepHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨codeAddress, d2⟩ h2
    refine xstepHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨inputIndex, d3⟩ h3
    refine xstepHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputSize, d4⟩ h4
    refine xstepHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨outputIndex, d5⟩ h5
    refine xstepHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputSize, d6⟩ h6
    refine xstepHalt_bind (chargeGas_haltOut (by
      simpa only [GasSchedule.accessDelegation_stateGas,
        addAccessedAddress_stateGas] using h6)) ?_
    intro d7 h7
    exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h7) hsn
  case staticcall =>
    refine xstepHalt_bind (Devm.pop_haltOut hs) ?_
    rintro ⟨gas, d1⟩ h1
    refine xstepHalt_bind (Devm.popToAdr_haltOut h1) ?_
    rintro ⟨target, d2⟩ h2
    refine xstepHalt_bind (Devm.popToNat_haltOut h2) ?_
    rintro ⟨inputIndex, d3⟩ h3
    refine xstepHalt_bind (Devm.popToNat_haltOut h3) ?_
    rintro ⟨inputSize, d4⟩ h4
    refine xstepHalt_bind (Devm.popToNat_haltOut h4) ?_
    rintro ⟨outputIndex, d5⟩ h5
    refine xstepHalt_bind (Devm.popToNat_haltOut h5) ?_
    rintro ⟨outputSize, d6⟩ h6
    refine xstepHalt_bind (chargeGas_haltOut (by
      simpa only [GasSchedule.accessDelegation_stateGas,
        addAccessedAddress_stateGas] using h6)) ?_
    intro d7 h7
    exact genericCall.step_halt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by simpa using h7) hsn

theorem Xinst.step_halt (sevm : Sevm) (devm : Devm) (x : Xinst)
    {s : StateGasMeter} {n : Nat}
    (hs : devm.mach.stateGas = s) (hsn : s.spilled + s.committedSpill ≤ n)
    (hn : devm.gasMeasure ≤ n) :
    (Xinst.step sevm devm x).Halt n := by
  cases hstate : sevm.benvStat.rules.stateGas with
  | none =>
    exact Xinst.step_halt_legacy sevm devm x hs hsn hstate
  | some state =>
    cases x <;> simp only [Xinst.step, hstate] <;> apply XStep.ofExcept_haltLe
    case create =>
      refine HaltLe.bind (assertDynamic_haltLe sevm hn) ?_
      intro _ h0
      refine HaltLe.bind (Devm.pop_haltLe h0) ?_
      rintro ⟨endowment, d1⟩ h1
      refine HaltLe.bind (Devm.popToNat_haltLe h1) ?_
      rintro ⟨memoryIndex, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨memorySize, d3⟩ h3
      refine HaltLe.bind (chargeGas_haltLe _ h3) ?_
      intro d4 h4
      refine HaltLe.bind (assert_haltLe _ (by decide) h4) ?_
      intro _ _
      apply genericCreateAmsterdam.step_halt
      simpa only [Devm.memExtends_gasMeasure] using h4
    case create2 =>
      refine HaltLe.bind (assertDynamic_haltLe sevm hn) ?_
      intro _ h0
      refine HaltLe.bind (Devm.pop_haltLe h0) ?_
      rintro ⟨endowment, d1⟩ h1
      refine HaltLe.bind (Devm.popToNat_haltLe h1) ?_
      rintro ⟨memoryIndex, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨memorySize, d3⟩ h3
      refine HaltLe.bind (Devm.pop_haltLe h3) ?_
      rintro ⟨salt, d4⟩ h4
      refine HaltLe.bind (chargeGas_haltLe _ h4) ?_
      intro d5 h5
      refine HaltLe.bind (assert_haltLe _ (by decide) h5) ?_
      intro _ _
      apply genericCreateAmsterdam.step_halt
      simpa only [Devm.memExtends_gasMeasure] using h5
    case call =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨callee, d2⟩ h2
      refine HaltLe.bind (Devm.pop_haltLe h2) ?_
      rintro ⟨value, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputIndex, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨inputSize, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputIndex, d6⟩ h6
      refine HaltLe.bind (Devm.popToNat_haltLe h6) ?_
      rintro ⟨outputSize, d7⟩ h7
      refine HaltLe.bind (assert_haltLe _ (by decide) h7) ?_
      intro _ hstatic
      refine HaltLe.bind (assert_haltLe _ (by decide) hstatic) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess (addAccessedAddress d7 callee)
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 callee) callee).1
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 callee) callee).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure] using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d8 h8
        split
        · refine HaltLe.bind (chargeStateGas_haltLe _ h8) ?_
          intro d9 h9
          refine HaltLe.bind (chargeGas_haltLe _ h9) ?_
          intro d10 h10
          apply genericCallAmsterdam.step_halt
          exact Nat.le_trans (Devm.spill_le_gasMeasure _)
            (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
              Devm.memExtends_gasMeasure] using h10)
        · simp only [bind, Except.bind]
          refine HaltLe.bind (chargeGas_haltLe _ h8) ?_
          intro d9 h9
          apply genericCallAmsterdam.step_halt
          exact Nat.le_trans (Devm.spill_le_gasMeasure _)
            (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
              Devm.memExtends_gasMeasure] using h9)
    case callcode =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨codeAddress, d2⟩ h2
      refine HaltLe.bind (Devm.pop_haltLe h2) ?_
      rintro ⟨value, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputIndex, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨inputSize, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputIndex, d6⟩ h6
      refine HaltLe.bind (Devm.popToNat_haltLe h6) ?_
      rintro ⟨outputSize, d7⟩ h7
      refine HaltLe.bind (assert_haltLe _ (by decide) h7) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess (addAccessedAddress d7 codeAddress)
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 codeAddress) codeAddress).1
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d7 codeAddress) codeAddress).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure] using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d8 h8
        apply genericCallAmsterdam.step_halt
        exact Nat.le_trans (Devm.spill_le_gasMeasure _)
          (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
            Devm.memExtends_gasMeasure] using h8)
    case delegatecall =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨codeAddress, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨inputIndex, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputSize, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨outputIndex, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputSize, d6⟩ h6
      refine HaltLe.bind (assert_haltLe _ (by decide) h6) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess (addAccessedAddress d6 codeAddress)
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).1
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure] using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d7 h7
        apply genericCallAmsterdam.step_halt
        exact Nat.le_trans (Devm.spill_le_gasMeasure _)
          (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
            Devm.memExtends_gasMeasure] using h7)
    case staticcall =>
      refine HaltLe.bind (Devm.pop_haltLe hn) ?_
      rintro ⟨gas, d1⟩ h1
      refine HaltLe.bind (Devm.popToAdr_haltLe h1) ?_
      rintro ⟨codeAddress, d2⟩ h2
      refine HaltLe.bind (Devm.popToNat_haltLe h2) ?_
      rintro ⟨inputIndex, d3⟩ h3
      refine HaltLe.bind (Devm.popToNat_haltLe h3) ?_
      rintro ⟨inputSize, d4⟩ h4
      refine HaltLe.bind (Devm.popToNat_haltLe h4) ?_
      rintro ⟨outputIndex, d5⟩ h5
      refine HaltLe.bind (Devm.popToNat_haltLe h5) ?_
      rintro ⟨outputSize, d6⟩ h6
      refine HaltLe.bind (assert_haltLe _ (by decide) h6) ?_
      intro _ hpre
      refine HaltLe.bind (assert_haltLe _ (by decide) ?_) ?_
      · simpa only [addAccessedAddress_gasMeasure] using hpre
      · intro _ hfull
        have haccess :
            (completeDelegationAccess (addAccessedAddress d6 codeAddress)
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).1
              (sevm.benvStat.rules.gas.delegationCost
                (addAccessedAddress d6 codeAddress) codeAddress).2.1).2.gasMeasure ≤ n := by
          simpa only [completeDelegationAccess_gasMeasure] using hfull
        refine HaltLe.bind (chargeGas_haltLe _ haccess) ?_
        intro d7 h7
        apply genericCallAmsterdam.step_halt
        exact Nat.le_trans (Devm.spill_le_gasMeasure _)
          (by simpa only [Devm.drainStateGasReservoir_gasMeasure,
            Devm.memExtends_gasMeasure] using h7)

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
  ∀ stateGas : Option StateGasRules, ∀ d : Devm,
    executeCode.handleErrorWith stateGas ex = .ok d → d.gasMeasure ≤ n

theorem Execution.SettledGasLe.mono {m n : Nat} {ex : Execution} (h : m ≤ n)
    (hs : ex.SettledGasLe m) : ex.SettledGasLe n :=
  fun stateGas d hd => Nat.le_trans (hs stateGas d hd) h

/-- The route the `Rinst`/`Jinst`/`Linst` corpus takes. -/
theorem Execution.settledGasLe_of_gasLe {n : Nat} {ex : Execution}
    (h : ex.gasMeasure ≤ n) : ex.SettledGasLe n :=
  fun _ _ hd => Nat.le_trans (executeCode.handleErrorWith_ok_gasLe hd) h

/-- The route the `Xinst` family takes: bound the successful branch, rule out
the one tag that would let an error carry live gas through, and bound the spill
an exceptional halt keeps. -/
theorem Execution.settledGasLe_of_halt {n : Nat} {ex : Execution}
    (hok : ∀ d, ex = .ok d → d.gasMeasure ≤ n)
    (hhalt : ∀ p, ex = .error p → p.1 ≠ .revert ∧ p.2.spill ≤ n) :
    ex.SettledGasLe n := by
  intro stateGas d hd
  cases ex with
  | ok d0 =>
    cases stateGas <;>
      simp only [executeCode.handleErrorWith, executeCode.handleError,
        executeCode.handleErrorAmsterdam, Except.ok.injEq] at hd <;>
      subst d <;> exact hok d0 rfl
  | error p =>
    obtain ⟨err, evm⟩ := p
    obtain ⟨hnr, hsp⟩ := hhalt _ rfl
    dsimp only at hnr hsp
    cases stateGas with
    | none =>
      cases err with
      | halt reason =>
        simp only [executeCode.handleErrorWith, executeCode.handleError,
          Except.ok.injEq] at hd
        rw [← hd, Devm.setMeta_gasMeasure, Devm.withGasLeft_gasMeasure]
        omega
      | revert => exact absurd rfl hnr
      | crypto reason => exact absurd hd (by simp [executeCode.handleErrorWith,
          executeCode.handleError])
      | internal reason => exact absurd hd (by simp [executeCode.handleErrorWith,
          executeCode.handleError])
    | some state =>
      cases err with
      | halt reason =>
        simp only [executeCode.handleErrorWith, executeCode.handleErrorAmsterdam,
          Except.ok.injEq] at hd
        rw [← hd, Devm.setMeta_gasMeasure]
        exact Nat.le_trans
          (Devm.restoreStateGas_forfeitRemainingGas_gasMeasure_le_spill _)
          hsp
      | revert => exact absurd rfl hnr
      | crypto reason => exact absurd hd (by simp [executeCode.handleErrorWith,
          executeCode.handleErrorAmsterdam])
      | internal reason => exact absurd hd (by simp [executeCode.handleErrorWith,
          executeCode.handleErrorAmsterdam])

theorem processCreateMessage.chargeCodeGas_gasLe (rules : ForkRules) (devm : Devm) :
    (processCreateMessage.chargeCodeGas rules devm).gasMeasure ≤ devm.gasMeasure := by
  unfold processCreateMessage.chargeCodeGas
  dsimp only
  split
  · split
    · simp
    · refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
      intro d
      split <;> simp
  · split
    · simp
    · split
      · simp
      · refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
        intro d
        exact chargeStateGas_result_gasLe _ d

theorem processMessage.settle_ok_gasLe {msg : Msg}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {d : Devm}
    (h : processMessage.settle msg r = .ok d) :
    ∃ d0, r = .ok d0 ∧ d.gasMeasure ≤ d0.gasMeasure := by
  cases r with
  | error e =>
    exact absurd h (by simp [processMessage.settle, bind, Except.bind])
  | ok d0 =>
    refine ⟨d0, rfl, ?_⟩
    simp only [processMessage.settle, bind, Except.bind] at h
    split at h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.rollback_gasMeasure]
    · simp only [Except.ok.injEq] at h
      rw [← h]

theorem processCreateMessage.settle_ok_gasLe {msg : Msg}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {d : Devm}
    (h : processCreateMessage.settle msg r = .ok d) :
    ∃ d0, r = .ok d0 ∧ d.gasMeasure ≤ d0.gasMeasure := by
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
        simp only [Execution.gasMeasure_error, Execution.gasMeasure_ok] at hc
      · cases err with
        | halt reason =>
          dsimp only at h
          split at h
          · simp only [Except.ok.injEq] at h
            rw [← h]
            unfold processCreateMessage.exceptionalHalt
            rw [Devm.setMeta_gasMeasure, Devm.withGasLeft_gasMeasure,
              Devm.rollback_spill]
            have hm := Devm.gasMeasure_eq d1
            omega
          · simp only [Except.ok.injEq] at h
            rw [← h]
            unfold processCreateMessage.exceptionalHaltAmsterdam
            rw [Devm.setMeta_gasMeasure]
            exact Nat.le_trans (Devm.forfeitRemainingGas_gasMeasure_le _)
              (by simpa using hc)
        | revert => nomatch h
        | crypto reason => nomatch h
        | internal reason => nomatch h
      · dsimp only at h
        simp only [Except.ok.injEq] at h
        rw [← h, Devm.setCode_gasMeasure]
        exact hc
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.rollback_gasMeasure]

theorem Frame.settleMsg_ok_gasLe {f : Frame}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {d : Devm}
    (h : f.settleMsg r = .ok d) : ∃ d0, r = .ok d0 ∧ d.gasMeasure ≤ d0.gasMeasure := by
  unfold Frame.settleMsg at h
  dsimp only at h
  split at h
  · obtain ⟨d1, h1, hle1⟩ := processCreateMessage.settle_ok_gasLe h
    obtain ⟨d0, h0, hle0⟩ := processMessage.settle_ok_gasLe h1
    exact ⟨d0, h0, Nat.le_trans hle1 hle0⟩
  · exact processMessage.settle_ok_gasLe h

theorem Frame.settle_gasLe {f : Frame} {raw : Execution} {n : Nat} {d : Devm}
    (hraw : raw.SettledGasLe n) (h : f.settle raw = .ok d) : d.gasMeasure ≤ n := by
  unfold Frame.settle at h
  obtain ⟨d0, h0, hle⟩ := Frame.settleMsg_ok_gasLe h
  exact Nat.le_trans hle (hraw f.inner.benv.stat.rules.stateGas d0 h0)

/-! ## Entering a frame

A frame either hands the child exactly the inner message's gas, or resolves
without running a child at all — and in that case its result is a settled
precompile outcome, which the settlement bound already covers. -/

@[simp] theorem Msg.withBenv_gas (msg : Msg) (benv : Benv) :
    (msg.withBenv benv).gas = msg.gas := rfl

@[simp] theorem initEvm_gasMeasure (msg : Msg) :
    (initEvm msg).dyna.gasMeasure = msg.gas := rfl

theorem executeCode.enter_inl_gasMeasure {msg : Msg} {evm : Evm}
    (h : executeCode.enter msg = .inl evm) : evm.dyna.gasMeasure = msg.gas := by
  unfold executeCode.enter at h
  dsimp only at h
  split at h
  · simp only [Sum.inl.injEq] at h
    rw [← h, initEvm_gasMeasure]
  · split at h
    · nomatch h
    · simp only [Sum.inl.injEq] at h
      rw [← h, initEvm_gasMeasure]

theorem executeCode.enter_inr_gasLe {msg : Msg} {raw : Execution}
    (h : executeCode.enter msg = .inr raw) : raw.gasMeasure ≤ msg.gas := by
  unfold executeCode.enter at h
  dsimp only at h
  split at h
  · nomatch h
  · split at h
    · simp only [Sum.inr.injEq] at h
      rw [← h]
      exact executePrecomp_gasLe _ _
    · nomatch h

/-! ### Every frame the interpreter enters runs under the same rules

The gas-decreasing obligations now rest on `rules.Valid` -- Amsterdam reprices
the numbers they lean on, so the numbers are no longer literals a `decide` can
settle. The driver recurses into *child* frames, so it needs the premise to
travel with them, and this is the invariant that makes it travel: a spawned
frame's rules are the spawning frame's rules.

That is a fact about the message-building path rather than about gas. A child's
`Benv` is the parent's `benvStat` with only its `state` moved -- `callMsg` and
`createMsg` copy `sevm.benvStat` verbatim, `benvAfterTransfer` rewrites
balances, `processCreateMessage.msg` rewrites storage and the nonce -- so
nothing between the spawn and the child's first instruction can change which
fork it is running. -/

@[simp] theorem Msg.withBenv_stat_rules (msg : Msg) (benv : Benv) :
    (msg.withBenv benv).benv.stat.rules = benv.stat.rules := rfl

@[simp] theorem initEvm_rules (msg : Msg) :
    (initEvm msg).sta.benvStat.rules = msg.benv.stat.rules := rfl

@[simp] theorem Benv.withState_stat (benv : Benv) (st : State) :
    (benv.withState st).stat = benv.stat := rfl

@[simp] theorem Benv.addBal_stat (benv : Benv) (adr : Adr) (val : B256) :
    (benv.addBal adr val).stat = benv.stat := rfl

theorem Benv.subBal_stat {benv benv' : Benv} {adr : Adr} {val : B256}
    (h : benv.subBal adr val = some benv') : benv'.stat = benv.stat := by
  unfold Benv.subBal at h
  cases hs : benv.state.subBal adr val with
  | none => rw [hs] at h; nomatch h
  | some wor =>
    rw [hs] at h
    cases h
    rfl

theorem Msg.benvAfterTransfer_rules {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) :
    benv.stat.rules = msg.benv.stat.rules := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · obtain ⟨b, hb, hok⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at hok
    rw [← hok]
    -- Both halves of the transfer rewrite only `Benv.state`, so the rules
    -- survive once the `Option.toExcept` is resolved.
    unfold Option.toExcept at hb
    cases hsub : msg.benv.subBal msg.caller msg.value with
    | none => rw [hsub] at hb; nomatch hb
    | some b' =>
      rw [hsub] at hb
      simp only [Except.ok.injEq] at hb
      rw [← hb, Benv.addBal_stat, Benv.subBal_stat hsub]
  · simp only [Except.ok.injEq] at h
    rw [← h]

theorem executeCode.enter_inl_rules {msg : Msg} {evm : Evm}
    (h : executeCode.enter msg = .inl evm) :
    evm.sta.benvStat.rules = msg.benv.stat.rules := by
  unfold executeCode.enter at h
  dsimp only at h
  split at h
  · simp only [Sum.inl.injEq] at h
    rw [← h, initEvm_rules]
  · split at h
    · nomatch h
    · simp only [Sum.inl.injEq] at h
      rw [← h, initEvm_rules]

theorem Frame.enter_run_rules {f : Frame} {child : Evm}
    (h : f.enter = .run child) :
    child.sta.benvStat.rules = f.inner.benv.stat.rules := by
  unfold Frame.enter at h
  split at h
  · nomatch h
  · rename_i benv hbenv
    split at h
    · rename_i evm henter
      simp only [FrameEntry.run.injEq] at h
      rw [← h, executeCode.enter_inl_rules henter, Msg.withBenv_stat_rules,
        Msg.benvAfterTransfer_rules hbenv]
    · nomatch h

/-! ### A spawned frame carries the spawning frame's block environment

Both frame builders copy `sevm.benvStat` verbatim -- `callMsg` and `createMsg`
write `stat := sevm.benvStat` into the child's `Benv`, and `Frame.ofCreate`'s
`processCreateMessage.msg` rewrites only storage and the nonce -- so a spawned
frame runs under the spawning frame's rules by construction. These lemmas lift
that from the two builders to `Evm.step`, which is where the driver needs it. -/

@[simp] theorem callMsg_stat
    (sevm : Sevm) (evm1 : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (shouldTransferValue isStaticcall : Bool)
    (calldata : Bytes) (code : ByteArray) (disablePrecompiles : Bool) :
    (callMsg sevm evm1 gas value caller target codeAddress shouldTransferValue
      isStaticcall calldata code disablePrecompiles).benv.stat
      = sevm.benvStat := rfl

@[simp] theorem createMsg_stat
    (sevm : Sevm) (devm : Devm) (createGas : Nat) (endowment : B256)
    (newAddress : Adr) (calldata : Bytes) :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.stat
      = sevm.benvStat := rfl

@[simp] theorem processCreateMessage_msg_stat (msg : Msg) :
    (processCreateMessage.msg msg).benv.stat = msg.benv.stat := rfl

@[simp] theorem Frame.ofCall_inner_stat (msg : Msg) :
    (Frame.ofCall msg).inner.benv.stat = msg.benv.stat := rfl

@[simp] theorem Frame.ofCreate_inner_stat (msg : Msg) :
    (Frame.ofCreate msg).inner.benv.stat = msg.benv.stat := rfl

/-- A spawn survives `XStep.ofExcept` only by having been one. -/
theorem XStep.ofExcept_spawn {x : Except (EvmError × Devm) XStep}
    {frame : Frame} {rsm : Resume} (h : XStep.ofExcept x = .spawn frame rsm) :
    x = .ok (.spawn frame rsm) := by
  cases x with
  | error e => simp only [XStep.ofExcept] at h; nomatch h
  | ok step => simp only [XStep.ofExcept] at h; rw [h]

theorem genericCall.step_spawn_stat {sevm : Sevm} {devm : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {frame : Frame} {rsm : Resume}
    (h : genericCall.step sevm devm gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex
      outputSize code disablePrecompiles = .spawn frame rsm) :
    frame.inner.benv.stat = sevm.benvStat := by
  unfold genericCall.step at h
  split at h
  · -- The depth-0 refund never spawns.
    have hx := XStep.ofExcept_spawn h
    obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hx
    nomatch hx
  · simp only [XStep.spawn.injEq] at h
    rw [← h.1, Frame.ofCall_inner_stat, callMsg_stat]

theorem genericCreate.step_spawn_stat {sevm : Sevm} {devm : Devm}
    {endowment : B256} {newAddress : Adr} {memoryIndex memorySize : Nat}
    {frame : Frame} {rsm : Resume}
    (h : genericCreate.step sevm devm endowment newAddress memoryIndex
      memorySize = .spawn frame rsm) :
    frame.inner.benv.stat = sevm.benvStat := by
  unfold genericCreate.step at h
  have hx := XStep.ofExcept_spawn h
  obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
  obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
  dsimp only at hx
  split at hx
  · -- Insufficient balance, nonce overflow or depth zero: no spawn.
    obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hx
    nomatch hx
  · split at hx
    · -- The address is occupied: no spawn.
      obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at hx
      nomatch hx
    · simp only [Pure.pure, Except.pure, Except.ok.injEq, XStep.spawn.injEq] at hx
      rw [← hx.1, Frame.ofCreate_inner_stat, createMsg_stat]

theorem Frame.enter_run_gasMeasure {f : Frame} {child : Evm}
    (h : f.enter = .run child) : child.dyna.gasMeasure = f.inner.gas := by
  unfold Frame.enter at h
  split at h
  · nomatch h
  · split at h
    · rename_i evm henter
      simp only [FrameEntry.run.injEq] at h
      rw [← h, executeCode.enter_inl_gasMeasure henter, Msg.withBenv_gas]
    · nomatch h

theorem Frame.enter_done_gasLe {f : Frame}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {d : Devm}
    (h : f.enter = .done r) (hd : r = .ok d) : d.gasMeasure ≤ f.inner.gas := by
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

`Resume.run_ok_gasMeasure` already bounds the successful result by
`rsm.parentGas + child.gasMeasure`. The bound below covers the error branch as
well, which the driver needs because a resume that overflows the parent's stack
still produces a raw result the *grandparent* has to settle. -/

theorem Resume.run_gasLe {rsm : Resume}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {m : Nat}
    (hr : ∀ d, r = .ok d → d.gasMeasure ≤ m) :
    Execution.gasMeasure (rsm.run r) ≤ rsm.parentGas + m := by
  cases rsm with
  | create parent newAddress =>
    cases r with
    | error e =>
      simp only [Resume.run, liftToExecution, bind, Except.bind,
        Execution.gasMeasure_error, Resume.parentGas, Devm.setWorld_gasMeasure,
        Devm.withCreatedAccounts_gasMeasure]
      omega
    | ok child =>
      have hc := hr child rfl
      have hcl := Devm.gasLeft_le_gasMeasure child
      simp only [Resume.run, liftToExecution, bind, Except.bind, Resume.parentGas]
      split <;> simp only [Devm.push_gasLe, incorporateChildOnError_gasMeasure,
        incorporateChildOnSuccess_gasMeasure] <;> omega
  | call parent outputIndex outputSize =>
    cases r with
    | error e =>
      simp only [Resume.run, liftToExecution, bind, Except.bind,
        Execution.gasMeasure_error, Resume.parentGas, Devm.setWorld_gasMeasure,
        Devm.withCreatedAccounts_gasMeasure]
      omega
    | ok child =>
      have hc := hr child rfl
      have hcl := Devm.gasLeft_le_gasMeasure child
      simp only [Resume.run, liftToExecution, bind, Except.bind, Resume.parentGas]
      split <;>
        refine gasLe_bind_id ?_ (fun d => by simp) <;>
        simp only [Devm.push_gasLe, incorporateChildOnError_gasMeasure,
          incorporateChildOnSuccess_gasMeasure] <;> omega
  | createAmsterdam state parent newAddress newAccountCharged =>
    cases r with
    | error e =>
      simp only [Resume.run, liftToExecution, bind, Except.bind,
        Execution.gasMeasure_error, Resume.parentGas, Devm.setWorld_gasMeasure,
        Devm.withCreatedAccounts_gasMeasure]
      omega
    | ok child =>
      have hc := hr child rfl
      simp only [Resume.run, liftToExecution, bind, Except.bind, Resume.parentGas]
      split
      · by_cases hsettled : child.AmsterdamFailedChildSettled
        · simp only [Except.assert, if_pos hsettled, Devm.push_gasLe, apply_ite,
            Devm.creditStateGasRefund_gasMeasure, ite_self]
          have he := incorporateChildAmsterdamOnError_gasMeasure_of_child_settled
            (parent := parent) (child := child) (rd := child.output) hsettled
          omega
        · simp only [Except.assert, if_neg hsettled, Execution.gasMeasure_error]
          omega
      · by_cases huncommitted : child.AmsterdamChildUncommitted
        · simp only [Except.assert, if_pos huncommitted, Devm.push_gasLe]
          have he :=
            incorporateChildAmsterdamOnSuccess_gasMeasure_of_child_uncommitted
              (parent := parent) (child := child) (rd := []) huncommitted
          omega
        · simp only [Except.assert, if_neg huncommitted, Execution.gasMeasure_error]
          omega
  | callAmsterdam state parent outputIndex outputSize newAccountCharged =>
    cases r with
    | error e =>
      simp only [Resume.run, liftToExecution, bind, Except.bind,
        Execution.gasMeasure_error, Resume.parentGas, Devm.setWorld_gasMeasure,
        Devm.withCreatedAccounts_gasMeasure]
      omega
    | ok child =>
      have hc := hr child rfl
      simp only [Resume.run, liftToExecution, bind, Except.bind, Resume.parentGas]
      split
      · by_cases hsettled : child.AmsterdamFailedChildSettled
        · simp only [Except.assert, if_pos hsettled]
          refine gasLe_bind_id ?_ (fun d => by simp)
          simp only [Devm.push_gasLe, apply_ite,
            Devm.creditStateGasRefund_gasMeasure, ite_self]
          have he := incorporateChildAmsterdamOnError_gasMeasure_of_child_settled
            (parent := parent) (child := child) (rd := child.output) hsettled
          omega
        · simp only [Except.assert, if_neg hsettled, Execution.gasMeasure_error]
          omega
      · by_cases huncommitted : child.AmsterdamChildUncommitted
        · simp only [Except.assert, if_pos huncommitted]
          refine gasLe_bind_id ?_ (fun d => by simp)
          simp only [Devm.push_gasLe]
          have he :=
            incorporateChildAmsterdamOnSuccess_gasMeasure_of_child_uncommitted
              (parent := parent) (child := child) (rd := child.output) huncommitted
          omega
        · simp only [Except.assert, if_neg huncommitted, Execution.gasMeasure_error]
          omega

/-! ## The step-level obligation

One statement covering all three outcomes of `Evm.step`, so that the driver
induction has a single hypothesis to consume. -/

/-- What one step of the driver owes, measured against the frame's gas at the
start of the step. -/
def Step.GasBound (sevm : Sevm) (n : Nat) : Step → Prop
  | .halt ex => ex.SettledGasLe n
  | .cont _ devm => devm.gasMeasure < n
  | .spawn frame rsm _ =>
      frame.inner.gas + rsm.parentGas < n ∧
        frame.inner.benv.stat.rules = sevm.benvStat.rules

theorem Step.ofExecution_gasBound {sevm : Sevm} {pc n : Nat} {ex : Execution}
    (hok : ∀ d, ex = .ok d → d.gasMeasure < n) (hset : ex.SettledGasLe n) :
    (Step.ofExecution pc ex).GasBound sevm n := by
  cases ex with
  | error e => exact hset
  | ok d => exact hok d rfl

theorem Step.ofJump_gasBound {sevm : Sevm} {n : Nat}
    {x : Except (EvmError × Devm) (Nat × Devm)}
    (hok : ∀ p, x = .ok p → p.2.gasMeasure < n) (hle : resultGas Prod.snd x ≤ n) :
    (Step.ofJump x).GasBound sevm n := by
  cases x with
  | error e => exact Execution.settledGasLe_of_gasLe hle
  | ok p => exact hok p rfl

theorem XStep.toStep_gasBound {sevm : Sevm} {pc n : Nat} {step : XStep}
    (hdec : step.GasDecreasing sevm n) (hh : step.Halt n) :
    (XStep.toStep pc step).GasBound sevm n := by
  cases step with
  | done ex =>
    refine Step.ofExecution_gasBound hdec ?_
    exact Execution.settledGasLe_of_halt
      (fun d hd => Nat.le_of_lt (hdec d hd)) hh
  | spawn frame rsm => exact hdec

theorem Ninst.step_push_gasLt {xs : Bytes} {evm : Evm} {devm : Devm}
    (h : (chargeGas (if xs = [] then gBase else gVerylow) evm.dyna >>=
      Devm.push xs.toB256) = .ok devm) : devm.gasMeasure < evm.dyna.gasMeasure := by
  obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
  have e1 := chargeGas_gasMeasure h1
  have e2 := Devm.push_gasMeasure h2
  have hpos : 0 < (if xs = [] then gBase else gVerylow) := by
    split <;> decide
  omega

theorem Ninst.step_gasBound (evm : Evm) (n : Ninst)
    (hv : evm.sta.benvStat.rules.Valid) :
    (Ninst.step evm n).GasBound evm.sta evm.dyna.gasMeasure := by
  cases n with
  | push xs b =>
    refine Step.ofExecution_gasBound (fun d hd => Ninst.step_push_gasLt hd) ?_
    refine Execution.settledGasLe_of_gasLe ?_
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => Nat.le_of_eq (Devm.push_gasLe _ d))
  | reg r =>
    refine Step.ofExecution_gasBound
      (fun d hd => Rinst.runCore_gasLt evm.pc evm.dyna evm.sta r hv hd) ?_
    exact Execution.settledGasLe_of_gasLe
      (Rinst.runCore_gasLe evm.pc evm.dyna evm.sta r)
  | exec x =>
    exact XStep.toStep_gasBound (Xinst.step_gasDecreasing evm.sta evm.dyna x hv)
      (Xinst.step_halt evm.sta evm.dyna x rfl
        (Devm.spill_le_gasMeasure _) (Nat.le_refl _))

theorem Evm.step_gasBound (evm : Evm) (hv : evm.sta.benvStat.rules.Valid) :
    evm.step.GasBound evm.sta evm.dyna.gasMeasure := by
  unfold Evm.step
  split
  · exact Execution.settledGasLe_of_gasLe (Nat.le_of_eq rfl)
  · exact Ninst.step_gasBound evm _ hv
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
    (execFueled evm fuel).run = some raw → evm.sta.benvStat.rules.Valid →
      raw.SettledGasLe evm.dyna.gasMeasure := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm raw h _hv
    rw [execFueled] at h
    simp only [Fueled.exhausted_run] at h
    nomatch h
  | succ fuel ih =>
    intro evm raw h hv
    have hstep := Evm.step_gasBound evm hv
    rw [execFueled] at h
    rcases hs : evm.step with ⟨ex⟩ | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩
    · rw [hs] at h hstep
      simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      rw [← h]
      exact hstep
    · rw [hs] at h hstep
      simp only [Step.GasBound] at hstep
      exact (ih _ h hv).mono (Nat.le_of_lt hstep)
    · rw [hs] at h hstep
      simp only [Step.GasBound] at hstep
      -- The spawn obligation now also says the child runs under these rules,
      -- which is what carries the validity premise into the recursion.
      obtain ⟨hstep, hrules⟩ := hstep
      dsimp only at h
      rcases he : frame.enter with r | child
      · rw [he] at h
        dsimp only at h
        have hres := Resume.run_gasLe (rsm := rsm) (m := frame.inner.gas)
          (fun d hd => Frame.enter_done_gasLe he hd)
        rcases hrun : rsm.run r with ⟨e⟩ | d1
        · rw [hrun] at h hres
          simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          simp only [Execution.gasMeasure_error] at hres
          rw [← h]
          refine Execution.settledGasLe_of_gasLe ?_
          simp only [Execution.gasMeasure_error]
          omega
        · rw [hrun] at h hres
          simp only [Execution.gasMeasure_ok] at hres
          exact (ih _ h hv).mono (show d1.gasMeasure ≤ evm.dyna.gasMeasure by omega)
      · rw [he] at h
        dsimp only at h
        rcases hc : (execFueled child fuel).run with _ | raw'
        · rw [hc] at h
          simp only [Fueled.exhausted_run] at h
          nomatch h
        · rw [hc] at h
          dsimp only at h
          have hchild :=
            ih child hc (by rw [Frame.enter_run_rules he, hrules]; exact hv)
          rw [Frame.enter_run_gasMeasure he] at hchild
          have hres := Resume.run_gasLe (rsm := rsm) (r := frame.settle raw')
            (m := frame.inner.gas) (fun d hd => Frame.settle_gasLe hchild hd)
          rcases hrun : rsm.run (frame.settle raw') with ⟨e⟩ | d1
          · rw [hrun] at h hres
            simp only [Fueled.ofExcept_run, Option.some.injEq] at h
            simp only [Execution.gasMeasure_error] at hres
            rw [← h]
            refine Execution.settledGasLe_of_gasLe ?_
            simp only [Execution.gasMeasure_error]
            omega
          · rw [hrun] at h hres
            simp only [Execution.gasMeasure_ok] at hres
            exact (ih _ h hv).mono (show d1.gasMeasure ≤ evm.dyna.gasMeasure by omega)

/-- **Sufficiency.** Fuel strictly greater than the frame's measure always
carries the driver to a result. The base case is vacuous: the hypothesis forces
`fuel > 0`. -/
theorem execFueled_run_isSome : ∀ (fuel : Nat) (evm : Evm),
    evm.dyna.gasMeasure < fuel → evm.sta.benvStat.rules.Valid →
      ∃ raw : Execution, (execFueled evm fuel).run = some raw := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm h _hv
    omega
  | succ fuel ih =>
    intro evm h hv
    have hstep := Evm.step_gasBound evm hv
    rw [execFueled]
    rcases hs : evm.step with ⟨ex⟩ | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩ <;>
      rw [hs] at hstep <;> simp only [Step.GasBound] at hstep <;> dsimp only
    · exact ⟨ex, rfl⟩
    · have hlt : devm.gasMeasure < fuel := by omega
      exact ih _ hlt hv
    · obtain ⟨hstep, hrules⟩ := hstep
      rcases he : frame.enter with r | child <;> dsimp only
      · rcases hrun : rsm.run r with ⟨e⟩ | d1 <;> dsimp only
        · exact ⟨.error e, rfl⟩
        · obtain ⟨d0, hd0, hgas⟩ := Resume.run_ok_gasMeasure hrun
          have hle : d0.gasMeasure ≤ frame.inner.gas := Frame.enter_done_gasLe he hd0
          have hlt : d1.gasMeasure < fuel := by omega
          exact ih _ hlt hv
      · have hgas : child.dyna.gasMeasure = frame.inner.gas := Frame.enter_run_gasMeasure he
        have hcv : child.sta.benvStat.rules.Valid := by
          rw [Frame.enter_run_rules he, hrules]; exact hv
        have hchildlt : child.dyna.gasMeasure < fuel := by omega
        obtain ⟨raw', hraw'⟩ := ih child hchildlt hcv
        rw [hraw']
        dsimp only
        rcases hrun : rsm.run (frame.settle raw') with ⟨e⟩ | d1 <;> dsimp only
        · exact ⟨.error e, rfl⟩
        · obtain ⟨d0, hd0, hgas2⟩ := Resume.run_ok_gasMeasure hrun
          have hsettled := execFueled_settledGasLe fuel child hraw' hcv
          rw [hgas] at hsettled
          have hle : d0.gasMeasure ≤ frame.inner.gas := Frame.settle_gasLe hsettled hd0
          have hlt : d1.gasMeasure < fuel := by omega
          exact ih _ hlt hv

theorem execFueled_ne_exhausted (evm : Evm) (fuel : Nat)
    (h : evm.dyna.gasMeasure < fuel) (hv : evm.sta.benvStat.rules.Valid) :
    execFueled evm fuel ≠ Fueled.exhausted := by
  obtain ⟨raw, hraw⟩ := execFueled_run_isSome fuel evm h hv
  intro hcon
  rw [hcon] at hraw
  simp only [Fueled.exhausted_run] at hraw
  nomatch hraw

/-- The form the total `exec` consumes. The additive constant is **1**: seeding
the driver with `gasMeasure + 1` is always enough, so the total wrapper can
discharge the `Option` with this witness. -/
theorem execFueled_succ_ne_exhausted (evm : Evm)
    (hv : evm.sta.benvStat.rules.Valid) :
    execFueled evm (evm.dyna.gasMeasure + 1) ≠ Fueled.exhausted :=
  execFueled_ne_exhausted evm (evm.dyna.gasMeasure + 1) (Nat.lt_succ_self _) hv

/-! ## The total interpreter

Everything below is fuel-free. `execFueled` survives as the structurally
recursive definition downstream proofs reason over, but no consumer has to
thread a fuel parameter or handle an exhaustion outcome any more. -/

/-- The fuel budget seeded from a frame's gas measure. The additive constant is
the one `execFueled_succ_ne_exhausted` proves sufficient: **1**. Under
`rules.stateGas = none` the measure is `gasLeft`, so the seed is the seed it
always was; under `some _` it also counts the spill a refund can hand back. -/
def sufficientFuel (gas : Nat) : Nat := gas + 1

theorem execFueled_run_sufficientFuel_isSome (evm : Evm)
    (hv : evm.sta.benvStat.rules.Valid) :
    ((execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run).isSome := by
  obtain ⟨raw, hraw⟩ :=
    execFueled_run_isSome (sufficientFuel evm.dyna.gasMeasure) evm
      (Nat.lt_succ_self _) hv
  rw [hraw]
  rfl

/-- **The total interpreter.** Fuel is an implementation detail: the driver is
seeded from the frame's own gas measure, and the seeded budget is enough for
any rule set the semantics can use.

The exhaustion branch is not discharged at the definition site any more, and
that is the one thing the Amsterdam metering shape changes about `exec`. The
sufficiency proof now rests on `rules.Valid` -- Amsterdam reprices the numbers
it leans on, so they are no longer literals a `decide` can settle -- and a
`def` cannot demand a hypothesis without moving its signature, which fixed
decision 7 forbids. So the branch becomes a *typed internal invariant error*,
the pattern this executable already uses for the unreachable, and
`exec_of_valid` below is the proof that under a usable rule set it is never
taken. Every named fork carries the witness, so no entry point can reach it. -/
def exec (evm : Evm) : Except (EvmError × Devm) Devm :=
  match (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | some r => r
  | none => .error ⟨.internal (.invariant .none), evm.dyna⟩

/-- **Bridge equation.** Under a usable rule set the driver at the seeded budget
returns exactly the total result, so no downstream proof has to reason about
the invariant branch. -/
theorem execFueled_run_sufficientFuel (evm : Evm)
    (hv : evm.sta.benvStat.rules.Valid) :
    (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run = some (exec evm) := by
  obtain ⟨raw, hraw⟩ :=
    execFueled_run_isSome (sufficientFuel evm.dyna.gasMeasure) evm
      (Nat.lt_succ_self _) hv
  rw [hraw]
  unfold exec
  rw [hraw]

/-- The invariant branch is unreachable under a usable rule set: `exec` is the
driver's own answer, not a fallback. -/
theorem exec_of_valid (evm : Evm) (hv : evm.sta.benvStat.rules.Valid) :
    ∃ raw, (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run = some raw
      ∧ exec evm = raw :=
  ⟨exec evm, execFueled_run_sufficientFuel evm hv, rfl⟩

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
theorem execFueled_run_of_lt {evm : Evm} {fuel : Nat} (h : evm.dyna.gasMeasure < fuel)
    (hv : evm.sta.benvStat.rules.Valid) :
    (execFueled evm fuel).run = some (exec evm) :=
  execFueled_run_mono _ evm h (execFueled_run_sufficientFuel evm hv)

/-- Reading a fueled result off as the total one: the shape a proof stated over
`execFueled` uses to transfer to `exec`. -/
theorem exec_eq_of_run {evm : Evm} {fuel : Nat} {raw : Execution}
    (hlt : evm.dyna.gasMeasure < fuel) (hv : evm.sta.benvStat.rules.Valid)
    (h : (execFueled evm fuel).run = some raw) :
    exec evm = raw := by
  rw [execFueled_run_of_lt hlt hv] at h
  exact Option.some.inj h

/-! ## The total frame wrappers

These are the public entry points. They lost their `fuel` parameter and their
`Fueled` result type together: a frame is entered, the driver runs to a
definite result, and the frame settles it. -/

def runFrame (frame : Frame) : Except (EvmError × State × AdrSet × Tra) Devm :=
  match frame.enter with
  | .done r => r
  | .run evm => frame.settle (exec evm)

def executeCode (msg : Msg) : Except (EvmError × State × AdrSet × Tra) Devm :=
  match executeCode.enter msg with
  | .inl evm => executeCode.handleError (exec evm)
  | .inr raw => executeCode.handleError raw

def processMessage (msg : Msg) : Except (EvmError × State × AdrSet × Tra) Devm :=
  runFrame (Frame.ofCall msg)

def processCreateMessage (msg : Msg) :
    Except (EvmError × State × AdrSet × Tra) Devm :=
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
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    Option (Option SettledHalt × List B256 × Bytes × Nat) :=
  match r with
  | .ok devm => some ⟨devm.error, devm.stack, devm.output, devm.gasMeasure⟩
  | .error _ => none

-- Arithmetic loop: the state that exhausted `execFueled` at fuel 20 now runs to a
-- definite out-of-gas result, because the seeded budget is provably sufficient.
private def totalGuardArithmeticLoop : Bool :=
  let msg := totalGuardMsg [0x5B, 0x60, 0x00, 0x56] 1000 8
  match exec (initEvm msg), processMessage msg with
  | .error ⟨err, _⟩, .ok devm =>
    err == .halt (.outOfGas .none) &&
      devm.error == some (.halt (.outOfGas .none)) &&
      devm.gasMeasure == 0
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
    devm.error == none && devm.stack.head? == some 0 && devm.gasMeasure == 1062
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
  | .ok viaPrecomp, .ok viaCode => viaPrecomp.gasMeasure == 7000 && viaCode.gasMeasure == 10000
  | _, _ => false

#guard totalGuardPrecompileDispatch

-- Depth zero prevents spawning: the same parent that gets failure word 1 at
-- depth 8 gets 0 at depth 0, with the call never reaching the driver.
private def totalGuardDepthZero : Bool :=
  match processMessage {totalGuardNestedCallMsg with depth := 0} with
  | .ok devm => devm.stack.head? == some 0 && devm.gasMeasure == 97379
  | .error _ => false

#guard totalGuardDepthZero

-- A PUSH with zero gas halts through the frozen OutOfGasError channel.
private def totalGuardOog : Bool :=
  let msg := totalGuardMsg [0x60, 0x01, 0x00] 0 8
  match exec (initEvm msg) with
  | .error ⟨err, _⟩ => err == .halt (.outOfGas .none)
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
    devm.error == some .revert &&
      devm.output.length == 32 &&
      devm.output.getLast? == some 0x2A &&
      devm.gasMeasure == 982
  | .error _ => false

#guard totalGuardRevert

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 3, first slice: the fuel-free wrappers inherit canonicality
-- from `execFueled_run_canonical` through the seeded-budget bridge.

/-- Inversion for the `Option.toExcept` lifts that thread the transaction
chain: a successful lift pins the option. -/
theorem Option.toExcept_eq_ok {ξ : Type u} {υ : Type v} {x : ξ} {o : Option υ}
    {v : υ} (h : Option.toExcept x o = .ok v) : o = some v := by
  cases o with
  | none => nomatch h
  | some w => cases h; rfl

/-- **The total interpreter preserves canonicality** on both channels.

Canonicality needs no validity premise, and that is the point of making the
exhaustion branch a typed internal error rather than a proof obligation: the
error channel of `exec` carries the frame's own `Devm`, which is canonical by
hypothesis, so the branch is canonical for free. Every downstream canonicality
statement therefore keeps the signature it had. -/
theorem exec_canonical {evm : Evm} (h : evm.Canonical) :
    Execution.Canonical (exec evm) := by
  unfold exec
  cases hr : (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | none => exact h.2
  | some raw => exact execFueled_run_canonical _ evm h hr

theorem runFrame_canonicalSettle {frame : Frame} (hf : frame.Canonical) :
    (runFrame frame).CanonicalSettle := by
  unfold runFrame
  have hent := Frame.enter_canonical hf
  rcases he : frame.enter with r | evm <;> rw [he] at hent
  · exact hent
  · exact Frame.settle_canonicalSettle hf (exec_canonical hent)

theorem executeCode_canonicalSettle {msg : Msg} (hm : msg.Canonical) :
    (executeCode msg).CanonicalSettle := by
  unfold executeCode
  have hent := executeCode.enter_canonical hm
  rcases he : executeCode.enter msg with evm | raw <;> rw [he] at hent
  · exact executeCode.handleError_canonicalSettle (exec_canonical hent)
  · exact executeCode.handleError_canonicalSettle hent

theorem processMessage_canonicalSettle {msg : Msg} (hm : msg.Canonical) :
    (processMessage msg).CanonicalSettle :=
  runFrame_canonicalSettle (Frame.canonical_ofCall hm)

theorem processCreateMessage_canonicalSettle {msg : Msg} (hm : msg.Canonical) :
    (processCreateMessage msg).CanonicalSettle :=
  runFrame_canonicalSettle (Frame.canonical_ofCreate hm)

-- The eq-conditioned forms downstream walks consume without spelling the
-- message, plus the inversion for the `bimap Prod.fst id` error-erasure the
-- transaction layer applies to both.

theorem processMessage_ok_canonical {msg : Msg} (hm : msg.Canonical) {d : Devm}
    (h : processMessage msg = .ok d) : d.Canonical := by
  have hs := processMessage_canonicalSettle hm
  rw [h] at hs
  exact hs

theorem processCreateMessage_ok_canonical {msg : Msg} (hm : msg.Canonical)
    {d : Devm} (h : processCreateMessage msg = .ok d) : d.Canonical := by
  have hs := processCreateMessage_canonicalSettle hm
  rw [h] at hs
  exact hs

theorem Except.bimap_id_eq_ok {ε : Type u0} {δ : Type u1} {ξ : Type u2}
    {f : ε → δ} {x : Except ε ξ} {v : ξ}
    (h : Except.bimap f id x = .ok v) : x = .ok v := by
  cases x with
  | error e => nomatch h
  | ok a =>
    injection h with h2
    rw [← h2]
    rfl

end Jaune

namespace Jaune.DualGasProbe

/-!
# Amsterdam dual-gas sufficiency probe

This bounded model tests whether the termination argument in
`Jaune.Sufficiency` has a replacement for its current `Devm.gasLeft` measure
under Amsterdam's two gas reservoirs.  It follows `GasMeter` at
`ethereum/execution-specs` commit
`6e4808927cb7140f05c43890b48630afcc368d91`:

* state charges draw from `state` first, then spill into `execution`;
* a state refund repays `spilled` execution gas before refilling `state`;
* a child receives the parent's whole state reservoir but only a withheld
  execution grant; and
* the parent absorbs both reservoirs and spill when the child returns.

The model retains `committedSpill` in the measure even though neither selected
instruction site commits it.  Amsterdam permits committed spill only in the
top frame; at the two sites below it is carried unchanged, while spawned child
frames start with zero.

The tested measure deliberately omits the state reservoir.  State gas cannot
fund interpreter steps until it spills into execution gas, and a reservoir
charge can later be refunded.  The outstanding spill is included so that such
a refund is measure-neutral rather than an apparent increase.
-/

structure Meter where
  execution : Nat
  state : Nat
  spilled : Nat
  committedSpill : Nat

/-- Execution gas that can still fund steps, including spill that a rollback
or state-gas refund can restore to the execution reservoir. -/
def Meter.measure (m : Meter) : Nat :=
  m.execution + m.spilled + m.committedSpill

def chargeExecution (amount : Nat) (m : Meter) : Option Meter :=
  if amount ≤ m.execution then
    some { m with execution := m.execution - amount }
  else
    none

/-- Reservoir-first state charging, including Amsterdam's spill into execution
gas when the state reservoir is insufficient. -/
def chargeState (amount : Nat) (m : Meter) : Option Meter :=
  if amount ≤ m.state then
    some { m with state := m.state - amount }
  else
    let remainder := amount - m.state
    if remainder ≤ m.execution then
      some { m with
        execution := m.execution - remainder
        state := 0
        spilled := m.spilled + remainder }
    else
      none

/-- LIFO state refund: repay spill into execution gas first, then refill the
state reservoir. -/
def refundState (amount : Nat) (m : Meter) : Meter :=
  if amount ≤ m.spilled then
    { m with
      execution := m.execution + amount
      spilled := m.spilled - amount }
  else
    { m with
      execution := m.execution + m.spilled
      state := m.state + (amount - m.spilled)
      spilled := 0 }

structure Spawn where
  parent : Meter
  child : Meter

/-- Withhold an execution grant and drain the whole state reservoir into a
fresh child, matching Amsterdam's call/create child-grant shape. -/
def spawn (grant : Nat) (m : Meter) : Option Spawn :=
  if grant ≤ m.execution then
    some {
      parent := { m with execution := m.execution - grant, state := 0 }
      child := {
        execution := grant
        state := m.state
        spilled := 0
        committedSpill := 0
      }
    }
  else
    none

/-- Return a child meter to its parent.  The actual Amsterdam implementation
also requires the child's committed spill to be zero; allowing addition here
is conservative for the arithmetic result. -/
def incorporateChild (parent child : Meter) : Meter :=
  { parent with
    execution := parent.execution + child.execution
    state := parent.state + child.state
    spilled := parent.spilled + child.spilled
    committedSpill := parent.committedSpill + child.committedSpill }

theorem chargeExecution_measure {amount : Nat} {pre post : Meter}
    (h : chargeExecution amount pre = some post) :
    post.measure + amount = pre.measure := by
  unfold chargeExecution at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp only [Meter.measure]
    omega
  · contradiction

theorem chargeState_measure {amount : Nat} {pre post : Meter}
    (h : chargeState amount pre = some post) :
    post.measure = pre.measure := by
  unfold chargeState at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    rfl
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      rw [← h]
      simp only [Meter.measure]
      omega
    · contradiction

theorem refundState_measure (amount : Nat) (m : Meter) :
    (refundState amount m).measure = m.measure := by
  unfold refundState
  split <;> simp only [Meter.measure] <;> omega

theorem spawn_measure {grant : Nat} {pre : Meter} {post : Spawn}
    (h : spawn grant pre = some post) :
    post.parent.measure + post.child.measure = pre.measure := by
  unfold spawn at h
  split at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp only [Meter.measure]
    omega
  · contradiction

theorem incorporateChild_measure (parent child : Meter) :
    (incorporateChild parent child).measure = parent.measure + child.measure := by
  simp only [incorporateChild, Meter.measure]
  omega

/-- The original single-field measure cannot be reused unchanged: refunding a
prior spill can increase `execution`, even though the spill-adjusted measure is
unchanged by `refundState_measure`. -/
theorem executionGas_alone_can_increase :
    let before : Meter := {
      execution := 3
      state := 0
      spilled := 7
      committedSpill := 0
    }
    (refundState 7 before).execution > before.execution := by
  decide

/-- Representative site 1: `Rinst.runCore_gasLt`'s `.sstore` arm in
`Jaune.Sufficiency`.  Amsterdam SSTORE charges positive execution gas, then
performs a reservoir charge or a refund.  Even allowing both state operations
in sequence, each is neutral in the adjusted measure, so the execution charge
keeps the instruction strictly decreasing. -/
theorem sstore_site_measure_decreases
    {executionCost stateCost refund : Nat}
    {pre afterExecution afterState : Meter}
    (hCost : 0 < executionCost)
    (hExecution :
      chargeExecution executionCost pre = some afterExecution)
    (hState : chargeState stateCost afterExecution = some afterState) :
    (refundState refund afterState).measure < pre.measure := by
  have he := chargeExecution_measure hExecution
  have hs := chargeState_measure hState
  have hr := refundState_measure refund afterState
  omega

/-- Representative site 2: `Xinst.step_call_gasDecreasing` and its
spawn/settle obligation.  Amsterdam may spill a new-account state charge before
calculating the child grant, drains the state reservoir into the child, and
later incorporates the child's remaining gas.  If the child does not increase
the adjusted measure, any positive total execution charge before the spawn
still makes the settled parent strictly smaller than the step's input. -/
theorem call_site_spawn_settle_measure_decreases
    {entryCost stateCost grantCost childGrant : Nat}
    {pre afterEntry afterState afterCosts : Meter}
    {fork : Spawn} {childResult : Meter}
    (hPositive : 0 < entryCost + grantCost)
    (hEntry : chargeExecution entryCost pre = some afterEntry)
    (hState : chargeState stateCost afterEntry = some afterState)
    (hGrantCost :
      chargeExecution grantCost afterState = some afterCosts)
    (hSpawn : spawn childGrant afterCosts = some fork)
    (hChild : childResult.measure ≤ fork.child.measure) :
    (incorporateChild fork.parent childResult).measure < pre.measure := by
  have he := chargeExecution_measure hEntry
  have hs := chargeState_measure hState
  have hg := chargeExecution_measure hGrantCost
  have hsp := spawn_measure hSpawn
  have hi := incorporateChild_measure fork.parent childResult
  omega

end Jaune.DualGasProbe
