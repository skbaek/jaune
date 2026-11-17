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

@[simp] theorem withStack_gasLeft (devm : Devm) (stack : List U256) :
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

@[simp] theorem setStorVal_gasLeft (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).gasLeft = devm.gasLeft := rfl

@[simp] theorem setTransVal_gasLeft (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).gasLeft = devm.gasLeft := rfl

@[simp] theorem incrNonce_gasLeft (devm : Devm) (adr : Address) :
    (devm.incrNonce adr).gasLeft = devm.gasLeft := rfl

@[simp] theorem setCode_gasLeft (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).gasLeft = devm.gasLeft := rfl

@[simp] theorem rollback_gasLeft (devm : Devm) (wor : State) (tra : TransientStorage) :
    (devm.rollback wor tra).gasLeft = devm.gasLeft := rfl

end Devm

@[simp] theorem addAccessedAddress_gasLeft (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).gasLeft = devm.gasLeft := rfl

@[simp] theorem addAccessedStorageKey_gasLeft (devm : Devm) (a : Address) (k : U256) :
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

@[simp] theorem withStack_stateGas (devm : Devm) (stack : List U256) :
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

@[simp] theorem setStorVal_stateGas (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem setTransVal_stateGas (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem incrNonce_stateGas (devm : Devm) (adr : Address) :
    (devm.incrNonce adr).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem setCode_stateGas (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem rollback_stateGas (devm : Devm) (wor : State) (tra : TransientStorage) :
    (devm.rollback wor tra).mach.stateGas = devm.mach.stateGas := rfl

end Devm

@[simp] theorem addAccessedAddress_stateGas (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).mach.stateGas = devm.mach.stateGas := rfl

@[simp] theorem addAccessedStorageKey_stateGas (devm : Devm) (a : Address)
    (k : U256) :
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

@[simp] theorem rollback_spill (devm : Devm) (wor : State) (tra : TransientStorage) :
    (devm.rollback wor tra).spill = devm.spill := rfl

@[simp] theorem setMach_gasMeasure (devm : Devm) (mach : Mach) :
    (devm.setMach mach).gasMeasure = mach.gasMeasure := rfl

@[simp] theorem setMeta_gasMeasure (devm : Devm) (view : Meta) :
    (devm.setMeta view).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setWorld_gasMeasure (devm : Devm) (world : World) :
    (devm.setWorld world).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withStorageWrites_gasMeasure (devm : Devm) (writes : KeySet) :
    (devm.withStorageWrites writes).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem clearStorageWritesIfEmpty_gasMeasure (devm : Devm) (a : Address) :
    (devm.clearStorageWritesIfEmpty a).gasMeasure = devm.gasMeasure := rfl

theorem withGasLeft_gasMeasure (devm : Devm) (n : Nat) :
    (devm.withGasLeft n).gasMeasure = n + devm.spill := by
  simp only [Devm.withGasLeft, Devm.setMach, Devm.gasMeasure, Mach.gasMeasure,
    Devm.spill]
  omega

@[simp] theorem withStack_gasMeasure (devm : Devm) (stack : List U256) :
    (devm.withStack stack).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withMemory_gasMeasure (devm : Devm) (memory : Mem) :
    (devm.withMemory memory).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withLogs_gasMeasure (devm : Devm) (logs : List Log) :
    (devm.withLogs logs).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem withRefundCounter_gasMeasure (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).gasMeasure = devm.gasMeasure := rfl

/-- The `SELFDESTRUCT` refund hook is meta-only: it preserves the gas measure. -/
@[simp] theorem creditSelfdestructRefund_gasMeasure (rules : ForkRules)
    (alreadyScheduled : Prop) [Decidable alreadyScheduled] (devm : Devm) :
    (creditSelfdestructRefund rules alreadyScheduled devm).gasMeasure =
      devm.gasMeasure := by
  unfold creditSelfdestructRefund
  split <;> simp [withRefundCounter_gasMeasure]

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

@[simp] theorem setStorVal_gasMeasure (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setStorVal adr key val).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setTransVal_gasMeasure (devm : Devm) (adr : Address) (key val : U256) :
    (devm.setTransVal adr key val).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem incrNonce_gasMeasure (devm : Devm) (adr : Address) :
    (devm.incrNonce adr).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem setCode_gasMeasure (devm : Devm) (adr : Address) (code : ByteArray) :
    (devm.setCode adr code).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem rollback_gasMeasure (devm : Devm) (wor : State) (tra : TransientStorage) :
    (devm.rollback wor tra).gasMeasure = devm.gasMeasure := rfl

end Devm

@[simp] theorem addAccessedAddress_gasMeasure (devm : Devm) (a : Address) :
    (addAccessedAddress devm a).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem addAccessedStorageKey_gasMeasure (devm : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey devm a k).gasMeasure = devm.gasMeasure := rfl

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
  · simp only [safeSub, ite_eq_left hle, Except.ok.injEq] at h
    subst h
    simp only [Devm.setMach, Mach.gasMeasure, Devm.gasMeasure, Devm.gasLeft] at hle ⊢
    omega
  · exact absurd h (by simp [safeSub, ite_eq_right hle])

/-! ## Stack primitives

Pushing and popping never touch `gasLeft` or the meter. These are the inversion
forms the instruction walks need: the hypothesis is the `.ok` equation that
survives a `split`, and the conclusion feeds `omega`. -/

theorem Devm.push_gasMeasure {x : U256} {devm devm' : Devm}
    (h : Devm.push x devm = .ok devm') : devm'.gasMeasure = devm.gasMeasure := by
  rw [Devm.push_def] at h
  unfold Except.assert at h
  split at h
  · simp only [bind, Except.bind, Except.ok.injEq] at h
    subst h; rfl
  · exact absurd h (by simp [bind, Except.bind])

theorem Devm.pop_gasMeasure {devm : Devm} {x : U256} {devm' : Devm}
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

theorem Devm.popToAdr_gasMeasure {devm : Devm} {a : Address} {devm' : Devm}
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

theorem Devm.popN_gasMeasure {devm : Devm} {n : Nat} {xs : List U256} {devm' : Devm}
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

theorem pop_gasMeasure {mach mach' : Mach} {x : U256}
    (h : mach.pop = .ok (x, mach')) : mach'.gasMeasure = mach.gasMeasure := by
  unfold Mach.pop at h
  split at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl

theorem push_gasMeasure {x : U256} {mach mach' : Mach} {u : Unit}
    (h : Mach.push x mach = .ok (u, mach')) : mach'.gasMeasure = mach.gasMeasure := by
  unfold Mach.push at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl
  · exact absurd h (by simp)

theorem pushItem_gasMeasure {x : U256} {c : Nat} {mach mach' : Mach} {u : Unit}
    (h : Mach.pushItem x c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.pushItem at h
  rcases hc : Mach.chargeGas c mach with ⟨err, m⟩ | ⟨uc, m1⟩ <;> simp only [hc] at h
  · exact absurd h (by simp)
  · rw [push_gasMeasure h, ← Mach.chargeGas_gasMeasure hc]

theorem applyUnary_gasMeasure {f : U256 → U256} {c : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.applyUnary f c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.applyUnary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rw [pushItem_gasMeasure h, pop_gasMeasure hp]

theorem applyBinary_gasMeasure {f : U256 → U256 → U256} {c : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.applyBinary f c mach = .ok (u, mach')) :
    mach'.gasMeasure + c = mach.gasMeasure := by
  unfold Mach.applyBinary at h
  rcases hp : mach.pop with ⟨err, m⟩ | ⟨x, m1⟩ <;> simp only [hp] at h
  · exact absurd h (by simp)
  · rcases hq : m1.pop with ⟨err, m⟩ | ⟨y, m2⟩ <;> simp only [hq] at h
    · exact absurd h (by simp)
    · rw [pushItem_gasMeasure h, pop_gasMeasure hq, pop_gasMeasure hp]

theorem applyTernary_gasMeasure {f : U256 → U256 → U256 → U256} {c : Nat}
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

theorem pushItem_gasMeasure {x : U256} {c : Nat} {devm devm' : Devm}
    (h : pushItem x c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.pushItem_gasMeasure hcore]

theorem applyUnary_gasMeasure {f : U256 → U256} {c : Nat} {devm devm' : Devm}
    (h : applyUnary f c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.applyUnary_gasMeasure hcore]

theorem applyBinary_gasMeasure {f : U256 → U256 → U256} {c : Nat} {devm devm' : Devm}
    (h : applyBinary f c devm = .ok devm') : devm'.gasMeasure + c = devm.gasMeasure := by
  obtain ⟨_, mach', hcore, hmach⟩ := liftMachExecution_ok h
  show devm'.mach.gasMeasure + c = devm.mach.gasMeasure
  rw [hmach, Mach.applyBinary_gasMeasure hcore]

theorem applyTernary_gasMeasure {f : U256 → U256 → U256 → U256} {c : Nat}
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
    (devm : Devm) (a : Address) (k : U256) :
    (if c then addAccessedStorageKey devm a k else devm).gasMeasure
      = devm.gasMeasure := by
  split <;> simp

@[simp] theorem Devm.ite_addAccessedStorageKey_gasMeasure' {c : Prop} [Decidable c]
    (devm : Devm) (a : Address) (k : U256) :
    (if c then devm else addAccessedStorageKey devm a k).gasMeasure
      = devm.gasMeasure := by
  split <;> simp

/-- Amsterdam's `SSTORE` execution charge is at least the warm access, so the
arm still decreases the measure whatever the slot's history. -/
theorem sstoreAmsterdamGasCost_pos (state : StateGasRules)
    (new_value original_value current_value : U256) (cold : Bool) :
    0 < sstoreAmsterdamGasCost state new_value original_value current_value cold := by
  unfold sstoreAmsterdamGasCost Gas.coldSloadCost Gas.warmStorageReadCost
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

theorem access_cost_pos (x : Address) (a : AdrSet) : 0 < accessCost x a := by
  unfold accessCost Gas.warmStorageReadCost Gas.coldAccountAccessCost
  split <;> omega

theorem Gas.warmStorageReadCost_le_access_cost (x : Address) (a : AdrSet) :
    Gas.warmStorageReadCost ≤ accessCost x a := by
  unfold accessCost Gas.warmStorageReadCost Gas.coldAccountAccessCost
  split <;> omega

/-! ### The same two facts, of the schedule the interpreter reads

The two lemmas above are about `accessCost`, which is Prague's function and
stays exactly that -- Blanc names it 121 times. The interpreter now reads
`rules.gas.accessCost`, whose cold half is whatever the fork's schedule says,
so the same two facts have to be available of an arbitrary schedule. That is
what `GasSchedule.Valid` buys, and it is the only thing the family asks of a
schedule it did not choose. -/

theorem GasSchedule.access_cost_pos {gas : GasSchedule} (hv : gas.Valid)
    (x : Address) (a : AdrSet) : 0 < gas.accessCost x a :=
  hv.accessCost_pos x a

theorem GasSchedule.warmStorageReadCost_le_access_cost {gas : GasSchedule}
    (hv : gas.Valid) (x : Address) (a : AdrSet) :
    Gas.warmStorageReadCost ≤ gas.accessCost x a :=
  hv.warmAccess_le_accessCost x a

/-- Under the flat (pre-EIP-2929) schedule every family's price is positive:
the termination argument's one need of that shape, from `ForkRules.Valid`. -/
theorem ForkRules.Valid.flatAccess {r : ForkRules} (hv : r.Valid)
    {g : FlatAccessGas} (h : r.access = .flat g) : g.Valid := by
  have ha := hv.access
  rw [h] at ha
  exact ha

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
  split <;> split <;> simp_all

/-! ## Pilot

Step 1 discharges a representative slice of the corpus rather than all of it:
one instruction from each shape Step 2 will meet, so that the cost of the grind
can be estimated honestly and the combinator layer is known to be the right one.

The slice is `.add` (the `apply*` family, 25 constructors), `.mstore` (a
memory-extending body, 7 constructors), `.extcodesize` (a warm/cold access body
with the charge inside an `if`, 4 constructors), `Jinst.jumpdest` (the smallest
charge in the machine, `gJumpdest = 1`), and `Xinst.step .call` — the hard case,
covering a spawn and both of its refund branches. -/

@[simp] theorem accessDelegation_gasMeasure (devm : Devm) (adr : Address) :
    (accessDelegation devm adr).2.2.2.2.gasMeasure = devm.gasMeasure := by
  unfold accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_gasMeasure]

@[simp] theorem accessDelegation_stateGas (devm : Devm) (adr : Address) :
    (accessDelegation devm adr).2.2.2.2.mach.stateGas = devm.mach.stateGas := by
  unfold accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_stateGas]

@[simp] theorem GasSchedule.accessDelegation_gasMeasure
    (gas : GasSchedule) (devm : Devm) (adr : Address) :
    (gas.accessDelegation devm adr).2.2.2.2.gasMeasure = devm.gasMeasure := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_gasMeasure]

@[simp] theorem GasSchedule.accessDelegation_stateGas
    (gas : GasSchedule) (devm : Devm) (adr : Address) :
    (gas.accessDelegation devm adr).2.2.2.2.mach.stateGas = devm.mach.stateGas := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> simp only [addAccessedAddress_stateGas]

@[simp] theorem ForkRules.accessDelegation_gasMeasure
    (rules : ForkRules) (devm : Devm) (adr : Address) :
    (rules.accessDelegation devm adr).2.2.2.2.gasMeasure = devm.gasMeasure := by
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_gasMeasure rules.gas devm adr
  · rfl

@[simp] theorem ForkRules.accessDelegation_stateGas
    (rules : ForkRules) (devm : Devm) (adr : Address) :
    (rules.accessDelegation devm adr).2.2.2.2.mach.stateGas = devm.mach.stateGas := by
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_stateGas rules.gas devm adr
  · rfl

@[simp] theorem completeDelegationAccess_gasMeasure
    (devm : Devm) (delegated : Bool) (adr : Address) :
    (completeDelegationAccess devm delegated adr).2.gasMeasure =
      devm.gasMeasure := by
  unfold completeDelegationAccess
  dsimp only
  split <;> simp only [addAccessedAddress_gasMeasure]

@[simp] theorem completeDelegationAccess_stateGas
    (devm : Devm) (delegated : Bool) (adr : Address) :
    (completeDelegationAccess devm delegated adr).2.mach.stateGas =
      devm.mach.stateGas := by
  unfold completeDelegationAccess
  dsimp only
  split <;> simp only [addAccessedAddress_stateGas]

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

theorem PlainOp.runCore_mstore_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm} (h : PlainOp.runCore pc devm sevm .mstore = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  simp only [PlainOp.runCore] at h
  obtain ⟨⟨start_index, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨value, d2⟩, h2, h⟩ := Except.bind_eq_ok h
  obtain ⟨d3, h3, h⟩ := Except.bind_eq_ok h
  dsimp only at h h1 h2 h3
  simp only [Except.ok.injEq] at h
  have e1 := Devm.popToNat_gasMeasure h1
  have e2 := Devm.pop_gasMeasure h2
  have e3 := chargeGas_gasMeasure h3
  rw [← h, Devm.memWrite_gasMeasure]
  unfold Gas.veryLow at e3
  omega

theorem PlainOp.runCore_extcodesize_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {devm' : Devm}
    (h : PlainOp.runCore pc devm sevm .extcodesize = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  simp only [PlainOp.runCore] at h
  obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
  dsimp only at h h1
  have e1 := Devm.popToAdr_gasMeasure h1
  -- The charge sits inside the warm/cold `if`, and the elaborator pushed the
  -- continuation into both arms; both charge a positive constant, and the cold
  -- arm's `addAccessedAddress` preserves gas.
  split at h
  · split at h
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasMeasure h2
      have e3 := Devm.push_gasMeasure h3
      simp only [Devm.balReadAccount_gasMeasure] at e3
      unfold Gas.warmStorageReadCost at e2
      omega
    · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasMeasure h2
      rw [addAccessedAddress_gasMeasure] at e2
      have e3 := Devm.push_gasMeasure h3
      simp only [Devm.balReadAccount_gasMeasure] at e3
      -- The cold half is now whatever the fork's schedule says, so positivity
      -- comes from `Valid` rather than from a literal.
      have hc := hv.gas.warmAccess_le
      unfold Gas.warmStorageReadCost at hc
      omega
  · -- Flat: one fixed positive price, the accessed set untouched.
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasMeasure h2
    have e3 := Devm.push_gasMeasure h3
    simp only [Devm.balReadAccount_gasMeasure] at e3
    obtain ⟨_, _, _, _, _⟩ := hv.flatAccess (by assumption)
    omega

theorem JumpOp.runCore_jumpdest_gasLt {pc : Nat} {devm : Devm} {sevm : Sevm}
    {pc' : Nat} {devm' : Devm}
    (h : JumpOp.runCore pc devm sevm .jumpdest = .ok (pc', devm')) :
    devm'.gasMeasure < devm.gasMeasure := by
  simp only [JumpOp.runCore] at h
  obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  have e1 := chargeGas_gasMeasure h1
  unfold Gas.jumpdest at e1
  rw [← h.2]
  omega

/-! ## Strict-decrease corpus: reusable short walks -/

theorem pushItem_gasLt {x : U256} {c : Nat} {devm devm' : Devm}
    (hc : 0 < c) (h : pushItem x c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := pushItem_gasMeasure h
  omega

theorem applyUnary_gasLt {f : U256 → U256} {c : Nat} {devm devm' : Devm}
    (hc : 0 < c) (h : applyUnary f c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := applyUnary_gasMeasure h
  omega

theorem applyBinary_gasLt {f : U256 → U256 → U256} {c : Nat}
    {devm devm' : Devm} (hc : 0 < c)
    (h : applyBinary f c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := applyBinary_gasMeasure h
  omega

theorem applyTernary_gasLt {f : U256 → U256 → U256 → U256} {c : Nat}
    {devm devm' : Devm} (hc : 0 < c)
    (h : applyTernary f c devm = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have e := applyTernary_gasMeasure h
  omega

theorem popChargePush_gasLt (pre : Devm)
    (cost : U256 → Devm → Nat) (value : U256 → Devm → U256)
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
    (cost : U256 → U256 → Devm → Nat)
    (value : U256 → U256 → Devm → U256)
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
    (cost : Nat → U256 → Devm → Nat)
    (next : Nat → U256 → Devm → Devm)
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

theorem PlainOp.balance_runCore_gasLt {pc : Nat} {devm devm' : Devm}
    {sevm : Sevm}
    (h : PlainOp.runCore pc devm sevm .balance = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have hvalid := Sevm.rules_valid sevm
  simp only [PlainOp.runCore] at h
  obtain ⟨u, view', hcore, hout⟩ := liftMachMetaWorldExecution_ok h
  unfold PlainOp.balanceCore at hcore
  cases hp : devm.mach.pop with
  | error e => simp [hp] at hcore
  | ok p =>
    rcases p with ⟨x, mach1⟩
    simp only [hp] at hcore
    rcases hA : sevm.benvStat.rules.access with g | _
    · -- Flat: one fixed positive price, the accessed set untouched.
      obtain ⟨hb, -, -, -, -⟩ := hvalid.flatAccess hA
      simp only [hA] at hcore
      cases hc : Mach.chargeGas g.balance mach1 with
      | error e => simp [hc] at hcore
      | ok p =>
        rcases p with ⟨u2, mach2⟩
        simp only [hc] at hcore
        cases hpush : Mach.push (devm.world.state.get x.toAddress).balance mach2 with
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
          omega
    simp only [hA] at hcore
    by_cases hw : x.toAddress ∈ devm.meta.accessedAddresses
    · simp only [hw, ite_eq_left] at hcore
      cases hc : Mach.chargeGas Gas.warmStorageReadCost mach1 with
      | error e => simp [hc] at hcore
      | ok p =>
        rcases p with ⟨u2, mach2⟩
        simp only [hc] at hcore
        cases hpush : Mach.push (devm.world.state.get x.toAddress).balance mach2 with
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
          unfold Gas.warmStorageReadCost at ec
          omega
    · simp only [hw, ite_false] at hcore
      cases hc : Mach.chargeGas sevm.benvStat.rules.gas.coldAccountAccess
          mach1 with
      | error e => simp [hc] at hcore
      | ok p =>
        rcases p with ⟨u2, mach2⟩
        simp only [hc] at hcore
        cases hpush : Mach.push (devm.world.state.get x.toAddress).balance mach2 with
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
          unfold Gas.warmStorageReadCost at hcold
          omega

theorem popAddressAccessChargePush_gasLt (pre : Devm) {gas : GasSchedule}
    (hv : gas.Valid)
    (value : Address → Devm → U256) {post : Devm}
    (h : (do
      let ⟨adr, d⟩ ← pre.popToAdr
      let d' ←
        if adr ∈ d.accessedAddresses then chargeGas Gas.warmStorageReadCost d
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
    unfold Gas.warmStorageReadCost at e2
    omega
  · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e2 := chargeGas_gasMeasure h2
    rw [addAccessedAddress_gasMeasure] at e2
    have e3 := Devm.push_gasMeasure h3
    have hc := hv.warmAccess_le
    unfold Gas.warmStorageReadCost at hc
    omega

theorem PlainOp.runCore_gasLt (pc : Nat) (devm : Devm) (sevm : Sevm)
    (r : PlainOp) {devm' : Devm}
    (h : PlainOp.runCore pc devm sevm r = .ok devm') :
    devm'.gasMeasure < devm.gasMeasure := by
  have hv := Sevm.rules_valid sevm
  cases r <;> simp only [PlainOp.runCore] at h
  all_goals first
    | exact applyBinary_gasLt (by decide) h
    | exact applyUnary_gasLt (by decide) h
    | exact applyTernary_gasLt (by decide) h
    | exact pushItem_gasLt (by decide) h
    | skip
  case exp =>
    exact pop2ChargePush_gasLt devm
      (fun _ exponent _ => Gas.exp + Gas.expByte * exponent.bytecount)
      (fun base exponent _ => U256.exp base exponent)
      (by intros; unfold Gas.exp; omega) h
  case clz =>
    split at h
    · exact applyUnary_gasLt (by decide) h
    · simp at h
  case slotnum =>
    split at h
    · exact pushItem_gasLt (by decide) h
    · simp at h
  case shl | shr | sar =>
    split at h
    · exact applyBinary_gasLt (by decide) h
    · simp at h
  case chainid | basefee | blobbasefee =>
    split at h
    · exact pushItem_gasLt (by decide) h
    · simp at h
  case keccak256 =>
    change PlainOp.runCore pc devm sevm .keccak256 = .ok devm' at h
    rw [PlainOp.runCore_keccak256_eq_reference] at h
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨size, d2⟩, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasMeasure h1
    have e2 := Devm.popToNat_gasMeasure h2
    have e3 := chargeGas_gasMeasure h3
    have e4 := Devm.push_gasMeasure h4
    rw [Devm.withMemory_gasMeasure] at e4
    unfold Gas.keccak256 at e3
    omega
  case balance =>
    apply PlainOp.balance_runCore_gasLt (pc := pc) (sevm := sevm)
    simpa only [PlainOp.runCore] using h
  case calldataload =>
    exact popChargePush_gasLt devm
      (fun _ _ => Gas.veryLow)
      (fun start _ => Bytes.toU256 <| sevm.data.sliceD start.toNat 32 0)
      (by intros; decide) h
  case calldatacopy =>
    exact popNat3ChargePure_gasLt devm
      (fun memoryStart _ size d =>
        Gas.veryLow + Gas.copy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart dataStart size d =>
        d.memWrite memoryStart (sevm.data.sliceD dataStart size 0))
      (by intros; unfold Gas.veryLow; omega)
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
      unfold Gas.veryLow at e4
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
    · split at h
      · obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
        simp only [Except.ok.injEq] at h6
        have e5 := chargeGas_gasMeasure h5
        rw [← h6, Devm.memWrite_gasMeasure, Devm.balReadAccount_gasMeasure]
        unfold Gas.warmStorageReadCost at e5
        omega
      · obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
        simp only [Except.ok.injEq] at h6
        have e5 := chargeGas_gasMeasure h5
        rw [addAccessedAddress_gasMeasure] at e5
        rw [← h6, Devm.memWrite_gasMeasure, Devm.balReadAccount_gasMeasure]
        have hc := hv.gas.warmAccess_le
        unfold Gas.warmStorageReadCost at hc
        omega
    · -- Flat: one fixed positive price, the accessed set untouched.
      obtain ⟨d5, h5, h6⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq] at h6
      have e5 := chargeGas_gasMeasure h5
      rw [← h6, Devm.memWrite_gasMeasure, Devm.balReadAccount_gasMeasure]
      obtain ⟨_, _, _, _, _⟩ := hv.flatAccess (by assumption)
      omega
  case extcodesize =>
    apply PlainOp.runCore_extcodesize_gasLt (pc := pc) (sevm := sevm)
    simpa only [PlainOp.runCore] using h
  case extcodehash =>
    -- As `extcodesize`: the EIP-7928 read recorder sits between the charge
    -- and the push and is measure-neutral.
    split at h
    · obtain ⟨⟨adr, d1⟩, h1, h⟩ := Except.bind_eq_ok h
      dsimp only at h h1
      have e1 := Devm.popToAdr_gasMeasure h1
      split at h
      · split at h
        · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
          have e2 := chargeGas_gasMeasure h2
          have e3 := Devm.push_gasMeasure h3
          simp only [Devm.balReadAccount_gasMeasure] at e3
          unfold Gas.warmStorageReadCost at e2
          omega
        · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
          have e2 := chargeGas_gasMeasure h2
          rw [addAccessedAddress_gasMeasure] at e2
          have e3 := Devm.push_gasMeasure h3
          simp only [Devm.balReadAccount_gasMeasure] at e3
          have hc := hv.gas.warmAccess_le
          unfold Gas.warmStorageReadCost at hc
          omega
      · -- Flat: one fixed positive price, the accessed set untouched.
        obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
        have e2 := chargeGas_gasMeasure h2
        have e3 := Devm.push_gasMeasure h3
        simp only [Devm.balReadAccount_gasMeasure] at e3
        obtain ⟨_, _, _, _, _⟩ := hv.flatAccess (by assumption)
        omega
    · simp at h
  case selfbalance =>
    split at h
    · obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
      have e1 := chargeGas_gasMeasure h1
      have e2 := Devm.push_gasMeasure h
      simp only [Devm.balReadAccount_gasMeasure] at e2
      unfold Gas.low at e1
      omega
    · simp at h
  case blockhash =>
    exact popChargePush_gasLt devm
      (fun _ _ => Gas.blockhash)
      (fun blockNumberWord _ =>
        if sevm.benvStat.number ≤ blockNumberWord.toNat ∨
            blockNumberWord.toNat + 256 < sevm.benvStat.number then 0
        else sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length -
            (sevm.benvStat.number - blockNumberWord.toNat)) 0)
      (by intros; unfold Gas.blockhash; omega) h
  case blobhash =>
    split at h
    · exact popChargePush_gasLt devm
        (fun _ _ => Gas.hashOpcodeGas)
        (fun index _ => sevm.tenvStat.blobVersionedHashes.getD index.toNat 0)
        (by intros; unfold Gas.hashOpcodeGas; omega) h
    · simp at h
  case pop =>
    cases hp : devm.pop with
    | error e =>
      change Except.bind (Except.map Prod.snd devm.pop) (chargeGas Gas.base) =
        .ok devm' at h
      simp only [hp, Except.map, Except.bind] at h
      nomatch h
    | ok p =>
      have e1 := Devm.pop_gasMeasure hp
      change Except.bind (Except.map Prod.snd devm.pop) (chargeGas Gas.base) =
        .ok devm' at h
      simp only [hp, Except.map, Except.bind] at h
      have e2 := chargeGas_gasMeasure h
      unfold Gas.base at e2
      omega
  case mload =>
    obtain ⟨⟨start, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
    have e1 := Devm.popToNat_gasMeasure h1
    have e2 := chargeGas_gasMeasure h2
    have e3 := Devm.push_gasMeasure h3
    dsimp only at e1 e2 e3
    rw [Devm.memRead_gasMeasure] at e3
    unfold Gas.veryLow at e2
    omega
  case mstore =>
    apply PlainOp.runCore_mstore_gasLt (pc := pc) (sevm := sevm)
    simpa only [PlainOp.runCore] using h
  case mstore8 =>
    exact popNatPopChargePure_gasLt devm
      (fun start _ d => Gas.veryLow + d.extCost [(start, 1)])
      (fun start value d => d.memWrite start [value.2.2.toUInt8])
      (by intros; unfold Gas.veryLow; omega)
      (by intros; simp only [Devm.memWrite_gasMeasure]) h
  case mcopy =>
    split at h
    · exact popNat3ChargePure_gasLt devm
        (fun destinationStart sourceStart size d =>
          Gas.veryLow + Gas.copy * ceilDiv size 32 +
            d.extCost [(sourceStart, size), (destinationStart, size)])
        (fun destinationStart sourceStart size d =>
          (d.memRead sourceStart size).2.memWrite destinationStart
            (d.memRead sourceStart size).1)
        (by intros; unfold Gas.veryLow; omega)
        (by intros; simp only [Devm.memWrite_gasMeasure, Devm.memRead_gasMeasure]) h
    · simp at h
  case sstore =>
    split at h
    · split at h
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
          split <;> simp only [addAccessedStorageKey_gasMeasure, Devm.balReadStorage_gasMeasure]
        have hRefundGas : d3.gasMeasure = d2.gasMeasure := by
          rw [← hRefund, Devm.withRefundCounter_gasMeasure, hPairGas]
        have hCostPos : 0 < cost := by
          rw [← hCost]
          split
          · split
            · unfold Gas.sstoreSetGas
              omega
            · unfold Gas.sstoreResetGas Gas.coldSloadCost
              omega
          · unfold Gas.warmStorageReadCost
            omega
        dsimp only at e1 e2 hFinal
        rw [← hFinal, Devm.setStorVal_gasMeasure, Devm.balReadAccount_gasMeasure]
        omega
      · -- The pre-Berlin regimes: the same binds; the cold pair cases on
        -- access and the execution cost is the regime schedule.
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
          split
          · simp only [Devm.balReadStorage_gasMeasure]
          · split <;> simp only [addAccessedStorageKey_gasMeasure, Devm.balReadStorage_gasMeasure]
        have hRefundGas : d3.gasMeasure = d2.gasMeasure := by
          rw [← hRefund, Devm.withRefundCounter_gasMeasure, hPairGas]
        have hCostPos : 0 < cost := by
          rw [← hCost]
          exact sstoreRegimeGasCost_pos _ (ForkRules.Valid.access hv) _ _ _ _
        dsimp only at e1 e2 hFinal
        rw [← hFinal, Devm.setStorVal_gasMeasure, Devm.balReadAccount_gasMeasure]
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
        Devm.balReadStorage_gasMeasure, Devm.ite_addAccessedStorageKey_gasMeasure] at e3
      dsimp only at e1 e2 hFinal
      rw [← hFinal, Devm.setStorVal_gasMeasure, Devm.balReadAccount_gasMeasure]
      omega
  case sload =>
    obtain ⟨⟨key, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    have e1 := Devm.pop_gasMeasure h1
    dsimp only at h e1
    split at h
    · split at h
      · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
        have e2 := chargeGas_gasMeasure h2
        have e3 := Devm.push_gasMeasure h3
        simp only [Devm.balReadStorage_gasMeasure] at e3
        unfold Gas.warmStorageReadCost at e2
        omega
      · obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
        have e2 := chargeGas_gasMeasure h2
        rw [addAccessedStorageKey_gasMeasure] at e2
        have e3 := Devm.push_gasMeasure h3
        simp only [Devm.balReadStorage_gasMeasure] at e3
        unfold Gas.coldSloadCost at e2
        omega
    · -- Flat: one fixed positive price, the accessed set untouched.
      obtain ⟨d2, h2, h3⟩ := Except.bind_eq_ok h
      have e2 := chargeGas_gasMeasure h2
      have e3 := Devm.push_gasMeasure h3
      simp only [Devm.balReadStorage_gasMeasure] at e3
      obtain ⟨_, _, _, _, _⟩ := hv.flatAccess (by assumption)
      omega
  case tload =>
    split at h
    · obtain ⟨⟨key, d1⟩, h1, h2⟩ := Except.bind_eq_ok h
      have e1 := Devm.pop_gasMeasure h1
      have e2 := pushItem_gasLt (by unfold Gas.warmStorageReadCost; omega) h2
      dsimp only at e1 e2
      omega
    · simp at h
  case tstore =>
    split at h
    · split at h
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
        unfold Gas.warmStorageReadCost at e3
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
        unfold Gas.warmStorageReadCost at e3
        omega
    · simp at h
  case gas =>
    obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasMeasure h1
    have e2 := Devm.push_gasMeasure h2
    unfold Gas.base at e1
    omega
  case dup i =>
    obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasMeasure h1
    split at h
    · nomatch h
    · have e2 := Devm.push_gasMeasure h
      unfold Gas.veryLow at e1
      omega
  case swap i =>
    obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    have e1 := chargeGas_gasMeasure h1
    split at h
    · nomatch h
    · simp only [Except.ok.injEq] at h
      rw [← h, Devm.withStack_gasMeasure]
      unfold Gas.veryLow at e1
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
    unfold Gas.log at e4
    omega
  case codecopy =>
    exact popNat3ChargePure_gasLt devm
      (fun memoryStart _ size d =>
        Gas.veryLow + Gas.copy * ceilDiv size 32 + d.extCost [(memoryStart, size)])
      (fun memoryStart codeStart size d =>
        d.memWrite memoryStart
          (sevm.code.sliceD codeStart size (HaltOp.toUInt8 .stop)))
      (by intros; unfold Gas.veryLow; omega)
      (by intros; simp only [Devm.memWrite_gasMeasure]) h

theorem JumpOp.runCore_gasLt (pc : Nat) (devm : Devm) (sevm : Sevm)
    (j : JumpOp) {pc' : Nat} {devm' : Devm}
    (h : JumpOp.runCore pc devm sevm j = .ok (pc', devm')) :
    devm'.gasMeasure < devm.gasMeasure := by
  cases j
  case jumpdest =>
    exact JumpOp.runCore_jumpdest_gasLt h
  case jump =>
    simp only [JumpOp.runCore] at h
    obtain ⟨⟨destination, d1⟩, h1, h⟩ := Except.bind_eq_ok h
    obtain ⟨d2, h2, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _hassert, h3⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h3
    have e1 := Devm.pop_gasMeasure h1
    have e2 := chargeGas_gasMeasure h2
    dsimp only at e1 e2
    rw [← h3.2]
    unfold Gas.mid at e2
    omega
  case jumpi =>
    simp only [JumpOp.runCore] at h
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
      unfold Gas.high at e3
      omega
    · obtain ⟨_, _hassert, h⟩ := Except.bind_eq_ok h
      obtain ⟨nextPc, _hpc, h4⟩ := Except.bind_eq_ok h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h4
      rw [← h4.2]
      unfold Gas.high at e3
      omega

theorem except64th_le (n : Nat) : except64th n ≤ n := by
  unfold except64th
  omega

theorem executePrecompile_gasLe (evm : Evm) (adr : Address) :
    (executePrecompile evm adr).gasMeasure ≤ evm.dyna.gasMeasure := by
  unfold executePrecompile applyPrecompileResult
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

@[simp] theorem chargeGas_result_gasLe (cost : Nat) (devm : Devm) :
    (chargeGas cost devm).gasMeasure ≤ devm.gasMeasure := by
  rw [chargeGas_def]
  by_cases hc : cost ≤ devm.gasLeft
  · simp only [safeSub, hc, ite_eq_left, Execution.gasMeasure_ok,
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

@[simp] theorem push_machResultGas (x : U256) (mach : Mach) :
    machResultGas (Mach.push x mach) = mach.gasMeasure := by
  unfold Mach.push
  split <;> rfl

@[simp] theorem chargeGas_machResultGas (c : Nat) (mach : Mach) :
    machResultGas (Mach.chargeGas c mach) ≤ mach.gasMeasure := by
  unfold Mach.chargeGas safeSub
  by_cases hc : c ≤ mach.gasLeft
  · simp only [ite_eq_left hc, machResultGas, Mach.gasMeasure]
    omega
  · simp only [ite_eq_right hc, machResultGas, Mach.gasMeasure]
    omega

@[simp] theorem pushItem_machResultGas (x : U256) (c : Nat) (mach : Mach) :
    machResultGas (Mach.pushItem x c mach) ≤ mach.gasMeasure := by
  unfold Mach.pushItem
  have hc := Mach.chargeGas_machResultGas c mach
  rcases hg : Mach.chargeGas c mach with ⟨err, m⟩ | ⟨u, m⟩ <;> rw [hg] at hc <;>
    simp only [machResultGas] at hc
  · exact hc
  · exact Nat.le_trans (Nat.le_of_eq (push_machResultGas x m)) hc

@[simp] theorem applyUnary_machResultGas (f : U256 → U256) (c : Nat) (mach : Mach) :
    machResultGas (Mach.applyUnary f c mach) ≤ mach.gasMeasure := by
  unfold Mach.applyUnary
  have hp := Mach.pop_machResultGas mach
  rcases hg : mach.pop with ⟨err, m⟩ | ⟨x, m⟩ <;> rw [hg] at hp <;>
    simp only [machResultGas] at hp ⊢
  · exact Nat.le_of_eq hp
  · exact Nat.le_trans (pushItem_machResultGas _ _ m) (Nat.le_of_eq hp)

@[simp] theorem applyBinary_machResultGas (f : U256 → U256 → U256) (c : Nat)
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

@[simp] theorem applyTernary_machResultGas (f : U256 → U256 → U256 → U256) (c : Nat)
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

@[simp] theorem Devm.push_gasLe (x : U256) (devm : Devm) :
    (devm.push x).gasMeasure = devm.gasMeasure := by
  rw [Devm.push, liftMachExecution_resultGas, Mach.push_machResultGas]
  rfl

@[simp] theorem pushItem_gasLe (x : U256) (c : Nat) (devm : Devm) :
    (pushItem x c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [pushItem, liftMachExecution_resultGas]
  exact Mach.pushItem_machResultGas x c devm.mach

@[simp] theorem applyUnary_gasLe (f : U256 → U256) (c : Nat) (devm : Devm) :
    (applyUnary f c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [applyUnary, liftMachExecution_resultGas]
  exact Mach.applyUnary_machResultGas f c devm.mach

@[simp] theorem applyBinary_gasLe (f : U256 → U256 → U256) (c : Nat) (devm : Devm) :
    (applyBinary f c devm).gasMeasure ≤ devm.gasMeasure := by
  rw [applyBinary, liftMachExecution_resultGas]
  exact Mach.applyBinary_machResultGas f c devm.mach

@[simp] theorem applyTernary_gasLe (f : U256 → U256 → U256 → U256) (c : Nat)
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

theorem PlainOp.balanceCore_resultGasLe (rules : ForkRules) (world : World)
    (mach : Mach) (view : Meta) :
    machMetaResultGas (PlainOp.balanceCore rules world mach view) ≤ mach.gasMeasure := by
  have hp := Mach.pop_machResultGas mach
  have hc : ∀ (c : Nat) (m : Mach), machResultGas (Mach.chargeGas c m) ≤ m.gasMeasure :=
    Mach.chargeGas_machResultGas
  have hc' : ∀ {c : Nat} {m : Mach} {r}, Mach.chargeGas c m = r →
      machResultGas r ≤ m.gasMeasure := fun h => h ▸ hc _ _
  have hs : ∀ (x : U256) (m : Mach), machResultGas (Mach.push x m) = m.gasMeasure :=
    Mach.push_machResultGas
  unfold PlainOp.balanceCore
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
      have := hc' heq2
      simp only [machResultGas] at this
      simp only [machMetaResultGas]
      omega
    · rename_i u m2 heq2
      have h2 := hc' heq2
      simp only [machResultGas] at h2
      split
      · rename_i err m3 heq3
        have h3 := hs (world.state.get x.toAddress).balance m2
        rw [heq3] at h3
        simp only [machResultGas] at h3
        simp only [machMetaResultGas]
        omega
      · rename_i u2 m3 heq3
        have h3 := hs (world.state.get x.toAddress).balance m2
        rw [heq3] at h3
        simp only [machResultGas] at h3
        simp only [machMetaResultGas]
        omega

/-- Every `Rinst` body leaves at most the gas it started with, in *either*
branch. The successful branch is already covered strictly by
`Rinst.runCore_gasLt`; this is the error branch the `"Revert"` path needs. -/
theorem PlainOp.runCore_gasLe (pc : Nat) (devm : Devm) (sevm : Sevm) (r : PlainOp) :
    (PlainOp.runCore pc devm sevm r).gasMeasure ≤ devm.gasMeasure := by
  cases r <;> simp only [PlainOp.runCore]
  all_goals first
    | exact pushItem_gasLe _ _ _
    | exact applyUnary_gasLe _ _ _
    | exact applyBinary_gasLe _ _ _
    | exact applyTernary_gasLe _ _ _
    | skip
  case balance =>
    rw [liftMachMetaWorldExecution, liftMachMetaExecution_resultGas]
    exact PlainOp.balanceCore_resultGasLe _ _ _ _
  case clz =>
    split
    · exact applyUnary_gasLe _ _ _
    · simp
  case slotnum =>
    split
    · exact pushItem_gasLe _ _ _
    · simp
  case shl | shr | sar =>
    split
    · exact applyBinary_gasLe _ _ _
    · simp
  case chainid | basefee | blobbasefee =>
    split
    · exact pushItem_gasLe _ _ _
    · simp
  case pop =>
    exact gasLe_bind_id (Nat.le_of_eq (Devm.pop_map_snd_gasLe devm))
      (fun d => chargeGas_result_gasLe _ d)
  case blobhash =>
    split
    · refine gasLe_bind_snd (by simp) ?_
      rintro ⟨x, d1⟩
      exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => by simp)
    · simp
  case calldataload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => by simp)
  case blockhash =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => by simp)
  case gas =>
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => by simp)
  case exp =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    exact gasLe_bind_id (chargeGas_result_gasLe _ _)
      (fun d => by simp)
  case tload =>
    split
    · refine gasLe_bind_snd (by simp) ?_
      rintro ⟨x, d1⟩
      exact pushItem_gasLe _ _ _
    · simp
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
  case calldatacopy | codecopy =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨x, d1⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨y, d2⟩
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨z, d3⟩
    refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
    intro d4
    simp
  case mcopy =>
    split
    · refine gasLe_bind_snd (by simp) ?_
      rintro ⟨x, d1⟩
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨y, d2⟩
      refine gasLe_bind_snd (by simp) ?_
      rintro ⟨z, d3⟩
      refine gasLe_bind_id (chargeGas_result_gasLe _ _) ?_
      intro d4
      simp
    · simp
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
  case selfbalance =>
    split
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _) (fun d => by simp)
    · simp
  case extcodesize =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨adr, d1⟩
    split
    · split
      · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
          (fun d => by simp)
      · exact gasLe_bind_id
          (Nat.le_trans (chargeGas_result_gasLe _ _)
            (Nat.le_of_eq (addAccessedAddress_gasMeasure _ _)))
          (fun d => by simp)
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => by simp)
  case extcodehash =>
    split
    · refine gasLe_bind_snd (by simp) ?_
      rintro ⟨adr, d1⟩
      split
      · split
        · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
            (fun d => by simp)
        · exact gasLe_bind_id
            (Nat.le_trans (chargeGas_result_gasLe _ _)
              (Nat.le_of_eq (addAccessedAddress_gasMeasure _ _)))
            (fun d => by simp)
      · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
          (fun d => by simp)
    · simp
  case sload =>
    refine gasLe_bind_snd (by simp) ?_
    rintro ⟨key, d1⟩
    split
    · split
      · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
          (fun d => by simp)
      · exact gasLe_bind_id
          (Nat.le_trans (chargeGas_result_gasLe _ _)
            (Nat.le_of_eq (addAccessedStorageKey_gasMeasure _ _ _)))
          (fun d => by simp)
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _)
        (fun d => by simp)
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
    · split
      · exact gasLe_bind_id (chargeGas_result_gasLe _ _) (fun d => by simp)
      · exact gasLe_bind_id
          (Nat.le_trans (chargeGas_result_gasLe _ _)
            (Nat.le_of_eq (addAccessedAddress_gasMeasure _ _)))
          (fun d => by simp)
    · exact gasLe_bind_id (chargeGas_result_gasLe _ _) (fun d => by simp)
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
    · split
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
    · simp
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
    · split
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
      · -- The pre-Berlin regimes: the same binds; the cold pair cases on
        -- access, then on the slot's warmth.
        refine gasLe_bind_snd (by simp) ?_
        rintro ⟨key, d1⟩
        refine gasLe_bind_snd (by simp) ?_
        rintro ⟨val, d2⟩
        refine gasLe_bind_const (devm := d2) (by simp) ?_
        intro _
        refine gasLe_bind (proj := Prod.fst) ?_ ?_
        · simp only [resultGas_ok]
          split
          · simp
          · split <;> simp
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

theorem JumpOp.runCore_gasLe (pc : Nat) (devm : Devm) (sevm : Sevm) (j : JumpOp) :
    resultGas Prod.snd (JumpOp.runCore pc devm sevm j) ≤ devm.gasMeasure := by
  cases j <;> simp only [JumpOp.runCore]
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

@[simp] theorem Devm.subBal_gasMeasure {devm devm' : Devm} {a : Address} {v : U256}
    (h : devm.subBal a v = some devm') : devm'.gasMeasure = devm.gasMeasure := by
  unfold Devm.subBal at h
  rcases hs : devm.state.subBal a v with _ | state <;> rw [hs] at h <;>
    simp only [bind, Option.bind, Option.some.injEq] at h
  · nomatch h
  · rw [← h, Devm.clearStorageWritesIfEmpty_gasMeasure, Devm.withState_gasMeasure]

@[simp] theorem Devm.setBal_gasMeasure (devm : Devm) (a : Address) (v : U256) :
    (devm.setBal a v).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem addAccountToDelete_gasMeasure (devm : Devm) (a : Address) :
    (addAccountToDelete devm a).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem Devm.recordTouch_gasMeasure (devm : Devm) (rules : ForkRules) (cond : Bool)
    (a : Address) : (devm.recordTouch rules cond a).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem Devm.addBal_gasMeasure (devm : Devm) (a : Address) (v : U256) :
    (devm.addBal a v).gasMeasure = devm.gasMeasure := rfl

@[simp] theorem Devm.creditBeneficiary_gasMeasure (devm : Devm) (rules : ForkRules)
    (a : Address) (v : U256) :
    (devm.creditBeneficiary rules a v).gasMeasure = devm.gasMeasure := by
  unfold Devm.creditBeneficiary
  split <;> rfl

@[simp] theorem Devm.emitTransferLog_gasMeasure
    (devm : Devm) (sender recipient : Address) (amount : U256) :
    (devm.emitTransferLog sender recipient amount).gasMeasure = devm.gasMeasure := by
  unfold Devm.emitTransferLog
  split <;> simp

@[simp] theorem Devm.withOutput_gasMeasure (devm : Devm) (output : Bytes) :
    (devm.withOutput output).gasMeasure = devm.gasMeasure := rfl

/-- The halting instructions. `.revert` is the reason this whole layer exists: it
is the sole producer of the `"Revert"` tag, the one error `handleError` turns
back into a successful frame result carrying live gas. -/
theorem HaltOp.run_gasLe (sevm : Sevm) (devm : Devm) (l : HaltOp) :
    Execution.gasMeasure (HaltOp.run sevm devm l) ≤ devm.gasMeasure := by
  cases l <;> simp only [HaltOp.run]
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
        split <;> (try split) <;> simp
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
      -- The two EIP-7928 read recorders between the warming and the charges.
      let dR := (d2.balReadAccount sevm.benvStat.rules donee).balReadAccount
        sevm.benvStat.rules sevm.currentTarget
      have hdR : dR.gasMeasure = d1.gasMeasure := by
        simp only [dR, Devm.balReadAccount_gasMeasure, hd2]
      refine gasLe_bind_id ?_ ?_
      · exact Nat.le_trans (chargeGas_result_gasLe _ dR) (Nat.le_of_eq hdR)
      · intro d3
        refine gasLe_bind_id (chargeStateGas_result_gasLe _ d3) ?_
        intro d4
        refine gasLe_bind_id ?_ ?_
        · -- The balance is read through the recorders; split the match itself.
          simp only [Option.toExcept]
          split
          · simp
          · rename_i d5 hb
            simp [Devm.subBal_gasMeasure hb]
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

theorem Mach.push_haltOut {x : U256} {mach : Mach} {s : StateGasMeter}
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

theorem Devm.push_haltOut {x : U256} {devm : Devm} {s : StateGasMeter}
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

theorem Devm.pop_haltLe {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun p : U256 × Devm => p.2.gasMeasure ≤ n) devm.pop :=
  HaltLe.ofHaltOut (Devm.pop_haltOut rfl) (by simpa using hn)

theorem Devm.popToNat_haltLe {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun p : Nat × Devm => p.2.gasMeasure ≤ n) devm.popToNat :=
  HaltLe.ofHaltOut (Devm.popToNat_haltOut rfl) (by simpa using hn)

theorem Devm.popToAdr_haltLe {devm : Devm} {n : Nat}
    (hn : devm.gasMeasure ≤ n) :
    HaltLe n (fun p : Address × Devm => p.2.gasMeasure ≤ n) devm.popToAdr :=
  HaltLe.ofHaltOut (Devm.popToAdr_haltOut rfl) (by simpa using hn)

theorem Devm.push_haltLe (x : U256) {devm : Devm} {n : Nat}
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

theorem Devm.push_haltLe_spill (x : U256) {devm : Devm} {n : Nat}
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

/-! ## Settling a finished frame

`settle` turns a child's raw result into what its caller resumes from, and it is where the two
halting routes above are consumed. Stating the obligation once, as `Execution.SettledGasLe`, is
what lets the driver stay ignorant of which route a given instruction family took. -/

/-- What a halting outcome owes the parent frame: every frame result that settlement (`settle`)
makes of it, under either state-gas regime, measures at most `n`. A success is reported as it
stands; a revert keeps its gas (under state gas its meter is refilled first); an exceptional halt
forfeits its execution gas (under state gas, after the refill); a fault is not a frame result and
owes nothing. -/
def Execution.SettledGasLe (n : Nat) : Execution → Prop
  | .ok d => d.gasMeasure ≤ n
  | .error (.revert, d) => d.gasMeasure ≤ n ∧ d.restoreStateGas.gasMeasure ≤ n
  | .error (.halt _, d) =>
    (d.withGasLeft 0).gasMeasure ≤ n ∧ d.restoreStateGas.forfeitRemainingGas.gasMeasure ≤ n
  | .error (.crypto _, _) => True
  | .error (.internal _, _) => True

theorem Execution.SettledGasLe.mono {m n : Nat} {ex : Execution} (h : m ≤ n)
    (hs : ex.SettledGasLe m) : ex.SettledGasLe n := by
  match ex, hs with
  | .ok _, hs => exact Nat.le_trans hs h
  | .error (.revert, _), hs => exact ⟨Nat.le_trans hs.1 h, Nat.le_trans hs.2 h⟩
  | .error (.halt _, _), hs => exact ⟨Nat.le_trans hs.1 h, Nat.le_trans hs.2 h⟩
  | .error (.crypto _, _), _ => trivial
  | .error (.internal _, _), _ => trivial

/-- The route the `Rinst`/`Jinst`/`Linst` corpus takes. -/
theorem Execution.settledGasLe_of_gasLe {n : Nat} {ex : Execution}
    (h : ex.gasMeasure ≤ n) : ex.SettledGasLe n := by
  match ex with
  | .ok d => exact h
  | .error (.revert, d) =>
    simp only [Execution.gasMeasure_error] at h
    exact ⟨h, by rw [Devm.restoreStateGas_gasMeasure]; exact h⟩
  | .error (.halt _, d) =>
    simp only [Execution.gasMeasure_error] at h
    have hm := Devm.gasMeasure_eq d
    refine ⟨?_, Nat.le_trans (Devm.forfeitRemainingGas_gasMeasure_le _)
      (by rw [Devm.restoreStateGas_gasMeasure]; exact h)⟩
    rw [Devm.withGasLeft_gasMeasure]
    omega
  | .error (.crypto _, _) => trivial
  | .error (.internal _, _) => trivial

/-- The route the `Xinst` family takes: bound the successful branch, rule out
the one tag that would let an error carry live gas through, and bound the spill
an exceptional halt keeps. -/
theorem Execution.settledGasLe_of_halt {n : Nat} {ex : Execution}
    (hok : ∀ d, ex = .ok d → d.gasMeasure ≤ n)
    (hhalt : ∀ p, ex = .error p → p.1 ≠ .revert ∧ p.2.spill ≤ n) :
    ex.SettledGasLe n := by
  match ex with
  | .ok d => exact hok d rfl
  | .error (.revert, d) => exact absurd rfl (hhalt _ rfl).1
  | .error (.halt _, d) =>
    have hsp := (hhalt _ rfl).2
    dsimp only at hsp
    refine ⟨?_, Nat.le_trans (Devm.restoreStateGas_forfeitRemainingGas_gasMeasure_le_spill _) hsp⟩
    rw [Devm.withGasLeft_gasMeasure]
    omega
  | .error (.crypto _, _) => trivial
  | .error (.internal _, _) => trivial

/-- A successful `liftMachExecution` changes only the machine. -/
theorem liftMachExecution_ok_eq_setMach {core : Mach → Footprint.Outcome Mach Unit}
    {devm devm' : Devm} (h : liftMachExecution core devm = .ok devm') :
    devm' = devm.setMach devm'.mach := by
  unfold liftMachExecution liftMach Footprint.toExecution Footprint.liftOutcome at h
  rcases hc : core devm.mach with ⟨err, view⟩ | ⟨u, mach'⟩ <;> simp only [hc] at h
  · exact absurd h (by simp)
  · simp only [Except.ok.injEq] at h
    rw [← h]
    rfl

/-! ## Entering a frame

A frame either hands the child exactly the inner message's gas, or resolves
without running a child at all — and in that case its result is a settled
precompile outcome, which the settlement bound already covers. -/

@[simp] theorem Msg.withBenv_gas (msg : Msg) (benv : Benv) :
    (msg.withBenv benv).gas = msg.gas := rfl

@[simp] theorem initEvm_gasMeasure (msg : Msg) :
    (initEvm msg).dyna.gasMeasure = msg.gas := rfl

/-! ### Every frame the interpreter enters runs under the same rules

The gas-decreasing obligations rest on `rules.Valid` -- Amsterdam reprices the
numbers they lean on, so the numbers are no longer literals a `decide` can
settle. Since goal `jaune-forks-by-construction-v1` the witness is a fact about
the machine (`Sevm.rules_valid`, from `Fork.ruleSet_valid`) rather than a
premise, so nothing has to *travel* into a child frame: the child is a machine
and carries its own. The invariant below is kept because it is what makes the
recursion's rule-identity claim true rather than assumed, and because the
spawn obligation still states it: a spawned frame's rules are the spawning
frame's rules.

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

@[simp] theorem Benv.addBal_stat (benv : Benv) (adr : Address) (val : U256) :
    (benv.addBal adr val).stat = benv.stat := rfl

theorem Benv.subBal_stat {benv benv' : Benv} {adr : Address} {val : U256}
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

/-! ### A spawned frame carries the spawning frame's block environment

Both frame builders copy `sevm.benvStat` verbatim -- `callMsg` and `createMsg`
write `stat := sevm.benvStat` into the child's `Benv`, and `Frame.ofCreate`'s
`processCreateMessage.msg` rewrites only storage and the nonce -- so a spawned
frame runs under the spawning frame's rules by construction. These lemmas lift
that from the two builders to `Evm.step`, which is where the driver needs it. -/

@[simp] theorem callMsg_stat
    (sevm : Sevm) (evm1 : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (calldata : Bytes) (code : ByteArray) (disablePrecompiles : Bool) :
    (callMsg sevm evm1 gas value caller target codeAddress shouldTransferValue
      isStaticcall calldata code disablePrecompiles).benv.stat
      = sevm.benvStat := rfl

@[simp] theorem createMsg_stat
    (sevm : Sevm) (devm : Devm) (createGas : Nat) (endowment : U256)
    (newAddress : Address) (calldata : Bytes) :
    (createMsg sevm devm createGas endowment newAddress calldata).benv.stat
      = sevm.benvStat := rfl

/-! ## A PUSH lowers the measure

The successful branch of `NextOp.step`'s PUSH case, which `NextOp.step_gasBound`
(`Jaune/MessageCall/StepGas.lean`) consumes. -/

theorem NextOp.step_push_gasLt {xs : Bytes} {evm : Evm} {devm : Devm}
    (h : (chargeGas (if xs = [] then Gas.base else Gas.veryLow) evm.dyna >>=
      Devm.push xs.toU256) = .ok devm) : devm.gasMeasure < evm.dyna.gasMeasure := by
  obtain ⟨d1, h1, h2⟩ := Except.bind_eq_ok h
  have e1 := chargeGas_gasMeasure h1
  have e2 := Devm.push_gasMeasure h2
  have hpos : 0 < (if xs = [] then Gas.base else Gas.veryLow) := by
    split <;> decide
  omega

/-! ## Inversions for the transaction layer's lifts -/

/-- Inversion for the `Option.toExcept` lifts that thread the transaction
chain: a successful lift pins the option. -/
theorem Option.toExcept_eq_ok {ξ : Type u} {υ : Type v} {x : ξ} {o : Option υ}
    {v : υ} (h : Option.toExcept x o = .ok v) : o = some v := by
  cases o with
  | none => nomatch h
  | some w => cases h; rfl

/-- Inversion for the `bimap Prod.fst id` error erasure. -/
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
