import Jaune.Bridge.MessageCall
import Jaune.Sufficiency

/-!
# The clean-result invariant (W1 unit F0, bridge)

Today's interpreter writes `Meta.error` only at settlement. So a frame entered with no stored
error never yields a raw `.ok d` that stores one: every instruction, every spawn's saved caller
and every resume keep the field as they found it. The bridges of units C, D and E take this as
their premise `Execution.Clean`; this module proves it, about the old definitions, and is deleted
with them after the gate's tag (the W1 design note, third revision, section 3.2, unit F0).

The walk is over every instruction arm under both rule shapes. It follows the shape of the
state-gas-zero family in `Jaune.Execution`, with one difference: only the success channel is
constrained, so an error result needs nothing.
-/

namespace Jaune

namespace Legacy

/-! ### Results that keep a field on success -/

/-- `P` holds of the payload of a successful result; an error result satisfies it vacuously. -/
def OnSuccess {ε α : Type} (P : α → Prop) : Except ε α → Prop
  | .ok a => P a
  | .error _ => True

@[simp] theorem onSuccess_ok {ε α : Type} {P : α → Prop} {a : α} :
    OnSuccess P (Except.ok a : Except ε α) ↔ P a := Iff.rfl

@[simp] theorem onSuccess_error {ε α : Type} {P : α → Prop} {x : ε} :
    OnSuccess P (Except.error x : Except ε α) := trivial

@[simp] theorem onSuccess_pure {ε α : Type} {P : α → Prop} {a : α} :
    OnSuccess P (pure a : Except ε α) ↔ P a := Iff.rfl

/-- `OnSuccess` of `if`. -/
theorem onSuccess_if {ε α : Type} {P : α → Prop} {c : Prop} [Decidable c]
    {a b : Except ε α} (ha : c → OnSuccess P a) (hb : ¬c → OnSuccess P b) :
    OnSuccess P (if c then a else b) := by
  by_cases h : c
  · simpa only [h, ite_true] using ha h
  · simpa only [h, ite_false] using hb h

/-- `OnSuccess` of `dependent_if`. -/
theorem onSuccess_dependent_if {ε α : Type} {P : α → Prop} {c : Prop} [Decidable c]
    {a : c → Except ε α} {b : ¬c → Except ε α} (ha : ∀ h, OnSuccess P (a h))
    (hb : ∀ h, OnSuccess P (b h)) :
    OnSuccess P (if h : c then a h else b h) := by
  by_cases h : c
  · simpa only [h, dite_true] using ha h
  · simpa only [h, dite_false] using hb h

/-- Bind through a machine-valued result whose machine keeps the error `e`. -/
theorem OnSuccess.bind_machine {ε β : Type} {e : Option SettledHalt} {Q : β → Prop}
    {x : Except ε Devm} {f : Devm → Except ε β}
    (hx : OnSuccess (fun d => d.error = e) x)
    (hf : ∀ d : Devm, d.error = e → OnSuccess Q (f d)) :
    OnSuccess Q (x >>= f) := by
  cases x with
  | error _ => trivial
  | ok d => exact hf d hx

/-- Bind through a result paired with a machine that keeps the error `e`. -/
theorem OnSuccess.bind_pair {ε γ β : Type} {e : Option SettledHalt} {Q : β → Prop}
    {x : Except ε (γ × Devm)} {f : γ × Devm → Except ε β}
    (hx : OnSuccess (fun a => a.2.error = e) x)
    (hf : ∀ a : γ × Devm, a.2.error = e → OnSuccess Q (f a)) :
    OnSuccess Q (x >>= f) := by
  cases x with
  | error _ => trivial
  | ok a => exact hf a hx

/-- Bind through a result whose machine comes first in the pair. -/
theorem OnSuccess.bind_pair_first {ε γ β : Type} {e : Option SettledHalt} {Q : β → Prop}
    {x : Except ε (Devm × γ)} {f : Devm × γ → Except ε β}
    (hx : OnSuccess (fun a => a.1.error = e) x)
    (hf : ∀ a : Devm × γ, a.1.error = e → OnSuccess Q (f a)) :
    OnSuccess Q (x >>= f) := by
  cases x with
  | error _ => trivial
  | ok a => exact hf a hx

/-- Bind through a result that carries no machine (an assertion, a number). -/
theorem OnSuccess.bind_any {ε γ β : Type} {Q : β → Prop}
    {x : Except ε γ} {f : γ → Except ε β}
    (hf : ∀ v : γ, OnSuccess Q (f v)) :
    OnSuccess Q (x >>= f) := by
  cases x with
  | error _ => trivial
  | ok a => exact hf a

/-! ### Setters keep `error`

Every machine update outside settlement leaves `Meta.error` alone. -/

/-- Closes `(setter d).error = d.error` by unfolding and splitting the setter's branches. -/
macro "setter_error" : tactic => `(tactic| (repeat' (first | rfl | split | (simp only [Devm.error]))))

/-- `Devm.withGasLeft` leaves `error` alone. -/
theorem Devm.withGasLeft_error (d : Devm) (n : Nat) :
    (d.withGasLeft n).error = d.error := by
  rfl

/-- `Devm.withReturnData` leaves `error` alone. -/
theorem Devm.withReturnData_error (d : Devm) (b : Bytes) :
    (d.withReturnData b).error = d.error := by
  rfl

/-- `Devm.withStack` leaves `error` alone. -/
theorem Devm.withStack_error (d : Devm) (s : List U256) :
    (d.withStack s).error = d.error := by
  rfl

/-- `Devm.withMemory` leaves `error` alone. -/
theorem Devm.withMemory_error (d : Devm) (m : Mem) :
    (d.withMemory m).error = d.error := by
  rfl

/-- `Devm.withRefundCounter` leaves `error` alone. -/
theorem Devm.withRefundCounter_error (d : Devm) (r : Int) :
    (d.withRefundCounter r).error = d.error := by
  rfl

/-- `Devm.withAccountsToDelete` leaves `error` alone. -/
theorem Devm.withAccountsToDelete_error (d : Devm) (s : AdrSet) :
    (d.withAccountsToDelete s).error = d.error := by
  rfl

/-- `Devm.withCreatedAccounts` leaves `error` alone. -/
theorem Devm.withCreatedAccounts_error (d : Devm) (s : AdrSet) :
    (d.withCreatedAccounts s).error = d.error := by
  rfl

/-- `Devm.withState` leaves `error` alone. -/
theorem Devm.withState_error (d : Devm) (s : State) :
    (d.withState s).error = d.error := by
  rfl

/-- `Devm.withStorageWrites` leaves `error` alone. -/
theorem Devm.withStorageWrites_error (d : Devm) (s : KeySet) :
    (d.withStorageWrites s).error = d.error := by
  rfl

/-- `Devm.withTransientStorage` leaves `error` alone. -/
theorem Devm.withTransientStorage_error (d : Devm) (t : TransientStorage) :
    (d.withTransientStorage t).error = d.error := by
  rfl

/-- `Devm.balReadAccount` leaves `error` alone. -/
theorem Devm.balReadAccount_error (rules : ForkRules) (a : Address) (d : Devm) :
    (d.balReadAccount rules a).error = d.error := by
  simp only [Devm.error]; unfold Devm.balReadAccount Devm.setMeta; setter_error

/-- `Devm.balReadStorage` leaves `error` alone. -/
theorem Devm.balReadStorage_error (rules : ForkRules) (a : Address) (k : U256) (d : Devm) :
    (d.balReadStorage rules a k).error = d.error := by
  simp only [Devm.error]; unfold Devm.balReadStorage Devm.setMeta; setter_error

/-- `Devm.memWrite` leaves `error` alone. -/
theorem Devm.memWrite_error (d : Devm) (i : Nat) (b : Bytes) :
    (d.memWrite i b).error = d.error := by
  rfl

/-- `Devm.memExtends` leaves `error` alone. -/
theorem Devm.memExtends_error (d : Devm) (p : List (Nat × Nat)) :
    (d.memExtends p).error = d.error := by
  rfl

/-- The machine `Devm.memRead` returns leaves `error` alone. -/
theorem Devm.memRead_second_error (d : Devm) (i s : Nat) :
    (d.memRead i s).2.error = d.error := by
  rfl

/-- `Devm.incrNonce` leaves `error` alone. -/
theorem Devm.incrNonce_error (d : Devm) (a : Address) :
    (d.incrNonce a).error = d.error := by
  rfl

/-- `Devm.setBal` leaves `error` alone. -/
theorem Devm.setBal_error (d : Devm) (a : Address) (v : U256) :
    (d.setBal a v).error = d.error := by
  rfl

/-- `Devm.addBal` leaves `error` alone. -/
theorem Devm.addBal_error (d : Devm) (a : Address) (v : U256) :
    (d.addBal a v).error = d.error := by
  rfl

/-- `Devm.creditBeneficiary` leaves `error` alone. -/
theorem Devm.creditBeneficiary_error (rules : ForkRules) (a : Address) (v : U256) (d : Devm) :
    (d.creditBeneficiary rules a v).error = d.error := by
  simp only [Devm.error]; unfold Devm.creditBeneficiary; setter_error

/-- `addAccountToDelete` leaves `error` alone. -/
theorem addAccountToDelete_error (d : Devm) (a : Address) :
    (addAccountToDelete d a).error = d.error := by
  rfl

/-- `creditSelfdestructRefund` leaves `error` alone. -/
theorem creditSelfdestructRefund_error (rules : ForkRules) (p : Prop) [Decidable p] (d : Devm) :
    (creditSelfdestructRefund rules p d).error = d.error := by
  simp only [Devm.error]; unfold creditSelfdestructRefund; setter_error

/-- `Devm.emitTransferLog` leaves `error` alone. -/
theorem Devm.emitTransferLog_error (d : Devm) (a b : Address) (v : U256) :
    (d.emitTransferLog a b v).error = d.error := by
  simp only [Devm.error]; unfold Devm.emitTransferLog; setter_error

/-- `Devm.addLog` leaves `error` alone. -/
theorem Devm.addLog_error' (d : Devm) (l : Log) :
    (d.addLog l).error = d.error := by
  rfl

/-- `Devm.setStorVal` leaves `error` alone. -/
theorem Devm.setStorVal_error' (d : Devm) (a : Address) (k v : U256) :
    (d.setStorVal a k v).error = d.error := by
  rfl

/-- `Devm.setTransVal` leaves `error` alone. -/
theorem Devm.setTransVal_error' (d : Devm) (a : Address) (k v : U256) :
    (d.setTransVal a k v).error = d.error := by
  rfl

/-- `Devm.creditStateGasRefund` leaves `error` alone. -/
theorem Devm.creditStateGasRefund_error (n : Nat) (d : Devm) :
    (d.creditStateGasRefund n).error = d.error := by
  rfl

/-- `Devm.restoreChildGas` leaves `error` alone. -/
theorem Devm.restoreChildGas_error (g r : Nat) (d : Devm) :
    (d.restoreChildGas g r).error = d.error := by
  rfl

/-- The machine `Devm.withholdCreateGas` returns leaves `error` alone. -/
theorem Devm.withholdCreateGas_second_error (d : Devm) :
    d.withholdCreateGas.2.error = d.error := by
  rfl

/-- The machine `Devm.drainStateGasReservoir` returns leaves `error` alone. -/
theorem Devm.drainStateGasReservoir_second_error (d : Devm) :
    d.drainStateGasReservoir.2.error = d.error := by
  rfl

/-- `addAccessedAddress` leaves `error` alone. -/
theorem addAccessedAddress_error' (d : Devm) (a : Address) :
    (addAccessedAddress d a).error = d.error := by
  rfl

/-- `addAccessedStorageKey` leaves `error` alone. -/
theorem addAccessedStorageKey_error' (d : Devm) (a : Address) (k : U256) :
    (addAccessedStorageKey d a k).error = d.error := by
  rfl

/-- `accessDelegation` leaves `error` alone. -/
theorem accessDelegation_error (d : Devm) (a : Address) :
    (accessDelegation d a).2.2.2.2.error = d.error := by
  simp only [Devm.error]; unfold accessDelegation; setter_error

/-- `GasSchedule.accessDelegation` leaves `error` alone. -/
theorem GasSchedule.accessDelegation_error (g : GasSchedule) (d : Devm) (a : Address) :
    (g.accessDelegation d a).2.2.2.2.error = d.error := by
  simp only [Devm.error]; unfold GasSchedule.accessDelegation; setter_error

/-- `ForkRules.accessDelegation` leaves `error` alone. -/
theorem ForkRules.accessDelegation_error (rules : ForkRules) (d : Devm) (a : Address) :
    (rules.accessDelegation d a).2.2.2.2.error = d.error := by
  simp only [Devm.error]; unfold ForkRules.accessDelegation GasSchedule.accessDelegation; setter_error

/-- `completeDelegationAccess` leaves `error` alone. -/
theorem completeDelegationAccess_error (d : Devm) (b : Bool) (a : Address) :
    (completeDelegationAccess d b a).2.error = d.error := by
  simp only [Devm.error]; unfold completeDelegationAccess; setter_error

/-- `incorporateChildOnError` leaves `error` alone. -/
theorem incorporateChildOnError_error (p c : Devm) (b : Bytes) :
    (incorporateChildOnError p c b).error = p.error := by
  rfl

/-- `incorporateChildOnSuccess` leaves `error` alone. -/
theorem incorporateChildOnSuccess_error (p c : Devm) (b : Bytes) :
    (incorporateChildOnSuccess p c b).error = p.error := by
  rfl

/-- `incorporateChildAmsterdamOnError` leaves `error` alone. -/
theorem incorporateChildAmsterdamOnError_error (p c : Devm) (b : Bytes) :
    (incorporateChildAmsterdamOnError p c b).error = p.error := by
  rfl

/-- `incorporateChildAmsterdamOnSuccess` leaves `error` alone. -/
theorem incorporateChildAmsterdamOnSuccess_error (p c : Devm) (b : Bytes) :
    (incorporateChildAmsterdamOnSuccess p c b).error = p.error := by
  rfl

/-! ### Primitive machine operations -/

/-- `liftMach` keeps the error of its machine on success. -/
theorem liftMach_onSuccess {α : Type} (core : Mach → Footprint.Outcome Mach α) {d : Devm}
    {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun a => a.2.error = e) (liftMach core d) := by
  unfold liftMach Footprint.liftOutcome
  split
  · trivial
  · exact h

/-- `liftMachExecution` keeps the error of its machine on success. -/
theorem liftMachExecution_onSuccess (core : Mach → Footprint.Outcome Mach Unit) {d : Devm}
    {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun d' => d'.error = e) (liftMachExecution core d) := by
  have hl := liftMach_onSuccess core h
  unfold liftMachExecution Footprint.toExecution
  revert hl
  cases liftMach core d with
  | error _ => intro; trivial
  | ok a => intro hl; exact hl

/-- `chargeGas` keeps the error of its machine on success. -/
theorem chargeGas_onSuccess (cost : Nat) {d : Devm} {e : Option SettledHalt}
    (h : d.error = e) : OnSuccess (fun d' => d'.error = e) (chargeGas cost d) :=
  liftMachExecution_onSuccess _ h

/-- `chargeStateGas` keeps the error of its machine on success. -/
theorem chargeStateGas_onSuccess (cost : Nat) {d : Devm} {e : Option SettledHalt}
    (h : d.error = e) : OnSuccess (fun d' => d'.error = e) (chargeStateGas cost d) :=
  liftMachExecution_onSuccess _ h

/-- `Devm.push` keeps the error of its machine on success. -/
theorem Devm.push_onSuccess (x : U256) {d : Devm} {e : Option SettledHalt}
    (h : d.error = e) : OnSuccess (fun d' => d'.error = e) (d.push x) :=
  liftMachExecution_onSuccess _ h

/-- `Devm.pop` keeps the error of its machine on success. -/
theorem Devm.pop_onSuccess {d : Devm} {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun a => a.2.error = e) d.pop :=
  liftMach_onSuccess _ h

/-- `Devm.popToNat` keeps the error of its machine on success. -/
theorem Devm.popToNat_onSuccess {d : Devm} {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun a => a.2.error = e) d.popToNat :=
  liftMach_onSuccess _ h

/-- `Devm.popToAdr` keeps the error of its machine on success. -/
theorem Devm.popToAdr_onSuccess {d : Devm} {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun a => a.2.error = e) d.popToAdr :=
  liftMach_onSuccess _ h

/-- `Devm.popN` keeps the error of its machine on success. -/
theorem Devm.popN_onSuccess {d : Devm} {e : Option SettledHalt} (h : d.error = e) (n : Nat) :
    OnSuccess (fun a => a.2.error = e) (d.popN n) :=
  liftMach_onSuccess _ h

/-- `applyUnary` keeps the error of its machine on success. -/
theorem applyUnary_onSuccess (f : U256 → U256) (c : Nat) {d : Devm} {e : Option SettledHalt}
    (h : d.error = e) : OnSuccess (fun d' => d'.error = e) (applyUnary f c d) :=
  liftMachExecution_onSuccess _ h

/-- `applyBinary` keeps the error of its machine on success. -/
theorem applyBinary_onSuccess (f : U256 → U256 → U256) (c : Nat) {d : Devm}
    {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun d' => d'.error = e) (applyBinary f c d) :=
  liftMachExecution_onSuccess _ h

/-- `applyTernary` keeps the error of its machine on success. -/
theorem applyTernary_onSuccess (f : U256 → U256 → U256 → U256) (c : Nat) {d : Devm}
    {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun d' => d'.error = e) (applyTernary f c d) :=
  liftMachExecution_onSuccess _ h

/-- `pushItem` keeps the error of its machine on success. -/
theorem pushItem_onSuccess (x : U256) (c : Nat) {d : Devm} {e : Option SettledHalt}
    (h : d.error = e) : OnSuccess (fun d' => d'.error = e) (pushItem x c d) :=
  liftMachExecution_onSuccess _ h

/-- A machine-and-substate core that keeps `Meta.error` keeps it through the lift. -/
theorem liftMachMetaExecution_onSuccess
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (hc : ∀ m v, OnSuccess (fun a => a.2.2.error = v.error) (core m v)) {d : Devm}
    {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun d' => d'.error = e) (liftMachMetaExecution core d) := by
  have hcd := hc d.mach d.meta
  cases hcore : core d.mach d.meta with
  | error _ =>
    simp only [liftMachMetaExecution, Footprint.toExecution, liftMachMeta,
      Footprint.liftOutcome, hcore, onSuccess_error]
  | ok a =>
    rw [hcore] at hcd
    simp only [liftMachMetaExecution, Footprint.toExecution, liftMachMeta,
      Footprint.liftOutcome, hcore, onSuccess_ok]
    exact hcd.trans h

/-- `PlainOp.balance` keeps the error of its machine on success. -/
theorem PlainOp.balance_onSuccess (rules : ForkRules) {d : Devm} {e : Option SettledHalt}
    (h : d.error = e) :
    OnSuccess (fun d' => d'.error = e)
      (liftMachMetaWorldExecution (PlainOp.balanceCore rules) d) := by
  refine liftMachMetaExecution_onSuccess _ (fun m v => ?_) h
  have hview : ∀ (a : Address),
      (match rules.access with
        | .eip2929 => if a ∈ v.accessedAddresses then v else v.addAccessedAddress a
        | .flat _ => v).error = v.error := by
    intro a; split
    · split <;> rfl
    · rfl
  unfold PlainOp.balanceCore
  rcases m.pop with ⟨err, m'⟩ | ⟨x, m'⟩
  · trivial
  · dsimp only
    rcases Mach.chargeGas _ m' with ⟨err, m''⟩ | ⟨u, m''⟩
    · trivial
    · dsimp only
      rcases Mach.push _ m'' with ⟨err, m'''⟩ | ⟨u', m'''⟩
      · trivial
      · show (if _ then _ else _ : Meta).error = v.error
        split
        · exact hview _
        · exact hview _

/-- Forgetting the payload beside a machine keeps the machine's error. -/
theorem OnSuccess.map_second {ε γ : Type} {e : Option SettledHalt} {x : Except ε (γ × Devm)}
    (hx : OnSuccess (fun a => a.2.error = e) x) :
    OnSuccess (fun d => d.error = e) (x <&> Prod.snd) := by
  cases x with
  | error _ => trivial
  | ok a => exact hx

/-- `Devm.subBal` keeps the error of its machine on success. -/
theorem Devm.subBal_onSuccess {ε : Type} (x : ε) {d : Devm} (a : Address) (v : U256)
    {e : Option SettledHalt} (h : d.error = e) :
    OnSuccess (fun d' => d'.error = e) (Option.toExcept x (d.subBal a v)) := by
  unfold Devm.subBal
  cases hs : d.state.subBal a v with
  | none => trivial
  | some st => exact h

/-- Closes `t.error = e` from an assumption about the machine `t` was built from. -/
syntax "error_close" : tactic

macro_rules
  | `(tactic| error_close) => `(tactic| (with_reducible show _ = _); first
  | with_reducible assumption
  | (simp only [Devm.withGasLeft_error, Devm.withReturnData_error, Devm.withStack_error, Devm.withMemory_error, Devm.withRefundCounter_error, Devm.withAccountsToDelete_error, Devm.withCreatedAccounts_error, Devm.withState_error, Devm.withStorageWrites_error, Devm.withTransientStorage_error, Devm.balReadAccount_error, Devm.balReadStorage_error, Devm.memWrite_error, Devm.memExtends_error, Devm.memRead_second_error, Devm.incrNonce_error, Devm.setBal_error, Devm.addBal_error, Devm.creditBeneficiary_error, addAccountToDelete_error, creditSelfdestructRefund_error, Devm.emitTransferLog_error, Devm.addLog_error', Devm.setStorVal_error', Devm.setTransVal_error', Devm.creditStateGasRefund_error, Devm.restoreChildGas_error, Devm.withholdCreateGas_second_error, Devm.drainStateGasReservoir_second_error, addAccessedAddress_error', addAccessedStorageKey_error', accessDelegation_error, GasSchedule.accessDelegation_error, ForkRules.accessDelegation_error, completeDelegationAccess_error, incorporateChildOnError_error, incorporateChildOnSuccess_error, incorporateChildAmsterdamOnError_error, incorporateChildAmsterdamOnSuccess_error, Devm.withOutput_error, Devm.setMach_error, Devm.setMeta_error, Devm.setWorld_error, apply_ite Devm.error, apply_dite Devm.error, ite_self, dite_eq_ite] <;> with_reducible assumption)
  | (split <;> error_close))

/-- The walk: through binds, branches and successful returns, closing each machine obligation
by an assumption about the machine it was built from (every setter but settlement leaves `error`
alone definitionally) or by a primitive lemma above. -/
syntax "error_step" : tactic

macro_rules
  | `(tactic| error_step) => `(tactic| first
  | with_reducible intro _
  | with_reducible exact onSuccess_error
  | with_reducible apply OnSuccess.bind_pair
  | with_reducible apply OnSuccess.bind_pair_first
  | with_reducible apply OnSuccess.bind_machine
  | with_reducible refine OnSuccess.bind_any ?_
  | with_reducible apply onSuccess_if
  | with_reducible apply onSuccess_dependent_if
  | (with_reducible refine onSuccess_ok.mpr ?_; beta_reduce)
  | (with_reducible refine onSuccess_pure.mpr ?_; beta_reduce)
  | with_reducible apply OnSuccess.map_second
  | (with_reducible apply chargeGas_onSuccess; error_close)
  | (with_reducible apply chargeStateGas_onSuccess; error_close)
  | (with_reducible apply Devm.push_onSuccess; error_close)
  | (with_reducible apply Devm.pop_onSuccess; error_close)
  | (with_reducible apply Devm.popToNat_onSuccess; error_close)
  | (with_reducible apply Devm.popToAdr_onSuccess; error_close)
  | (with_reducible apply Devm.popN_onSuccess; error_close)
  | (with_reducible apply Devm.subBal_onSuccess; error_close)
  | (with_reducible apply applyUnary_onSuccess; error_close)
  | (with_reducible apply applyBinary_onSuccess; error_close)
  | (with_reducible apply applyTernary_onSuccess; error_close)
  | (with_reducible apply pushItem_onSuccess; error_close)
  | (with_reducible apply PlainOp.balance_onSuccess; error_close)
  | (with_reducible apply liftMach_onSuccess; error_close)
  | (with_reducible apply liftMachExecution_onSuccess; error_close)
  | error_close
  | split)

/-- Repeat `error_step` on every goal. -/
macro "error_walk" : tactic => `(tactic| repeat' error_step)

/-- `JumpOp.run` keeps the error of its machine on success. -/
theorem JumpOp.run_onSuccess (evm : Evm) (j : JumpOp) :
    OnSuccess (fun a => a.2.error = evm.dyna.error) (j.run evm) := by
  have h0 : evm.dyna.error = evm.dyna.error := rfl
  unfold JumpOp.run JumpOp.runCore
  cases j <;> error_walk

/-- `HaltOp.run` keeps the error of its machine on success. -/
theorem HaltOp.run_onSuccess (sevm : Sevm) (devm : Devm) (l : HaltOp) :
    OnSuccess (fun d => d.error = devm.error) (l.run sevm devm) := by
  have h0 : devm.error = devm.error := rfl
  unfold HaltOp.run
  cases l
  case stop | revert | return_ => error_walk
  case selfdestruct => error_walk

/-- `ADD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_add (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .add) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MUL` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mul (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mul) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SUB` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_sub (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sub) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `DIV` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_div (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .div) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SDIV` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_sdiv (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sdiv) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MOD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mod (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mod) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SMOD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_smod (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .smod) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `ADDMOD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_addmod (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .addmod) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MULMOD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mulmod (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mulmod) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `EXP` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_exp (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .exp) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SIGNEXTEND` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_signextend (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .signextend) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `LT` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_lt (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .lt) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `GT` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_gt (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .gt) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SLT` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_slt (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .slt) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SGT` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_sgt (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sgt) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `EQ` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_eq (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .eq) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `ISZERO` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_iszero (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .iszero) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `AND` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_and (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .and) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `OR` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_or (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .or) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `XOR` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_xor (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .xor) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `NOT` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_not (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .not) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `BYTE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_byte (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .byte) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SHL` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_shl (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .shl) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SHR` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_shr (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .shr) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SAR` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_sar (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sar) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CLZ` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_clz (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .clz) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `KECCAK256` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_keccak256 (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .keccak256) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `ADDRESS` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_address (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .address) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `BALANCE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_balance (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .balance) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `ORIGIN` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_origin (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .origin) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CALLER` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_caller (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .caller) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CALLVALUE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_callvalue (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .callvalue) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CALLDATALOAD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_calldataload (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .calldataload) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CALLDATASIZE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_calldatasize (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .calldatasize) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CALLDATACOPY` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_calldatacopy (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .calldatacopy) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CODESIZE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_codesize (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .codesize) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CODECOPY` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_codecopy (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .codecopy) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `GASPRICE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_gasprice (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .gasprice) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `EXTCODESIZE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_extcodesize (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .extcodesize) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `EXTCODECOPY` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_extcodecopy (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .extcodecopy) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `RETURNDATASIZE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_returndatasize (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .returndatasize) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `RETURNDATACOPY` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_returndatacopy (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .returndatacopy) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `EXTCODEHASH` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_extcodehash (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .extcodehash) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `BLOCKHASH` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_blockhash (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .blockhash) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `COINBASE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_coinbase (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .coinbase) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `TIMESTAMP` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_timestamp (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .timestamp) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `NUMBER` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_number (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .number) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `PREVRANDAO` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_prevrandao (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .prevrandao) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `GASLIMIT` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_gaslimit (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .gaslimit) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `CHAINID` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_chainid (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .chainid) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SELFBALANCE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_selfbalance (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .selfbalance) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `BASEFEE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_basefee (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .basefee) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `BLOBHASH` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_blobhash (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .blobhash) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `BLOBBASEFEE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_blobbasefee (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .blobbasefee) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SLOTNUM` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_slotnum (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .slotnum) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `POP` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_pop (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .pop) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MLOAD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mload (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mload) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MSTORE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mstore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mstore) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MSTORE8` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mstore8 (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mstore8) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SLOAD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_sload (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sload) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SSTORE` keeps the stored error on success under rules without state gas. -/
theorem PlainOp.runCore_onSuccess_sstore_none (pc : Nat) (devm : Devm) (sevm : Sevm)
    (h : sevm.benvStat.rules.stateGas = none) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sstore) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore, h]; error_walk

/-- `SSTORE` keeps the stored error on success under rules with state gas. -/
theorem PlainOp.runCore_onSuccess_sstore_some (pc : Nat) (devm : Devm) (sevm : Sevm)
    (s : StateGasRules) (h : sevm.benvStat.rules.stateGas = some s) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sstore) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore, h]
  refine OnSuccess.bind_any (fun _ => ?_)
  refine OnSuccess.bind_pair (Devm.pop_onSuccess h0) (fun a ha => ?_)
  refine OnSuccess.bind_pair (Devm.pop_onSuccess ha) (fun b hb => ?_)
  refine OnSuccess.bind_any (fun _ => ?_)
  refine OnSuccess.bind_machine (e := devm.error) (chargeGas_onSuccess _ ?_) (fun c hc => ?_)
  · error_close
  refine OnSuccess.bind_machine (chargeStateGas_onSuccess _ hc) (fun d hd => ?_)
  exact onSuccess_ok.mpr (by error_close)

/-- `SSTORE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_sstore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .sstore) := by
  cases h : sevm.benvStat.rules.stateGas with
  | none => exact PlainOp.runCore_onSuccess_sstore_none pc devm sevm h
  | some s => exact PlainOp.runCore_onSuccess_sstore_some pc devm sevm s h

/-- `TLOAD` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_tload (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .tload) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `TSTORE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_tstore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .tstore) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MCOPY` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_mcopy (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .mcopy) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `PC` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_pc (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .pc) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `MSIZE` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_msize (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .msize) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `GAS` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_gas (pc : Nat) (devm : Devm) (sevm : Sevm) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm .gas) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `DUP` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_dup (pc : Nat) (devm : Devm) (sevm : Sevm) (n) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm (.dup n)) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `SWAP` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_swap (pc : Nat) (devm : Devm) (sevm : Sevm) (n) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm (.swap n)) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `LOG` keeps the stored error on success. -/
theorem PlainOp.runCore_onSuccess_log (pc : Nat) (devm : Devm) (sevm : Sevm) (n) :
    OnSuccess (fun d => d.error = devm.error) (PlainOp.runCore pc devm sevm (.log n)) := by
  have h0 : devm.error = devm.error := rfl
  simp only [PlainOp.runCore]; error_walk

/-- `PlainOp.run` keeps the error of its machine on success. -/
theorem PlainOp.run_onSuccess (evm : Evm) (r : PlainOp) :
    OnSuccess (fun d => d.error = evm.dyna.error) (r.run evm) := by
  unfold PlainOp.run
  cases r with
  | add => exact PlainOp.runCore_onSuccess_add _ _ _
  | mul => exact PlainOp.runCore_onSuccess_mul _ _ _
  | sub => exact PlainOp.runCore_onSuccess_sub _ _ _
  | div => exact PlainOp.runCore_onSuccess_div _ _ _
  | sdiv => exact PlainOp.runCore_onSuccess_sdiv _ _ _
  | mod => exact PlainOp.runCore_onSuccess_mod _ _ _
  | smod => exact PlainOp.runCore_onSuccess_smod _ _ _
  | addmod => exact PlainOp.runCore_onSuccess_addmod _ _ _
  | mulmod => exact PlainOp.runCore_onSuccess_mulmod _ _ _
  | exp => exact PlainOp.runCore_onSuccess_exp _ _ _
  | signextend => exact PlainOp.runCore_onSuccess_signextend _ _ _
  | lt => exact PlainOp.runCore_onSuccess_lt _ _ _
  | gt => exact PlainOp.runCore_onSuccess_gt _ _ _
  | slt => exact PlainOp.runCore_onSuccess_slt _ _ _
  | sgt => exact PlainOp.runCore_onSuccess_sgt _ _ _
  | eq => exact PlainOp.runCore_onSuccess_eq _ _ _
  | iszero => exact PlainOp.runCore_onSuccess_iszero _ _ _
  | and => exact PlainOp.runCore_onSuccess_and _ _ _
  | or => exact PlainOp.runCore_onSuccess_or _ _ _
  | xor => exact PlainOp.runCore_onSuccess_xor _ _ _
  | not => exact PlainOp.runCore_onSuccess_not _ _ _
  | byte => exact PlainOp.runCore_onSuccess_byte _ _ _
  | shl => exact PlainOp.runCore_onSuccess_shl _ _ _
  | shr => exact PlainOp.runCore_onSuccess_shr _ _ _
  | sar => exact PlainOp.runCore_onSuccess_sar _ _ _
  | clz => exact PlainOp.runCore_onSuccess_clz _ _ _
  | keccak256 => exact PlainOp.runCore_onSuccess_keccak256 _ _ _
  | address => exact PlainOp.runCore_onSuccess_address _ _ _
  | balance => exact PlainOp.runCore_onSuccess_balance _ _ _
  | origin => exact PlainOp.runCore_onSuccess_origin _ _ _
  | caller => exact PlainOp.runCore_onSuccess_caller _ _ _
  | callvalue => exact PlainOp.runCore_onSuccess_callvalue _ _ _
  | calldataload => exact PlainOp.runCore_onSuccess_calldataload _ _ _
  | calldatasize => exact PlainOp.runCore_onSuccess_calldatasize _ _ _
  | calldatacopy => exact PlainOp.runCore_onSuccess_calldatacopy _ _ _
  | codesize => exact PlainOp.runCore_onSuccess_codesize _ _ _
  | codecopy => exact PlainOp.runCore_onSuccess_codecopy _ _ _
  | gasprice => exact PlainOp.runCore_onSuccess_gasprice _ _ _
  | extcodesize => exact PlainOp.runCore_onSuccess_extcodesize _ _ _
  | extcodecopy => exact PlainOp.runCore_onSuccess_extcodecopy _ _ _
  | returndatasize => exact PlainOp.runCore_onSuccess_returndatasize _ _ _
  | returndatacopy => exact PlainOp.runCore_onSuccess_returndatacopy _ _ _
  | extcodehash => exact PlainOp.runCore_onSuccess_extcodehash _ _ _
  | blockhash => exact PlainOp.runCore_onSuccess_blockhash _ _ _
  | coinbase => exact PlainOp.runCore_onSuccess_coinbase _ _ _
  | timestamp => exact PlainOp.runCore_onSuccess_timestamp _ _ _
  | number => exact PlainOp.runCore_onSuccess_number _ _ _
  | prevrandao => exact PlainOp.runCore_onSuccess_prevrandao _ _ _
  | gaslimit => exact PlainOp.runCore_onSuccess_gaslimit _ _ _
  | chainid => exact PlainOp.runCore_onSuccess_chainid _ _ _
  | selfbalance => exact PlainOp.runCore_onSuccess_selfbalance _ _ _
  | basefee => exact PlainOp.runCore_onSuccess_basefee _ _ _
  | blobhash => exact PlainOp.runCore_onSuccess_blobhash _ _ _
  | blobbasefee => exact PlainOp.runCore_onSuccess_blobbasefee _ _ _
  | slotnum => exact PlainOp.runCore_onSuccess_slotnum _ _ _
  | pop => exact PlainOp.runCore_onSuccess_pop _ _ _
  | mload => exact PlainOp.runCore_onSuccess_mload _ _ _
  | mstore => exact PlainOp.runCore_onSuccess_mstore _ _ _
  | mstore8 => exact PlainOp.runCore_onSuccess_mstore8 _ _ _
  | sload => exact PlainOp.runCore_onSuccess_sload _ _ _
  | sstore => exact PlainOp.runCore_onSuccess_sstore _ _ _
  | tload => exact PlainOp.runCore_onSuccess_tload _ _ _
  | tstore => exact PlainOp.runCore_onSuccess_tstore _ _ _
  | mcopy => exact PlainOp.runCore_onSuccess_mcopy _ _ _
  | pc => exact PlainOp.runCore_onSuccess_pc _ _ _
  | msize => exact PlainOp.runCore_onSuccess_msize _ _ _
  | gas => exact PlainOp.runCore_onSuccess_gas _ _ _
  | dup n => exact PlainOp.runCore_onSuccess_dup _ _ _ n
  | swap n => exact PlainOp.runCore_onSuccess_swap _ _ _ n
  | log n => exact PlainOp.runCore_onSuccess_log _ _ _ n

/-! ### Message opcodes and their tails -/

/-- A message opcode's result keeps the error `e`: a result in place keeps it on success, and a
spawn's saved caller keeps it. -/
def MessageOpKeepsError (e : Option SettledHalt) : XStep → Prop
  | .done ex => OnSuccess (fun d => d.error = e) ex
  | .spawn _ rsm => rsm.parent.error = e

/-- `MessageOpKeepsError` for `ofExcept`. -/
theorem messageOpKeepsError_ofExcept {e : Option SettledHalt} {x : Except (EvmError × Devm) XStep}
    (h : OnSuccess (MessageOpKeepsError e) x) : MessageOpKeepsError e (XStep.ofExcept x) := by
  cases x with
  | error _ => trivial
  | ok s => exact h

/-- `MessageOpKeepsError` for `done_ok`. -/
theorem messageOpKeepsError_done_ok {e : Option SettledHalt} {d : Devm} (h : d.error = e) :
    MessageOpKeepsError e (.done (.ok d)) := h

/-- `messageOpKeepsError_done` leaves `error` alone. -/
theorem messageOpKeepsError_done_error {e : Option SettledHalt} {x : EvmError × Devm} :
    MessageOpKeepsError e (.done (.error x)) := trivial

/-- `MessageOpKeepsError` for `spawn_create`. -/
theorem messageOpKeepsError_spawn_create {e : Option SettledHalt} {f : Frame} {p : Devm}
    {a : Address} (h : p.error = e) : MessageOpKeepsError e (.spawn f (.create p a)) := h

/-- `MessageOpKeepsError` for `spawn_call`. -/
theorem messageOpKeepsError_spawn_call {e : Option SettledHalt} {f : Frame} {p : Devm}
    {i n : Nat} (h : p.error = e) : MessageOpKeepsError e (.spawn f (.call p i n)) := h

/-- `MessageOpKeepsError` for `spawn_createAmsterdam`. -/
theorem messageOpKeepsError_spawn_createAmsterdam {e : Option SettledHalt} {f : Frame}
    {s : StateGasRules} {p : Devm} {a : Address} {c : Bool} (h : p.error = e) :
    MessageOpKeepsError e (.spawn f (.createAmsterdam s p a c)) := h

/-- `MessageOpKeepsError` for `spawn_callAmsterdam`. -/
theorem messageOpKeepsError_spawn_callAmsterdam {e : Option SettledHalt} {f : Frame}
    {s : StateGasRules} {p : Devm} {i n : Nat} {c : Bool} (h : p.error = e) :
    MessageOpKeepsError e (.spawn f (.callAmsterdam s p i n c)) := h

macro_rules
  | `(tactic| error_step) => `(tactic| first
  | with_reducible apply messageOpKeepsError_ofExcept
  | with_reducible exact messageOpKeepsError_done_error
  | with_reducible apply messageOpKeepsError_done_ok
  | with_reducible apply messageOpKeepsError_spawn_create
  | with_reducible apply messageOpKeepsError_spawn_call
  | with_reducible apply messageOpKeepsError_spawn_createAmsterdam
  | with_reducible apply messageOpKeepsError_spawn_callAmsterdam)

/-- `genericCreate.step` keeps the stored error of the machine it starts from. -/
theorem genericCreate.step_keepsError (sevm : Sevm) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) :
    MessageOpKeepsError devm.error
      (genericCreate.step sevm devm endowment newAddress memoryIndex memorySize) := by
  have h0 : devm.error = devm.error := rfl
  unfold genericCreate.step
  error_walk

/-- `genericCall.step` keeps the stored error of the machine it starts from. -/
theorem genericCall.step_keepsError (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles : Bool) :
    MessageOpKeepsError devm.error
      (genericCall.step sevm devm gas value caller target codeAddress shouldTransferValue
        isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles) := by
  have h0 : devm.error = devm.error := rfl
  unfold genericCall.step
  error_walk

/-- `genericCallAmsterdam.step` keeps the stored error of the machine it starts from. -/
theorem genericCallAmsterdam.step_keepsError (sevm : Sevm) (state : StateGasRules)
    (devm : Devm) (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) :
    MessageOpKeepsError devm.error
      (genericCallAmsterdam.step sevm state devm gas reservoir value caller target codeAddress
        shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
        disablePrecompiles newAccountCharged insufficientBalance) := by
  have h0 : devm.error = devm.error := rfl
  unfold genericCallAmsterdam.step
  error_walk

/-- `genericCreateAmsterdam.step` keeps the stored error of the machine it starts from. -/
theorem genericCreateAmsterdam.step_keepsError (sevm : Sevm) (state : StateGasRules)
    (devm : Devm) (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat) :
    MessageOpKeepsError devm.error
      (genericCreateAmsterdam.step sevm state devm endowment newAddress memoryIndex
        memorySize) := by
  have h0 : devm.error = devm.error := rfl
  unfold genericCreateAmsterdam.step
  error_walk

/-- A tail started on a machine that keeps `e` keeps `e`. -/
theorem MessageOpKeepsError.congr {e : Option SettledHalt} {d : Devm} {s : XStep}
    (hs : MessageOpKeepsError d.error s) (h : d.error = e) : MessageOpKeepsError e s := h ▸ hs

macro_rules
  | `(tactic| error_step) => `(tactic| first
  | (with_reducible refine MessageOpKeepsError.congr (genericCreate.step_keepsError ..) ?_; error_close)
  | (with_reducible refine MessageOpKeepsError.congr (genericCall.step_keepsError ..) ?_; error_close)
  | (with_reducible refine MessageOpKeepsError.congr (genericCallAmsterdam.step_keepsError ..) ?_; error_close)
  | (with_reducible refine MessageOpKeepsError.congr (genericCreateAmsterdam.step_keepsError ..) ?_; error_close))

/-- Every message opcode keeps the error, in each rule shape. -/
theorem MessageOp.step_keepsError_create_none (sevm : Sevm) (devm : Devm)
    (h : sevm.benvStat.rules.stateGas = none) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .create) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CREATE` keeps the stored error, under rules with state gas. -/
theorem MessageOp.step_keepsError_create_some (sevm : Sevm) (devm : Devm) (s : StateGasRules)
    (h : sevm.benvStat.rules.stateGas = some s) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .create) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CREATE2` keeps the stored error, under rules without state gas. -/
theorem MessageOp.step_keepsError_create2_none (sevm : Sevm) (devm : Devm)
    (h : sevm.benvStat.rules.stateGas = none) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .create2) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CREATE2` keeps the stored error, under rules with state gas. -/
theorem MessageOp.step_keepsError_create2_some (sevm : Sevm) (devm : Devm) (s : StateGasRules)
    (h : sevm.benvStat.rules.stateGas = some s) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .create2) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CALL` keeps the stored error, under rules without state gas. -/
theorem MessageOp.step_keepsError_call_none (sevm : Sevm) (devm : Devm)
    (h : sevm.benvStat.rules.stateGas = none) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .call) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CALL` keeps the stored error, under rules with state gas. -/
theorem MessageOp.step_keepsError_call_some (sevm : Sevm) (devm : Devm) (s : StateGasRules)
    (h : sevm.benvStat.rules.stateGas = some s) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .call) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CALLCODE` keeps the stored error, under rules without state gas. -/
theorem MessageOp.step_keepsError_callcode_none (sevm : Sevm) (devm : Devm)
    (h : sevm.benvStat.rules.stateGas = none) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .callcode) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `CALLCODE` keeps the stored error, under rules with state gas. -/
theorem MessageOp.step_keepsError_callcode_some (sevm : Sevm) (devm : Devm) (s : StateGasRules)
    (h : sevm.benvStat.rules.stateGas = some s) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .callcode) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `DELEGATECALL` keeps the stored error, under rules without state gas. -/
theorem MessageOp.step_keepsError_delegatecall_none (sevm : Sevm) (devm : Devm)
    (h : sevm.benvStat.rules.stateGas = none) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .delegatecall) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `DELEGATECALL` keeps the stored error, under rules with state gas. -/
theorem MessageOp.step_keepsError_delegatecall_some (sevm : Sevm) (devm : Devm) (s : StateGasRules)
    (h : sevm.benvStat.rules.stateGas = some s) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .delegatecall) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `STATICCALL` keeps the stored error, under rules without state gas. -/
theorem MessageOp.step_keepsError_staticcall_none (sevm : Sevm) (devm : Devm)
    (h : sevm.benvStat.rules.stateGas = none) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .staticcall) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `STATICCALL` keeps the stored error, under rules with state gas. -/
theorem MessageOp.step_keepsError_staticcall_some (sevm : Sevm) (devm : Devm) (s : StateGasRules)
    (h : sevm.benvStat.rules.stateGas = some s) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm .staticcall) := by
  have h0 : devm.error = devm.error := rfl
  simp only [MessageOp.step, h]; error_walk

/-- `MessageOp.step` keeps the stored error of the machine it starts from. -/
theorem MessageOp.step_keepsError (sevm : Sevm) (devm : Devm) (x : MessageOp) :
    MessageOpKeepsError devm.error (MessageOp.step sevm devm x) := by
  cases x with
  | create =>
    cases h : sevm.benvStat.rules.stateGas with
    | none => exact MessageOp.step_keepsError_create_none sevm devm h
    | some s => exact MessageOp.step_keepsError_create_some sevm devm s h
  | create2 =>
    cases h : sevm.benvStat.rules.stateGas with
    | none => exact MessageOp.step_keepsError_create2_none sevm devm h
    | some s => exact MessageOp.step_keepsError_create2_some sevm devm s h
  | call =>
    cases h : sevm.benvStat.rules.stateGas with
    | none => exact MessageOp.step_keepsError_call_none sevm devm h
    | some s => exact MessageOp.step_keepsError_call_some sevm devm s h
  | callcode =>
    cases h : sevm.benvStat.rules.stateGas with
    | none => exact MessageOp.step_keepsError_callcode_none sevm devm h
    | some s => exact MessageOp.step_keepsError_callcode_some sevm devm s h
  | delegatecall =>
    cases h : sevm.benvStat.rules.stateGas with
    | none => exact MessageOp.step_keepsError_delegatecall_none sevm devm h
    | some s => exact MessageOp.step_keepsError_delegatecall_some sevm devm s h
  | staticcall =>
    cases h : sevm.benvStat.rules.stateGas with
    | none => exact MessageOp.step_keepsError_staticcall_none sevm devm h
    | some s => exact MessageOp.step_keepsError_staticcall_some sevm devm s h

/-! ### One step -/

/-- A step keeps the error `e`: a continuing or finished machine keeps it, and a spawn's saved
caller keeps it. -/
def StepKeepsError (e : Option SettledHalt) : Step → Prop
  | .halt ex => OnSuccess (fun d => d.error = e) ex
  | .cont _ d => d.error = e
  | .spawn _ rsm _ => rsm.parent.error = e

/-- `StepKeepsError` through `ofExecution`. -/
theorem stepKeepsError_ofExecution {e : Option SettledHalt} (pc : Nat) {x : Execution}
    (h : OnSuccess (fun d => d.error = e) x) : StepKeepsError e (Step.ofExecution pc x) := by
  cases x with
  | error _ => trivial
  | ok d => exact h

/-- `StepKeepsError` through `ofJump`. -/
theorem stepKeepsError_ofJump {e : Option SettledHalt}
    {x : Except (EvmError × Devm) (Nat × Devm)} (h : OnSuccess (fun a => a.2.error = e) x) :
    StepKeepsError e (Step.ofJump x) := by
  cases x with
  | error _ => trivial
  | ok a => exact h

/-- `StepKeepsError` through `toStep`. -/
theorem stepKeepsError_toStep {e : Option SettledHalt} (pc : Nat) {s : XStep}
    (h : MessageOpKeepsError e s) : StepKeepsError e (s.toStep pc) := by
  cases s with
  | done ex => exact stepKeepsError_ofExecution pc h
  | spawn f rsm => exact h

/-- `NextOp.step` keeps the stored error of the machine it starts from. -/
theorem NextOp.step_keepsError (evm : Evm) (n : NextOp) :
    StepKeepsError evm.dyna.error (NextOp.step evm n) := by
  have h0 : evm.dyna.error = evm.dyna.error := rfl
  cases n with
  | plain r => exact stepKeepsError_ofExecution _ (PlainOp.run_onSuccess evm r)
  | message x => exact stepKeepsError_toStep _ (MessageOp.step_keepsError evm.sta evm.dyna x)
  | push xs prf =>
    simp only [NextOp.step]
    split
    · exact stepKeepsError_ofExecution _ trivial
    · exact stepKeepsError_ofExecution _ (by error_walk)
  | dupn imm => exact stepKeepsError_ofExecution _ (by error_walk)
  | swapn imm => exact stepKeepsError_ofExecution _ (by error_walk)
  | exchange imm => exact stepKeepsError_ofExecution _ (by error_walk)

/-- `Evm.step` keeps the stored error of the machine it starts from. -/
theorem Evm.step_keepsError (evm : Evm) : StepKeepsError evm.dyna.error evm.step := by
  unfold Evm.step
  split
  · trivial
  · exact NextOp.step_keepsError evm _
  · exact stepKeepsError_ofJump (JumpOp.run_onSuccess evm _)
  · exact HaltOp.run_onSuccess evm.sta evm.dyna _

/-- **F0, one step.** A step keeps the stored error of the machine it starts from: in a
continuing or finished machine, and in the saved caller of a spawn. -/
theorem Evm.step_error (evm : Evm) :
    match Evm.step evm with
    | .cont _ d => d.error = evm.dyna.error
    | .halt (.ok d) => d.error = evm.dyna.error
    | .halt (.error _) => True
    | .spawn _ rsm _ => rsm.parent.error = evm.dyna.error := by
  have h := Evm.step_keepsError evm
  revert h
  rcases evm.step with (_ | _) | ⟨_, _⟩ | ⟨_, _, _⟩ <;> exact id

/-! ### Resume -/

/-- **F0, resume.** Resuming the saved caller keeps the caller's stored error, whatever the
child's settled result. -/
theorem Resume.run_ok_error {rsm : Resume}
    {r : Except (EvmError × State × AdrSet × TransientStorage) Devm} {d : Devm}
    (h : rsm.run r = .ok d) : d.error = rsm.parent.error := by
  have hk : OnSuccess (fun d => d.error = rsm.parent.error) (rsm.run r) := by
    cases rsm with
    | create parent a =>
      have h0 : parent.error = parent.error := rfl
      simp only [Resume.parent]
      unfold Resume.run
      refine OnSuccess.bind_any (fun child => ?_)
      error_walk
    | call parent i n =>
      have h0 : parent.error = parent.error := rfl
      simp only [Resume.parent]
      unfold Resume.run
      refine OnSuccess.bind_any (fun child => ?_)
      try dsimp only
      error_walk
    | createAmsterdam st parent a c =>
      have h0 : parent.error = parent.error := rfl
      simp only [Resume.parent]
      unfold Resume.run
      refine OnSuccess.bind_any (fun child => ?_)
      try dsimp only
      error_walk
    | callAmsterdam st parent i n c =>
      have h0 : parent.error = parent.error := rfl
      simp only [Resume.parent]
      unfold Resume.run
      refine OnSuccess.bind_any (fun child => ?_)
      try dsimp only
      error_walk
  rw [h] at hk
  exact hk

/-! ### Entry -/

/-- **F0, entry.** A frame's initial machine stores no error. -/
theorem initDevm_error (msg : Msg) : (initDevm msg).error = none := rfl

/-- **F0, precompiles.** A precompile sets only gas and output. -/
theorem executePrecompile_ok_error {evm : Evm} {a : Address} {d : Devm}
    (h : executePrecompile evm a = .ok d) : d.error = evm.dyna.error := by
  unfold executePrecompile applyPrecompileResult at h
  split at h
  · cases h
  · cases h; rfl

/-! ### The driver -/

/-- **F0, the driver.** A run that finishes successfully keeps the stored error of the machine
it started from. Children are entered, run and settled in between; their results never reach the
parent's `error`, because `Resume.run` keeps the saved caller's. -/
theorem execFueled_ok_error :
    ∀ (fuel : Nat) (evm : Evm) {d : Devm},
      (execFueled evm fuel).run = some (.ok d) → d.error = evm.dyna.error := by
  intro fuel
  induction fuel with
  | zero =>
    intro evm d hrun
    rw [execFueled] at hrun
    simp only [Fueled.exhausted_run] at hrun
    nomatch hrun
  | succ fuel ih =>
    intro evm d hrun
    have hstep := Evm.step_keepsError evm
    rw [execFueled] at hrun
    rcases hs : evm.step with ex | ⟨pc, devm⟩ | ⟨frame, rsm, pc⟩ <;>
      rw [hs] at hrun hstep <;> dsimp only at hrun
    · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
      subst hrun
      exact hstep
    · exact (ih ⟨pc, evm.sta, devm⟩ hrun).trans hstep
    · rcases he : frame.enter with r | child <;> rw [he] at hrun <;> dsimp only at hrun
      · rcases hr : rsm.run r with e | d' <;> rw [hr] at hrun <;> dsimp only at hrun
        · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
          nomatch hrun
        · exact ((ih ⟨pc, evm.sta, d'⟩ hrun).trans (Resume.run_ok_error hr)).trans hstep
      · rcases hc : (execFueled child fuel).run with _ | raw
        · rw [hc] at hrun
          simp only [Fueled.exhausted_run] at hrun
          nomatch hrun
        · rw [hc] at hrun
          dsimp only at hrun
          rcases hr : rsm.run (frame.settle raw) with e | d' <;> rw [hr] at hrun <;>
            dsimp only at hrun
          · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
            nomatch hrun
          · exact ((ih ⟨pc, evm.sta, d'⟩ hrun).trans (Resume.run_ok_error hr)).trans hstep

/-- **F0, the total interpreter.** A frame entered with no stored error yields a clean raw
result: `exec` never returns `.ok d` with `d.error` set. -/
theorem exec_clean {evm : Evm} (h : evm.dyna.error = none) : Execution.Clean (exec evm) := by
  unfold exec
  split
  · next r hr =>
    cases r with
    | error _ => trivial
    | ok d => exact (execFueled_ok_error _ evm hr).trans h
  · trivial

end Legacy

end Jaune
