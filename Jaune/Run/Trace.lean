import Jaune.Bridge.G2a.Old.Trace
import Jaune.TraceTransaction
import Jaune.Bridge.G2a.Consumers

/-!
# Tracing the message run and the transaction (goal `jaune-shape-and-names-v1`, W2 cut B2)

The tracer's transaction driver over the staged phases: it prepares the transaction, traces the
top-level message run and settles the run, and hands the trace summary the `MessageRun` instead of
a rendered output record. Each traced operation carries a certificate that its value is the public
operation: `runMessage` is `Message.run`, `runTransaction` is the state and block output of the
transaction run `B2.Transaction.run` (the production pipeline), which
`Jaune.Bridge.G2a.processTransaction_eq_b2` and `B2.Transaction.run_output` equate with today's.

The traced message run enters the prepared frame from its checkpoint exactly once, with the entry
and settlement events `Trace.runFrame` emits, so a precompile or the interpreter never runs twice;
it records the machine the frame entered the interpreter with, as `Message.run` does. Without state
gas a call reports its authorization refund before the frame is entered, as before.

Staged under `Jaune.Staging.TraceTransaction`; it supersedes `Jaune.TraceTransaction`'s message
and transaction drivers at the switch. Like that module it sits outside `Jaune.lean`'s import
closure.
-/

namespace Jaune.Staging.TraceTransaction

open Jaune Jaune.Staging
open Jaune.TraceTransaction (Certified)

/-- Trace a top-level message run. A preparation fault or a refusal returns without a frame. A
frame is entered from its checkpoint and traced as `Trace.runFrame` traces it; without state gas a
call first reports its authorization refund. -/
def runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) :
    m (Certified (Message.run msg)) := do
  match hprep : TopLevel.prepare msg with
  | .error e =>
    pure ⟨.error e, by simp only [Message.run, hprep]; rfl⟩
  | .ok (.refused reason halted) =>
    pure ⟨.ok ⟨msg, .refused reason halted, none, none⟩, by simp only [Message.run, hprep]; rfl⟩
  | .ok (.frame f a) =>
    if msg.benv.stat.rules.stateGas.isNone && msg.target.isSome then
      authorizationRefund a
    let context : Trace.Context := ⟨runId, 0, 1⟩
    match hentry : enterWith f f.checkpoint.toDevm with
    | .done settled =>
      sink (.entered context f (.done settled))
      sink (.settled context f settled)
      pure ⟨(do let r ← settled; pure ⟨msg, .frame f a, none, some r⟩), by
        simp only [Message.run, hprep, bind, Except.bind, hentry]⟩
    | .run evm =>
      sink (.entered context f (.run evm))
      let result ← Trace.exec sink evm context 1
      let settled := settle f result.value
      sink (.settled context f settled)
      pure ⟨(do let r ← settled; pure ⟨msg, .frame f a, some evm, some r⟩), by
        simp only [Message.run, hprep, bind, Except.bind, hentry, settled, result.erases]⟩

/-- The traced message run's value is `Message.run`. -/
theorem runMessage_erasure {msg : Msg} (result : Certified (Message.run msg)) :
    result.value = Message.run msg := result.erases

/-- A transaction's check and preparation. -/
def prepareTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError Transaction.Prepared := do
  let checked ← Transaction.check benv bout tx index
  Transaction.prepare checked tx index

/-- The transaction result and the message run the trace summary reads: none when the
transaction was rejected before its message ran or the run faulted. -/
structure TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat)
    extends Certified ((fun pair => (pair.1.state, pair.2)) <$> B2.Transaction.run benv bout tx index) where
  messageRun : Option MessageRun
  /-- The observed run is the transaction's top-level message run. -/
  observes : messageRun =
    ((prepareTransaction benv bout tx index).toOption.bind
      fun prepared => (Message.run prepared.msg).toOption)

/-- Execute one transaction with synchronous instruction observations: check and prepare it,
trace its message run, settle the run. The certificate connects the value to the public pipeline;
the message run is never run a second time. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) (runId : String) : m (TransactionResult benv bout tx index) := do
  match hprep : prepareTransaction benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageRun := none
      erases := by
        rw [B2.Transaction.run_output]
        simp only [prepareTransaction] at hprep
        simp only [B2.processTransaction]
        revert hprep
        cases Transaction.check benv bout tx index with
        | error e => intro h; cases h; rfl
        | ok checked =>
          simp only [bind, Except.bind]
          intro h
          rw [h]
      observes := by rw [hprep]; rfl }
  | .ok prepared =>
    let message ← runMessage sink authorizationRefund prepared.msg runId
    let value : Except TransitionError (State × BlockOutput) := do
      let run ← message.value.mapError (fun e => TransitionError.vm e.toEvmError)
      B2.Transaction.settle prepared tx index run
    let observed := match message.value with
      | .error _ => none
      | .ok run => some run
    pure {
      value := value
      messageRun := observed
      erases := by
        rw [B2.Transaction.run_output]
        simp only [prepareTransaction] at hprep
        simp only [B2.processTransaction, value, message.erases]
        revert hprep
        cases Transaction.check benv bout tx index with
        | error e => intro h; cases h
        | ok checked =>
          simp only [bind, Except.bind]
          intro h
          rw [h]
      observes := by
        rw [hprep]
        simp only [observed, message.erases, Except.toOption, Option.bind]
        cases Message.run prepared.msg <;> rfl }

/-- The traced transaction's value is the transaction run's state and block output. -/
theorem runTransaction_erasure {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} (result : TransactionResult benv bout tx index) :
    result.value = (fun pair => (pair.1.state, pair.2)) <$> B2.Transaction.run benv bout tx index :=
  result.erases

/-- **Bridge at the traced transaction's value.** For every monad, sink and input, the value the
staged traced transaction returns is today's `processTransaction` result, and so the value
`Jaune.TraceTransaction.runTransaction` returns. -/
theorem runTransaction_value_eq {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} (result : TransactionResult benv bout tx index)
    (old : Jaune.TraceTransaction.TransactionResult benv bout tx index) :
    result.value = old.value := by
  rw [result.erases, B2.Transaction.run_output, old.erases, Bridge.G2a.processTransaction_eq_b2]

end Jaune.Staging.TraceTransaction
