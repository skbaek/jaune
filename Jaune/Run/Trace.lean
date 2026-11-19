import Jaune.TraceTransaction
import Jaune.Run.Settle

/-!
# Tracing the message run and the transaction (goal `jaune-shape-and-names-v1`, W2 cut B2)

The tracer's transaction driver over the staged phases: it prepares the transaction, traces the
top-level message run and settles the run, and hands the trace summary the `MessageRun` instead of
a rendered output record. Each traced operation carries a certificate that its value is the public
operation: `runMessage` is `Message.run`, `runTransaction` is the state and block output of the
transaction run `B2.Transaction.run` (the production pipeline). The transaction is settled by
`B2.Transaction.settleRun`, the settlement of that run, so the value is computed by the run itself.

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
trace its message run, settle the run as `B2.Transaction.run` settles it. The certificate connects
the value to the public pipeline; the message run is never run a second time. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) (runId : String) : m (TransactionResult benv bout tx index) := do
  match hcheck : Transaction.check benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageRun := none
      erases := by simp only [B2.Transaction.run, hcheck, bind, Except.bind]; rfl
      observes := by simp only [prepareTransaction, hcheck, bind, Except.bind]; rfl }
  | .ok checked =>
    match hprep : Transaction.prepare checked tx index with
    | .error error =>
      pure {
        value := .error error
        messageRun := none
        erases := by simp only [B2.Transaction.run, hcheck, hprep, bind, Except.bind]; rfl
        observes := by simp only [prepareTransaction, hcheck, hprep, bind, Except.bind]; rfl }
    | .ok prepared =>
      let message ← runMessage sink authorizationRefund prepared.msg runId
      let value : Except TransitionError (State × BlockOutput) := do
        let run ← message.value.mapError (fun e => TransitionError.vm e.toEvmError)
        (fun pair => (pair.1.state, pair.2)) <$>
          B2.Transaction.settleRun checked prepared tx index run
      let observed := match message.value with
        | .error _ => none
        | .ok run => some run
      pure {
        value := value
        messageRun := observed
        erases := by
          simp only [value, message.erases, B2.Transaction.run, hcheck, hprep, bind, Except.bind]
          cases Except.mapError (fun e => TransitionError.vm e.toEvmError) (Message.run prepared.msg) <;>
            rfl
        observes := by
          simp only [prepareTransaction, hcheck, hprep, bind, Except.bind, observed, message.erases,
            Except.toOption, Option.bind]
          cases Message.run prepared.msg <;> rfl }

/-- The traced transaction's value is the transaction run's state and block output. -/
theorem runTransaction_erasure {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} (result : TransactionResult benv bout tx index) :
    result.value = (fun pair => (pair.1.state, pair.2)) <$> B2.Transaction.run benv bout tx index :=
  result.erases

end Jaune.Staging.TraceTransaction
