import Jaune.TraceTransaction
import Jaune.Run.Settle

/-!
# Tracing message and transaction runs

`TraceTransaction.runMessage` returns a certified observation of
`TopLevel.run`. It records the prepared frame's entry and settlement events
with `Trace.runFrame`, runs the frame at most once, and retains the machine
that entered the interpreter. Without state gas, a call reports its
authorization refund before frame entry.

`TraceTransaction.runTransaction` prepares the transaction, traces its
top-level message, and settles it with `Transaction.settleRun`. It certifies
the same state and block output as `Transaction.run` and retains the message
run for the trace summary. This module sits outside the `Jaune.lean` import
closure.
-/

namespace Jaune

open Jaune
open Jaune.TraceTransaction (Certified)

/-- Trace a top-level message run. A preparation fault or a refusal returns without a frame. A
frame is entered from its checkpoint and traced as `Trace.runFrame` traces it; without state gas a
call first reports its authorization refund. -/
def TraceTransaction.runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) :
    m (Certified (TopLevel.run msg)) := do
  match hprep : TopLevel.prepare msg with
  | .error e =>
    pure ⟨.error e, by simp only [TopLevel.run, hprep]; rfl⟩
  | .ok (.refused reason halted) =>
    pure ⟨.ok ⟨msg, .refused reason halted, none, none⟩, by simp only [TopLevel.run, hprep]; rfl⟩
  | .ok (.frame f a) =>
    if msg.benv.stat.rules.stateGas.isNone && msg.target.isSome then
      authorizationRefund a
    let context : Trace.Context := ⟨runId, 0, 1⟩
    match hentry : enterWith f f.checkpoint.toDevm with
    | .done settled =>
      sink (.entered context f (.done settled))
      sink (.settled context f settled)
      pure ⟨(do let r ← settled; pure ⟨msg, .frame f a, none, some r⟩), by
        simp only [TopLevel.run, hprep, bind, Except.bind, hentry]⟩
    | .run evm =>
      sink (.entered context f (.run evm))
      let result ← Trace.exec sink evm context 1
      let settled := settle f result.value
      sink (.settled context f settled)
      pure ⟨(do let r ← settled; pure ⟨msg, .frame f a, some evm, some r⟩), by
        simp only [TopLevel.run, hprep, bind, Except.bind, hentry, settled, result.erases]⟩

/-- The traced message run's value is `TopLevel.run`. -/
theorem TraceTransaction.runMessage_erasure {msg : Msg} (result : Certified (TopLevel.run msg)) :
    result.value = TopLevel.run msg := result.erases

/-- A transaction's check and preparation. -/
def TraceTransaction.prepareTransaction (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Except TransitionError Transaction.Prepared := do
  let checked ← Transaction.admit benv bout tx index
  Transaction.prepare checked tx index

/-- The transaction result and the message run the trace summary reads: none when the
transaction was rejected before its message ran or the run faulted. -/
structure TraceTransaction.TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat)
    extends Certified ((fun pair => (pair.1.state, pair.2)) <$> Transaction.run benv bout tx index) where
  messageRun : Option TopLevelRun
  /-- The observed run is the transaction's top-level message run. -/
  observes : messageRun =
    ((TraceTransaction.prepareTransaction benv bout tx index).toOption.bind
      fun prepared => (TopLevel.run prepared.msg).toOption)

/-- Execute one transaction with synchronous instruction observations: check and prepare it,
trace its message run, settle the run as `Transaction.run` settles it. The certificate connects
the value to the public pipeline; the message run is never run a second time. -/
def TraceTransaction.runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) (runId : String) : m (TraceTransaction.TransactionResult benv bout tx index) := do
  match hcheck : Transaction.admit benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageRun := none
      erases := by simp only [Transaction.run, hcheck, bind, Except.bind]; rfl
      observes := by simp only [TraceTransaction.prepareTransaction, hcheck, bind, Except.bind]; rfl }
  | .ok checked =>
    match hprep : Transaction.prepare checked tx index with
    | .error error =>
      pure {
        value := .error error
        messageRun := none
        erases := by simp only [Transaction.run, hcheck, hprep, bind, Except.bind]; rfl
        observes := by simp only [TraceTransaction.prepareTransaction, hcheck, hprep, bind, Except.bind]; rfl }
    | .ok prepared =>
      let message ← TraceTransaction.runMessage sink authorizationRefund prepared.msg runId
      let value : Except TransitionError (State × BlockOutput) := do
        let run ← message.value.mapError (fun e => TransitionError.vm e.toEvmError)
        (fun pair => (pair.1.state, pair.2)) <$>
          Transaction.settleRun checked prepared tx index run
      let observed := match message.value with
        | .error _ => none
        | .ok run => some run
      pure {
        value := value
        messageRun := observed
        erases := by
          simp only [value, message.erases, Transaction.run, hcheck, hprep, bind, Except.bind]
          cases Except.mapError (fun e => TransitionError.vm e.toEvmError) (TopLevel.run prepared.msg) <;>
            rfl
        observes := by
          simp only [TraceTransaction.prepareTransaction, hcheck, hprep, bind, Except.bind, observed, message.erases,
            Except.toOption, Option.bind]
          cases TopLevel.run prepared.msg <;> rfl }

/-- The traced transaction's value is the transaction run's state and block output. -/
theorem TraceTransaction.runTransaction_erasure {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} (result : TraceTransaction.TransactionResult benv bout tx index) :
    result.value = (fun pair => (pair.1.state, pair.2)) <$> Transaction.run benv bout tx index :=
  result.erases

end Jaune
