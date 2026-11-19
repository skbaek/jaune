import Jaune.MessageCall.CheckedState

/-! The Log family (S4): `LOG0`–`LOG4`.

A row is data: the topic count and the three prices. The family step runs over the frame-local
`Machine` and returns, besides the machine, one `Log`; `Frame.State.liftLog` appends that log and
changes nothing else outside the machine. A row has no field through which it could write the
world, the accessed sets, the refund or the trail. -/

namespace Jaune.Checked

open Jaune

structure LogRow where
  topics : Fin 5
  base : Nat := Gas.log
  perByte : Nat := Gas.logData
  perTopic : Nat := Gas.logTopic

/-- The charge of a log of `size` bytes at `offset`: the row's prices plus the memory extension. -/
def LogRow.cost (row : LogRow) (m : Machine) (offset size : Nat) : Nat :=
  row.base + row.perByte * size + row.perTopic * row.topics + m.extCost [⟨offset, size⟩]

/-- The family step: pop the offset, the size and the topics; charge the row's prices plus the
memory extension; refuse a static frame after the charge; read the data (extending memory). -/
def LogRow.step (row : LogRow) (ctx : CallContext) (m : Machine) :
    Except (ExceptionalHalt × Machine) (Machine × Log) := do
  let ⟨offset, m⟩ ← m.popToNat
  let ⟨size, m⟩ ← m.popToNat
  let ⟨topics, m⟩ ← m.popN row.topics
  let m ← m.chargeGas (row.cost m offset size)
  Except.assert (!ctx.isStatic) (.writeInStaticContext .none, m)
  let ⟨data, m⟩ := m.memRead offset size
  .ok (m, ⟨ctx.recipient, topics, data⟩)

/-- Lift a log step: the machine on both channels, the log appended on success; the world, the
trail and every other substate field are kept. -/
def Frame.State.liftLog (s : Frame.State)
    (r : Except (ExceptionalHalt × Machine) (Machine × Log)) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  match r with
  | .error (e, m) => .error (e, s.withMachine m)
  | .ok (m, log) => .ok ((s.withMachine m).addLog log)

end Jaune.Checked
