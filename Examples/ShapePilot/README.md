# Shape pilot

This is WP(a) of `jaune-shape-and-names-v1`, outside the production import
closure. It is an executable prototype of the accepted W1/W3 design and a proof
comparison, not a replacement interpreter or an all-fork equivalence claim. No
old/new interpreter equivalence is proved here.

- `Programs.lean` runs the current public frame entry. A Prague caller receives
  `0xAA` from a child that wrote storage and a log before reverting, then pushes
  42. An Amsterdam caller creates a child whose initcode successfully returns a
  STOP byte; deposit runs out of gas. The caller pushes 42, keeps its incremented
  nonce and warmed destination, loses the deployment and receives the new-account
  state-gas refund. The observations inspect raw child termination separately
  from settlement. The caller address is outside both the BLS and P256 precompiles.
- `Lifetime.lean` separates machine, world, substate and trail; a checkpoint is
  a world, substate and trail, and the caller's machine travels in the
  continuation. Failed results carry no world or substate; faults are not
  results and carry no payload. `resume` keeps Amsterdam's two meter
  assertions (a violation is a fault), absorbs a successful child's substate
  with today's merges (`Substate.absorb`), takes the caller's trail as
  `checkpoint.trail.absorb result.trail` in every outcome, and on a failed
  status push halts the caller at its own merged state. `resume_failed`,
  `resume_success`, `resume_overflow` and the `returnedMachine_*` lemmas state
  S3 (a)-(c) over `resume` alone.
- `Driver.lean` runs these records through `step`, `enter`, `settle`, `resume` and
  one bounded driver. A frame holds one message and one checkpoint. A message's
  kind is `.call codeAddress` or `.create`; `Frame.message_identity` states that
  creation is the kind and that a non-creation runs a named account's code, and
  the `setUp_*`, `dispatch_*` and `settle_ok_*` lemmas show entry set-up,
  precompile dispatch and code deposit dispatch on the kind. A child starts
  from today's seeds (`initDevm`). A failed frame's RIPEMD-160 touch is tested
  on the world after the creation set-up, as `processMessage.settle` does.
  `topFrame` makes a top-level message without a target a creation. Opcode
  execution, call preparation, creation set-up, transfer and the deposit charge
  still use existing primitives through an explicit adapter. Legacy frame
  settlement and `Resume.run` are not called.
- `OldProof.lean` proves world/substate survival against the current resume.
  Both cases need a rollback equality and successful resume. Amsterdam also
  needs `AmsterdamFailedChildSettled` and a split on the new-account charge.
  Neither proof opens a private helper. These are conditional resume facts,
  not proofs that the concrete bytecode executes.
- `Runs.lean` executes both programs through the prototype and proves the
  caller's returned machine, world, substate and trail for the two worked
  children (`call_example`, `create_example`, and the driver clients
  `call_return_survival`, `create_return_survival`), with guards checking each
  premise on the actual run. It also checks, against production, a top-level
  creation (set-up, deposit, `setCode`) and RIPEMD-160's surviving touch for a
  failed creation and a failed call to 0x03 under Berlin's rules.
- `FieldReaders.lean` is decision 13's Lean environment walk over the five
  `Sevm` fields `CallContext` drops and `TenvStat.indexInBlock`/`txHash`.

The fuel bound is a pilot resource bound; exhaustion is an internal fault,
never an EVM outcome. Transaction and block contexts still reuse their current
record types. Reusing instruction preparation, the bridges for every rule set,
the run invariant that discharges `committedSpill = 0`, total termination, and
replacing the old execution relations remain later work. No benchmark or
full-catalogue verdict follows from these examples.
