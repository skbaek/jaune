# Shape pilot

This is WP(a) of `jaune-shape-and-names-v1`, outside the production import
closure. It is an executable prototype and a proof comparison, not a replacement
interpreter or an all-fork equivalence claim.

- `Programs.lean` runs the current public frame entry. A Prague caller receives
  `0xAA` from a child that wrote storage and a log before reverting, then pushes
  42. An Amsterdam caller creates a child whose initcode successfully returns a
  STOP byte; deposit runs out of gas. The caller pushes 42, keeps its incremented
  nonce and warmed destination, loses the deployment and receives the new-account
  state-gas refund. The observations inspect raw child termination separately
  from settlement. The caller address is outside both the BLS and P256 precompiles.
- `Lifetime.lean` separates machine, world, substate and trail. Failed results
  carry no world or substate. `resume_revert` and `resume_halt` state the complete
  returned dynamic state; `returnedMachine` describes the zero stack result,
  call output window, return data, returned meters and new-account refund. Their
  only premise is stack capacity, and neither opens an interpreter definition
  or a private helper.
- `Driver.lean` runs these records through `step`, `enter`, `settle`, `resume` and
  one bounded driver. A frame contains one message and one checkpoint. The frame
  identity theorem names that message's creation kind and code address. Opcode
  execution and call preparation still use existing primitives through an
  explicit adapter. Legacy frame settlement and `Resume.run` are not called.
- `OldProof.lean` proves world/substate survival against the current resume.
  Both cases need a rollback equality and successful resume. Amsterdam also
  needs `AmsterdamFailedChildSettled` and a split on the new-account charge.
  Neither proof opens a private helper. These are conditional resume facts,
  not proofs that the concrete bytecode executes.
- `Runs.lean` executes both programs through the prototype and connects the
  driver's returned result to the new resume equations without unfolding the
  driver. Executable observations establish the concrete paths; symbolic
  theorems establish the resume property for arbitrary inputs meeting their
  premises. There is no kernel evaluation of a concrete memory/storage image.

The fuel bound is a pilot resource bound; exhaustion is an internal fault,
never an EVM outcome. Transaction and block contexts still reuse their current
record types. Reusing instruction preparation, proving the cumulative substate
entry/merge bridge for every rule set, propagating faults and malformed-meter
invariants at every boundary, total termination, and replacing the old execution
relations remain later work. No benchmark or full-catalogue verdict follows from
these examples. GP's report and required independent review remain separate.
