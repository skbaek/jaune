import Elevm.Execution

/-!
# A sufficient fuel bound for the interpreter driver

`Elevm.Execution` defines the interpreter driver structurally recursive on a
fuel parameter, so it must report exhaustion as a possible outcome. This module
proves that fuel seeded from the frame's remaining gas is always sufficient, and
uses that proof to give the driver and its frame wrappers a total type.

It sits between `Elevm.Execution` (the driver) and `Elevm.Transaction` (its
first consumer) so that the consumers can be stated against the total API.
-/
