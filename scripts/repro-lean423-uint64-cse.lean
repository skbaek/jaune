/-!
Standalone repro of the Lean v4.23.0 codegen bug worked around in
`Elevm/Hash.lean` (`fB64`): when one function contains duplicated large
`UInt64` literals, the compiler CSEs them into a shared value and the C
emitter issues `lean_inc` on an unboxed `uint64_t`, so the generated C does
not compile. Elaboration is clean — LSP diagnostics do not catch this; only
the `leanc` stage fails.

Not a Lake target and not imported by anything; compile manually:

  lean -c repro.c scripts/repro-lean423-uint64-cse.lean
  leanc -c -O2 -o repro.o repro.c

Expected on v4.23.0: clang error at the `lean_inc(...)` line
(`incompatible integer to pointer conversion ... 'uint64_t' ... 'lean_object *'`).
Expected on a fixed toolchain: both commands succeed. `-Dcompiler.extract_closed=false`
does NOT avoid the bug on v4.23.0.

Resolved during the v4.32.1 migration: on v4.23.0 both the failure above and its
exact `lean_inc` line reproduce; on v4.32.1 both commands succeed, the program
links and runs, and the generated C contains no `lean_inc` on an unboxed
`uint64_t`. Retained as a regression canary for future toolchain bumps. The
`B64.rdnc` read in `Elevm/Hash.lean`'s `fB64` is kept regardless — see the
doc comment there.

The shape mirrors `fB64`/`roundB64`: a non-inline function taking a `UInt64`
round constant and returning a scalar-field structure, called with a
duplicated literal (keccak's round schedule repeats 0x8000000080008081).
-/

structure S where
  (a0 a1 a2 a3 a4 : UInt64)

private def round (rc : UInt64) (s : S) : S :=
  let x := s.a0 ^^^ rc
  ⟨x, s.a1 ^^^ x, s.a2, s.a3, s.a4⟩

def f (s : S) : S :=
  let s := round 0x8000000080008081 s
  let s := round 0x0000000000008082 s
  let s := round 0x800000000000808a s
  let s := round 0x8000000080008081 s
  s

def main : IO Unit := do
  let s := f ⟨1, 2, 3, 4, 5⟩
  IO.println s!"{s.a0} {s.a1}"
