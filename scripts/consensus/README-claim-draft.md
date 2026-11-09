# README claim draft (for the user's review; not published)

Draft for goal `jaune-consensus-electra-fulu-v1`, outcome O8. This paragraph
states the honest claim from goal section 2. Counts need the user's approval
before use and appear as placeholders.

## Proposed paragraph

Jaune contains an executable specification of the Ethereum consensus layer
for Electra and Fulu, written in pure Lean from `ethereum/consensus-specs`
release `v1.6.1`. It passes every case of that release's official test
vectors whose fork is Electra or Fulu, on both the minimal and mainnet
presets, plus every general-preset case those forks use, with no
expected-failure allowance [COUNT: cases and files per preset and fork]. It
does so under Jaune's existing trusted base and gate discipline: pure Lean
with no FFI, the R1 to R6 integrity rules over the consensus modules, and
axiom evidence by the repository's union walk.

## Not claimed

- That the Lean equals the Python specification. Vectors are evidence from
  testing, not proof, as for the execution layer.
- Anything about any client implementation.
- Any fork other than Electra and Fulu, except the Deneb state and blocks
  that Electra's `fork` and `transition` vectors need as their pre-fork side.
- Any cross-layer theorem, or any proved property of the consensus layer.
  Those are follow-on goals this one enables.
- Performance at real mainnet state scale, or anything about ZK.
- That Jaune is Ethereum.
