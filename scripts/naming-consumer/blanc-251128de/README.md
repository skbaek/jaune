# Blanc 251128de migration inputs for the G0a rename

Inputs of the disposable Blanc-copy build (goal jaune-shape-and-names-v1, N1),
for Blanc at `251128de` (pinned Jaune `730aae65`) and the G0a map at Jaune
`46cd3868` (`scripts/naming-map.json`, sha256 f36c7c82…).

- `consumer-map.json`: written by `naming-tree.py consumer-map`; one row per
  Blanc declaration authored inside a Jaune namespace the map renames. `plan
  --consumer-map` rederives it and refuses any difference.
- `sites.json`: reviewed sites (`plan --sites`): 311 `unchanged` (local
  binders, Qq quotations, local-head named arguments, the `open Jaune.Ninst
  Ninst` token, `_root_`-authored Blanc names, user-named goals, compound
  ranges whose inner identifiers are respelled) and 9 `replace` (name literals
  of renamed Jaune constants and unelaborated simp-discharger spellings).
  Valid only for the listed Blanc file digests.
