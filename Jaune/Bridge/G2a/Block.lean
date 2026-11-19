import Jaune.Run.Block
import Jaune.Bridge.G2a.Body

/-!
# W2 cut E: bridges for the block run (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

Old side = cut D's `Bridge.G2a.Phased.stateTransitionCoreE`, whose own old side is
`stateTransitionCoreE` at `ba15f397` (`Jaune.Transaction`), unedited. New side = `Jaune.Run.Block`.

* `Block.check_ofPrefix`: `Block.check` over a prefix's commitments is today's
  `stateTransitionChecks` followed by `blockAccessListCheck`, on the whole result, so the same
  check fails first with the same reason and text.
* `E.stateTransitionCoreE_eq`: **the bridge.** The staged block transition equals cut D's, for every
  error embedding, fork, chain, block and ommer check, on the whole result.

Note (decision 16 / F4): the pre-cut composed difference theorem against `ba15f397`
(`E.stateTransitionCoreE_difference`) is recorded at pre-edit head
`5871922e3b60a3efa66f85ac3c2aab53a042aa0a` and joined to `gate/g2a` by the one-arm decoder edit
(`Bytes.toExceptTransaction_unknown_typeNotSupported`).
-/

namespace Jaune.Bridge.G2a

open Jaune

/-! ### The check -/

/-- **`Block.check` is today's two checks.** Over a body prefix's commitments, `Block.check` is
`stateTransitionChecks` with the transition's computed values, then `blockAccessListCheck`: the
whole result, so the first failing comparison and its text are today's. -/
theorem Block.check_ofPrefix (rules : ForkRules) (q : Body.Prefix) (header : Header) :
    Block.check header (Block.Commitments.ofPrefix rules q) =
      (stateTransitionChecks q.toBlockOutput header (getTransactionsRoot q.toBlockOutput)
          q.state.root (getReceiptRoot q.toBlockOutput) (logsBloom q.toBlockOutput.blockLogs)
          (getWithdrawalsRoot q.toBlockOutput)
          (if rules.header.requestsHash then some (computeRequestsHash q.toBlockOutput.requests)
            else none) >>= fun _ =>
        blockAccessListCheck rules q.toBlockOutput header) := by
  unfold Block.check
  refine congrArg₂ (fun a k => Bind.bind a k) ?_ ?_
  · rfl
  funext _
  unfold Block.checkAccessListHash blockAccessListCheck Block.Commitments.ofPrefix
  cases rules.blockAccessListRules <;> rfl

/-! ### The bridge -/

/-- **Bridge, cut E.** The staged block transition is cut D's, on the whole result: the same
header failure, the same ommer failure, the same body failure, the same first failing commitment
check with the same text, and the same chain. -/
theorem E.stateTransitionCoreE_eq {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    stateTransitionCoreE embed f ch block checkOmmers =
      Bridge.G2a.Phased.stateTransitionCoreE embed f ch block checkOmmers := by
  rw [staged_stateTransitionCoreE_eq_with]
  unfold stateTransitionCoreE stateTransitionCoreWith applyBody
  cases hv : validateHeader f.ruleSet ch block.header with
  | error e => rfl
  | ok u =>
    cases ho : checkOmmers () with
    | error e => simp only [bind, Except.bind, Except.mapError]
    | ok u' =>
      cases hq : Body.importer (initBlockEnvironment f ch block.header) block.transactions block.ommers
          block.withdrawals with
      | error e => simp only [bind, Except.bind, Except.mapError, Functor.map, Except.map]
      | ok q =>
        simp only [bind, Except.bind, Except.mapError, Functor.map, Except.map,
          Body.Prefix.output]
        rw [Block.check_ofPrefix]
        cases stateTransitionChecks q.toBlockOutput block.header _ _ _ _ _ _ <;>
          simp only [bind, Except.bind]

/-- The whole result, through `ba15f397`'s `stateTransitionCoreE` off the decode-order split. -/
theorem E.stateTransitionCoreE_eq_of_not_split {ε : Type} (embed : TransitionError → ε) (f : Fork)
    (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit)
    (h : ¬ BlockDecodeOrderSplit f ch block checkOmmers) :
    stateTransitionCoreE embed f ch block checkOmmers =
      Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers := by
  rw [E.stateTransitionCoreE_eq,
    Jaune.Bridge.G2a.stateTransitionCoreE_eq_of_not_split embed f ch block checkOmmers h]

end Jaune.Bridge.G2a
