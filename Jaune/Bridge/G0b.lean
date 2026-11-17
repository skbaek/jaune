import Jaune.Transaction

/-!
# Bridge for gate G0b: the two structured causes

Goal `jaune-shape-and-names-v1`, 3.1 and 3.2. Where a specification function
called a renderer -- the failed checked system call and the invalid ommer
header -- it now returns the structured cause
(`BlockValidationError.systemContractCallHalted`,
`BlockValidationError.invalidOmmerHeader`), and `BlockValidationError.detail`
writes the text.

The old definitions wait here, moved unchanged from `Jaune/Transaction.lean`
under the namespace `Jaune.G0b`, with their lemma. Each bridge theorem states,
for every input (and so for every `Fork`, which the input carries), that the
text the renderer writes for the new definition's result equals the text it
writes for the old definition's: plain `Eq` on the rendered result. This module
is deleted after the gate's tagged commit.
-/

namespace Jaune

namespace G0b

open Jaune

def processCheckedSystemTransaction
  (benv : Benv) (target : Address) (data : Bytes) :
  Except TransitionError (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  -- A mis-provisioned chain: the mandatory system contract holds no code. The
  -- pinned `process_checked_system_transaction` raises `InvalidBlock` here,
  -- before attempting the call, and the corpus names the reason
  -- `BlockException.SYSTEM_CONTRACT_EMPTY`; it is a block rejection with its
  -- own typed reason and its own fixture identity. (Until goal D this arm was
  -- a fail-closed *internal* invariant, with the note that the identity was
  -- "outside this build's reviewed vocabulary" and "unobserved in every
  -- corpus"; the Glamsterdam devnet transition corpus observes it in the four
  -- `deploy_after_fork` cases of `eip8282_…/test_contract_deployment.py`, so
  -- the reason is rewritten to the block channel -- goal D, packet DP-2,
  -- owner-approved.)
  if systemContractCode.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let ⟨state, systemTxOutput⟩ ←
    Except.mapError TransitionError.vm
      (processSystemTransaction benv target systemContractCode data)
  -- P0.6 item 3: the failure text is extracted by the total match, never by a
  -- partial projection out of the optional error field.
  match systemTxOutput.error with
  | some err =>
    .error <| .block <| .systemContractCallFailed <| .text
      s!"system contract ({target.toHex}) call failed: \
      {err.render}"
  | none => .ok ⟨state, systemTxOutput⟩

/-- Validate an ommer against its retained parent, preserving the existing
ommer diagnostic and internal-error channels. -/
def validateOmmerWithParent (rules : ForkRules) (chain : BlockChain)
    (ommer : Header) (parent : Block) : Except TransitionError Unit :=
  match validateHeader rules { chain with blocks := [parent] } ommer with
  | .ok () => .ok ()
  | .error (.block e) => ommersFail s!"ommer header is invalid: {e.render}"
  | .error e => .error e

theorem processCheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {p}
    (hp : processCheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 := by
  unfold processCheckedSystemTransaction at hp
  dsimp only at hp
  split at hp
  · obtain ⟨u, hu, hp⟩ := Except.bind_eq_ok hp
    nomatch hu
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨qs, qo⟩ := q
    dsimp only at hp
    split at hp
    · nomatch hp
    · cases hp
      exact processSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)

/-- Bridge for the failed checked system call: the renderer's text over the new
`processCheckedSystemTransaction` equals the old definition's, for every block
environment, target and calldata. -/
theorem processCheckedSystemTransaction_bridge (benv : Benv) (target : Address)
    (data : Bytes) :
    (Jaune.processCheckedSystemTransaction benv target data).mapError
        TransitionError.render =
      (processCheckedSystemTransaction benv target data).mapError
        TransitionError.render := by
  unfold Jaune.processCheckedSystemTransaction processCheckedSystemTransaction
  dsimp only
  split
  · rfl
  · cases processSystemTransaction benv target (benv.state.getCode target) data with
    | error e => rfl
    | ok q =>
      obtain ⟨state, output⟩ := q
      dsimp only [Except.mapError, bind, Except.bind]
      cases output.error with
      | none => rfl
      | some halt => rfl

/-- Bridge for the invalid ommer header: the renderer's text over the new
`validateOmmerWithParent` equals the old definition's, for every rule record,
chain, ommer and parent. -/
theorem validateOmmerWithParent_bridge (rules : ForkRules) (chain : BlockChain)
    (ommer : Header) (parent : Block) :
    (Jaune.validateOmmerWithParent rules chain ommer parent).mapError
        TransitionError.render =
      (validateOmmerWithParent rules chain ommer parent).mapError
        TransitionError.render := by
  unfold Jaune.validateOmmerWithParent validateOmmerWithParent
  generalize validateHeader rules { chain with blocks := [parent] } ommer = r
  rcases r with e | ⟨⟩
  · cases e <;> rfl
  · rfl

end G0b

end Jaune
