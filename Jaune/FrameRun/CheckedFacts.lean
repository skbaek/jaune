import Jaune.FrameRun.CheckedOrder
import Jaune.FrameRun.CheckedAdequacy
import Jaune.Run.BodyFacts
import Jaune.Run.CheckedTransaction
import Jaune.Transaction

/-!
# `Exec`-free restatements over the checked frame sequence (goal `jaune-shape-and-names-v1`, G2b)

The checked derivation facts that `Checked.Frame.Run` did not already state, with the same
conclusions: the canonical derivation is inhabited, a failed root retains no node, and the
same-frame continuation is reflexive, transitive and well-founded.
-/

namespace Jaune.Checked.Frame.Run

/-- Restates `Checked.Exec.nonempty`. -/
theorem nonempty (r : Frame.Running) : Nonempty (Frame.Run r (.exit (exec r))) := ⟨canonical r⟩

/-- Restates `Checked.Exec.retainedNodes_eq_nil_of_failed`. -/
theorem retainedNodes_eq_nil_of_failed {r out} (t : Frame.Run r (.exit out))
    (h : Exec.finished out = false) : retainedNodes t = [] := by
  simp [retainedNodes, h]

/-- Restates `Checked.Exec.committedFrames_eq_nil_of_failed`. -/
theorem committedFrames_eq_nil_of_failed {r out} (t : Frame.Run r (.exit out))
    (h : Exec.finished out = false) : committedFrames t = [] := by
  simp [committedFrames, h]

theorem Node.Prefix.refl (a : Node) : a.Prefix a := ⟨.stop _, rfl, by simp⟩

/-- Restates `Checked.Exec.Deriv.ParentPrefix.trans` (and `snoc`, its one-step case). -/
theorem Node.Prefix.trans {a b c : Node} (first : a.Prefix b) (last : b.Prefix c) : a.Prefix c := by
  rcases a with ⟨r, out, t⟩
  rcases b with ⟨s, u, q⟩
  rcases c with ⟨w, v, x⟩
  obtain ⟨p, hu, e⟩ := first
  obtain ⟨p', hv, e'⟩ := last
  dsimp only at hu hv p p' e e'
  subst hu hv
  exact ⟨append p p', rfl, by rw [e, e', append_assoc]⟩

private theorem mem_spine {r out} (t : Frame.Run r (.exit out)) (b : Node) (h : b ∈ spine t) :
    b = ⟨r, out, t⟩ ∨ Node.lt b ⟨r, out, t⟩ := by
  cases t with
  | halt | callDoneEnd | callRanEnd => simp only [spine, List.mem_singleton] at h; exact .inl h
  | next hs rest | callDone _ _ hs rest | callRan _ _ _ hs rest =>
    rw [spine] at h
    rcases List.mem_cons.mp h with h | h
    · exact .inl h
    · refine .inr ?_
      rcases mem_spine rest b h with rfl | lt
      · exact .single (by simp [Node.Sub, Node.children])
      · exact .tail lt (by simp [Node.Sub, Node.children])
termination_by sizeOf t

/-- Restates `Checked.Exec.Deriv.ParentStep.prec` and `ParentStep.lt`: a proper same-frame
continuation is strictly below its start in the structural order. -/
theorem Node.Prefix.lt {a b : Node} (h : a.Prefix b) (ne : b ≠ a) : Node.lt b a := by
  rcases a with ⟨r, out, t⟩
  rcases (mem_spine t b ((Node.prefix_iff_mem_spine _ b).mp h)) with eq | lt
  · exact absurd eq ne
  · exact lt

end Jaune.Checked.Frame.Run

namespace Jaune.Checked

/-- The code entry recorded by a top-level message, with its complete checked frame run. -/
structure Root where
  frame : Frame
  running : Frame.Running
  outcome : Except Fault Frame.Exit
  run : Frame.Run running (.exit outcome)

def Root.ofEntry (frame : Frame) (running : Frame.Running) : Root :=
  ⟨frame, running, exec running, Frame.Run.canonical running⟩

def Root.settled (root : Root) : Except Fault Frame.Result :=
  root.outcome >>= settle root.frame

/-- The root's own settlement can roll back a successful raw execution, including code deposit. -/
def Root.frames (root : Root) : List Frame.Run.Kept :=
  if Frame.settlementCommits root.frame root.outcome then root.run.committedFrames else []

theorem Root.frames_of_failed {root : Root}
    (failed : Frame.settlementCommits root.frame root.outcome = false) : root.frames = [] := by
  simp [Root.frames, failed]

theorem Root.frames_of_success {root : Root}
    (success : Frame.settlementCommits root.frame root.outcome = true) :
    root.frames = root.run.committedFrames := by
  simp [Root.frames, success]

/-- A refusal or a completion at entry, such as a precompile, contributes no code root. -/
def TopLevel.Run.enteredRoot : TopLevel.Run → Option Root
  | .refused _ => none
  | .frame f _ top => top.root.map (Root.ofEntry f)

def TopLevel.Run.frames (run : TopLevel.Run) : List Frame.Run.Kept :=
  run.enteredRoot.toList.flatMap Root.frames

theorem Frame.runTopWithRoot_settled {frame : Frame} {top : Frame.TopRun} {running : Frame.Running}
    (accepted : frame.runTopWithRoot = .ok top) (entry : top.root = some running) :
    (Root.ofEntry frame running).settled = .ok top.result := by
  have result := congrArg (Except.map Frame.TopRun.result) accepted
  change frame.runTop = .ok top.result at result
  rw [Frame.runTop_eq] at result
  have recorded := (Frame.runTopWithRoot_root accepted).symm.trans entry
  cases started : enterWith frame frame.checkpoint with
  | done => rw [started] at recorded; cases recorded
  | run root =>
    rw [started] at recorded result
    cases recorded
    exact result

/-- An entered root settles to the result held by the successful message that supplied it. -/
theorem TopLevel.runNative_root_settled {input : TopLevel.Input} {run : TopLevel.Run} {root : Root}
    (accepted : TopLevel.runNative input = .ok run) (entry : run.enteredRoot = some root) :
    ∃ top refund, run = .frame root.frame refund top ∧ root.settled = .ok top.result := by
  unfold TopLevel.runNative at accepted
  obtain ⟨prepared, _, accepted⟩ := Except.bind_eq_ok accepted
  cases preparation : prepared.toPreparation with
  | refused => rw [preparation] at accepted; cases accepted; cases entry
  | frame frame refund =>
    rw [preparation] at accepted
    cases acceptedFrame : frame.runTopWithRoot with
    | error err => simp [TopLevel.Preparation.run, acceptedFrame, Except.map] at accepted
    | ok top =>
      simp only [TopLevel.Preparation.run, acceptedFrame, Except.map, Except.ok.injEq] at accepted
      subst run
      cases recorded : top.root with
      | none => simp [TopLevel.Run.enteredRoot, recorded] at entry
      | some running =>
        simp only [TopLevel.Run.enteredRoot, recorded, Option.map_some, Option.some.injEq] at entry
        subst root
        exact ⟨top, refund, rfl, Frame.runTopWithRoot_settled acceptedFrame recorded⟩

/-- The roots of a successful message come from that run's sole possible code entry. -/
def MessageRoots (input : TopLevel.Input) (run : TopLevel.Run) (roots : List Root) : Prop :=
  TopLevel.runNative input = .ok run ∧ roots = run.enteredRoot.toList

theorem exists_messageRoots {input run} (accepted : TopLevel.runNative input = .ok run) :
    ∃ roots, MessageRoots input run roots := ⟨_, accepted, rfl⟩

theorem MessageRoots.atMostOne {input run roots} (h : MessageRoots input run roots) :
    roots.length ≤ 1 := by
  obtain ⟨_, rfl⟩ := h
  cases run.enteredRoot <;> simp

def TransactionRun.frames (transaction : TransactionRun) : List Frame.Run.Kept :=
  transaction.message.frames

/-- The transaction's sender, final observations and roots come from the same run. -/
def TransactionRoots (block : BlockContext) (start : State) (input : BlockOutput) (tx : Jaune.Transaction)
    (index : Nat) (state : State) (output : BlockOutput) (sender : Address) (roots : List Root) : Prop :=
  ∃ run, Transaction.run block start input tx index = .ok (run, output) ∧ run.state = state ∧
    run.sender = sender ∧ MessageRoots run.entry run.message roots

theorem Transaction.run_messageRoots {block start input tx index run output}
    (accepted : Transaction.run block start input tx index = .ok (run, output)) :
    MessageRoots run.entry run.message run.message.enteredRoot.toList := by
  unfold Transaction.run at accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨prepared, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨message, executed, settled⟩ := Except.bind_eq_ok accepted
  unfold Transaction.settleRun at settled
  obtain ⟨_, _, settled⟩ := Except.bind_eq_ok settled
  cases settled
  exact ⟨Except.mapError_eq_ok_iff.mp executed, rfl⟩

theorem exists_transactionRoots {block start input tx index state output}
    (accepted : (Transaction.run block start input tx index).map (fun (run, next) => (run.state, next)) =
      .ok (state, output)) :
    ∃ sender roots, TransactionRoots block start input tx index state output sender roots := by
  cases executed : Transaction.run block start input tx index with
  | error => simp [executed, Except.map] at accepted
  | ok pair =>
    rcases pair with ⟨run, next⟩
    simp only [executed, Except.map, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨run.sender, _, run, executed, rfl, rfl, Transaction.run_messageRoots executed⟩

def OpRun.enteredRoot : OpRun → Option Root
  | .systemCall _ _ run | .requestCall _ _ _ run => run.message.enteredRoot
  | .transaction run => run.message.enteredRoot
  | .withdrawals .. | .depositRequests .. | .rewards .. | .buildAccessList .. | .checkAccessListLimit => none

def BlockRun.roots (run : BlockRun) : List Root := run.ops.filterMap OpRun.enteredRoot

def BlockRun.frames (run : BlockRun) : List Frame.Run.Kept := run.roots.flatMap Root.frames

/-- The sender refund and coinbase fee are credited before self-destruct settlement. The
touched-account sweep runs on the resulting world. -/
theorem Transaction.settleRun_state (admitted : Transaction.Admitted) (prepared : Transaction.Prepared)
    (tx : Jaune.Transaction) (index : Nat) (message : TopLevel.Run)
    {record : TransactionRun} {output : BlockOutput}
    (accepted : settleRun admitted prepared tx index message = .ok (record, output)) :
    let block := prepared.input.message.context.block
    let effects := message.settlement prepared.input
    let refund := record.gasSettlement.gasLeft * prepared.effectiveGasPrice
    let fee := record.gasSettlement.gasUsed * (prepared.effectiveGasPrice - block.baseFeePerGas)
    record.state = sweepTouchedAccounts block.rules effects.touchedAccounts.toList
      (settleSelfdestructs block.rules effects.accountsToDelete.toList
        ((effects.state.addBal prepared.sender (Jaune.Nat.toU256 refund)).addBal
          block.coinbase (Jaune.Nat.toU256 fee))) := by
  unfold settleRun at accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  cases accepted
  rfl

/-- Admission reads only the block output's gas counters. -/
theorem checkTransaction_congr {block : BlockContext} {state : State} {b b' : BlockOutput}
    (tx : Jaune.Transaction) (hg : b.blockGasUsed = b'.blockGasUsed)
    (hs : b.blockStateGasUsed = b'.blockStateGasUsed) (hb : b.blobGasUsed = b'.blobGasUsed) :
    checkTransaction block state b tx = checkTransaction block state b' tx := by
  unfold checkTransaction checkTransactionGasLimits
  rw [hg, hs, hb]

/-- Admission and execution use the starting world and the output summary. The signed
record is independent of the other accumulated block output. -/
theorem Transaction.run_summary {block : BlockContext} {state : State} {b b' : BlockOutput}
    (tx : Jaune.Transaction) (index : Nat) (summary : outputSummary b = outputSummary b') :
    (fun (record, next) => (record, outputSummary next)) <$> run block state b tx index =
      (fun (record, next) => (record, outputSummary next)) <$> run block state b' tx index := by
  simp only [outputSummary, Prod.mk.injEq] at summary
  obtain ⟨hg, hs, hc, hb, hr⟩ := summary
  unfold run Transaction.admit Transaction.prepare Transaction.settleRun
  simp only [map_bind, bind_assoc, Except.ok_bind', pure_bind]
  rw [checkTransaction_congr (b := {b with
    transactionsTrie := b.transactionsTrie.insert (Rlp.Item.bytes (Jaune.Nat.toBytes index)).toBytes tx})
    (b' := {b' with transactionsTrie := b'.transactionsTrie.insert (Rlp.Item.bytes (Jaune.Nat.toBytes index)).toBytes tx})
    tx hg hs hb]
  refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => bind_congr fun _ =>
    bind_congr fun _ => bind_congr fun _ => ?_
  simp only [Functor.map, pure, Except.pure, Except.map, outputSummary, BlockOutput.withGasSettlement,
    receiptsRead_insert, hg, hs, hc, hb, hr]

/-- A signed transaction's block output: its gas settlement, its trie entries at its index and
its logs, beside the rebuilt access-list builder. -/
theorem Transaction.run_output {block : BlockContext} {state : State} {bout : BlockOutput}
    {tx : Jaune.Transaction} {index : Nat} {run : TransactionRun} {out : BlockOutput}
    (h : Transaction.run block state bout tx index = .ok (run, out)) :
    out = { bout.withGasSettlement run.gasSettlement run.blobGasUsed with
      transactionsTrie := bout.transactionsTrie.insert (rlpKey index) tx
      receiptKeys := bout.receiptKeys ++ [rlpKey index]
      receiptsTrie := bout.receiptsTrie.insert (rlpKey index) run.receipt
      blockLogs := bout.blockLogs ++ run.receipt.2.logs
      blockAccessListBuilder := out.blockAccessListBuilder } := by
  unfold Transaction.run at h
  obtain ⟨admitted, ha, h⟩ := Except.bind_eq_ok h
  obtain ⟨prepared, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨message, _, hs⟩ := Except.bind_eq_ok h
  have hab : admitted.bout = {bout with
      transactionsTrie := bout.transactionsTrie.insert (rlpKey index) tx} := by
    unfold Transaction.admit at ha
    obtain ⟨_, hb, ha⟩ := Except.bind_eq_ok ha
    obtain ⟨_, _, ha⟩ := Except.bind_eq_ok ha
    obtain ⟨⟨_, _⟩, _, ha⟩ := Except.bind_eq_ok ha
    obtain ⟨⟨_, _, _, _⟩, _, ha⟩ := Except.bind_eq_ok ha
    cases hb
    cases ha
    rfl
  have hpb : prepared.bout = admitted.bout := by
    unfold Transaction.prepare at hp
    obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    cases target : tx.type.to? <;> simp only [target, pure, Except.pure] at hp <;> cases hp <;> rfl
  unfold Transaction.settleRun at hs
  obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
  cases hs
  simp only [hpb, hab]
  rfl

/-- A transaction at the next index adds its receipt at that index, appends its logs and enters
the transaction under the same key. -/
theorem Body.Prefix.Receipts.step_transaction {block : BlockContext} {p q : Jaune.Body.Prefix}
    {tx : Jaune.Transaction} {n : Nat} {rcpts : List (Fin 5 × Receipt)} (hp : p.Receipts n rcpts)
    (h : Body.step block p (.transaction tx n) = .ok q) :
    ∃ receipt, q.Receipts (n + 1) (rcpts ++ [receipt]) ∧ q.logs = p.logs ++ receipt.2.logs ∧
      q.transactionsTrie = p.transactionsTrie.insert (rlpKey n) tx := by
  simp only [Body.step, Body.stepWith] at h
  obtain ⟨⟨run, out⟩, ht, h⟩ := Except.bind_eq_ok h
  cases h
  have hq := Transaction.run_output ht
  have hk : out.receiptKeys = p.receiptKeys ++ [rlpKey n] := congrArg BlockOutput.receiptKeys hq
  have htr : out.receiptsTrie = p.receiptsTrie.insert (rlpKey n) run.receipt :=
    congrArg BlockOutput.receiptsTrie hq
  refine ⟨run.receipt, ⟨?_, ?_, ?_⟩, congrArg BlockOutput.blockLogs hq,
    congrArg BlockOutput.transactionsTrie hq⟩
  · change out.receiptKeys = _
    rw [hk, hp.keys, List.range_succ, List.map_append]
    rfl
  · simp [hp.length]
  · intro i hi
    change out.receiptsTrie[rlpKey i]? = _
    rw [htr]
    simp only [Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq]
    have hlen := hp.length
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hin : i = n
    · subst hin
      simp only [↓reduceIte]
      rw [List.getElem_append_right (by omega)]
      simp [hlen]
    · have hne : rlpKey n ≠ rlpKey i := fun e => hin (rlpKey_injective e).symm
      simp only [hne, ↓reduceIte]
      rw [List.getElem_append_left (by omega)]
      exact hp.get i (by omega)

/-! ### Legacy gas accounting -/

/-- Under rules without state gas, a signed transaction's settlement charges the block what it
charges the sender, and no state gas. -/
theorem Transaction.run_legacyGas {block : BlockContext} {state : State} {bout : BlockOutput}
    {tx : Jaune.Transaction} {index : Nat} {run : TransactionRun} {out : BlockOutput}
    (hnone : block.rules.stateGas = none)
    (h : Transaction.run block state bout tx index = .ok (run, out)) :
    run.gasSettlement.executionGasUsed = run.gasSettlement.gasUsed ∧
      run.gasSettlement.stateGasUsed = 0 := by
  unfold Transaction.run at h
  obtain ⟨admitted, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨prepared, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨message, _, hs⟩ := Except.bind_eq_ok h
  have hb : prepared.input.message.context.block = block := by
    unfold Transaction.prepare at hp
    obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    cases target : tx.type.to? <;> simp only [target, pure, Except.pure] at hp <;> cases hp <;> rfl
  unfold Transaction.settleRun at hs
  obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
  cases hs
  dsimp only
  rw [hb]
  exact settleTransactionGas_none_invariants hnone _ _ _ _ _ _

/-- Under rules without state gas every operation keeps the legacy relation between the block
counters. -/
theorem Body.step_legacyGasAccounting {block : BlockContext} {p q : Jaune.Body.Prefix} {op : BodyOp}
    (hnone : block.rules.stateGas = none) (hp : p.toBlockOutput.LegacyGasAccounting)
    (h : Body.step block p op = .ok q) : q.toBlockOutput.LegacyGasAccounting := by
  cases op with
  | transaction tx index =>
    simp only [Body.step, Body.stepWith] at h
    obtain ⟨⟨run, out⟩, ht, h⟩ := Except.bind_eq_ok h
    cases h
    change out.LegacyGasAccounting
    rw [Transaction.run_output ht]
    exact BlockOutput.LegacyGasAccounting.withGasSettlement hp (Transaction.run_legacyGas hnone ht) run.blobGasUsed
  | systemCall address data index =>
    simp only [Body.step, Body.stepWith] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h; exact hp
  | withdrawals ws index =>
    simp only [Body.step, Body.stepWith] at h
    cases h; exact hp
  | depositRequests =>
    simp only [Body.step, Body.stepWith] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h; exact hp
  | requestCall type address index =>
    simp only [Body.step, Body.stepWith] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h; exact hp
  | rewards coinbase minerReward credits =>
    simp only [Body.step, Body.stepWith] at h
    cases h; exact hp
  | buildAccessList =>
    simp only [Body.step, Body.stepWith] at h
    cases h; exact hp
  | checkAccessListLimit =>
    simp only [Body.step, Body.stepWith] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h; exact hp

theorem Body.fold_legacyGasAccounting {block : BlockContext} (hnone : block.rules.stateGas = none) :
    ∀ (ops : List BodyOp) (p q : Jaune.Body.Prefix), p.toBlockOutput.LegacyGasAccounting →
      ops.foldlM (Body.step block) p = .ok q → q.toBlockOutput.LegacyGasAccounting
  | [], p, q, hp, h => by cases h; exact hp
  | op :: ops, p, q, hp, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨p', hs, h⟩ := Except.bind_eq_ok h
    exact Body.fold_legacyGasAccounting hnone ops p' q (Body.step_legacyGasAccounting hnone hp hs) h

theorem Body.importer_legacyGasAccounting {block : BlockContext} {state : State}
    (hnone : block.rules.stateGas = none)
    {txs : List (Bytes ⊕ Jaune.Transaction)} {ommers : List Header} {wds : List Withdrawal}
    {q : Jaune.Body.Prefix} (h : Body.importer block state txs ommers wds = .ok q) :
    q.toBlockOutput.LegacyGasAccounting := by
  unfold Body.importer at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  exact Body.fold_legacyGasAccounting hnone _ (Jaune.Body.Prefix.init state) _
    BlockOutput.init_legacyGasAccounting h

/-- **Legacy gas accounting in the block body.** A successful body under rules without state
gas keeps the legacy block-counter relation: every step does. -/
theorem applyBody_legacyGasAccounting {block : BlockContext} {state : State}
    (hnone : block.rules.stateGas = none)
    {txs : List (Bytes ⊕ Jaune.Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : applyBody block state txs ommers wds = .ok p) : p.2.LegacyGasAccounting := by
  unfold applyBody at hp
  cases h : Body.importer block state txs ommers wds with
  | error e => simp [h, Functor.map, Except.map] at hp
  | ok q =>
    simp only [h, Functor.map, Except.map, Except.ok.injEq] at hp
    subst hp
    exact Body.importer_legacyGasAccounting hnone h

/-- Every operation except the access-list build and its limit check reads only the summary
for its operation record and the next summary. -/
theorem Body.stepRun_summary (block : BlockContext) {p p' : Jaune.Body.Prefix} {op : BodyOp}
    (noBuild : op ≠ .buildAccessList) (noLimit : op ≠ .checkAccessListLimit)
    (summary : p.summary = p'.summary) :
    (stepRun block p op).map (fun (record, next) => (record, next.summary)) =
      (stepRun block p' op).map (fun (record, next) => (record, next.summary)) := by
  have out : outputSummary p.toBlockOutput = outputSummary p'.toBlockOutput := congrArg Prod.snd summary
  have state : p.state = p'.state := congrArg Prod.fst summary
  simp only [Jaune.Body.Prefix.summary, outputSummary, Jaune.Body.Prefix.toBlockOutput, Prod.mk.injEq] at summary
  obtain ⟨_, hg, hs, hc, hb, hr⟩ := summary
  cases op with
  | buildAccessList => exact absurd rfl noBuild
  | checkAccessListLimit => exact absurd rfl noLimit
  | transaction tx index =>
    have same := Transaction.run_summary (block := block) (state := p'.state) tx index out
    simp only [stepRun, stepWith, state]
    revert same
    cases Transaction.run block p'.state p.toBlockOutput tx index <;>
      cases Transaction.run block p'.state p'.toBlockOutput tx index <;>
      intro same <;>
      simp_all [Except.map, bind, Except.bind, pure, Except.pure, Jaune.Body.Prefix.summary]
  | systemCall address data index =>
    simp only [stepRun, stepWith, state]
    cases data with
    | error => rfl
    | ok bytes =>
      simp only [bind, Except.bind]
      cases processSystemRun block p'.state address (p'.state.getCode address) bytes with
      | error => rfl
      | ok run =>
        simp only [Except.mapError, Except.map, pure, Except.pure, Jaune.Body.Prefix.summary, outputSummary,
          Jaune.Body.Prefix.toBlockOutput, hg, hs, hc, hb, hr]
  | withdrawals ws index =>
    simp only [stepRun, stepWith, state, Except.map, pure, Except.pure, Jaune.Body.Prefix.summary,
      outputSummary, Jaune.Body.Prefix.toBlockOutput, hg, hs, hc, hb, hr]
  | depositRequests =>
    have deposits : parseDepositRequests p.toBlockOutput = parseDepositRequests p'.toBlockOutput :=
      parseDepositRequests_congr hr
    simp only [stepRun, stepWith, deposits]
    cases parseDepositRequests p'.toBlockOutput with
    | error => rfl
    | ok bytes =>
      simp only [bind, Except.bind, Except.map, pure, Except.pure, Jaune.Body.Prefix.summary,
        outputSummary, Jaune.Body.Prefix.toBlockOutput, state, hg, hs, hc, hb, hr]
  | requestCall kind address index =>
    simp only [stepRun, stepWith, state]
    cases processCheckedSystemRun block p'.state address [] with
    | error => rfl
    | ok run =>
      simp only [bind, Except.bind, Except.map, pure, Except.pure, Jaune.Body.Prefix.summary,
        outputSummary, Jaune.Body.Prefix.toBlockOutput, hg, hs, hc, hb, hr]
  | rewards coinbase minerReward credits =>
    simp only [stepRun, stepWith, state, Except.map, pure, Except.pure, Jaune.Body.Prefix.summary,
      outputSummary, Jaune.Body.Prefix.toBlockOutput, hg, hs, hc, hb, hr]

/-- Starting summaries determine the recorded operations and the final summary when the
schedule omits the two operations that read the accumulated access list. -/
theorem Body.run_summary (block : BlockContext) (ops : List BodyOp) (p p' : Jaune.Body.Prefix)
    (schedule : ∀ op ∈ ops, op ≠ .buildAccessList ∧ op ≠ .checkAccessListLimit)
    (summary : p.summary = p'.summary) :
    (run block p ops).map (fun (records, final) => (records, final.summary)) =
      (run block p' ops).map (fun (records, final) => (records, final.summary)) := by
  induction ops generalizing p p' with
  | nil => simp only [run, Except.map, summary]
  | cons op ops ih =>
    obtain ⟨noBuild, noLimit⟩ := schedule op (List.mem_cons_self ..)
    have same := stepRun_summary block noBuild noLimit summary
    simp only [run]
    generalize stepRun block p op = left at same ⊢
    generalize stepRun block p' op = right at same ⊢
    rcases left with err | ⟨record, next⟩ <;> rcases right with err' | ⟨record', next'⟩ <;>
      simp only [Except.map, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq] at same
    · cases same; rfl
    · cases same
    · cases same
    · obtain ⟨rfl, sameSummary⟩ := same
      have tail := ih next next' (fun op member => schedule op (List.mem_cons_of_mem _ member)) sameSummary
      simp only [bind, Except.bind]
      generalize run block next ops = left at tail ⊢
      generalize run block next' ops = right at tail ⊢
      rcases left with err | ⟨records, final⟩ <;> rcases right with err' | ⟨records', final'⟩ <;>
        simp only [Except.map, Except.ok.injEq, Except.error.injEq, Prod.mk.injEq] at tail
      · cases tail; rfl
      · cases tail
      · cases tail
      · obtain ⟨rfl, finalEq⟩ := tail
        simp only [Except.map, pure, Except.pure, finalEq]

/-- The streaming fold preserves the recording run's final prefix and its first failure. -/
theorem Body.run_prefix (block : BlockContext) (p : Jaune.Body.Prefix) (ops : List BodyOp) :
    (run block p ops).map Prod.snd = ops.foldlM (step block) p := by
  induction ops generalizing p with
  | nil => rfl
  | cons op ops ih =>
    rw [run, List.foldlM_cons, ← stepRun_prefix]
    rcases stepRun block p op with err | ⟨record, next⟩
    · rfl
    · change _ = ops.foldlM (step block) next
      rw [← ih next]
      simp only [bind, Except.bind]
      cases run block next ops <;> rfl

/-- Run the second part of a schedule from the prefix that the first part produced. -/
theorem Body.run_append (block : BlockContext) (p : Jaune.Body.Prefix) (xs ys : List BodyOp) :
    run block p (xs ++ ys) = (do
      let (left, mid) ← run block p xs
      let (right, final) ← run block mid ys
      pure (left ++ right, final)) := by
  induction xs generalizing p with
  | nil =>
    simp only [List.nil_append, run, bind, Except.bind]
    cases run block p ys <;> rfl
  | cons op xs ih =>
    rw [List.cons_append, run, run]
    rcases stepRun block p op with err | ⟨record, next⟩
    · rfl
    · simp only [bind, Except.bind]
      rw [ih next]
      rcases run block next xs with err | ⟨records, mid⟩
      · rfl
      · simp only [bind, Except.bind, pure, Except.pure]
        cases run block mid ys <;> rfl

/-- A recorded phase and the prefix consumed by the following phase. -/
structure BodyPhase where
  records : List OpRun
  final : Jaune.Body.Prefix

def BodyPhase.Ran (phase : BodyPhase) (block : BlockContext) (start : Jaune.Body.Prefix)
    (ops : List BodyOp) : Prop := Body.run block start ops = .ok (phase.records, phase.final)

def BodyPhase.roots (phase : BodyPhase) : List Root := phase.records.filterMap OpRun.enteredRoot

def BodyPhase.frames (phase : BodyPhase) : List Frame.Run.Kept := phase.roots.flatMap Root.frames

theorem Body.run_split {block start opsLeft opsRight records final}
    (accepted : run block start (opsLeft ++ opsRight) = .ok (records, final)) :
    ∃ left right : BodyPhase, left.Ran block start opsLeft ∧ right.Ran block left.final opsRight ∧
      records = left.records ++ right.records ∧ final = right.final := by
  rw [run_append] at accepted
  obtain ⟨⟨left, mid⟩, hleft, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨⟨right, finalRight⟩, hright, accepted⟩ := Except.bind_eq_ok accepted
  cases accepted
  exact ⟨⟨left, mid⟩, ⟨right, final⟩, hleft, hright, rfl, rfl⟩

theorem BodyPhase.exists_of_fold {block start ops final}
    (accepted : ops.foldlM (Body.step block) start = .ok final) :
    ∃ phase : BodyPhase, phase.Ran block start ops ∧ phase.final = final := by
  rw [← Body.run_prefix] at accepted
  cases execution : Body.run block start ops with
  | error => rw [execution] at accepted; cases accepted
  | ok pair =>
    rw [execution] at accepted
    exact ⟨⟨pair.1, pair.2⟩, execution, Except.ok.inj accepted⟩

def PreRoots (block : BlockContext) (state : State) (phase : BodyPhase) : Prop :=
  phase.Ran block (.init state) (Body.preOps block)

def RequestRoots (block : BlockContext) (index : Nat) (start : Jaune.Body.Prefix) (phase : BodyPhase) : Prop :=
  phase.Ran block start (Body.requestOps block index)

theorem exists_preRoots {block state final}
    (accepted : (Body.preOps block).foldlM (Body.step block) (.init state) = .ok final) :
    ∃ phase, PreRoots block state phase ∧ phase.final = final := BodyPhase.exists_of_fold accepted

theorem exists_requestRoots {block index start final}
    (accepted : (Body.requestOps block index).foldlM (Body.step block) start = .ok final) :
    ∃ phase, RequestRoots block index start phase ∧ phase.final = final := BodyPhase.exists_of_fold accepted

structure BodyRun where
  decoded : List Jaune.Transaction
  pre : BodyPhase
  transactions : BodyPhase
  withdrawals : BodyPhase
  requests : BodyPhase
  finish : BodyPhase

def BodyRun.records (run : BodyRun) : List OpRun :=
  run.pre.records ++ run.transactions.records ++ run.withdrawals.records ++ run.requests.records ++ run.finish.records

def BodyRun.roots (run : BodyRun) : List Root := run.records.filterMap OpRun.enteredRoot

def BodyRun.frames (run : BodyRun) : List Frame.Run.Kept := run.roots.flatMap Root.frames

/-- Every phase reads the previous phase's final prefix, for every configured fork. -/
structure BodyRoots (block : BlockContext) (state : State) (txs : List (Bytes ⊕ Jaune.Transaction))
    (ommers : List Header) (wds : List Withdrawal) (final : Jaune.Body.Prefix) (run : BodyRun) : Prop where
  decoded : txs.mapM (decodeTransaction block.rules) = .ok run.decoded
  pre : PreRoots block state run.pre
  transactions : run.transactions.Ran block run.pre.final (Jaune.Body.transactionOps run.decoded)
  withdrawals : run.withdrawals.Ran block run.transactions.final
    (Body.withdrawalOps block (run.decoded.length + 1) wds)
  requests : RequestRoots block (run.decoded.length + 1) run.withdrawals.final run.requests
  finish : run.finish.Ran block run.requests.final (Body.finishOps block ommers)
  final_eq : run.finish.final = final

theorem BodyRoots.of_run {block state txs decoded ommers wds records final}
    (decodedAll : txs.mapM (decodeTransaction block.rules) = .ok decoded)
    (executed : Body.run block (.init state) (Body.ops block decoded ommers wds) =
      .ok (records, final)) : ∃ run, BodyRoots block state txs ommers wds final run ∧ run.records = records := by
  rw [Body.ops, Body.postOps, List.append_assoc] at executed
  obtain ⟨pre, afterPre, hp, afterPreRun, recordsEq, finalEq⟩ := Body.run_split executed
  obtain ⟨txs, afterTxs, ht, afterTxsRun, txRecords, preFinal⟩ := Body.run_split afterPreRun
  obtain ⟨wds, afterWds, hw, afterWdsRun, wdRecords, txFinal⟩ := Body.run_split afterTxsRun
  obtain ⟨requests, finish, hq, hf, requestRecords, wdFinal⟩ := Body.run_split afterWdsRun
  exact ⟨⟨decoded, pre, txs, wds, requests, finish⟩,
    ⟨decodedAll, hp, ht, hw, hq, hf, (finalEq.trans (preFinal.trans (txFinal.trans wdFinal))).symm⟩,
    by simp only [BodyRun.records, recordsEq, txRecords, wdRecords, requestRecords, List.append_assoc]⟩

/-- The actual streaming importer is represented by the five ordered Checked phases. -/
theorem exists_bodyRoots {block state txs ommers wds final}
    (accepted : Body.importer block state txs ommers wds = .ok final) :
    ∃ run, BodyRoots block state txs ommers wds final run := by
  unfold Body.importer at accepted
  obtain ⟨decoded, hd, folded⟩ := Except.bind_eq_ok accepted
  obtain ⟨phase, executed, last⟩ := BodyPhase.exists_of_fold folded
  obtain ⟨run, body, _⟩ := BodyRoots.of_run hd executed
  exact ⟨run, last ▸ body⟩

/-- A block's recorded phases retain exactly its ordered roots and kept frames. -/
theorem BlockRun.exists_bodyRoots {fork parent block run}
    (executed : BlockRun.run fork parent block = .ok run) :
    ∃ body, BodyRoots run.context run.parent.state block.transactions block.ommers block.withdrawals
      run.final body ∧
      body.roots = run.roots ∧ body.frames = run.frames := by
  unfold BlockRun.run at executed
  obtain ⟨decoded, hd, executed⟩ := Except.bind_eq_ok executed
  obtain ⟨⟨ops, final⟩, hr, executed⟩ := Except.bind_eq_ok executed
  cases executed
  obtain ⟨body, roots, records⟩ := BodyRoots.of_run hd hr
  exact ⟨body, roots, congrArg (List.filterMap OpRun.enteredRoot) records,
    congrArg (fun xs => (xs.filterMap OpRun.enteredRoot).flatMap Root.frames) records⟩

theorem BlockRun.run_prefix (fork : Fork) (parent : BlockChain) (block : Block) :
    (BlockRun.run fork parent block).map BlockRun.final =
      Body.importer (initBlockContext fork parent block.header) parent.state block.transactions block.ommers
        block.withdrawals := by
  unfold BlockRun.run Body.importer
  dsimp only
  cases block.transactions.mapM (decodeTransaction (initBlockContext fork parent block.header).rules) with
  | error => rfl
  | ok decoded =>
    simp only [bind, Except.bind]
    rw [← Body.run_prefix]
    cases Body.run (initBlockContext fork parent block.header) (.init parent.state)
      (Body.ops (initBlockContext fork parent block.header) decoded block.ommers block.withdrawals) <;> rfl

/-- An accepted block has a Checked run whose final prefix supplied the accepted post-state. -/
theorem exists_blockRun {ε : Type} {embed : TransitionError → ε} {fork : Fork}
    {parent post : BlockChain} {block : Block} {ommers : Unit → Except ε Unit}
    (accepted : stateTransitionCoreE embed fork parent block ommers = .ok post) :
    ∃ run, BlockRun.run fork parent block = .ok run ∧ run.final.state = post.state := by
  unfold stateTransitionCoreE at accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  rw [← BlockRun.run_prefix] at accepted
  cases executed : BlockRun.run fork parent block with
  | error => rw [executed] at accepted; cases accepted
  | ok run =>
    rw [executed] at accepted
    simp only [Except.map, Except.mapError, bind, Except.bind] at accepted
    obtain ⟨_, _, committed⟩ := Except.bind_eq_ok accepted
    cases committed
    exact ⟨run, rfl, rfl⟩

/-- An accepted block with the Checked body run that produced its post-state. -/
structure KeptBlock where
  fork : Fork
  parent : BlockChain
  block : Block
  post : BlockChain
  run : BlockRun
  executed : BlockRun.run fork parent block = .ok run
  finalState : run.final.state = post.state

def KeptBlock.frames (block : KeptBlock) : List Frame.Run.Kept := block.run.frames

/-- The configured chain identity, fork lookup and typed transition all succeeded. -/
structure KeptStep (cfg : ChainConfig) (fork : Fork) (parent : BlockChain) (block : Block)
    (post : BlockChain) : Prop where
  chainId : cfg.checkChainId parent = .ok ()
  forkAt : cfg.forkAt block.header.number block.header.timestamp = .ok fork
  accepted : stateTransitionCoreE (Sum.inr (α := RulesLookupError)) fork parent block
    (fun _ => checkBlockOmmersScheduledE cfg fork.ruleSet parent block.header block.ommers) = .ok post

inductive KeptHistory (cfg : ChainConfig) (start : BlockChain) : List KeptBlock → BlockChain → Prop
  | refl : KeptHistory cfg start [] start
  | step {blocks : List KeptBlock} {last : KeptBlock} :
    KeptHistory cfg start blocks last.parent →
    KeptStep cfg last.fork last.parent last.block last.post →
    KeptHistory cfg start (blocks ++ [last]) last.post

def KeptHistory.frames (blocks : List KeptBlock) : List Frame.Run.Kept := blocks.flatMap KeptBlock.frames

theorem KeptHistory.frames_step (blocks : List KeptBlock) (last : KeptBlock) :
    KeptHistory.frames (blocks ++ [last]) = KeptHistory.frames blocks ++ last.frames := by
  simp [KeptHistory.frames]

theorem KeptStep.exists_block {cfg : ChainConfig} {fork parent block post}
    (checked : KeptStep cfg fork parent block post) :
    ∃ kept : KeptBlock, kept.fork = fork ∧ kept.parent = parent ∧ kept.block = block ∧ kept.post = post := by
  obtain ⟨run, executed, final⟩ := exists_blockRun checked.accepted
  exact ⟨⟨fork, parent, block, post, run, executed, final⟩, rfl, rfl, rfl, rfl⟩

theorem KeptHistory.exists_snoc {cfg : ChainConfig} {start parent post fork block blocks}
    (history : KeptHistory cfg start blocks parent) (checked : KeptStep cfg fork parent block post) :
    ∃ kept, kept.block = block ∧ KeptHistory cfg start (blocks ++ [kept]) post := by
  obtain ⟨run, executed, final⟩ := exists_blockRun checked.accepted
  exact ⟨⟨fork, parent, block, post, run, executed, final⟩, rfl, .step history checked⟩

/-- A successful sequence of configured steps provides all blocks in input order, across forks. -/
theorem KeptHistory.of_fold {ε : Type} {cfg : ChainConfig} {start current post : BlockChain}
    {blocks : List KeptBlock} {advance : BlockChain → Block → Except ε BlockChain}
    (checked : ∀ {parent block next}, advance parent block = .ok next → ∃ fork, KeptStep cfg fork parent block next)
    (prior : KeptHistory cfg start blocks current) (inputs : List Block)
    (accepted : inputs.foldlM advance current = .ok post) :
    ∃ suffix, suffix.map KeptBlock.block = inputs ∧ KeptHistory cfg start (blocks ++ suffix) post := by
  induction inputs generalizing current blocks with
  | nil =>
    cases accepted
    exact ⟨[], rfl, by simpa using prior⟩
  | cons first rest ih =>
    obtain ⟨next, entered, later⟩ := Except.bind_eq_ok accepted
    obtain ⟨fork, step⟩ := checked entered
    obtain ⟨kept, inputEq, history⟩ := prior.exists_snoc step
    obtain ⟨suffix, inputRest, full⟩ := ih history later
    exact ⟨kept :: suffix, by simp [inputEq, inputRest],
      by simpa only [List.append_assoc, List.singleton_append] using full⟩

end Jaune.Checked
