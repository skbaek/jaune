import Jaune.FrameRun.CheckedOrder
import Jaune.FrameRun.CheckedAdequacy
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
def TransactionRoots (benv : Benv) (input : BlockOutput) (tx : Jaune.Transaction) (index : Nat)
    (state : State) (output : BlockOutput) (sender : Address) (roots : List Root) : Prop :=
  ∃ run, Transaction.run benv input tx index = .ok (run, output) ∧ run.state = state ∧
    run.sender = sender ∧ MessageRoots run.entry run.message roots

theorem Transaction.run_messageRoots {benv input tx index run output}
    (accepted : Transaction.run benv input tx index = .ok (run, output)) :
    MessageRoots run.entry run.message run.message.enteredRoot.toList := by
  unfold Transaction.run at accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨prepared, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨message, executed, settled⟩ := Except.bind_eq_ok accepted
  unfold Transaction.settleRun at settled
  obtain ⟨_, _, settled⟩ := Except.bind_eq_ok settled
  cases settled
  exact ⟨Except.mapError_eq_ok_iff.mp executed, rfl⟩

theorem exists_transactionRoots {benv input tx index state output}
    (accepted : (Transaction.run benv input tx index).map (fun (run, next) => (run.state, next)) =
      .ok (state, output)) : ∃ sender roots, TransactionRoots benv input tx index state output sender roots := by
  cases executed : Transaction.run benv input tx index with
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

/-- The streaming fold preserves the recording run's final prefix and its first failure. -/
theorem Body.run_prefix (benv : Benv) (p : Jaune.Body.Prefix) (ops : List BodyOp) :
    (run benv p ops).map Prod.snd = ops.foldlM (step benv) p := by
  induction ops generalizing p with
  | nil => rfl
  | cons op ops ih =>
    rw [run, List.foldlM_cons, ← stepRun_prefix]
    rcases stepRun benv p op with err | ⟨record, next⟩
    · rfl
    · change _ = ops.foldlM (step benv) next
      rw [← ih next]
      simp only [bind, Except.bind]
      cases run benv next ops <;> rfl

/-- Run the second part of a schedule from the prefix that the first part produced. -/
theorem Body.run_append (benv : Benv) (p : Jaune.Body.Prefix) (xs ys : List BodyOp) :
    run benv p (xs ++ ys) = (do
      let (left, mid) ← run benv p xs
      let (right, final) ← run benv mid ys
      pure (left ++ right, final)) := by
  induction xs generalizing p with
  | nil =>
    simp only [List.nil_append, run, bind, Except.bind]
    cases run benv p ys <;> rfl
  | cons op xs ih =>
    rw [List.cons_append, run, run]
    rcases stepRun benv p op with err | ⟨record, next⟩
    · rfl
    · simp only [bind, Except.bind]
      rw [ih next]
      rcases run benv next xs with err | ⟨records, mid⟩
      · rfl
      · simp only [bind, Except.bind, pure, Except.pure]
        cases run benv mid ys <;> rfl

/-- A recorded phase and the prefix consumed by the following phase. -/
structure BodyPhase where
  records : List OpRun
  final : Jaune.Body.Prefix

def BodyPhase.Ran (phase : BodyPhase) (benv : Benv) (start : Jaune.Body.Prefix)
    (ops : List BodyOp) : Prop := Body.run benv start ops = .ok (phase.records, phase.final)

def BodyPhase.roots (phase : BodyPhase) : List Root := phase.records.filterMap OpRun.enteredRoot

def BodyPhase.frames (phase : BodyPhase) : List Frame.Run.Kept := phase.roots.flatMap Root.frames

theorem Body.run_split {benv start opsLeft opsRight records final}
    (accepted : run benv start (opsLeft ++ opsRight) = .ok (records, final)) :
    ∃ left right : BodyPhase, left.Ran benv start opsLeft ∧ right.Ran benv left.final opsRight ∧
      records = left.records ++ right.records ∧ final = right.final := by
  rw [run_append] at accepted
  obtain ⟨⟨left, mid⟩, hleft, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨⟨right, finalRight⟩, hright, accepted⟩ := Except.bind_eq_ok accepted
  cases accepted
  exact ⟨⟨left, mid⟩, ⟨right, final⟩, hleft, hright, rfl, rfl⟩

theorem BodyPhase.exists_of_fold {benv start ops final}
    (accepted : ops.foldlM (Body.step benv) start = .ok final) :
    ∃ phase : BodyPhase, phase.Ran benv start ops ∧ phase.final = final := by
  rw [← Body.run_prefix] at accepted
  cases execution : Body.run benv start ops with
  | error => rw [execution] at accepted; cases accepted
  | ok pair =>
    rw [execution] at accepted
    exact ⟨⟨pair.1, pair.2⟩, execution, Except.ok.inj accepted⟩

def Body.withdrawalOps (benv : Benv) (index : Nat) (withdrawals : List Withdrawal) : List BodyOp :=
  if benv.stat.rules.header.withdrawalsRoot then [.withdrawals withdrawals index] else []

/-- Deposit requests follow the receipts, followed by configured request-producing calls. -/
def Body.requestOps (benv : Benv) (index : Nat) : List BodyOp :=
  if benv.stat.rules.header.requestsHash then
    .depositRequests :: benv.stat.rules.requests.map fun ⟨kind, address⟩ => .requestCall kind address index
  else []

def Body.finishOps (benv : Benv) (ommers : List Header) : List BodyOp :=
  (match benv.stat.rules.proofOfWork with
   | none => []
   | some pow =>
     [.rewards benv.stat.coinbase (pow.blockReward + ommers.length * (pow.blockReward / 32))
       (ommers.map fun ommer =>
         (ommer.coinbase, (8 + ommer.number - benv.stat.number) * pow.blockReward / 8))]) ++
  [.buildAccessList, .checkAccessListLimit]

theorem Body.postOps_phases (benv : Benv) (n : Nat) (ommers : List Header) (wds : List Withdrawal) :
    Jaune.Body.postOps benv n ommers wds = Body.withdrawalOps benv (n + 1) wds ++
      (Body.requestOps benv (n + 1) ++ Body.finishOps benv ommers) := by
  simp only [Jaune.Body.postOps, Body.withdrawalOps, Body.requestOps, Body.finishOps, List.append_assoc]
  rfl

def PreRoots (benv : Benv) (phase : BodyPhase) : Prop :=
  phase.Ran benv (.init benv.state) (Jaune.Body.preOps benv)

def RequestRoots (benv : Benv) (index : Nat) (start : Jaune.Body.Prefix) (phase : BodyPhase) : Prop :=
  phase.Ran benv start (Body.requestOps benv index)

theorem exists_preRoots {benv final}
    (accepted : (Jaune.Body.preOps benv).foldlM (Body.step benv) (.init benv.state) = .ok final) :
    ∃ phase, PreRoots benv phase ∧ phase.final = final := BodyPhase.exists_of_fold accepted

theorem exists_requestRoots {benv index start final}
    (accepted : (Body.requestOps benv index).foldlM (Body.step benv) start = .ok final) :
    ∃ phase, RequestRoots benv index start phase ∧ phase.final = final := BodyPhase.exists_of_fold accepted

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
structure BodyRoots (benv : Benv) (txs : List (Bytes ⊕ Jaune.Transaction)) (ommers : List Header)
    (wds : List Withdrawal) (final : Jaune.Body.Prefix) (run : BodyRun) : Prop where
  decoded : txs.mapM (decodeTransaction benv.stat.rules) = .ok run.decoded
  pre : PreRoots benv run.pre
  transactions : run.transactions.Ran benv run.pre.final (Jaune.Body.transactionOps run.decoded)
  withdrawals : run.withdrawals.Ran benv run.transactions.final
    (Body.withdrawalOps benv (run.decoded.length + 1) wds)
  requests : RequestRoots benv (run.decoded.length + 1) run.withdrawals.final run.requests
  finish : run.finish.Ran benv run.requests.final (Body.finishOps benv ommers)
  final_eq : run.finish.final = final

theorem BodyRoots.of_run {benv txs decoded ommers wds records final}
    (decodedAll : txs.mapM (decodeTransaction benv.stat.rules) = .ok decoded)
    (executed : Body.run benv (.init benv.state) (Jaune.Body.ops benv decoded ommers wds) =
      .ok (records, final)) : ∃ run, BodyRoots benv txs ommers wds final run ∧ run.records = records := by
  rw [Jaune.Body.ops, Body.postOps_phases, List.append_assoc] at executed
  obtain ⟨pre, afterPre, hp, afterPreRun, recordsEq, finalEq⟩ := Body.run_split executed
  obtain ⟨txs, afterTxs, ht, afterTxsRun, txRecords, preFinal⟩ := Body.run_split afterPreRun
  obtain ⟨wds, afterWds, hw, afterWdsRun, wdRecords, txFinal⟩ := Body.run_split afterTxsRun
  obtain ⟨requests, finish, hq, hf, requestRecords, wdFinal⟩ := Body.run_split afterWdsRun
  exact ⟨⟨decoded, pre, txs, wds, requests, finish⟩,
    ⟨decodedAll, hp, ht, hw, hq, hf, (finalEq.trans (preFinal.trans (txFinal.trans wdFinal))).symm⟩,
    by simp only [BodyRun.records, recordsEq, txRecords, wdRecords, requestRecords, List.append_assoc]⟩

/-- The actual streaming importer is represented by the five ordered Checked phases. -/
theorem exists_bodyRoots {benv txs ommers wds final}
    (accepted : Body.importer benv txs ommers wds = .ok final) :
    ∃ run, BodyRoots benv txs ommers wds final run := by
  unfold Body.importer at accepted
  obtain ⟨decoded, hd, folded⟩ := Except.bind_eq_ok accepted
  obtain ⟨phase, executed, last⟩ := BodyPhase.exists_of_fold folded
  obtain ⟨run, body, _⟩ := BodyRoots.of_run hd executed
  exact ⟨run, last ▸ body⟩

/-- A block's recorded phases retain exactly its ordered roots and kept frames. -/
theorem BlockRun.exists_bodyRoots {fork parent block run}
    (executed : BlockRun.run fork parent block = .ok run) :
    ∃ body, BodyRoots run.benv block.transactions block.ommers block.withdrawals run.final body ∧
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
      Body.importer (initBlockEnvironment fork parent block.header) block.transactions block.ommers block.withdrawals := by
  unfold BlockRun.run Body.importer
  dsimp only
  cases block.transactions.mapM (decodeTransaction (initBlockEnvironment fork parent block.header).stat.rules) with
  | error => rfl
  | ok decoded =>
    simp only [bind, Except.bind]
    rw [← Body.run_prefix]
    cases Body.run (initBlockEnvironment fork parent block.header)
      (.init (initBlockEnvironment fork parent block.header).state)
      (Jaune.Body.ops (initBlockEnvironment fork parent block.header) decoded block.ommers block.withdrawals) <;> rfl

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
