import Jaune.FrameRun.Calls
import Jaune.MessageCall.SpawnFacts
import Jaune.MessageCall.PartsGas

/-!
# Entered frames (goal `jaune-shape-and-names-v1`, G2b, U102)

`Frame.Running.Entered` names a running frame exactly as the semantics enters one: at program
counter zero, with an empty stack, memory and return buffer, calldata short enough for
`CALLDATASIZE` to report its length, and a gas measure below the block gas limit cap that header
validation enforces (`checkGasLimit`'s `gasLimitMaximum`, `2 ^ 63`).

Entering a spawned child gives an entered frame (`step_spawn_enter_entered`), every frame start of
a run whose root is entered is entered (`visits_entered`), and so is the run of every call
(`calls_ran_entered`).
-/

namespace Jaune

open Jaune

/-- A running frame exactly as the semantics enters one. -/
structure Frame.Running.Entered (r : Frame.Running) : Prop where
  pc : r.pc = 0
  stack : r.state.machine.stack = []
  memory : r.state.machine.memory = .empty
  returnData : r.state.machine.returnData = []
  /-- The calldata length is a word, as `CALLDATASIZE` reports it. -/
  calldata : r.context.calldata.length < 2 ^ 256
  /-- The gas measure is below the cap header validation puts on a block's gas limit. -/
  gas : r.state.machine.gasMeasure < 2 ^ 63

theorem Frame.Running.Entered.gasLeft_lt {r : Frame.Running} (h : r.Entered) :
    r.state.machine.gasLeft < 2 ^ 63 :=
  Nat.lt_of_le_of_lt (by simp only [Machine.gasMeasure]; omega) h.gas

/-- Entering from a start state runs at program counter zero, under the message's context, with
the start state's machine. -/
theorem Frame.enterWith_run {f : Frame} {start : Frame.State} {r : Frame.Running}
    (h : enterWith f start = .run r) :
    r.pc = 0 ∧ r.context = f.message.context ∧ r.state.machine = start.machine := by
  unfold enterWith at h
  rcases ht : f.message.transfer f.enteredWorld with fault | world <;> simp only [ht] at h
  · cases h
  · rcases hc : f.message.codeAddress with _ | address <;> simp only [hc] at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · split at h
      · cases h
      · cases h; exact ⟨rfl, rfl, rfl⟩

/-- Entering a frame gives an entered frame, given the message's calldata and gas bounds. -/
theorem Frame.enter_run_entered {f : Frame} {r : Frame.Running} (h : enter f = .run r)
    (calldata : f.message.context.calldata.length < 2 ^ 256) (gas : f.message.gas < 2 ^ 63) :
    r.Entered := by
  obtain ⟨hpc, hctx, hm⟩ := Frame.enterWith_run (f := f) (start := f.startState) h
  refine ⟨hpc, ?_, ?_, ?_, hctx ▸ calldata, (enter_run_gasMeasure h).symm ▸ gas⟩ <;>
    rw [hm] <;> rfl

/-! ### The calldata a spawned child receives -/

private def CalldataPost : MessageOp.Outcome → Prop
  | .done _ => True
  | .spawn f _ => f.message.context.calldata.length < 2 ^ 256

private theorem callData {ctx s gas value caller target addr transfer static ii il oi ol code disabled f p}
    (h : prepareCall.step ctx s gas value caller target addr transfer static ii il oi ol code disabled =
      .spawn f p) (hl : il < 2 ^ 256) : f.message.context.calldata.length < 2 ^ 256 := by
  rw [prepareCall.step_spawn_data_length h]; exact hl

private theorem callStateData {ctx rules s gas reservoir value caller target addr transfer static
    ii il oi ol code disabled charged insufficient f p}
    (h : prepareCallAmsterdam.step ctx rules s gas reservoir value caller target addr transfer static ii il oi ol
      code disabled charged insufficient = .spawn f p) (hl : il < 2 ^ 256) :
    f.message.context.calldata.length < 2 ^ 256 := by
  unfold prepareCallAmsterdam.step at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    repeat' split at h
    all_goals cases h
  · cases h
    change (Jaune.Array.sliceD _ _ _ _).length < _
    rw [memory_slice_length]; exact hl

private theorem createData {ctx s value a i len f p}
    (h : prepareCreate.step ctx s value a i len = .spawn f p) :
    f.message.context.calldata.length < 2 ^ 256 := by
  simp only [prepareCreate.step, bind, Except.bind, pure, Except.pure, Except.assert,
    Frame.State.assertDynamic] at h
  repeat' split at h
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h; simp [createMessage]

private theorem createStateData {ctx rules s value a i len f p}
    (h : prepareCreateAmsterdam.step ctx rules s value a i len = .spawn f p) :
    f.message.context.calldata.length < 2 ^ 256 := by
  simp only [prepareCreateAmsterdam.step, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h; simp [createMessage]

private theorem walkAny {α β : Type} {P : β → Prop} {x : Except (ExceptionalHalt × Frame.State) α}
    {k : α → Except (ExceptionalHalt × Frame.State) β}
    (h : ∀ a, Walk (fun _ => True) P (k a)) : Walk (fun _ => True) P (x >>= k) := by
  cases x with
  | error e => trivial
  | ok a => exact h a

private theorem walkPopToNat {β : Type} {P : β → Prop} {s : Frame.State}
    {k : Nat × Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (h : ∀ a s', a < 2 ^ 256 → Walk (fun _ => True) P (k (a, s'))) :
    Walk (fun _ => True) P (s.popToNat >>= k) := by
  unfold Frame.State.popToNat Frame.State.liftMachineValue Machine.popToNat
  cases hp : s.machine.pop with
  | error e => trivial
  | ok p => exact h _ _ (U256.toNat_lt p.1)

private theorem ofExcept_calldataPost {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hx : Walk (fun _ => True) CalldataPost x) : CalldataPost (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error p => trivial
  | ok o => exact hx

private theorem tail_calldataPost {o : MessageOp.Outcome}
    (h : ∀ f p, o = .spawn f p → f.message.context.calldata.length < 2 ^ 256) : CalldataPost o := by
  cases o with
  | done r => trivial
  | spawn f p => exact h f p rfl

private theorem purePost (o : MessageOp.Outcome) (h : CalldataPost o) :
    Walk (ε := ExceptionalHalt) (fun _ => True) CalldataPost (pure o) := h

local macro "data_tail" : tactic => `(tactic|
  first | (apply tail_calldataPost; exact fun _ _ h => callData h (by assumption))
        | (apply tail_calldataPost; exact fun _ _ h => callStateData h (by assumption))
        | (apply tail_calldataPost; exact fun _ _ h => createData h)
        | (apply tail_calldataPost; exact fun _ _ h => createStateData h))

local macro "data_walk" : tactic => `(tactic| repeat' (first
  | (with_reducible apply walkPopToNat; intro _ _ _; try dsimp only)
  | (with_reducible apply walkAny; intro a; try (guard_hyp a : _ × _; rcases a with ⟨_, _⟩); try dsimp only)
  | (apply purePost; first | exact True.intro | data_tail)
  | (apply (Walk.error_iff _).mpr; trivial)
  | data_tail
  | split
  | trivial))

private theorem op_calldataPost (ctx : CallContext) (s : Frame.State) (op : Jaune.MessageOp) :
    CalldataPost (MessageOp.step ctx s op) := by
  cases op <;> simp only [MessageOp.step]
  all_goals repeat' split
  all_goals apply ofExcept_calldataPost; data_walk

/-- A spawned child's calldata length is a word. -/
theorem step_spawn_calldata {r : Frame.Running} {child : Frame} {p : Pending} {pc : Nat}
    (h : step r = .ok (.spawn child p pc)) : child.message.context.calldata.length < 2 ^ 256 := by
  obtain ⟨x, hx⟩ := step_spawn_message h
  have post := op_calldataPost r.context r.state x
  rw [hx] at post
  exact post

/-- Entering a spawned child gives an entered frame, given the caller's gas bound. -/
theorem step_spawn_enter_entered {r cr : Frame.Running} {child : Frame} {p : Pending} {pc : Nat}
    (hs : step r = .ok (.spawn child p pc)) (he : enter child = .run cr)
    (gas : r.state.machine.gasMeasure < 2 ^ 63) : cr.Entered :=
  Frame.enter_run_entered he (step_spawn_calldata hs)
    (Nat.lt_of_le_of_lt (Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
      (step_gasBound r _ hs).1)) gas)

/-! ### Propagation over a run -/

namespace Frame.Run

private theorem eventsFrom_entered {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter)
    (gas : r.state.machine.gasMeasure < 2 ^ 63) (start : frameStart = true → r.Entered) :
    ∀ v, Event.visit v ∈ eventsFrom t path kept frameStart enclosing counter →
      v.node.start.state.machine.gasMeasure < 2 ^ 63 ∧ (v.frameStart = true → v.node.start.Entered) := by
  intro v hv
  cases t with
  | halt =>
    simp only [eventsFrom, List.mem_singleton, Event.visit.injEq] at hv
    subst hv; exact ⟨gas, start⟩
  | callDoneEnd =>
    simp only [eventsFrom, List.mem_singleton, Event.visit.injEq] at hv
    subst hv; exact ⟨gas, start⟩
  | next hs rest =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ⟨gas, start⟩
    · exact eventsFrom_entered rest _ _ _ _ _
        ((Frame.Running.step_next_gasMeasure_lt hs).trans gas) (fun h => by cases h) v hv
  | callDone hs he hr rest =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ⟨gas, start⟩
    · exact eventsFrom_entered rest _ _ _ _ _
        ((Frame.Running.call_gasMeasure_lt hs (.done he) hr).trans gas) (fun h => by cases h) v hv
  | callRan hs he child hr rest =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ⟨gas, start⟩
    · have hcr := step_spawn_enter_entered hs he gas
      rcases List.mem_append.mp hv with hv | hv
      · exact eventsFrom_entered child _ _ _ _ _ hcr.gas (fun _ => hcr) v hv
      · rcases List.mem_cons.mp hv with hv | hv
        · cases hv
        · have hout := (exec_iff ..).mp ⟨child⟩
          have hlt := Frame.Running.call_gasMeasure_lt hs (.ran he) (by simpa only [hout] using hr)
          exact eventsFrom_entered rest _ _ _ _ _ (hlt.trans gas) (fun h => by cases h) v hv
  | callRanEnd hs he child hr =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ⟨gas, start⟩
    · have hcr := step_spawn_enter_entered hs he gas
      rcases List.mem_append.mp hv with hv | hv
      · exact eventsFrom_entered child _ _ _ _ _ hcr.gas (fun _ => hcr) v hv
      · simp at hv
termination_by sizeOf t

/-- Every frame start of a run whose root is entered is entered. -/
theorem visits_entered {r out} (t : Frame.Run r (.exit out)) (root : r.Entered) {v : Visit}
    (hv : v ∈ visits t) (start : v.frameStart = true) : v.node.start.Entered := by
  obtain ⟨e, he, hx⟩ := List.mem_filterMap.mp hv
  cases e with
  | exit _ => cases hx
  | visit w =>
    cases hx
    exact (eventsFrom_entered t _ _ _ _ _ root.gas (fun _ => root) _ he).2 start

/-- Every visit of a run whose root is entered keeps the root's gas bound. -/
theorem visits_gasMeasure_lt {r out} (t : Frame.Run r (.exit out)) (root : r.Entered) {v : Visit}
    (hv : v ∈ visits t) : v.node.start.state.machine.gasMeasure < 2 ^ 63 := by
  obtain ⟨e, he, hx⟩ := List.mem_filterMap.mp hv
  cases e with
  | exit _ => cases hx
  | visit w =>
    cases hx
    exact (eventsFrom_entered t _ _ _ _ _ root.gas (fun _ => root) _ he).1

/-- Every frame of a run whose root is entered starts entered. -/
theorem frames_entered {r out} (t : Frame.Run r (.exit out)) (root : r.Entered) {n : Node}
    (hn : n ∈ frames t) : n.start.Entered := by
  simp only [frames, List.mem_map, List.mem_filter] at hn
  obtain ⟨v, ⟨hv, hs⟩, rfl⟩ := hn
  exact visits_entered t root hv hs

/-- Combined: in a run whose root is entered, every call that ran started its child entered. A
callee specification stated over entered frames therefore applies at every call site. -/
theorem calls_ran_entered {r out} (t : Frame.Run r (.exit out)) (root : r.Entered) {c : Call} {n : Node}
    (hc : c ∈ calls t) (hran : c.ran = some n) : n.start.Entered := by
  apply frames_entered t root
  rw [frames_eq_calls]
  exact List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨c, hc, hran⟩)

/-- Every call's caller was at a state within the root's gas bound. -/
theorem calls_site_gasMeasure_lt {r out} (t : Frame.Run r (.exit out)) (root : r.Entered) {c : Call}
    (hc : c ∈ calls t) : c.site.node.start.state.machine.gasMeasure < 2 ^ 63 :=
  visits_gasMeasure_lt t root (calls_site_mem hc)

end Frame.Run

end Jaune
