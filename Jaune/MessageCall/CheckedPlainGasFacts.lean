import Jaune.CheckedSufficiencyWalk
import Jaune.Sufficiency
import Jaune.Instructions.WordFacts
import Jaune.Instructions.ShuffleFacts
import Jaune.Instructions.LogFacts
import Jaune.Instructions.MemoryFacts
import Jaune.Instructions.ReadFacts
import Jaune.Instructions.StoreFacts

/-! Gas bounds for the plain instructions over the lifetime-grouped state. A successful
step strictly decreases the machine's measure. An exceptional halt stays within the bound
supplied by the caller. -/

namespace Jaune.Checked

open Jaune

private abbrev PlainGas (s : Frame.State) (n : Nat) :=
  Walk (ε := ExceptionalHalt) (α := Frame.State) (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < s.machine.gasMeasure)

/-! ### One gas walk per family (S4)

Each family's step either halts within the input's measure or continues strictly below it, given
that the row's charge is positive; the table lemmas say which rows have a positive charge. -/

private theorem plainGas_of {s : Frame.State} {n : Nat}
    {x : Except (ExceptionalHalt × Frame.State) Frame.State} (h : s.machine.gasMeasure ≤ n)
    (law : Walk (·.machine.gasMeasure ≤ s.machine.gasMeasure)
      (·.machine.gasMeasure < s.machine.gasMeasure) x) : PlainGas s n x :=
  Walk.mono' law (fun _ ht => ht.trans h) (fun _ ht => ht)

private theorem liftMachine_law {s : Frame.State}
    {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    (herr : ∀ e out, core s.machine = .error (e, out) → out.gasMeasure ≤ s.machine.gasMeasure)
    (hok : ∀ out, core s.machine = .ok out → out.gasMeasure < s.machine.gasMeasure) :
    Walk (·.machine.gasMeasure ≤ s.machine.gasMeasure)
      (·.machine.gasMeasure < s.machine.gasMeasure) (s.liftMachine core) := by
  unfold Frame.State.liftMachine
  split
  · rename_i e m he; exact herr _ _ he
  · rename_i m he; exact hok _ he

theorem WordRow.run_gas (row : WordRow) (hpos : ∀ args, 0 < row.cost args) (x : Frame.Running)
    {n : Nat} (h : x.state.machine.gasMeasure ≤ n) : PlainGas x.state n ((Family.word row).run x) := by
  apply plainGas_of h
  apply liftMachine_law
  · intro e out he
    have hl := WordRow.step_gasMeasure_le row x.context.block.rules.opcodes ⟨x.pc, x.context⟩
      x.state.machine
    rw [he] at hl
    exact hl
  · intro out he
    exact WordRow.step_gasMeasure_lt_of_ok hpos he

theorem ShuffleRow.run_gas (row : ShuffleRow) (hpos : 0 < row.cost) (x : Frame.Running)
    {n : Nat} (h : x.state.machine.gasMeasure ≤ n) :
    PlainGas x.state n ((Family.shuffle row).run x) := by
  apply plainGas_of h
  apply liftMachine_law
  · intro e out he
    have hf := ShuffleRow.step_frame row x.context.block.rules.opcodes x.state.machine
    rw [he] at hf
    obtain ⟨_, _, hg, rfl⟩ := hf
    simp only [Machine.gasMeasure]
    omega
  · intro out he
    exact ShuffleRow.step_gasMeasure_lt_of_ok hpos he

theorem MemoryRow.run_gas (row : MemoryRow) (hpos : ∀ args, 0 < row.base args) (x : Frame.Running)
    {n : Nat} (h : x.state.machine.gasMeasure ≤ n) :
    PlainGas x.state n ((Family.memory row).run x) := by
  apply plainGas_of h
  apply liftMachine_law
  · intro e out he
    rcases MemoryRow.step_error he with ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ |
      ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ <;>
      simp only [Machine.gasMeasure] <;> omega
  · intro out he
    obtain ⟨_, args, rest, pushed, _, hg, _, _, hsg, _⟩ := MemoryRow.step_ok he
    have := hpos args
    simp only [Machine.gasMeasure, hsg]
    omega

theorem LogRow.run_gas (row : LogRow) (hpos : 0 < row.base) (x : Frame.Running)
    {n : Nat} (h : x.state.machine.gasMeasure ≤ n) : PlainGas x.state n ((Family.log row).run x) := by
  apply plainGas_of h
  have hf := LogRow.step_frame row x.context x.state.machine
  show Walk _ _ (x.state.liftLog (row.step x.context x.state.machine))
  unfold Frame.State.liftLog
  split <;> rename_i he <;> rw [he] at hf
  · obtain ⟨hg, hsg, _⟩ := hf
    show Machine.gasMeasure _ ≤ _
    simp only [Frame.State.withMachine_machine, Machine.gasMeasure, hsg]
    omega
  · exact LogRow.step_gasMeasure_lt_of_ok hpos he

private theorem gcases {α : Type} {H : Machine → Prop} {P : α → Prop}
    {x : Except (ExceptionalHalt × Machine) α}
    (h : MWalk H P x) : (∀ e m, x = .error (e, m) → H m) ∧ (∀ a, x = .ok a → P a) := by
  constructor
  · intro e m he; subst he; exact h
  · intro a ha; subst ha; exact h

/-- A Read step halts within the measure and, at a positive price, continues below it. -/
private def TouchGas {τ : Type} (g : Nat) : Except (ExceptionalHalt × Machine × τ) (Machine × τ) → Prop
  | .error (_, m, _) => m.gasMeasure ≤ g
  | .ok (m, _) => m.gasMeasure < g

private theorem ReadTarget.pop_gas (t : ReadTarget) (m : Machine) :
    MWalk (ε := ExceptionalHalt) (·.gasMeasure ≤ m.gasMeasure)
      (fun p => p.2.gasMeasure = m.gasMeasure) (t.pop m) := by
  cases t with
  | account => exact Machine.popToAddress_gas (Nat.le_refl _)
  | slot => exact Machine.pop_gas (Nat.le_refl _)
  | transient => exact Machine.pop_gas (Nat.le_refl _)
  | recipient => rfl

private theorem ReadRow.step_gas (row : ReadRow) (rules : ForkRules) (ctx : CallContext)
    (v : ReadView) (m : Machine) (hpos : ∀ key, 0 < (row.price.quote rules ctx v key).1) :
    TouchGas m.gasMeasure (row.step rules ctx v m) := by
  rcases row with ⟨avail, target, price, result⟩
  unfold ReadRow.step
  dsimp only
  split
  · exact Nat.le_refl _
  · have hpop := gcases (ReadTarget.pop_gas target m)
    split
    · rename_i e m' hp; exact hpop.1 _ _ hp
    · rename_i key m₁ hp
      have e₁ : m₁.gasMeasure = m.gasMeasure := hpop.2 _ hp
      have hp₀ : 0 < (price.quote rules ctx v key).1 := hpos key
      cases result with
      | push f =>
        simp only [ReadResult.finish]
        have hc := gcases (Machine.chargeGas_gas (price.quote rules ctx v key).1 (Nat.le_refl m₁.gasMeasure))
        split
        · rename_i e m' he; exact (hc.1 _ _ he).trans e₁.le
        · rename_i m₂ he
          have e₂ : m₂.gasMeasure + _ = m₁.gasMeasure := hc.2 _ he
          have hq := gcases (Machine.push_gas (f ctx v.world key) (Nat.le_refl m₂.gasMeasure))
          split
          · rename_i e m' he'
            have := hq.1 _ _ he'
            show Machine.gasMeasure _ ≤ _
            omega
          · rename_i m₃ he'
            have := hq.2 _ he'
            show Machine.gasMeasure _ < _
            omega
      | copyCode perWord =>
        simp only [ReadResult.finish]
        have p1 := gcases (Machine.popToNat_gas (Nat.le_refl m₁.gasMeasure))
        split
        · rename_i e m' he; exact (p1.1 _ _ he).trans e₁.le
        · rename_i d m₂ he
          have e₂ : m₂.gasMeasure = m₁.gasMeasure := p1.2 _ he
          have p2 := gcases (Machine.popToNat_gas (Nat.le_refl m₂.gasMeasure))
          split
          · rename_i e m' he'; exact ((p2.1 _ _ he').trans e₂.le).trans e₁.le
          · rename_i o m₃ he'
            have e₃ : m₃.gasMeasure = m₂.gasMeasure := p2.2 _ he'
            have p3 := gcases (Machine.popToNat_gas (Nat.le_refl m₃.gasMeasure))
            split
            · rename_i e m' he''
              exact (((p3.1 _ _ he'').trans e₃.le).trans e₂.le).trans e₁.le
            · rename_i k m₄ he''
              have e₄ : m₄.gasMeasure = m₃.gasMeasure := p3.2 _ he''
              split
              · rename_i e m' h5
                have := (gcases (Machine.chargeGas_gas _ (Nat.le_refl m₄.gasMeasure))).1 _ _ h5
                show Machine.gasMeasure _ ≤ _
                omega
              · rename_i m₅ h5
                have := (gcases (Machine.chargeGas_gas _ (Nat.le_refl m₄.gasMeasure))).2 _ h5
                show Machine.gasMeasure _ < _
                simp only [Machine.memWrite_gasMeasure]
                omega

private theorem quote_account_pos (warm cold : ForkRules → Nat) (flat : ForkRules → FlatAccessGas → Nat)
    (rules : ForkRules) (ctx : CallContext) (v : ReadView) (a : Address)
    (hw : 0 < warm rules) (hc : 0 < cold rules) (hf : ∀ g, rules.access = .flat g → 0 < flat rules g) :
    0 < ((ReadPrice.account warm cold flat).quote rules ctx v a).1 := by
  simp only [ReadPrice.quote]
  split
  · split <;> assumption
  · exact hf _ ‹_›

private theorem quote_slot_pos (warm cold : ForkRules → Nat) (flat : ForkRules → FlatAccessGas → Nat)
    (rules : ForkRules) (ctx : CallContext) (v : ReadView) (k : U256)
    (hw : 0 < warm rules) (hc : 0 < cold rules) (hf : ∀ g, rules.access = .flat g → 0 < flat rules g) :
    0 < ((ReadPrice.slot warm cold flat).quote rules ctx v k).1 := by
  simp only [ReadPrice.quote]
  split
  · split <;> assumption
  · exact hf _ ‹_›

/-- Under valid rules every Read row's quoted price is positive. -/
private theorem readRow?_price_pos {op : Jaune.PlainOp} {row : ReadRow}
    (hrow : PlainOp.readRow? op = some row) (ctx : CallContext) (v : ReadView) (key : row.target.Key) :
    0 < (row.price.quote ctx.block.rules ctx v key).1 := by
  have valid := BenvStat.rules_valid ctx.block
  have cold := valid.gas.1
  cases op <;> simp only [PlainOp.readRow?, PlainOp.family, Option.some.injEq, reduceCtorEq] at hrow <;>
    subst hrow
  case balance | extcodesize | extcodecopy | extcodehash =>
    apply quote_account_pos
    · simp only [Gas.warmStorageReadCost]; omega
    · omega
    · intro g hg
      obtain ⟨_, _, _, _, _⟩ := valid.flatAccess hg
      omega
  case sload =>
    apply quote_slot_pos
    · simp only [Gas.warmStorageReadCost]; omega
    · simp only [Gas.coldSloadCost]; omega
    · intro g hg
      obtain ⟨_, _, _, _, _⟩ := valid.flatAccess hg
      omega
  case selfbalance | tload =>
    simp only [ReadPrice.quote, Gas.low, Gas.warmStorageReadCost]; omega

theorem ReadRow.run_gas (row : ReadRow) (x : Frame.Running)
    (hpos : ∀ key, 0 < (row.price.quote x.context.block.rules x.context x.state.readView key).1)
    {n : Nat} (h : x.state.machine.gasMeasure ≤ n) : PlainGas x.state n ((Family.read row).run x) := by
  apply plainGas_of h
  have hs := ReadRow.step_gas row x.context.block.rules x.context x.state.readView x.state.machine hpos
  show Walk _ _ (x.state.liftRead _ _)
  unfold Frame.State.liftRead
  split <;> rename_i he <;> rw [he] at hs
  · show Machine.gasMeasure (Frame.State.machine _) ≤ _
    rw [(Frame.State.applyReadTouch_keeps _ _ _).1]
    exact hs
  · show Machine.gasMeasure (Frame.State.machine _) < _
    rw [(Frame.State.applyReadTouch_keeps _ _ _).1]
    exact hs

theorem PlainOp.sstore_run_gas (x : Frame.Running) {n : Nat} (h : x.state.machine.gasMeasure ≤ n) :
    PlainGas x.state n ((Family.store .persistent).run x) := by
  apply plainGas_of h
  cases hr : (Family.store .persistent).run x with
  | ok s' =>
    exact PlainOp.sstore_run_gasMeasure_lt x (BenvStat.rules_valid x.context.block).access hr
  | error p =>
    obtain ⟨e, s'⟩ := p
    show s'.machine.gasMeasure ≤ _
    revert hr
    show x.state.liftStore _ _ _ = _ → _
    unfold Frame.State.liftStore
    split
    · rename_i e' m t he
      intro hr
      cases hr
      rw [Frame.State.applyStoreTouch_machine]
      exact (SstoreRow.step_error he).2.2.2.1
    · intro hr; cases hr

theorem PlainOp.tstore_run_gas (x : Frame.Running) {n : Nat} (h : x.state.machine.gasMeasure ≤ n) :
    PlainGas x.state n ((Family.store .transient).run x) := by
  apply plainGas_of h
  cases hr : (Family.store .transient).run x with
  | ok s' => exact PlainOp.tstore_run_gasMeasure_lt x hr
  | error p =>
    obtain ⟨e, s'⟩ := p
    show s'.machine.gasMeasure ≤ _
    revert hr
    show x.state.liftStore _ _ _ = _ → _
    unfold Frame.State.liftStore
    split
    · rename_i e' m t he
      intro hr
      cases hr
      rw [Frame.State.applyStoreTouch_machine]
      exact (TstoreRow.step_error he).2.2.2.2.1
    · intro hr; cases hr

/-- Each plain instruction either halts within the input gas bound or continues with a strictly
smaller measure. This includes the state-gas spill in both bounds. A corollary of the families'
gas walks and the table's positivity lemmas. -/
theorem PlainOp.runCore_gas (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp)
    {n : Nat} (h : s.machine.gasMeasure ≤ n) :
    Walk (·.machine.gasMeasure ≤ n) (·.machine.gasMeasure < s.machine.gasMeasure)
      (PlainOp.runCore pc ctx s op) := by
  show PlainGas s n ((PlainOp.family op).run ⟨pc, ctx, s⟩)
  cases hf : PlainOp.family op with
  | word row => exact WordRow.run_gas row (PlainOp.wordRow?_cost_pos (PlainOp.wordRow?_eq_some.2 hf)) _ h
  | shuffle row =>
    exact ShuffleRow.run_gas row (PlainOp.shuffleRow?_cost (PlainOp.shuffleRow?_eq_some.2 hf)).2 _ h
  | memory row =>
    exact MemoryRow.run_gas row (PlainOp.memoryRow?_base_pos (PlainOp.memoryRow?_eq_some.2 hf)) _ h
  | log row =>
    exact LogRow.run_gas row (PlainOp.logRow?_prices (PlainOp.logRow?_eq_some.2 hf)).2.2.2 _ h
  | read row =>
    exact ReadRow.run_gas row ⟨pc, ctx, s⟩
      (readRow?_price_pos (PlainOp.readRow?_eq_some.2 hf) ctx s.readView) h
  | store kind =>
    cases kind with
    | persistent => exact PlainOp.sstore_run_gas ⟨pc, ctx, s⟩ h
    | transient => exact PlainOp.tstore_run_gas ⟨pc, ctx, s⟩ h

end Jaune.Checked
