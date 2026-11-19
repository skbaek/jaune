import Jaune.Run.Message
import Jaune.Bridge.Memory

/-! Top-level preparation, including EIP-7702 authorization, starts a frame with empty memory. -/

namespace Jaune.Staging

private abbrev EmptyMemory (d : Devm) : Prop := d.memory = Mem.empty

private theorem EmptyMemory.chargeGas {a : Nat} {d d' : Devm} (h : EmptyMemory d)
    (hc : Jaune.chargeGas a d = .ok d') : EmptyMemory d' := by
  rw [chargeGas_def] at hc
  split at hc <;> cases hc
  exact h

private theorem EmptyMemory.chargeStateGas {a : Nat} {d d' : Devm} (h : EmptyMemory d)
    (hc : Jaune.chargeStateGas a d = .ok d') : EmptyMemory d' := by
  unfold Jaune.chargeStateGas liftMachExecution liftMach Footprint.toExecution Footprint.liftOutcome
    Mach.chargeStateGas at hc
  by_cases ha : a ≤ d.mach.stateGas.left
  · simp only [ha, ite_true] at hc
    cases hc
    exact h
  · by_cases hb : a - d.mach.stateGas.left ≤ d.mach.gasLeft <;>
      simp only [ha, hb, ite_false, ite_true] at hc <;> cases hc
    exact h

private theorem EmptyMemory.balReadAccount {d : Devm} (h : EmptyMemory d) (r : ForkRules) (a : Address) :
    EmptyMemory (d.balReadAccount r a) := by
  unfold Devm.balReadAccount; split <;> exact h

private theorem EmptyMemory.addAccessedAddress {d : Devm} (h : EmptyMemory d) (a : Address) :
    EmptyMemory (addAccessedAddress d a) := h

private theorem EmptyMemory.setCode {d : Devm} (h : EmptyMemory d) (a : Address) (c : ByteArray) :
    EmptyMemory (d.setCode a c) := h

private theorem EmptyMemory.incrNonce {d : Devm} (h : EmptyMemory d) (a : Address) : EmptyMemory (d.incrNonce a) := h

private theorem EmptyMemory.commitStateGas {d : Devm} (h : EmptyMemory d) : EmptyMemory d.commitStateGas := h

private theorem chargeNewAuthorityAmsterdam_emptyMemory {state : StateGasRules} {a : Address} {d d' : Devm}
    (h : EmptyMemory d) (hc : chargeNewAuthorityAmsterdam state a d = .ok d') : EmptyMemory d' := by
  unfold chargeNewAuthorityAmsterdam at hc
  split at hc
  · exact h.chargeStateGas hc
  · cases hc; exact h

private theorem chargePaidAccountWriteAmsterdam_emptyMemory {state : StateGasRules} {a : Address} {d : Devm}
    {s : AdrSet} {p : Devm × AdrSet} (h : EmptyMemory d)
    (hc : chargePaidAccountWriteAmsterdam state a d s = .ok p) : EmptyMemory p.1 := by
  unfold chargePaidAccountWriteAmsterdam at hc
  split at hc
  · cases hc; exact h
  · obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
    cases hc; exact h.chargeGas h1

private theorem chargeAuthBaseAmsterdam_emptyMemory {state : StateGasRules} {msg : Msg} {a t : Address}
    {d : Devm} {s : AdrSet} {p : Devm × AdrSet × ByteArray} (h : EmptyMemory d)
    (hc : chargeAuthBaseAmsterdam state msg a t d s = .ok p) : EmptyMemory p.1 := by
  unfold chargeAuthBaseAmsterdam at hc
  split at hc
  · cases hc; exact h
  · dsimp only at hc
    split at hc
    · obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
      cases hc; exact h.chargeStateGas h1
    · obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
      cases h1; cases hc; exact h

private theorem applyValidatedDelegationAmsterdam_emptyMemory {state : StateGasRules} {msg : Msg}
    {a t : Address} {d : Devm} {s1 s2 : AdrSet} {p : AmsterdamDelegationResult} (h : EmptyMemory d)
    (hc : applyValidatedDelegationAmsterdam state msg a t d s1 s2 = .ok p) : EmptyMemory p.1 := by
  unfold applyValidatedDelegationAmsterdam at hc
  obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
  obtain ⟨⟨d2, w2⟩, h2, hc⟩ := Except.bind_eq_ok hc
  obtain ⟨⟨d3, w3, c3⟩, h3, hc⟩ := Except.bind_eq_ok hc
  cases hc
  exact (((chargeAuthBaseAmsterdam_emptyMemory (chargePaidAccountWriteAmsterdam_emptyMemory
    (chargeNewAuthorityAmsterdam_emptyMemory h h1) h2) h3).setCode _ _).incrNonce _)

private theorem setDelegationAmsterdamStep_emptyMemory {state : StateGasRules} {msg : Msg}
    {auth : Authorization} {d : Devm} {s1 s2 : AdrSet} {p : AmsterdamDelegationResult}
    (h : EmptyMemory d) (hc : setDelegationAmsterdamStep state msg auth d s1 s2 = .ok p) :
    EmptyMemory p.1 := by
  unfold setDelegationAmsterdamStep at hc
  split at hc
  · cases hc; exact h
  · split at hc
    · cases hc; exact h
    · split at hc
      · cases hc; exact h
      · simp only [reduceCtorEq] at hc
      · rename_i authority _
        have hD := (h.addAccessedAddress authority).balReadAccount msg.benv.stat.rules authority
        dsimp only at hc
        generalize Devm.balReadAccount msg.benv.stat.rules authority
          (addAccessedAddress d authority) = D at hD hc
        split at hc
        · cases hc; exact hD
        · split at hc
          · cases hc; exact hD
          · exact applyValidatedDelegationAmsterdam_emptyMemory hD hc

private theorem setDelegationAmsterdamLoop_emptyMemory {state : StateGasRules} {msg : Msg} :
    ∀ (auths : List Authorization) {d : Devm} {s1 s2 : AdrSet} {p : AmsterdamDelegationResult},
      EmptyMemory d → setDelegationAmsterdamLoop state msg auths d s1 s2 = .ok p → EmptyMemory p.1
  | [], _, _, _, _, h, hc => by cases hc; exact h
  | auth :: auths, d, s1, s2, p, h, hc => by
    unfold setDelegationAmsterdamLoop at hc
    obtain ⟨⟨d1, w1, w2⟩, h1, hc⟩ := Except.bind_eq_ok hc
    exact setDelegationAmsterdamLoop_emptyMemory auths (setDelegationAmsterdamStep_emptyMemory h h1) hc

private theorem resolveTopLevelCallAmsterdam_emptyMemory {msg : Msg} {d : Devm} {p : Msg × Devm} (h : EmptyMemory d)
    (hc : resolveTopLevelCallAmsterdam msg d = .ok p) : EmptyMemory p.2 := by
  unfold resolveTopLevelCallAmsterdam at hc
  obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
  cases hc
  show EmptyMemory (Devm.balReadAccount _ _ _)
  refine EmptyMemory.balReadAccount ?_ _ _
  show EmptyMemory (Jaune.completeDelegationAccess _ _ _).2
  unfold Jaune.completeDelegationAccess
  dsimp only
  split
  · exact (h.chargeGas h1).addAccessedAddress _
  · exact h.chargeGas h1

theorem prepareTopLevelAmsterdam_emptyMemory {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) : p.2.memory = Mem.empty := by
  have key : ∀ d1, EmptyMemory d1 → finishTopLevelAmsterdam state msg d1 = .ok p → EmptyMemory p.2 := by
    intro d1 hd1 h
    unfold finishTopLevelAmsterdam dispatchTopLevelAmsterdam at h
    have hd2 : EmptyMemory (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) := by
      split
      · exact hd1
      · exact hd1.commitStateGas
    generalize (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) = d2 at hd2 h
    have hd3 := hd2.balReadAccount msg.benv.stat.rules msg.currentTarget
    dsimp only at h
    split at h
    · split at h
      · simp only [reduceCtorEq] at h
      · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> cases h
        · exact hd3.chargeStateGas h4
        · cases h4; exact hd3
    · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h
      · exact resolveTopLevelCallAmsterdam_emptyMemory (hd3.chargeStateGas h4) h
      · cases h4; exact resolveTopLevelCallAmsterdam_emptyMemory hd3 h
  have h0 : EmptyMemory (initDevm msg) := rfl
  unfold prepareTopLevelAmsterdam at h
  dsimp only at h
  split at h
  · obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    cases h1
    exact key _ h0 h
  · obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h
    unfold setDelegationAmsterdam at h1
    obtain ⟨⟨d2, w1, w2⟩, h2, h1⟩ := Except.bind_eq_ok h1
    cases h1
    exact key _ (setDelegationAmsterdamLoop_emptyMemory _ h0 h2) h

theorem prepareTopLevelAmsterdam_memory_wf {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) : p.2.memory.Wf := by
  rw [show p.2.memory = Mem.empty from prepareTopLevelAmsterdam_emptyMemory h]
  exact Mem.wf_empty

/-- Every frame handed to the interpreter by top-level preparation starts with empty memory. -/
theorem TopLevel.prepare_frame_emptyMemory {msg : Msg} {f : Frame} {refund : Nat}
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f refund)) : f.checkpoint.machine.memory = Mem.empty := by
  have amsterdam : ∀ (state : StateGasRules) (isCreate : Bool),
      Staging.TopLevel.prepare.amsterdam state msg isCreate = .ok (.frame f refund) →
        f.checkpoint.machine.memory = Mem.empty := by
    intro state isCreate hp
    unfold Staging.TopLevel.prepare.amsterdam at hp
    split at hp
    · cases hp
    · rename_i devm he
      exact absurd he (Staging.prepareTopLevelAmsterdam_error_ne_revert state msg devm)
    · cases hp
    · cases hp
    · rename_i prepared devm he
      cases hp
      exact prepareTopLevelAmsterdam_emptyMemory he
  unfold Staging.TopLevel.prepare at hp
  split at hp
  · unfold Staging.TopLevel.prepare.create at hp
    split at hp
    · split at hp
      · cases hp
      · cases hp; rfl
    · exact amsterdam _ _ hp
  · unfold Staging.TopLevel.prepare.call at hp
    split at hp
    · split at hp
      · cases hp
      · cases hp; rfl
    · exact amsterdam _ _ hp

theorem TopLevel.prepare_frame_memory_wf {msg : Msg} {f : Frame} {refund : Nat}
    (hp : Staging.TopLevel.prepare msg = .ok (.frame f refund)) : f.checkpoint.machine.memory.Wf := by
  rw [TopLevel.prepare_frame_emptyMemory hp]
  exact Mem.wf_empty

end Jaune.Staging
