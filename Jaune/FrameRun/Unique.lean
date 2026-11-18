import Jaune.FrameRun.Prefix

namespace Jaune.Staging.Frame.Run

private theorem prefix_loop {r s} (p : Prefix r s) (hs : s = r) : HEq p (Frame.Run.stop r) := by
  cases p with
  | stop => rfl
  | next step rest =>
    have h := Frame.Running.step_cont_gasMeasure_lt step
    have k := Prefix.gasMeasure_le rest
    cases hs
    dsimp only at k
    omega
  | callDone step entry resume rest =>
    have h := Frame.Running.call_gasMeasure_lt step (.done entry) resume
    have k := Prefix.gasMeasure_le rest
    cases hs
    dsimp only at k
    omega
  | callRan step entry child resume rest =>
    have fine := (exec_iff ..).mp ⟨child⟩
    have h := Frame.Running.call_gasMeasure_lt step (.ran entry) (by simpa only [fine] using resume)
    have k := Prefix.gasMeasure_le rest
    cases hs
    dsimp only at k
    omega

private theorem self_prefix_eq_stop {r} (p : Prefix r r) : p = .stop r := eq_of_heq (prefix_loop p rfl)

private theorem end_map_inj {a b : Except Fault Frame.Exit} (h : a.map Step.exit = b.map Step.exit) : a = b := by
  cases a <;> cases b <;> simp_all [Except.map]

private theorem end_map_ne_next (out : Except Fault Frame.Exit) (pc s) :
    out.map Step.exit ≠ .ok (.next pc s) := by cases out <;> simp [Except.map]

private theorem end_map_ne_spawn (out : Except Fault Frame.Exit) (c p pc) :
    out.map Step.exit ≠ .ok (.spawn c p pc) := by cases out <;> simp [Except.map]

/-- Fixed endpoints determine the full sequence including the witnesses for completed children. -/
private theorem uniqueRun : ∀ {r e} (t u : Frame.Run r e), t = u
  | _, _, .stop _, u => by
    cases u with
    | stop => rfl
    | _ => exact (self_prefix_eq_stop _).symm
  | _, _, .halt hs₁, u => by
    cases u with
    | halt hs₂ => rfl
    | next hs₂ _ => exact absurd (hs₁.symm.trans hs₂) (end_map_ne_next _ _ _)
    | callDone hs₂ _ _ _ | callRan hs₂ _ _ _ _ | callDoneEnd hs₂ _ _ | callRanEnd hs₂ _ _ _ =>
      exact absurd (hs₁.symm.trans hs₂) (end_map_ne_spawn _ _ _ _)
  | _, _, .next hs₁ rest₁, u => by
    cases u with
    | stop => exact self_prefix_eq_stop _
    | halt hs₂ => exact absurd (hs₂.symm.trans hs₁) (end_map_ne_next _ _ _)
    | next hs₂ rest₂ =>
      cases hs₁.symm.trans hs₂
      congr 1; exact uniqueRun rest₁ rest₂
    | callDone hs₂ _ _ _ | callRan hs₂ _ _ _ _ | callDoneEnd hs₂ _ _ | callRanEnd hs₂ _ _ _ =>
      cases hs₁.symm.trans hs₂
  | _, _, .callDone hs₁ he₁ hr₁ rest₁, u => by
    cases u with
    | stop => exact self_prefix_eq_stop _
    | halt hs₂ => exact absurd (hs₂.symm.trans hs₁) (end_map_ne_spawn _ _ _ _)
    | next hs₂ _ => cases hs₁.symm.trans hs₂
    | callDone hs₂ he₂ hr₂ rest₂ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂; cases hr₁.symm.trans hr₂
      congr 1; exact uniqueRun rest₁ rest₂
    | callRan hs₂ he₂ _ _ _ | callRanEnd hs₂ he₂ _ _ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
    | callDoneEnd hs₂ he₂ hr₂ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂; cases hr₁.symm.trans hr₂
  | _, _, .callRan hs₁ he₁ c₁ hr₁ rest₁, u => by
    cases u with
    | stop => exact self_prefix_eq_stop _
    | halt hs₂ => exact absurd (hs₂.symm.trans hs₁) (end_map_ne_spawn _ _ _ _)
    | next hs₂ _ => cases hs₁.symm.trans hs₂
    | callDone hs₂ he₂ _ _ | callDoneEnd hs₂ he₂ _ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
    | callRan hs₂ he₂ c₂ hr₂ rest₂ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
      cases exit_unique c₁ c₂; cases hr₁.symm.trans hr₂
      congr 1 <;> first | exact uniqueRun c₁ c₂ | exact uniqueRun rest₁ rest₂
    | callRanEnd hs₂ he₂ c₂ hr₂ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
      cases exit_unique c₁ c₂; cases hr₁.symm.trans hr₂
  | _, _, .callDoneEnd hs₁ he₁ hr₁, u => by
    cases u with
    | halt hs₂ => exact absurd (hs₂.symm.trans hs₁) (end_map_ne_spawn _ _ _ _)
    | next hs₂ _ => cases hs₁.symm.trans hs₂
    | callDone hs₂ he₂ hr₂ _ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂; cases hr₁.symm.trans hr₂
    | callRan hs₂ he₂ _ _ _ | callRanEnd hs₂ he₂ _ _ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
    | callDoneEnd hs₂ he₂ hr₂ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂; rfl
  | _, _, .callRanEnd hs₁ he₁ c₁ hr₁, u => by
    cases u with
    | halt hs₂ => exact absurd (hs₂.symm.trans hs₁) (end_map_ne_spawn _ _ _ _)
    | next hs₂ _ => cases hs₁.symm.trans hs₂
    | callDone hs₂ he₂ _ _ | callDoneEnd hs₂ he₂ _ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
    | callRan hs₂ he₂ c₂ hr₂ _ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
      cases exit_unique c₁ c₂; cases hr₁.symm.trans hr₂
    | callRanEnd hs₂ he₂ c₂ hr₂ =>
      cases hs₁.symm.trans hs₂; cases he₁.symm.trans he₂
      cases exit_unique c₁ c₂; congr 1; exact uniqueRun c₁ c₂
termination_by _ _ t _ => sizeOf t

theorem Prefix.unique {r s} (p q : Prefix r s) : p = q := uniqueRun p q

instance {r s} : Subsingleton (Prefix r s) := ⟨Prefix.unique⟩

instance {r out} : Subsingleton (Frame.Run r (.exit out)) := ⟨uniqueRun⟩

end Jaune.Staging.Frame.Run
