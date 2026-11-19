import Jaune.MessageCall.CheckedState

/-! Outcomes of the checked machine's primitive steps (`chargeGas`, `pop`, `popToNat`, `popN`,
`push`), on both channels. The family laws of `Jaune.Instructions` are read off these. They sit
in their own namespace `InstrStep` so that they cannot collide with `Machine.*` lemmas elsewhere;
they are candidates for a shared module beside `CheckedState`. -/

namespace Jaune.Checked.InstrStep

open Jaune

theorem chargeGas_eq_ok {m out : Machine} {cost : Nat} (h : m.chargeGas cost = .ok out) :
    cost ≤ m.gasLeft ∧ out = { m with gasLeft := m.gasLeft - cost } := by
  by_cases enough : cost ≤ m.gasLeft
  · exact ⟨enough, by simpa [Machine.chargeGas, safeSub, enough, eq_comm] using h⟩
  · simp [Machine.chargeGas, safeSub, enough] at h

theorem chargeGas_eq_error {m out : Machine} {cost : Nat} {e : ExceptionalHalt}
    (h : m.chargeGas cost = .error (e, out)) :
    e = .outOfGas .none ∧ m.gasLeft < cost ∧ out = m := by
  by_cases enough : cost ≤ m.gasLeft
  · simp [Machine.chargeGas, safeSub, enough] at h
  · simp [Machine.chargeGas, safeSub, enough] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, Nat.lt_of_not_le enough, rfl⟩

theorem chargeGas_of_le {m : Machine} {cost : Nat} (h : cost ≤ m.gasLeft) :
    m.chargeGas cost = .ok { m with gasLeft := m.gasLeft - cost } := by
  simp [Machine.chargeGas, safeSub, h]

theorem chargeGas_of_lt {m : Machine} {cost : Nat} (h : m.gasLeft < cost) :
    m.chargeGas cost = .error (.outOfGas .none, m) := by
  simp [Machine.chargeGas, safeSub, Nat.not_le.mpr h]

theorem pop_eq_ok {m out : Machine} {x : U256} (h : m.pop = .ok (x, out)) :
    ∃ rest, m.stack = x :: rest ∧ out = { m with stack := rest } := by
  unfold Machine.pop at h
  split at h
  · contradiction
  · rename_i first rest hs
    cases h
    exact ⟨rest, hs, rfl⟩

theorem pop_eq_error {m out : Machine} {e : ExceptionalHalt} (h : m.pop = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack = [] ∧ out = { m with stack := [] } := by
  rcases m with ⟨stk, mem, gl, sg, rd⟩
  cases stk with
  | nil =>
    simp only [Machine.pop, Except.error.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  | cons _ _ => simp [Machine.pop] at h

theorem popToNat_eq_ok {m out : Machine} {x : Nat} (h : m.popToNat = .ok (x, out)) :
    ∃ w rest, m.stack = w :: rest ∧ x = w.toNat ∧ out = { m with stack := rest } := by
  unfold Machine.popToNat at h
  split at h
  · contradiction
  · rename_i w m' hp
    cases h
    obtain ⟨rest, hs, rfl⟩ := pop_eq_ok hp
    exact ⟨w, rest, hs, rfl, rfl⟩

theorem popToNat_eq_error {m out : Machine} {e : ExceptionalHalt}
    (h : m.popToNat = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack = [] ∧ out = { m with stack := [] } := by
  unfold Machine.popToNat at h
  split at h
  · rename_i err hp
    cases h
    exact pop_eq_error hp
  · contradiction

theorem popN_eq_ok {n : Nat} {m out : Machine} {xs : List U256}
    (h : m.popN n = .ok (xs, out)) :
    ∃ rest, m.stack = xs ++ rest ∧ xs.length = n ∧ out = { m with stack := rest } := by
  induction n generalizing m xs with
  | zero =>
    simp only [Machine.popN, Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨m.stack, rfl, rfl, rfl⟩
  | succ n ih =>
    unfold Machine.popN at h
    split at h
    · contradiction
    · rename_i x m' hp
      split at h
      · contradiction
      · rename_i ys m'' hq
        cases h
        obtain ⟨tail, hs, rfl⟩ := pop_eq_ok hp
        obtain ⟨rest, hs', hlen, rfl⟩ := ih hq
        refine ⟨rest, ?_, by simp [hlen], rfl⟩
        simp only at hs'
        simp [hs, hs']

theorem popN_eq_error {n : Nat} {m out : Machine} {e : ExceptionalHalt}
    (h : m.popN n = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack.length < n ∧ out = { m with stack := [] } := by
  induction n generalizing m with
  | zero => simp [Machine.popN] at h
  | succ n ih =>
    unfold Machine.popN at h
    split at h
    · rename_i err hp
      cases h
      obtain ⟨rfl, hs, rfl⟩ := pop_eq_error hp
      exact ⟨rfl, by simp [hs], rfl⟩
    · rename_i x m' hp
      split at h
      · rename_i err hq
        cases h
        obtain ⟨tail, hs, rfl⟩ := pop_eq_ok hp
        obtain ⟨rfl, hlen, rfl⟩ := ih hq
        simp only at hlen
        exact ⟨rfl, by simp [hs]; omega, rfl⟩
      · contradiction

theorem push_eq_ok {m out : Machine} {x : U256} (h : m.push x = .ok out) :
    m.stack.length < 1024 ∧ out = { m with stack := x :: m.stack } := by
  unfold Machine.push at h
  split at h
  · cases h
    exact ⟨‹_›, rfl⟩
  · contradiction

theorem push_eq_error {m out : Machine} {x : U256} {e : ExceptionalHalt}
    (h : m.push x = .error (e, out)) :
    e = .stackOverflow .none ∧ 1024 ≤ m.stack.length ∧ out = m := by
  unfold Machine.push at h
  split at h
  · contradiction
  · cases h
    exact ⟨rfl, Nat.le_of_not_lt ‹_›, rfl⟩

end Jaune.Checked.InstrStep
