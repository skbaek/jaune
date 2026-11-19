import Jaune.Bridge.G2b.BodyRoots

namespace Jaune.Staging

/-- The five phase certificates compose to the exact recorded body, including its final prefix. -/
theorem BodyRoots.ran {benv txs ommers wds state output run}
    (h : BodyRoots benv txs ommers wds state output run) :
    Body.run benv (.init benv.state) (Body.ops benv run.decoded ommers wds) =
      .ok (run.records, run.finish.final) := by
  obtain ⟨_, pre, tx, withdrawals, requests, finish, _⟩ := h
  unfold PreRoots BodyPhase.Ran at pre
  unfold RequestRoots BodyPhase.Ran at requests
  unfold BodyPhase.Ran at tx withdrawals finish
  rw [Body.ops, Body.postOps_phases, List.append_assoc]
  simp only [Body.run_append, pre, tx, withdrawals, requests, finish, bind, Except.bind,
    pure, Except.pure, BodyRun.records, List.append_assoc]

theorem BodyRoots.applied {benv txs ommers wds state output run}
    (h : BodyRoots benv txs ommers wds state output run) :
    applyBody benv txs ommers wds = .ok (state, output) := by
  simp [applyBody, Body.importer, h.decoded, Body.fold_eq_run, h.ran, h.output_eq,
    bind, Except.bind, Functor.map, Except.map]

theorem bodyRoots_iff {benv txs ommers wds state output} :
    (∃ run, BodyRoots benv txs ommers wds state output run) ↔
      applyBody benv txs ommers wds = .ok (state, output) :=
  ⟨fun ⟨_, h⟩ => h.applied, exists_bodyRoots⟩

theorem BodyPhase.Ran.unique {benv start ops a b}
    (ha : BodyPhase.Ran a benv start ops) (hb : BodyPhase.Ran b benv start ops) : a = b := by
  cases a with
  | mk records state =>
    cases b with
    | mk records' state' =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (ha.symm.trans hb))
      rfl

theorem BodyRoots.unique {benv txs ommers wds state output state' output' a b}
    (ha : BodyRoots benv txs ommers wds state output a)
    (hb : BodyRoots benv txs ommers wds state' output' b) :
    a = b ∧ state = state' ∧ output = output' := by
  cases a with
  | mk decoded pre tx withdrawals requests finish =>
    cases b with
    | mk decoded' pre' tx' withdrawals' requests' finish' =>
      obtain rfl := Except.ok.inj (ha.decoded.symm.trans hb.decoded)
      obtain rfl := BodyPhase.Ran.unique ha.pre hb.pre
      obtain rfl := BodyPhase.Ran.unique ha.transactions hb.transactions
      obtain rfl := BodyPhase.Ran.unique ha.withdrawals hb.withdrawals
      obtain rfl := BodyPhase.Ran.unique ha.requests hb.requests
      obtain rfl := BodyPhase.Ran.unique ha.finish hb.finish
      exact ⟨rfl, Prod.mk.inj (ha.output_eq.symm.trans hb.output_eq)⟩

end Jaune.Staging
