import Jaune.Execution

/-! Facts about account presence under balance changes and beneficiary credits. -/

namespace Jaune

/-- A protected account survives an erasing update that keeps its nonce and code. Its storage is
exactly the storage the update wrote. -/
theorem State.Protected.get_writeAccount {w : State} {a : Address} (hp : w.Protected a)
    (f : Account → Account) (hn : (f (w.get a)).nonce = (w.get a).nonce)
    (hc : (f (w.get a)).code = (w.get a).code) :
    (w.writeAccount .erase a f).get a = f (w.get a) := by
  have nonempty : ¬ (f (w.get a)).isEmpty := by
    intro h
    exact hp.elim (fun n => n (hn.symm.trans h.2.1))
      (fun c => c ((congrArg ByteArray.size hc).symm.trans h.1))
  simp only [State.writeAccount, nonempty, decide_false, Bool.false_eq_true, ite_false]
  exact State.get_setPresent_self _ _ _

theorem Account.clearIfEmpty_withBalance_of_nonce {ac : Account} (v : U256) (hn : ac.nonce ≠ 0) :
    (ac.withBalance v).clearIfEmpty = ac.withBalance v := by
  unfold Account.clearIfEmpty
  split
  · rename_i h
    exact (hn h.2.1).elim
  · rfl

theorem Account.clearIfEmpty_of_code {ac : Account} (hc : ac.code.size ≠ 0) :
    ac.clearIfEmpty = ac := by
  unfold Account.clearIfEmpty
  split
  · rename_i h
    exact (hc h.1).elim
  · rfl

theorem State.Protected.setBalance {w : State} {a : Address} (hp : w.Protected a) (b : Address) (v : U256) :
    (w.setBalance b v).Protected a := by
  by_cases he : b = a
  · subst b
    simpa only [State.Protected, State.setBalance_get_self, Account.clearIfEmpty_nonce,
      Account.clearIfEmpty_code, Account.withBalance] using hp
  · simpa only [State.Protected, State.setBalance_get_ne he] using hp

theorem State.setBalance_storage_of_protected {w : State} {a b : Address} {v : U256}
    (hp : w.Protected a) : ((w.setBalance b v).get a).storage = (w.get a).storage := by
  rw [State.setBalance_get_storage]
  split_ifs with h
  · obtain ⟨rfl, h⟩ := h
    exact (hp.elim (fun hn => hn h.2.1) (fun hc => hc h.1)).elim
  · rfl

theorem State.protected_iff_hasCodeOrNonce (w : State) (a : Address) :
    w.Protected a ↔ accountHasCodeOrNonce w a = true := by
  simp only [State.Protected, accountHasCodeOrNonce, State.getNonce, State.getCode,
    Bool.or_eq_true, Bool.not_eq_true']
  have nonce : (w.get a).nonce ≠ 0 ↔ 0 < (w.get a).nonce := by
    rw [Ne, ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt]
    exact Nat.pos_iff_ne_zero.symm
  rw [nonce]
  apply or_congr
  · exact decide_eq_true_iff.symm
  · simp only [ByteArray.isEmpty, beq_eq_false_iff_ne, ne_eq]

end Jaune
