import Jaune.Execution

/-! Equations between the existing account writers and the per-operation empty-account rules. -/

namespace Jaune

theorem State.writeAccount_eraseNil (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .eraseNil a f = w.set a (f (w.get a)) := by
  simp [State.writeAccount, State.set]

theorem State.writeAccount_keep (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .keep a f = w.setPresent a (f (w.get a)) := rfl

theorem State.writeAccount_keepIfPresent (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .keepIfPresent a f =
      if AccountExists w a then w.setPresent a (f (w.get a)) else w.set a (f (w.get a)) := by
  by_cases present : AccountExists w a
  · simp [State.writeAccount, AccountExists] at present ⊢
    simp [present, State.setPresent]
  · simp [AccountExists] at present
    simp [State.writeAccount, State.set, AccountExists, present]

theorem State.writeAccount_erase (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .erase a f = w.setAccount a (f (w.get a)) := by
  by_cases empty : (f (w.get a)).isEmpty
  · simp [State.writeAccount, State.setAccount, Account.clearIfEmpty, State.set, empty]
  · have nondefault : f (w.get a) ≠ .nil := by
      intro equal
      apply empty
      rw [equal]
      decide
    simp [State.writeAccount, State.setAccount, Account.clearIfEmpty, State.set, empty, nondefault]

theorem State.setBal_eq_writeAccount (w : State) (a : Address) (v : U256) :
    w.setBal a v = w.writeAccount .erase a (fun ac => ac.withBalance v) :=
by
  rw [State.writeAccount_erase]
  rfl

theorem State.setCode_eq_writeAccount (w : State) (a : Address) (code : ByteArray) :
    w.setCode a code = w.writeAccount .erase a (fun ac => {ac with code}) :=
by
  rw [State.writeAccount_erase]
  rfl

theorem State.incrNonce_eq_writeAccount (w : State) (a : Address) :
    w.incrNonce a = w.writeAccount .erase a (fun ac => {ac with nonce := ac.nonce + 1}) :=
by
  rw [State.writeAccount_erase]
  rfl

theorem State.setStor_eq_writeAccount (w : State) (a : Address) (s : Storage) :
    w.setStor a s = w.writeAccount .keepIfPresent a (fun ac => {ac with storage := s}) :=
by
  rw [State.writeAccount_keepIfPresent]
  rfl

theorem State.setStorVal_eq_writeAccount (w : State) (a : Address) (key value : U256) :
    w.setStorVal a key value = w.writeAccount .keepIfPresent a
      (fun ac => {ac with storage := ac.storage.set key value}) :=
by
  rw [State.writeAccount_keepIfPresent]
  rfl

theorem Benv.clearStorageWritesIfEmpty_eq (benv : Benv) (a : Address) :
    benv.clearStorageWritesIfEmpty a =
      {benv with storageWrites := benv.storageWrites.clearIfEmpty benv.state a} := rfl

theorem Devm.clearStorageWritesIfEmpty_eq (devm : Devm) (a : Address) :
    devm.clearStorageWritesIfEmpty a =
      devm.withStorageWrites (devm.world.storageWrites.clearIfEmpty devm.state a) := rfl

end Jaune
