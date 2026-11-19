import Jaune.MessageCall

/-! Equations between the existing account writers and the per-operation empty-account rules. -/

namespace Jaune

namespace Bridge.OldAccount

def set (w : State) (a : Address) (ac : Account) : State :=
  if ac = .nil then w.erase a else w.insert a ac

def setPresent (w : State) (a : Address) (ac : Account) : State :=
  w.insert a ac

def setAccount (w : State) (a : Address) (ac : Account) : State :=
  set w a ac.clearIfEmpty

def setBal (st : State) (adr : Address) (val : U256) : State :=
  setAccount st adr <| (st.get adr).withBalance val

def setCode (ω : State) (a : Address) (cd : ByteArray) : State :=
  let ac := ω.get a
  setAccount ω a {ac with code := cd}

def incrNonce (w : State) (a : Address) : State :=
  let ac := w.get a
  let ac' : Account := {ac with nonce := ac.nonce + 1}
  setAccount w a ac'

def setStor (w : State) (a : Address) (s : Storage) : State :=
  let ac := (w.get a)
  if AccountExists w a then setPresent w a {ac with storage := s}
  else set w a {ac with storage := s}

def setStorVal (wor : State) (adr : Address) (key val : U256) : State :=
  let acct : Account := wor.get adr
  if AccountExists wor adr then setPresent wor adr {acct with storage := acct.storage.set key val}
  else set wor adr {acct with storage := acct.storage.set key val}

def clearBenv (benv : Benv) (a : Address) : Benv :=
  {benv with storageWrites :=
    if (benv.state.get a).isEmpty then benv.storageWrites.eraseAddress a
    else benv.storageWrites}

def clearDevm (devm : Devm) (a : Address) : Devm :=
  devm.withStorageWrites
    (if (devm.state.get a).isEmpty then devm.world.storageWrites.eraseAddress a
     else devm.world.storageWrites)

/-- The world-level clearing body before the shared KeySet helper. -/
def clearWorld (w : World) (a : Address) : World :=
  { w with storageWrites :=
      if (w.state.get a).isEmpty then w.storageWrites.eraseAddress a else w.storageWrites }

end Bridge.OldAccount

theorem State.writeAccount_eraseNil (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .eraseNil a f = Bridge.OldAccount.set w a (f (w.get a)) := by
  simp [State.writeAccount, Bridge.OldAccount.set]

theorem State.writeAccount_keep (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .keep a f = Bridge.OldAccount.setPresent w a (f (w.get a)) := rfl

theorem State.writeAccount_keepIfPresent (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .keepIfPresent a f =
      if AccountExists w a then Bridge.OldAccount.setPresent w a (f (w.get a)) else Bridge.OldAccount.set w a (f (w.get a)) := by
  by_cases present : AccountExists w a
  · simp [State.writeAccount, AccountExists] at present ⊢
    simp [present, Bridge.OldAccount.setPresent]
  · simp [AccountExists] at present
    simp [State.writeAccount, Bridge.OldAccount.set, AccountExists, present]

theorem State.writeAccount_erase (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .erase a f = Bridge.OldAccount.setAccount w a (f (w.get a)) := by
  by_cases empty : (f (w.get a)).isEmpty
  · simp [State.writeAccount, Bridge.OldAccount.setAccount, Account.clearIfEmpty, Bridge.OldAccount.set, empty]
  · have nondefault : f (w.get a) ≠ .nil := by
      intro equal
      apply empty
      rw [equal]
      decide
    simp [State.writeAccount, Bridge.OldAccount.setAccount, Account.clearIfEmpty, Bridge.OldAccount.set, empty, nondefault]

/-- The convenience setter preserves the historical default-account erasure. -/
theorem State.set_eq_oldAccount (w : State) (a : Address) (ac : Account) :
    w.set a ac = Bridge.OldAccount.set w a ac :=
  State.writeAccount_eraseNil w a (fun _ => ac)

/-- The presence-preserving setter still inserts every account value. -/
theorem State.setPresent_eq_oldAccount (w : State) (a : Address) (ac : Account) :
    w.setPresent a ac = Bridge.OldAccount.setPresent w a ac :=
  State.writeAccount_keep w a (fun _ => ac)

/-- The normalizing setter preserves the historical empty-account deletion. -/
theorem State.setAccount_eq_oldAccount (w : State) (a : Address) (ac : Account) :
    w.setAccount a ac = Bridge.OldAccount.setAccount w a ac :=
  State.writeAccount_erase w a (fun _ => ac)

theorem State.setBal_eq_writeAccount (w : State) (a : Address) (v : U256) :
    Bridge.OldAccount.setBal w a v = w.writeAccount .erase a (fun ac => ac.withBalance v) := by
  rw [State.writeAccount_erase]
  rfl

theorem State.setCode_eq_writeAccount (w : State) (a : Address) (code : ByteArray) :
    Bridge.OldAccount.setCode w a code = w.writeAccount .erase a (fun ac => {ac with code}) := by
  rw [State.writeAccount_erase]
  rfl

theorem State.incrNonce_eq_writeAccount (w : State) (a : Address) :
    Bridge.OldAccount.incrNonce w a = w.writeAccount .erase a (fun ac => {ac with nonce := ac.nonce + 1}) := by
  rw [State.writeAccount_erase]
  rfl

theorem State.setStor_eq_writeAccount (w : State) (a : Address) (s : Storage) :
    Bridge.OldAccount.setStor w a s = w.writeAccount .keepIfPresent a (fun ac => {ac with storage := s}) := by
  rw [State.writeAccount_keepIfPresent]
  rfl

theorem State.setStorVal_eq_writeAccount (w : State) (a : Address) (key value : U256) :
    Bridge.OldAccount.setStorVal w a key value = w.writeAccount .keepIfPresent a
      (fun ac => {ac with storage := ac.storage.set key value}) := by
  rw [State.writeAccount_keepIfPresent]
  rfl

theorem State.setBal_eq_oldAccount (w : State) (a : Address) (v : U256) :
    w.setBal a v = Bridge.OldAccount.setBal w a v :=
  (State.setBal_eq_writeAccount w a v).symm

theorem State.setCode_eq_oldAccount (w : State) (a : Address) (code : ByteArray) :
    w.setCode a code = Bridge.OldAccount.setCode w a code :=
  (State.setCode_eq_writeAccount w a code).symm

theorem State.incrNonce_eq_oldAccount (w : State) (a : Address) :
    w.incrNonce a = Bridge.OldAccount.incrNonce w a :=
  (State.incrNonce_eq_writeAccount w a).symm

theorem State.setStor_eq_oldAccount (w : State) (a : Address) (s : Storage) :
    w.setStor a s = Bridge.OldAccount.setStor w a s :=
  (State.setStor_eq_writeAccount w a s).symm

theorem State.setStorVal_eq_oldAccount (w : State) (a : Address) (key value : U256) :
    w.setStorVal a key value = Bridge.OldAccount.setStorVal w a key value :=
  (State.setStorVal_eq_writeAccount w a key value).symm

theorem KeySet.clearIfEmpty_eq (writes : KeySet) (state : State) (a : Address) :
    writes.clearIfEmpty state a =
      if (state.get a).isEmpty then writes.eraseAddress a else writes := rfl

theorem Benv.clearStorageWritesIfEmpty_eq (benv : Benv) (a : Address) :
    benv.clearStorageWritesIfEmpty a = Bridge.OldAccount.clearBenv benv a := rfl

theorem Devm.clearStorageWritesIfEmpty_eq (devm : Devm) (a : Address) :
    devm.clearStorageWritesIfEmpty a = Bridge.OldAccount.clearDevm devm a := rfl

theorem World.clearStorageWritesIfEmpty_eq (w : World) (a : Address) :
    w.clearStorageWritesIfEmpty a = Bridge.OldAccount.clearWorld w a := rfl

end Jaune
