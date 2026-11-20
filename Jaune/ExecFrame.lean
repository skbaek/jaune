import Jaune.Execution
import Jaune.MessageCall.Measures

/-!
Generic frame and step relations used by complete execution derivations.
This module depends only on Jaune and its ordinary Lean dependencies.
Compiler stack-prefix relations remain owned by Blanc.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

def JumpOp.Run (evm : Evm) :
    JumpOp → Except (EvmError × Devm) (Nat × Devm) → Prop :=
  λ j ex => j.run evm = ex

def HaltOp.Run (sevm : Sevm) (devm : Devm) : HaltOp → Execution → Prop :=
  λ l ex => l.run sevm devm = ex

/-- Fieldwise relations used to assemble the canonical `Devm.Rel` frames. -/
structure Devm.Rels : Type where
  (stack : List U256 → List U256 → Prop)
  (memory : Mem → Mem → Prop)
  (gasLeft : Nat → Nat → Prop)
  (logs : List Log → List Log → Prop)
  (refundCounter : Int → Int → Prop)
  (output : Bytes → Bytes → Prop)
  (accountsToDelete : AdrSet → AdrSet → Prop)
  (returnData : Bytes → Bytes → Prop)
  (error : Option SettledHalt → Option SettledHalt → Prop)
  (accessedAddresses : AdrSet → AdrSet → Prop)
  (accessedStorageKeys : KeySet → KeySet → Prop)
  (state : State → State → Prop)
  (createdAccounts : AdrSet → AdrSet → Prop)
  (transientStorage : TransientStorage → TransientStorage → Prop)
  (stateGas : StateGasMeter → StateGasMeter → Prop)
  (accountReads : AdrSet → AdrSet → Prop)
  (storageReads : KeySet → KeySet → Prop)
  (storageWrites : KeySet → KeySet → Prop)
  (touchedAccounts : AdrSet → AdrSet → Prop)

/-- Canonical relation between dynamic EVM states, assembled field by field. -/
structure Devm.Rel (rels : Devm.Rels) (devm devm' : Devm) : Prop where
  (stack : rels.stack devm.stack devm'.stack)
  (memory : rels.memory devm.memory devm'.memory)
  (gasLeft : rels.gasLeft devm.gasLeft devm'.gasLeft)
  (logs : rels.logs devm.logs devm'.logs)
  (refundCounter : rels.refundCounter devm.refundCounter devm'.refundCounter)
  (output : rels.output devm.output devm'.output)
  ( accountsToDelete :
    rels.accountsToDelete devm.accountsToDelete devm'.accountsToDelete)
  (returnData : rels.returnData devm.returnData devm'.returnData)
  (error : rels.error devm.error devm'.error)
  ( accessedAddresses :
    rels.accessedAddresses devm.accessedAddresses devm'.accessedAddresses )
  ( accessedStorageKeys :
    rels.accessedStorageKeys devm.accessedStorageKeys devm'.accessedStorageKeys )
  (state : rels.state devm.state devm'.state)
  ( createdAccounts :
    rels.createdAccounts devm.createdAccounts devm'.createdAccounts )
  ( transientStorage :
    rels.transientStorage devm.transientStorage devm'.transientStorage )
  (stateGas : rels.stateGas devm.stateGas devm'.stateGas)
  ( accountReads :
    rels.accountReads devm.meta.accountReads devm'.meta.accountReads )
  ( storageReads :
    rels.storageReads devm.meta.storageReads devm'.meta.storageReads )
  ( storageWrites :
    rels.storageWrites devm.world.storageWrites devm'.world.storageWrites )
  ( touchedAccounts :
    rels.touchedAccounts devm.meta.touchedAccounts devm'.meta.touchedAccounts )

def Devm.Rels.eq : Devm.Rels :=
  {
    stack := _root_.Eq,
    memory := _root_.Eq,
    gasLeft := _root_.Eq,
    logs := _root_.Eq,
    refundCounter := _root_.Eq,
    output := _root_.Eq,
    accountsToDelete := _root_.Eq,
    returnData := _root_.Eq,
    error := _root_.Eq,
    accessedAddresses := _root_.Eq,
    accessedStorageKeys := _root_.Eq,
    state := _root_.Eq,
    createdAccounts := _root_.Eq,
    transientStorage := _root_.Eq,
    stateGas := _root_.Eq,
    accountReads := _root_.Eq,
    storageReads := _root_.Eq
    storageWrites := _root_.Eq
    touchedAccounts := _root_.Eq
  }

def Devm.Burn : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := (· ≥ · )
  }

/-! ### Fieldwise laws of `Devm.Rel`

Names and statements are the ones Blanc carried; Jaune now owns them, so a new
`Devm.Rels` field is repaired here, once. -/

/-- Functional compatibility form of reflexivity, avoiding the deprecated root alias. -/
abbrev ReflexiveRel {α : Sort _} (r : α → α → Prop) : Prop := ∀ x, r x x

/-- Functional compatibility form of transitivity, avoiding the deprecated root alias. -/
abbrev TransitiveRel {α : Sort _} (r : α → α → Prop) : Prop :=
  ∀ ⦃x y z⦄, r x y → r y z → r x z

def Devm.Rels.Refl (r : Devm.Rels) : Prop :=
  ReflexiveRel r.stack ∧ ReflexiveRel r.memory ∧ ReflexiveRel r.gasLeft ∧
  ReflexiveRel r.logs ∧ ReflexiveRel r.refundCounter ∧ ReflexiveRel r.output ∧
  ReflexiveRel r.accountsToDelete ∧ ReflexiveRel r.returnData ∧ ReflexiveRel r.error ∧
  ReflexiveRel r.accessedAddresses ∧ ReflexiveRel r.accessedStorageKeys ∧
  ReflexiveRel r.state ∧ ReflexiveRel r.createdAccounts ∧
  ReflexiveRel r.transientStorage ∧ ReflexiveRel r.stateGas ∧
  ReflexiveRel r.accountReads ∧ ReflexiveRel r.storageReads ∧ ReflexiveRel r.storageWrites ∧
  ReflexiveRel r.touchedAccounts

def Devm.Rels.Trans (r : Devm.Rels) : Prop :=
  TransitiveRel r.stack ∧ TransitiveRel r.memory ∧ TransitiveRel r.gasLeft ∧
  TransitiveRel r.logs ∧ TransitiveRel r.refundCounter ∧ TransitiveRel r.output ∧
  TransitiveRel r.accountsToDelete ∧ TransitiveRel r.returnData ∧ TransitiveRel r.error ∧
  TransitiveRel r.accessedAddresses ∧ TransitiveRel r.accessedStorageKeys ∧
  TransitiveRel r.state ∧ TransitiveRel r.createdAccounts ∧
  TransitiveRel r.transientStorage ∧ TransitiveRel r.stateGas ∧
  TransitiveRel r.accountReads ∧ TransitiveRel r.storageReads ∧ TransitiveRel r.storageWrites ∧
  TransitiveRel r.touchedAccounts

theorem Devm.rel_refl {r : Devm.Rels} (hr : Devm.Rels.Refl r) :
    ReflexiveRel (Devm.Rel r) := by
  intro d
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hr
  exact ⟨h1 _, h2 _, h3 _, h4 _, h5 _, h6 _, h7 _, h8 _, h9 _, h10 _, h11 _, h12 _,
    h13 _, h14 _, h15 _, h16 _, h17 _, h18 _, h19 _⟩

theorem Devm.rel_trans {r : Devm.Rels} (hr : Devm.Rels.Trans r) :
    TransitiveRel (Devm.Rel r) := by
  intro a b c hab hbc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19⟩ := hr
  exact ⟨h1 hab.stack hbc.stack, h2 hab.memory hbc.memory, h3 hab.gasLeft hbc.gasLeft,
    h4 hab.logs hbc.logs, h5 hab.refundCounter hbc.refundCounter,
    h6 hab.output hbc.output, h7 hab.accountsToDelete hbc.accountsToDelete,
    h8 hab.returnData hbc.returnData, h9 hab.error hbc.error,
    h10 hab.accessedAddresses hbc.accessedAddresses,
    h11 hab.accessedStorageKeys hbc.accessedStorageKeys, h12 hab.state hbc.state,
    h13 hab.createdAccounts hbc.createdAccounts,
    h14 hab.transientStorage hbc.transientStorage, h15 hab.stateGas hbc.stateGas,
    h16 hab.accountReads hbc.accountReads, h17 hab.storageReads hbc.storageReads,
    h18 hab.storageWrites hbc.storageWrites,
    h19 hab.touchedAccounts hbc.touchedAccounts⟩

/-- A relation that is equality off the machine fields relates `d` only to
`d` with a new `Mach`. Consumers read the equation instead of unpacking the
fields positionally. -/
theorem Devm.Rel.eq_setMach {stack : List U256 → List U256 → Prop}
    {memory : Mem → Mem → Prop} {gasLeft : Nat → Nat → Prop}
    {stateGas : StateGasMeter → StateGasMeter → Prop} {d d' : Devm}
    (h : Devm.Rel {Devm.Rels.eq with
      stack := stack, memory := memory, gasLeft := gasLeft, stateGas := stateGas} d d') :
    d' = d.setMach d'.mach := by
  obtain ⟨_, _, _, hlogs, hrefund, houtput, hdel, hret, herr, haddr, hkeys, hstate,
    hcreated, htra, _, hreads, hsreads, hwrites, htouched⟩ := h
  rcases d with ⟨mach, ⟨logs, refund, output, toDelete, returnData, err, addr, keys, created,
    reads, sreads, touched⟩, ⟨state, tra, writes⟩⟩
  rcases d' with ⟨mach', ⟨logs', refund', output', toDelete', returnData', err', addr', keys',
    created', reads', sreads', touched'⟩, ⟨state', tra', writes'⟩⟩
  simp only [Devm.Rels.eq] at *
  cases hlogs; cases hrefund; cases houtput; cases hdel; cases hret; cases herr
  cases haddr; cases hkeys; cases hstate; cases hcreated; cases htra; cases hreads
  cases hsreads; cases hwrites; cases htouched
  rfl

/-- `Devm.Burn` changes only the machine. -/
theorem Devm.Burn.eq_setMach {d d' : Devm} (h : Devm.Burn d d') :
    d' = d.setMach d'.mach :=
  Devm.Rel.eq_setMach h


def HaltOp.At (code : ByteArray) (pc : Nat) (l : HaltOp) : Prop := code.getOp pc = some (.halt l)
def NextOp.At (code : ByteArray) (pc : Nat) (n : NextOp) : Prop := code.getOp pc = some (.next n)
def JumpOp.At (code : ByteArray) (pc : Nat) (j : JumpOp) : Prop := code.getOp pc = some (.jump j)
def PlainOp.At (code : ByteArray) (pc : Nat) (r : PlainOp) : Prop := code.getOp pc = some (.next (.plain r))
def MessageOp.At (code : ByteArray) (pc : Nat) (x : MessageOp) : Prop := code.getOp pc = some (.next (.message x))

/-! ### The value transfer at message entry -/

/-- Moving the call value preserves the block environment's static part.

`benvAfterTransfer` either returns the environment untouched or rebuilds it
through `Benv.withState`, which replaces the state and nothing else.

Lives here, below every consumer, because it had been proved three times:
in `Blanc/DeploymentMessage.lean` for four deployment-message families, again
privately in `Blanc/Weth10AllowanceArmsPermit.lean`. Both copies are gone and every caller
resolves to this one unchanged. -/
lemma benvAfterTransfer_stat {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) : benv.stat = msg.benv.stat := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · rcases Except.bind_eq_ok h with ⟨b, hb, hok⟩
    cases hok
    unfold Option.toExcept at hb
    split at hb
    · cases hb
    · cases hb
      rename_i w hw
      unfold Benv.subBal at hw
      rcases Option.bind_eq_some_iff.mp hw with ⟨st, hst, hb2⟩
      cases hb2
      rfl
  · cases h; rfl

/-- `benvAfterTransfer` without a value transfer returns the environment. -/
lemma of_benvAfterTransfer_no {msg : Msg} {benv' : Benv}
    (h_stv : ¬ msg.shouldTransferValue = true)
    (h : msg.benvAfterTransfer = .ok benv') : benv' = msg.benv := by
  unfold Msg.benvAfterTransfer at h
  simp only [h_stv] at h
  exact (Except.ok.inj h).symm

/-- `benvAfterTransfer` with a nonzero value transfer is a debit then a credit. -/
lemma of_benvAfterTransfer {msg : Msg} {benv' : Benv}
    (h_stv : msg.shouldTransferValue = true)
    (h_nonzero : msg.value ≠ 0)
    (h : msg.benvAfterTransfer = .ok benv') :
    ∃ st_mid, msg.benv.state.subBal msg.caller msg.value = some st_mid ∧
      benv' = ((msg.benv.withState st_mid).clearStorageWritesIfEmpty msg.caller).addBal
        msg.currentTarget msg.value := by
  unfold Msg.benvAfterTransfer at h
  rw [ite_eq_left ⟨h_stv, h_nonzero⟩] at h
  unfold Benv.subBal at h
  rcases hq : msg.benv.state.subBal msg.caller msg.value with _ | st_mid <;>
    rw [hq] at h <;>
    simp only [Option.toExcept, bind, Option.bind, Except.bind] at h
  · cases h
  · injection h with h
    exact ⟨st_mid, rfl, h.symm⟩

/-- Value transfer changes balances but preserves code. -/
lemma benvAfterTransfer_ok_getCode {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Address) :
    benv.state.getCode a = msg.benv.state.getCode a := by
  by_cases hzero : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero hzero] at h
    cases h
    rfl
  by_cases h_stv : msg.shouldTransferValue = true
  · obtain ⟨st_mid, h_sub, rfl⟩ := of_benvAfterTransfer h_stv hzero h
    exact (State.addBal_getCode _ _ _ _).trans (State.subBal_getCode h_sub)
  · rw [of_benvAfterTransfer_no h_stv h]

/-- Zero-value entry preserves storage everywhere. Nonzero value transfer preserves
storage at an account protected by a nonzero nonce or nonempty code. -/
lemma benvAfterTransfer_ok_getStor {msg : Msg} {benv : Benv}
    (h : msg.benvAfterTransfer = .ok benv) (a : Address)
    (hpreserved : msg.value = 0 ∨ (msg.benv.state.get a).nonce ≠ 0 ∨
      (msg.benv.state.get a).code.size ≠ 0) :
    benv.state.getStor a = msg.benv.state.getStor a := by
  by_cases hzero : msg.value = 0
  · rw [Msg.benvAfterTransfer_of_value_zero hzero] at h
    cases h
    rfl
  have hprotected := hpreserved.resolve_left hzero
  have preserve {st : State} {b : Address} {v : U256}
      (hp : (st.get a).nonce ≠ 0 ∨ (st.get a).code.size ≠ 0) :
      ((st.setBal b v).get a).storage = (st.get a).storage := by
    rw [State.setBal_get_stor]
    split
    · rename_i he
      rcases he with ⟨rfl, he⟩
      rcases hp with hn | hc
      · exact (hn he.2.1).elim
      · exact (hc he.1).elim
    · rfl
  by_cases h_stv : msg.shouldTransferValue = true
  · obtain ⟨st_mid, h_sub, rfl⟩ := of_benvAfterTransfer h_stv hzero h
    have hmid : (st_mid.get a).nonce ≠ 0 ∨ (st_mid.get a).code.size ≠ 0 := by
      rw [(State.of_subBal h_sub).2]
      by_cases ha : msg.caller = a
      · rw [ha, State.setBal_get_self]
        simpa only [Account.clearIfEmpty_nonce, Account.clearIfEmpty_code, Account.withBalance]
          using hprotected
      · rw [State.setBal_get_ne ha]
        exact hprotected
    apply (preserve hmid).trans
    rw [(State.of_subBal h_sub).2]
    exact preserve hprotected
  · rw [of_benvAfterTransfer_no h_stv h]

/-- A zero-value message entry preserves the complete balance map, including
the self-call case where caller and callee coincide. -/
lemma benvAfterTransfer_bal_of_value_zero {msg : Msg} {post : Benv}
    (hzero : msg.value = 0)
    (hrun : msg.benvAfterTransfer = .ok post) :
    post.state.bal = msg.benv.state.bal := by
  rw [Msg.benvAfterTransfer_of_value_zero hzero] at hrun
  cases hrun
  rfl

/-- A zero-value message entry always succeeds. -/
lemma benvAfterTransfer_exists_of_value_zero {msg : Msg} (hzero : msg.value = 0) :
    ∃ post, msg.benvAfterTransfer = .ok post := by
  exact ⟨msg.benv, Msg.benvAfterTransfer_of_value_zero hzero⟩

/-- `initSevm` copies the message's block context. -/
lemma initSevm_benvStat (msg : Msg) : (initSevm msg).benvStat = msg.benv.stat :=
  rfl

/-- `Msg.withBenv` replaces the whole block context. -/
lemma Msg.withBenv_benvStat (msg : Msg) (benv : Benv) :
    (msg.withBenv benv).benv.stat = benv.stat :=
  rfl


end Jaune
