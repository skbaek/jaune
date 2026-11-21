import Jaune.MessageCall.State
import Jaune.MessageCall.Context

/-! The Read family as rows (goal `jaune-shape-and-names-v1`, S4).

`BALANCE`, `EXTCODESIZE`, `EXTCODECOPY`, `EXTCODEHASH`, `SELFBALANCE`, `SLOAD` and `TLOAD` read the
world and, at most, warm one key and record one EIP-7928 read. A row is data: a target (what the
key is and how it is popped), a price indexed by the target (only account and slot targets can
carry warm/cold pricing), and a result (a pure read pushed, or `EXTCODECOPY`'s copy of code).

The step works on the machine and a read-only `ReadView`; the only effects it can hand back
outside the machine are a `ReadTouch`: a key warmed and a read recorded. `Frame.State.liftRead`
applies the touch on both channels, so by its type a read keeps the world, the logs, the
refund, the self-destructs, the touched accounts and the created accounts. -/

namespace Jaune

open Jaune

/-- What a Read row's key is. -/
inductive ReadTarget where
  /-- Pops an address. -/
  | account
  /-- Pops a key of the recipient's storage. -/
  | slot
  /-- Pops a key of the recipient's transient storage. -/
  | transient
  /-- Pops nothing; reads the recipient. -/
  | recipient
deriving DecidableEq, Repr

/-- The key type of a target. -/
def ReadTarget.Key : ReadTarget → Type
  | .account => Address
  | .slot => U256
  | .transient => U256
  | .recipient => Unit

/-- Pop the target's key. -/
def ReadTarget.pop : (t : ReadTarget) → Machine →
    Except (ExceptionalHalt × Machine) (t.Key × Machine)
  | .account, m => m.popToAddress
  | .slot, m => m.pop
  | .transient, m => m.pop
  | .recipient, m => .ok ((), m)

/-- A key of the accessed sets and of the EIP-7928 reads. -/
inductive ReadAccessKey where
  | address (a : Address)
  | slot (a : Address) (k : U256)
deriving DecidableEq

/-- The EIP-7928 read a target records. Total: a transient key records nothing. -/
def ReadTarget.readKey (ctx : CallContext) : (t : ReadTarget) → t.Key → Option ReadAccessKey
  | .account, a => some (.address a)
  | .slot, k => some (.slot ctx.recipient k)
  | .transient, _ => none
  | .recipient, _ => some (.address ctx.recipient)

/-- Read-only input of a read: the world and the two accessed sets. -/
structure ReadView where
  world : World
  accessedAddresses : AddressSet
  accessedStorageKeys : KeySet

/-- A frame state's read view. -/
def Frame.State.readView (s : Frame.State) : ReadView where
  world := s.world
  accessedAddresses := s.accessedAddresses
  accessedStorageKeys := s.accessedStorageKeys

/-- A read's price. Warm/cold pricing exists only for targets that have an accessed set. -/
inductive ReadPrice : ReadTarget → Type where
  | account (warm cold : ForkRules → Nat) (flat : ForkRules → FlatAccessGas → Nat) :
      ReadPrice .account
  | slot (warm cold : ForkRules → Nat) (flat : ForkRules → FlatAccessGas → Nat) : ReadPrice .slot
  | fixed {t : ReadTarget} (cost : Nat) : ReadPrice t

/-- The price at the key's warmth, and the key warmed before the charge: only under EIP-2929
access, and only a cold key. -/
def ReadPrice.quote : {t : ReadTarget} → ReadPrice t → ForkRules → CallContext → ReadView →
    t.Key → Nat × Option ReadAccessKey
  | _, .account warm cold flat, rules, _, v, (a : Address) =>
    match rules.access with
    | .eip2929 =>
      if a ∈ v.accessedAddresses then (warm rules, none)
      else (cold rules, some (.address a))
    | .flat g => (flat rules g, none)
  | _, .slot warm cold flat, rules, ctx, v, k =>
    match rules.access with
    | .eip2929 =>
      if ((ctx.recipient, k) : Address × U256) ∈ v.accessedStorageKeys then (warm rules, none)
      else (cold rules, some (.slot ctx.recipient k))
    | .flat g => (flat rules g, none)
  | _, .fixed cost, _, _, _, _ => (cost, none)

/-- What a read hands back. -/
inductive ReadResult : ReadTarget → Type where
  /-- Push a pure function of the call context, the world and the key. -/
  | push {t : ReadTarget} (read : CallContext → World → t.Key → U256) : ReadResult t
  /-- `EXTCODECOPY`: three more operands (destination, offset, size); the charge adds
  `perWord` per word and the extension of the destination range to the access price. -/
  | copyCode (perWord : Nat) : ReadResult .account

/-- The only substate and trail effects a read may have. -/
structure ReadTouch where
  /-- Set before the charge, so present on an out-of-gas payload. -/
  warmed : Option ReadAccessKey := none
  /-- Set after the charge and before the push: absent on an out-of-gas or underflow payload,
  present on a stack-overflow payload. -/
  read : Option ReadAccessKey := none
deriving DecidableEq

/-- A Read row. -/
structure ReadRow where
  available : OpcodeRules → Bool := fun _ => true
  target : ReadTarget
  price : ReadPrice target
  result : ReadResult target

/-- The part of a read after its key is popped and priced: the copy's extra pops, the charge,
the push or copy. `warmed` and `read` are what the touch carries once each is due. -/
def ReadResult.finish : {t : ReadTarget} → ReadResult t → CallContext → World → t.Key →
    (price : Nat) → (warmed read : Option ReadAccessKey) → Machine →
    Except (ExceptionalHalt × Machine × ReadTouch) (Machine × ReadTouch)
  | _, .push f, ctx, w, key, price, warmed, read, m =>
    match m.chargeGas price with
    | .error (e, m') => .error (e, m', { warmed := warmed })
    | .ok m₁ =>
      match m₁.push (f ctx w key) with
      | .error (e, m') => .error (e, m', { warmed := warmed, read := read })
      | .ok m₂ => .ok (m₂, { warmed := warmed, read := read })
  | _, .copyCode perWord, _, w, a, price, warmed, read, m =>
    match m.popToNat with
    | .error (e, m') => .error (e, m', {})
    | .ok (d, m₁) =>
      match m₁.popToNat with
      | .error (e, m') => .error (e, m', {})
      | .ok (o, m₂) =>
        match m₂.popToNat with
        | .error (e, m') => .error (e, m', {})
        | .ok (n, m₃) =>
          match m₃.chargeGas (price + perWord * ceilDiv n 32 + m₃.memoryExpansionCost [(d, n)]) with
          | .error (e, m') => .error (e, m', { warmed := warmed })
          | .ok m₄ =>
            .ok (m₄.writeMemory d
              ((Jaune.State.get w.state a).code.sliceD o n (HaltOp.toUInt8 .stop)),
              { warmed := warmed, read := read })

/-- The one step of the Read family: availability, the key's pop, the quote, then the result. -/
def ReadRow.step (row : ReadRow) (rules : ForkRules) (ctx : CallContext) (v : ReadView)
    (m : Machine) : Except (ExceptionalHalt × Machine × ReadTouch) (Machine × ReadTouch) :=
  if !row.available rules.opcodes then .error (.invalidOpcode .none, m, {})
  else
    match row.target.pop m with
    | .error (e, m') => .error (e, m', {})
    | .ok (key, m₁) =>
      let q := row.price.quote rules ctx v key
      row.result.finish ctx v.world key q.1 q.2 (row.target.readKey ctx key) m₁

/-- Apply a touch: warm the key, then record the read (the identity without block-access-list
rules). -/
def Frame.State.applyReadTouch (rules : ForkRules) (t : ReadTouch) (s : Frame.State) : Frame.State :=
  let s := match t.warmed with
    | none => s
    | some (.address a) => s.addAccessedAddress a
    | some (.slot a k) => s.addAccessedStorageKey a k
  match t.read with
  | none => s
  | some (.address a) => s.recordAccountRead rules a
  | some (.slot a k) => s.recordStorageRead rules a k

/-- Lift a read step onto the frame state: the machine and the touch, on both channels. -/
def Frame.State.liftRead (rules : ForkRules)
    (core : Machine → Except (ExceptionalHalt × Machine × ReadTouch) (Machine × ReadTouch))
    (s : Frame.State) : Except (ExceptionalHalt × Frame.State) Frame.State :=
  match core s.machine with
  | .error (e, m, t) => .error (e, (s.withMachine m).applyReadTouch rules t)
  | .ok (m, t) => .ok ((s.withMachine m).applyReadTouch rules t)

end Jaune
