import Jaune.RlpEval

/-!
# Receipt and transaction keys are injective (goal `jaune-shape-and-names-v1`, W2 cut F)

A body's tries are keyed by the RLP encoding of each operation's index. This module proves that
the key map `i ↦ (Rlp.Item.bytes i.toBytes).toBytes` is injective, from two generic facts:
`Nat.toBytes` (minimal big-endian bytes) is inverted by `Bytes.toNat`, and the RLP encoding of a
byte string is injective.
-/

namespace Jaune

/-! ### Big-endian bytes -/

theorem Bytes.toNat.aux_eq (acc : Nat) (bs : Bytes) :
    Bytes.toNat.aux acc bs = acc * 256 ^ bs.length + Bytes.toNat.aux 0 bs := by
  induction bs generalizing acc with
  | nil => simp [Bytes.toNat.aux]
  | cons b bs ih =>
    simp only [Bytes.toNat.aux]
    rw [ih, ih (0 * 256 + b.toNat)]
    simp only [List.length_cons, Nat.pow_succ, Nat.zero_mul, Nat.zero_add, Nat.add_mul]
    rw [Nat.mul_assoc, Nat.mul_comm 256 (256 ^ bs.length), Nat.add_assoc]

theorem Bytes.toNat_cons (b : UInt8) (bs : Bytes) :
    Bytes.toNat (b :: bs) = b.toNat * 256 ^ bs.length + Bytes.toNat bs := by
  show Bytes.toNat.aux 0 (b :: bs) = _
  simp only [Bytes.toNat.aux]
  rw [Bytes.toNat.aux_eq]
  simp [Bytes.toNat]

theorem Nat.toBytes.aux_toNat :
    ∀ (n : Nat) (acc : Bytes),
      Bytes.toNat (Nat.toBytes.aux acc n) = n * 256 ^ acc.length + Bytes.toNat acc
  | 0, acc => by simp [Nat.toBytes.aux]
  | n + 1, acc => by
    rw [Nat.toBytes.aux]
    have := Nat.toBytes.aux_toNat ((n + 1) / 256) (((n + 1) % 256).toUInt8 :: acc)
    rw [this, Bytes.toNat_cons]
    have hm : (((n + 1) % 256).toUInt8).toNat = (n + 1) % 256 := by
      simp [Nat.toUInt8]
    rw [hm, List.length_cons, Nat.pow_succ, ← Nat.add_assoc]
    conv_rhs => rw [← Nat.div_add_mod (n + 1) 256]
    simp only [Nat.add_mul, Nat.mul_assoc]
    rw [Nat.mul_comm (256 ^ List.length acc) 256, Nat.mul_left_comm]
termination_by n => n
decreasing_by omega

theorem Bytes.toNat_toBytes (n : Nat) : Bytes.toNat (Nat.toBytes n) = n := by
  have := Nat.toBytes.aux_toNat n []
  simpa [Nat.toBytes, Bytes.toNat, Bytes.toNat.aux] using this

theorem Nat.toBytes_injective : Function.Injective Nat.toBytes := by
  intro m n h
  rw [← Bytes.toNat_toBytes m, ← Bytes.toNat_toBytes n, h]

theorem Nat.toBytes.aux_append :
    ∀ (n : Nat) (acc : Bytes), Nat.toBytes.aux acc n = Nat.toBytes.aux [] n ++ acc
  | 0, acc => by simp [Nat.toBytes.aux]
  | n + 1, acc => by
    conv_lhs => rw [Nat.toBytes.aux]
    conv_rhs => rw [Nat.toBytes.aux]
    rw [Nat.toBytes.aux_append ((n + 1) / 256) (((n + 1) % 256).toUInt8 :: acc),
      Nat.toBytes.aux_append ((n + 1) / 256) [((n + 1) % 256).toUInt8]]
    simp
termination_by n => n
decreasing_by all_goals omega

theorem Nat.toBytes_length_succ (n : Nat) :
    (Nat.toBytes (n + 1)).length = (Nat.toBytes ((n + 1) / 256)).length + 1 := by
  unfold Nat.toBytes
  rw [Nat.toBytes.aux, Nat.toBytes.aux_append]
  simp

theorem Nat.toBytes_length_mono : ∀ (n m : Nat), m ≤ n →
    (Nat.toBytes m).length ≤ (Nat.toBytes n).length
  | n, 0, _ => by simp [Nat.toBytes, Nat.toBytes.aux]
  | 0, m + 1, h => by omega
  | n + 1, m + 1, h => by
    rw [Nat.toBytes_length_succ, Nat.toBytes_length_succ]
    have := Nat.toBytes_length_mono ((n + 1) / 256) ((m + 1) / 256) (Nat.div_le_div_right h)
    omega
termination_by n => n
decreasing_by omega

theorem Nat.toBytesPack_of_pos {n : Nat} (h : 0 < n) : Nat.toBytesPack n = Nat.toBytes n := by
  cases n with
  | zero => omega
  | succ n => rfl

/-! ### The RLP encoding of a byte string -/

theorem Rlp.Item.toBytes_bytes_small {b : UInt8} (h : b < 0x80) :
    (Rlp.Item.bytes [b]).toBytes = [b] := by
  simp [Rlp.Item.toBytes, h]

theorem Rlp.Item.toBytes_bytes_short {bs : Bytes} (hl : bs.length < 56)
    (hs : ∀ b, bs = [b] → ¬ b < 0x80) :
    (Rlp.Item.bytes bs).toBytes = (0x80 + bs.length.toUInt8) :: bs := by
  match bs, hl, hs with
  | [b], _, hs =>
    have := hs b rfl
    simp [Rlp.Item.toBytes, this]
  | [], _, _ => simp [Rlp.Item.toBytes]
  | b :: c :: bs, hl, _ =>
    simp only [Rlp.Item.toBytes]
    simp only [hl, ↓reduceIte]

theorem Rlp.Item.toBytes_bytes_long {bs : Bytes} (hl : ¬ bs.length < 56) :
    (Rlp.Item.bytes bs).toBytes =
      (0xB7 + (Nat.toBytes bs.length).length.toUInt8) :: (Nat.toBytes bs.length ++ bs) := by
  match bs, hl with
  | [], hl => simp at hl
  | [b], hl => simp at hl
  | b :: c :: bs, hl =>
    simp only [Rlp.Item.toBytes]
    simp only [hl, ↓reduceIte]
    rw [Nat.toBytesPack_of_pos (by simp)]

/-- The RLP encoding of a byte string is injective. -/
theorem Rlp.Item.toBytes_bytes_injective :
    Function.Injective (fun bs : Bytes => (Rlp.Item.bytes bs).toBytes) := by
  intro bs cs h
  simp only at h
  -- Classify by form: one small byte, short, long.
  by_cases hbs : bs.length < 56 <;> by_cases hcs : cs.length < 56
  · by_cases hb : ∃ b, bs = [b] ∧ b < 0x80 <;> by_cases hc : ∃ c, cs = [c] ∧ c < 0x80
    · obtain ⟨b, rfl, hb⟩ := hb
      obtain ⟨c, rfl, hc⟩ := hc
      rw [Rlp.Item.toBytes_bytes_small hb, Rlp.Item.toBytes_bytes_small hc] at h
      exact h
    · obtain ⟨b, rfl, hb⟩ := hb
      rw [Rlp.Item.toBytes_bytes_small hb,
        Rlp.Item.toBytes_bytes_short hcs (fun c e hc' => hc ⟨c, e, hc'⟩)] at h
      have hl := congrArg List.length h
      simp at hl
      subst hl
      simp at h
      subst h
      exact absurd hb (by decide)
    · obtain ⟨c, rfl, hc⟩ := hc
      rw [Rlp.Item.toBytes_bytes_small hc,
        Rlp.Item.toBytes_bytes_short hbs (fun b e hb' => hb ⟨b, e, hb'⟩)] at h
      have hl := congrArg List.length h
      simp at hl
      subst hl
      simp at h
      subst h
      exact absurd hc (by decide)
    · rw [Rlp.Item.toBytes_bytes_short hbs (fun b e hb' => hb ⟨b, e, hb'⟩),
        Rlp.Item.toBytes_bytes_short hcs (fun c e hc' => hc ⟨c, e, hc'⟩)] at h
      exact (List.cons.inj h).2
  · exfalso
    have hl := congrArg List.length h
    by_cases hb : ∃ b, bs = [b] ∧ b < 0x80
    · obtain ⟨b, rfl, hb⟩ := hb
      rw [Rlp.Item.toBytes_bytes_small hb, Rlp.Item.toBytes_bytes_long hcs] at hl
      simp only [List.length_cons, List.length_append] at hl hbs hcs
      omega
    · rw [Rlp.Item.toBytes_bytes_short hbs (fun b e hb' => hb ⟨b, e, hb'⟩),
        Rlp.Item.toBytes_bytes_long hcs] at hl
      simp only [List.length_cons, List.length_append] at hl hbs hcs
      omega
  · exfalso
    have hl := congrArg List.length h
    by_cases hc : ∃ c, cs = [c] ∧ c < 0x80
    · obtain ⟨c, rfl, hc⟩ := hc
      rw [Rlp.Item.toBytes_bytes_small hc, Rlp.Item.toBytes_bytes_long hbs] at hl
      simp only [List.length_cons, List.length_append] at hl hbs hcs
      omega
    · rw [Rlp.Item.toBytes_bytes_short hcs (fun c e hc' => hc ⟨c, e, hc'⟩),
        Rlp.Item.toBytes_bytes_long hbs] at hl
      simp only [List.length_cons, List.length_append] at hl hbs hcs
      omega
  · rw [Rlp.Item.toBytes_bytes_long hbs, Rlp.Item.toBytes_bytes_long hcs] at h
    have h' := (List.cons.inj h).2
    have hl := congrArg List.length h'
    simp only [List.length_append] at hl
    have hlen : bs.length = cs.length := by
      rcases Nat.lt_trichotomy bs.length cs.length with hlt | heq | hgt
      · have := Nat.toBytes_length_mono cs.length bs.length (Nat.le_of_lt hlt)
        omega
      · exact heq
      · have := Nat.toBytes_length_mono bs.length cs.length (Nat.le_of_lt hgt)
        omega
    rw [hlen] at h'
    exact List.append_cancel_left h'

/-- The key of index `i` in a body's tries: the RLP encoding of `i`'s minimal big-endian bytes
(`Rlp.Item.toBytes (.bytes i.toBytes)`, as the transaction, receipt and withdrawal steps write it). -/
def rlpKey (i : Nat) : Bytes := (Rlp.Item.bytes (Nat.toBytes i)).toBytes

/-- Distinct indices have distinct trie keys. -/
theorem rlpKey_injective : Function.Injective rlpKey := by
  intro i j h
  exact Nat.toBytes_injective (Rlp.Item.toBytes_bytes_injective h)

end Jaune
