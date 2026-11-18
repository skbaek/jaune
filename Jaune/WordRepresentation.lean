import Jaune.MulDiv

namespace Jaune.WordRepresentation

/-- The exact representation map for the interpreter experiment. -/
def encode (x : U256) : BitVec 256 := BitVec.ofNat 256 x.toNat

def decode (v : BitVec 256) : U256 := Nat.toU256 v.toNat

theorem encode_toNat (x : U256) : (encode x).toNat = x.toNat := by
  rw [encode, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (U256.toNat_lt x)]

theorem decode_toNat (v : BitVec 256) : (decode v).toNat = v.toNat :=
  U256.toNat_toU256_of_lt v.isLt

theorem decode_encode (x : U256) : decode (encode x) = x := by
  rw [decode, encode_toNat, toU256_toNat]

theorem encode_decode (v : BitVec 256) : encode (decode v) = v := by
  exact BitVec.eq_of_toNat_eq ((encode_toNat _).trans (decode_toNat _))

def equivalence : U256 ≃ BitVec 256 := ⟨encode, decode, decode_encode, encode_decode⟩

theorem encode_add (x y : U256) : encode (x + y) = encode x + encode y := by
  apply BitVec.eq_of_toNat_eq
  rw [encode_toNat, U256.toNat_add, BitVec.toNat_add, encode_toNat, encode_toNat]
  rfl

theorem encode_sub (x y : U256) : encode (x - y) = encode x - encode y := by
  apply BitVec.eq_of_toNat_eq
  rw [encode_toNat, U256.toNat_sub, BitVec.toNat_sub, encode_toNat, encode_toNat]
  have hy := U256.toNat_lt y
  rw [Nat.lo_eq, show 2 ^ 256 + x.toNat - y.toNat = 2 ^ 256 - y.toNat + x.toNat by omega]

theorem encode_mul (x y : U256) : encode (x * y) = encode x * encode y := by
  apply BitVec.eq_of_toNat_eq
  rw [encode_toNat, U256.toNat_mul, BitVec.toNat_mul, encode_toNat, encode_toNat]
  rfl

theorem encode_zero : encode 0 = 0 := rfl

def remainder (x y : BitVec 256) : BitVec 256 := if y = 0 then 0 else x % y

theorem encode_remainder (x y : U256) : encode (x % y) = remainder (encode x) (encode y) := by
  by_cases zero : y = 0
  · subst y
    have hmod : x % (0 : U256) = 0 := by
      change (U256.divMod x 0).snd = 0
      simp [U256.divMod]
    rw [hmod, encode_zero, remainder, ite_eq_left rfl]
  · have nz : encode y ≠ 0 := fun eq => zero (equivalence.injective (eq.trans encode_zero.symm))
    rw [remainder, ite_eq_right nz]
    apply BitVec.eq_of_toNat_eq
    rw [encode_toNat, U256.toNat_mod zero, BitVec.toNat_umod, encode_toNat, encode_toNat]

end Jaune.WordRepresentation
