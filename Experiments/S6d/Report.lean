import Experiments.S6d.Count

-- The 32 measured pairs (group, Jaune name, B256 side, BitVec side): see pairs.json.

#s6d_count Jaune.B256.s6d_toNat_lt S6d.V.toNat_lt
#s6d_count Jaune.B256.s6d_toNat_inj S6d.V.toNat_inj
#s6d_count Jaune.B256.s6d_toNat_toB256 S6d.V.toNat_ofNat
#s6d_count Jaune.B256.s6d_toNat_toB256_of_lt S6d.V.toNat_ofNat_of_lt
#s6d_count Jaune.B256.s6d_toNat_mul S6d.V.toNat_mul
#s6d_count Jaune.B256.s6d_toNat_mod S6d.V.toNat_mod
#s6d_count Jaune.B256.s6d_toNat_add S6d.V.toNat_add
#s6d_count Jaune.B256.s6d_toNat_add_eq_of_nof S6d.V.toNat_add_eq_of_nof
#s6d_count Jaune.B256.s6d_toNat_sub_eq_of_le S6d.V.toNat_sub_eq_of_le
#s6d_count Jaune.B256.s6d_toNat_div S6d.V.toNat_div
#s6d_count Jaune.B256.s6d_toNat_lt_toNat S6d.V.toNat_lt_toNat
#s6d_count Jaune.B256.s6d_lt_iff_toNat_lt_toNat S6d.V.lt_iff_toNat_lt_toNat
#s6d_count Jaune.B256.s6d_le_iff_toNat_le_toNat S6d.V.le_iff_toNat_le_toNat
#s6d_count Jaune.B256.s6d_one_ne_zero S6d.V.one_ne_zero
#s6d_count Jaune.B256.s6d_eqCheck_ne_zero_iff S6d.V.eqCheck_ne_zero_iff
#s6d_count Jaune.B256.s6d_ltCheck_ne_zero_iff S6d.V.ltCheck_ne_zero_iff
#s6d_count Jaune.B256.s6d_gtCheck_eq_zero_iff S6d.V.gtCheck_eq_zero_iff
#s6d_count Jaune.B256.s6d_ltCheck_eq_zero_of_toNat_le S6d.V.ltCheck_eq_zero_of_toNat_le
#s6d_count Jaune.B256.s6d_gtCheck_ne_zero_of_toNat_lt S6d.V.gtCheck_ne_zero_of_toNat_lt
#s6d_count Jaune.B256.s6d_length_toBytes S6d.V.length_toBytes
#s6d_count Jaune.B256.s6d_toB256_toBytes S6d.V.toW_toBytes
#s6d_count Jaune.List.s6d_toB256_pair S6d.V.toW_pair
#s6d_count Jaune.B256.s6d_toNat_shiftRight S6d.V.toNat_shiftRight
#s6d_count Jaune.B256.s6d_toNat_shiftLeft S6d.V.toNat_shiftLeft
#s6d_count Jaune.B256.s6d_sdiv_smin_negOne S6d.V.sdiv_smin_negOne
#s6d_count Jaune.B256.s6d_sdiv_of_nonneg S6d.V.sdiv_of_nonneg
#s6d_count Jaune.B256.s6d_arithShiftRight_of_nonneg S6d.V.sar_of_nonneg
#s6d_count Jaune.B256.s6d_toNat_ne_zero S6d.V.toNat_ne_zero
#s6d_count Jaune.B256.s6d_nofm_iff_le_div S6d.V.nofm_iff_le_div
#s6d_count Jaune.B256.s6d_toNat_mul_eq_of_nofm S6d.V.toNat_mul_eq_of_nofm
#s6d_count Jaune.B256.s6d_toNat_mulmod S6d.V.toNat_mulmod
#s6d_count Jaune.B256.s6d_toNat_addmod S6d.V.toNat_addmod
