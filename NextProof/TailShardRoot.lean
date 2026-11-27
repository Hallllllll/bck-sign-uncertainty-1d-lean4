import NextProof.TailShardCore

import NextProof.TailQRoot

import NextProof.TailShardArithmetic

namespace NextProof.Tail.Shards

set_option maxHeartbeats 0

set_option maxRecDepth 200000

set_option exponentiation.threshold 1000000

theorem valid_node00_02 : Valid node00_02 0 := by
  exact join_valid (valid_of_checked c00) (valid_of_checked c01) (by decide +kernel)

theorem valid_node02_04 : Valid node02_04 512 := by
  exact join_valid (valid_of_checked c02) (valid_of_checked c03) (by decide +kernel)

theorem valid_node00_04 : Valid node00_04 0 := by
  exact join_valid valid_node00_02 valid_node02_04 (by decide +kernel)

theorem valid_node04_06 : Valid node04_06 1024 := by
  exact join_valid (valid_of_checked c04) (valid_of_checked c05) (by decide +kernel)

theorem valid_node06_08 : Valid node06_08 1536 := by
  exact join_valid (valid_of_checked c06) (valid_of_checked c07) (by decide +kernel)

theorem valid_node04_08 : Valid node04_08 1024 := by
  exact join_valid valid_node04_06 valid_node06_08 (by decide +kernel)

theorem valid_node00_08 : Valid node00_08 0 := by
  exact join_valid valid_node00_04 valid_node04_08 (by decide +kernel)

theorem valid_node08_10 : Valid node08_10 2048 := by
  exact join_valid (valid_of_checked c08) (valid_of_checked c09) (by decide +kernel)

theorem valid_node10_12 : Valid node10_12 2560 := by
  exact join_valid (valid_of_checked c10) (valid_of_checked c11) (by decide +kernel)

theorem valid_node08_12 : Valid node08_12 2048 := by
  exact join_valid valid_node08_10 valid_node10_12 (by decide +kernel)

theorem valid_node12_14 : Valid node12_14 3072 := by
  exact join_valid (valid_of_checked c12) (valid_of_checked c13) (by decide +kernel)

theorem valid_node14_16 : Valid node14_16 3584 := by
  exact join_valid (valid_of_checked c14) (valid_of_checked c15) (by decide +kernel)

theorem valid_node12_16 : Valid node12_16 3072 := by
  exact join_valid valid_node12_14 valid_node14_16 (by decide +kernel)

theorem valid_node08_16 : Valid node08_16 2048 := by
  exact join_valid valid_node08_12 valid_node12_16 (by decide +kernel)

theorem valid_node00_16 : Valid node00_16 0 := by
  exact join_valid valid_node00_08 valid_node08_16 (by decide +kernel)

theorem valid_node16_18 : Valid node16_18 4096 := by
  exact join_valid (valid_of_checked c16) (valid_of_checked c17) (by decide +kernel)

theorem valid_node18_20 : Valid node18_20 4608 := by
  exact join_valid (valid_of_checked c18) (valid_of_checked c19) (by decide +kernel)

theorem valid_node16_20 : Valid node16_20 4096 := by
  exact join_valid valid_node16_18 valid_node18_20 (by decide +kernel)

theorem valid_node20_22 : Valid node20_22 5120 := by
  exact join_valid (valid_of_checked c20) (valid_of_checked c21) (by decide +kernel)

theorem valid_node22_24 : Valid node22_24 5632 := by
  exact join_valid (valid_of_checked c22) (valid_of_checked c23) (by decide +kernel)

theorem valid_node20_24 : Valid node20_24 5120 := by
  exact join_valid valid_node20_22 valid_node22_24 (by decide +kernel)

theorem valid_node16_24 : Valid node16_24 4096 := by
  exact join_valid valid_node16_20 valid_node20_24 (by decide +kernel)

theorem valid_node24_26 : Valid node24_26 6144 := by
  exact join_valid (valid_of_checked c24) (valid_of_checked c25) (by decide +kernel)

theorem valid_node26_28 : Valid node26_28 6656 := by
  exact join_valid (valid_of_checked c26) (valid_of_checked c27) (by decide +kernel)

theorem valid_node24_28 : Valid node24_28 6144 := by
  exact join_valid valid_node24_26 valid_node26_28 (by decide +kernel)

theorem valid_node28_30 : Valid node28_30 7168 := by
  exact join_valid (valid_of_checked c28) (valid_of_checked c29) (by decide +kernel)

theorem valid_node30_32 : Valid node30_32 7680 := by
  exact join_valid (valid_of_checked c30) (valid_of_checked c31) (by decide +kernel)

theorem valid_node28_32 : Valid node28_32 7168 := by
  exact join_valid valid_node28_30 valid_node30_32 (by decide +kernel)

theorem valid_node24_32 : Valid node24_32 6144 := by
  exact join_valid valid_node24_28 valid_node28_32 (by decide +kernel)

theorem valid_node16_32 : Valid node16_32 4096 := by
  exact join_valid valid_node16_24 valid_node24_32 (by decide +kernel)

theorem valid_node00_32 : Valid node00_32 0 := by
  exact join_valid valid_node00_16 valid_node16_32 (by decide +kernel)

theorem valid_node32_34 : Valid node32_34 8192 := by
  exact join_valid (valid_of_checked c32) (valid_of_checked c33) (by decide +kernel)

theorem valid_node34_36 : Valid node34_36 8704 := by
  exact join_valid (valid_of_checked c34) (valid_of_checked c35) (by decide +kernel)

theorem valid_node32_36 : Valid node32_36 8192 := by
  exact join_valid valid_node32_34 valid_node34_36 (by decide +kernel)

theorem valid_node36_38 : Valid node36_38 9216 := by
  exact join_valid (valid_of_checked c36) (valid_of_checked c37) (by decide +kernel)

theorem valid_node38_40 : Valid node38_40 9728 := by
  exact join_valid (valid_of_checked c38) (valid_of_checked c39) (by decide +kernel)

theorem valid_node36_40 : Valid node36_40 9216 := by
  exact join_valid valid_node36_38 valid_node38_40 (by decide +kernel)

theorem valid_node32_40 : Valid node32_40 8192 := by
  exact join_valid valid_node32_36 valid_node36_40 (by decide +kernel)

theorem valid_node40_42 : Valid node40_42 10240 := by
  exact join_valid (valid_of_checked c40) (valid_of_checked c41) (by decide +kernel)

theorem valid_node42_44 : Valid node42_44 10752 := by
  exact join_valid (valid_of_checked c42) (valid_of_checked c43) (by decide +kernel)

theorem valid_node40_44 : Valid node40_44 10240 := by
  exact join_valid valid_node40_42 valid_node42_44 (by decide +kernel)

theorem valid_node44_46 : Valid node44_46 11264 := by
  exact join_valid (valid_of_checked c44) (valid_of_checked c45) (by decide +kernel)

theorem valid_node46_48 : Valid node46_48 11776 := by
  exact join_valid (valid_of_checked c46) (valid_of_checked c47) (by decide +kernel)

theorem valid_node44_48 : Valid node44_48 11264 := by
  exact join_valid valid_node44_46 valid_node46_48 (by decide +kernel)

theorem valid_node40_48 : Valid node40_48 10240 := by
  exact join_valid valid_node40_44 valid_node44_48 (by decide +kernel)

theorem valid_node32_48 : Valid node32_48 8192 := by
  exact join_valid valid_node32_40 valid_node40_48 (by decide +kernel)

theorem valid_node48_50 : Valid node48_50 12288 := by
  exact join_valid (valid_of_checked c48) (valid_of_checked c49) (by decide +kernel)

theorem valid_node50_52 : Valid node50_52 12800 := by
  exact join_valid (valid_of_checked c50) (valid_of_checked c51) (by decide +kernel)

theorem valid_node48_52 : Valid node48_52 12288 := by
  exact join_valid valid_node48_50 valid_node50_52 (by decide +kernel)

theorem valid_node52_54 : Valid node52_54 13312 := by
  exact join_valid (valid_of_checked c52) (valid_of_checked c53) (by decide +kernel)

theorem valid_node54_56 : Valid node54_56 13824 := by
  exact join_valid (valid_of_checked c54) (valid_of_checked c55) (by decide +kernel)

theorem valid_node52_56 : Valid node52_56 13312 := by
  exact join_valid valid_node52_54 valid_node54_56 (by decide +kernel)

theorem valid_node48_56 : Valid node48_56 12288 := by
  exact join_valid valid_node48_52 valid_node52_56 (by decide +kernel)

theorem valid_node56_58 : Valid node56_58 14336 := by
  exact join_valid (valid_of_checked c56) (valid_of_checked c57) (by decide +kernel)

theorem valid_node58_60 : Valid node58_60 14848 := by
  exact join_valid (valid_of_checked c58) (valid_of_checked c59) (by decide +kernel)

theorem valid_node56_60 : Valid node56_60 14336 := by
  exact join_valid valid_node56_58 valid_node58_60 (by decide +kernel)

theorem valid_node60_62 : Valid node60_62 15360 := by
  exact join_valid (valid_of_checked c60) (valid_of_checked c61) (by decide +kernel)

theorem valid_node62_64 : Valid node62_64 15872 := by
  exact join_valid (valid_of_checked c62) (valid_of_checked c63) (by decide +kernel)

theorem valid_node62_65 : Valid node62_65 15872 := by
  exact join_valid valid_node62_64 (valid_of_checked c64) (by decide +kernel)

theorem valid_node60_65 : Valid node60_65 15360 := by
  exact join_valid valid_node60_62 valid_node62_65 (by decide +kernel)

theorem valid_node56_65 : Valid node56_65 14336 := by
  exact join_valid valid_node56_60 valid_node60_65 (by decide +kernel)

theorem valid_node48_65 : Valid node48_65 12288 := by
  exact join_valid valid_node48_56 valid_node56_65 (by decide +kernel)

theorem valid_node32_65 : Valid node32_65 8192 := by
  exact join_valid valid_node32_48 valid_node48_65 (by decide +kernel)

theorem valid_node00_65 : Valid node00_65 0 := by
  exact join_valid valid_node00_32 valid_node32_65 (by decide +kernel)

theorem powerLower_eq_literalPower : powerLower = literalPower := by
  exact root_eq valid_node00_65 (by decide +kernel) whole_value whole_bound (by decide +kernel)

theorem literalPower_le (z : ℝ) (hz : 0 ≤ z) :
    horner z literalPower ≤ (2:ℝ)^100 * Exterior.projected16384.eval₂ (algebraMap ℚ ℝ) (65536*z) := by
  rw [← powerLower_eq_literalPower]
  exact powerLower_le z hz

end NextProof.Tail.Shards

#print axioms NextProof.Tail.Shards.powerLower_eq_literalPower
#print axioms NextProof.Tail.Shards.literalPower_le
