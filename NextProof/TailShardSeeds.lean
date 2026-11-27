import NextProof.TailShardWindow

namespace NextProof.Tail.Shards

set_option maxRecDepth 200000

set_option maxHeartbeats 0

def seed00 : ℕ := (tailInt% "00-seed.bin").toNat

theorem seed_ok00 : Light.seed 0 = seed00 := by
  rfl

def seed01 : ℕ := (tailInt% "01-seed.bin").toNat

theorem seed_ok01 : Light.seed 128 = seed01 := by
  rw [show 128 = 0 + 128 by rfl, Light.seed_add, seed_ok00]
  decide +kernel

def seed02 : ℕ := (tailInt% "02-seed.bin").toNat

theorem seed_ok02 : Light.seed 256 = seed02 := by
  rw [show 256 = 128 + 128 by rfl, Light.seed_add, seed_ok01]
  decide +kernel

def seed03 : ℕ := (tailInt% "03-seed.bin").toNat

theorem seed_ok03 : Light.seed 384 = seed03 := by
  rw [show 384 = 256 + 128 by rfl, Light.seed_add, seed_ok02]
  decide +kernel

def seed04 : ℕ := (tailInt% "04-seed.bin").toNat

theorem seed_ok04 : Light.seed 512 = seed04 := by
  rw [show 512 = 384 + 128 by rfl, Light.seed_add, seed_ok03]
  decide +kernel

def seed05 : ℕ := (tailInt% "05-seed.bin").toNat

theorem seed_ok05 : Light.seed 640 = seed05 := by
  rw [show 640 = 512 + 128 by rfl, Light.seed_add, seed_ok04]
  decide +kernel

def seed06 : ℕ := (tailInt% "06-seed.bin").toNat

theorem seed_ok06 : Light.seed 768 = seed06 := by
  rw [show 768 = 640 + 128 by rfl, Light.seed_add, seed_ok05]
  decide +kernel

def seed07 : ℕ := (tailInt% "07-seed.bin").toNat

theorem seed_ok07 : Light.seed 896 = seed07 := by
  rw [show 896 = 768 + 128 by rfl, Light.seed_add, seed_ok06]
  decide +kernel

def seed08 : ℕ := (tailInt% "08-seed.bin").toNat

theorem seed_ok08 : Light.seed 1024 = seed08 := by
  rw [show 1024 = 896 + 128 by rfl, Light.seed_add, seed_ok07]
  decide +kernel

def seed09 : ℕ := (tailInt% "09-seed.bin").toNat

theorem seed_ok09 : Light.seed 1152 = seed09 := by
  rw [show 1152 = 1024 + 128 by rfl, Light.seed_add, seed_ok08]
  decide +kernel

def seed10 : ℕ := (tailInt% "10-seed.bin").toNat

theorem seed_ok10 : Light.seed 1280 = seed10 := by
  rw [show 1280 = 1152 + 128 by rfl, Light.seed_add, seed_ok09]
  decide +kernel

def seed11 : ℕ := (tailInt% "11-seed.bin").toNat

theorem seed_ok11 : Light.seed 1408 = seed11 := by
  rw [show 1408 = 1280 + 128 by rfl, Light.seed_add, seed_ok10]
  decide +kernel

def seed12 : ℕ := (tailInt% "12-seed.bin").toNat

theorem seed_ok12 : Light.seed 1536 = seed12 := by
  rw [show 1536 = 1408 + 128 by rfl, Light.seed_add, seed_ok11]
  decide +kernel

def seed13 : ℕ := (tailInt% "13-seed.bin").toNat

theorem seed_ok13 : Light.seed 1664 = seed13 := by
  rw [show 1664 = 1536 + 128 by rfl, Light.seed_add, seed_ok12]
  decide +kernel

def seed14 : ℕ := (tailInt% "14-seed.bin").toNat

theorem seed_ok14 : Light.seed 1792 = seed14 := by
  rw [show 1792 = 1664 + 128 by rfl, Light.seed_add, seed_ok13]
  decide +kernel

def seed15 : ℕ := (tailInt% "15-seed.bin").toNat

theorem seed_ok15 : Light.seed 1920 = seed15 := by
  rw [show 1920 = 1792 + 128 by rfl, Light.seed_add, seed_ok14]
  decide +kernel

def seed16 : ℕ := (tailInt% "16-seed.bin").toNat

theorem seed_ok16 : Light.seed 2048 = seed16 := by
  rw [show 2048 = 1920 + 128 by rfl, Light.seed_add, seed_ok15]
  decide +kernel

def seed17 : ℕ := (tailInt% "17-seed.bin").toNat

theorem seed_ok17 : Light.seed 2176 = seed17 := by
  rw [show 2176 = 2048 + 128 by rfl, Light.seed_add, seed_ok16]
  decide +kernel

def seed18 : ℕ := (tailInt% "18-seed.bin").toNat

theorem seed_ok18 : Light.seed 2304 = seed18 := by
  rw [show 2304 = 2176 + 128 by rfl, Light.seed_add, seed_ok17]
  decide +kernel

def seed19 : ℕ := (tailInt% "19-seed.bin").toNat

theorem seed_ok19 : Light.seed 2432 = seed19 := by
  rw [show 2432 = 2304 + 128 by rfl, Light.seed_add, seed_ok18]
  decide +kernel

def seed20 : ℕ := (tailInt% "20-seed.bin").toNat

theorem seed_ok20 : Light.seed 2560 = seed20 := by
  rw [show 2560 = 2432 + 128 by rfl, Light.seed_add, seed_ok19]
  decide +kernel

def seed21 : ℕ := (tailInt% "21-seed.bin").toNat

theorem seed_ok21 : Light.seed 2688 = seed21 := by
  rw [show 2688 = 2560 + 128 by rfl, Light.seed_add, seed_ok20]
  decide +kernel

def seed22 : ℕ := (tailInt% "22-seed.bin").toNat

theorem seed_ok22 : Light.seed 2816 = seed22 := by
  rw [show 2816 = 2688 + 128 by rfl, Light.seed_add, seed_ok21]
  decide +kernel

def seed23 : ℕ := (tailInt% "23-seed.bin").toNat

theorem seed_ok23 : Light.seed 2944 = seed23 := by
  rw [show 2944 = 2816 + 128 by rfl, Light.seed_add, seed_ok22]
  decide +kernel

def seed24 : ℕ := (tailInt% "24-seed.bin").toNat

theorem seed_ok24 : Light.seed 3072 = seed24 := by
  rw [show 3072 = 2944 + 128 by rfl, Light.seed_add, seed_ok23]
  decide +kernel

def seed25 : ℕ := (tailInt% "25-seed.bin").toNat

theorem seed_ok25 : Light.seed 3200 = seed25 := by
  rw [show 3200 = 3072 + 128 by rfl, Light.seed_add, seed_ok24]
  decide +kernel

def seed26 : ℕ := (tailInt% "26-seed.bin").toNat

theorem seed_ok26 : Light.seed 3328 = seed26 := by
  rw [show 3328 = 3200 + 128 by rfl, Light.seed_add, seed_ok25]
  decide +kernel

def seed27 : ℕ := (tailInt% "27-seed.bin").toNat

theorem seed_ok27 : Light.seed 3456 = seed27 := by
  rw [show 3456 = 3328 + 128 by rfl, Light.seed_add, seed_ok26]
  decide +kernel

def seed28 : ℕ := (tailInt% "28-seed.bin").toNat

theorem seed_ok28 : Light.seed 3584 = seed28 := by
  rw [show 3584 = 3456 + 128 by rfl, Light.seed_add, seed_ok27]
  decide +kernel

def seed29 : ℕ := (tailInt% "29-seed.bin").toNat

theorem seed_ok29 : Light.seed 3712 = seed29 := by
  rw [show 3712 = 3584 + 128 by rfl, Light.seed_add, seed_ok28]
  decide +kernel

def seed30 : ℕ := (tailInt% "30-seed.bin").toNat

theorem seed_ok30 : Light.seed 3840 = seed30 := by
  rw [show 3840 = 3712 + 128 by rfl, Light.seed_add, seed_ok29]
  decide +kernel

def seed31 : ℕ := (tailInt% "31-seed.bin").toNat

theorem seed_ok31 : Light.seed 3968 = seed31 := by
  rw [show 3968 = 3840 + 128 by rfl, Light.seed_add, seed_ok30]
  decide +kernel

def seed32 : ℕ := (tailInt% "32-seed.bin").toNat

theorem seed_ok32 : Light.seed 4096 = seed32 := by
  rw [show 4096 = 3968 + 128 by rfl, Light.seed_add, seed_ok31]
  decide +kernel

def seed33 : ℕ := (tailInt% "33-seed.bin").toNat

theorem seed_ok33 : Light.seed 4224 = seed33 := by
  rw [show 4224 = 4096 + 128 by rfl, Light.seed_add, seed_ok32]
  decide +kernel

def seed34 : ℕ := (tailInt% "34-seed.bin").toNat

theorem seed_ok34 : Light.seed 4352 = seed34 := by
  rw [show 4352 = 4224 + 128 by rfl, Light.seed_add, seed_ok33]
  decide +kernel

def seed35 : ℕ := (tailInt% "35-seed.bin").toNat

theorem seed_ok35 : Light.seed 4480 = seed35 := by
  rw [show 4480 = 4352 + 128 by rfl, Light.seed_add, seed_ok34]
  decide +kernel

def seed36 : ℕ := (tailInt% "36-seed.bin").toNat

theorem seed_ok36 : Light.seed 4608 = seed36 := by
  rw [show 4608 = 4480 + 128 by rfl, Light.seed_add, seed_ok35]
  decide +kernel

def seed37 : ℕ := (tailInt% "37-seed.bin").toNat

theorem seed_ok37 : Light.seed 4736 = seed37 := by
  rw [show 4736 = 4608 + 128 by rfl, Light.seed_add, seed_ok36]
  decide +kernel

def seed38 : ℕ := (tailInt% "38-seed.bin").toNat

theorem seed_ok38 : Light.seed 4864 = seed38 := by
  rw [show 4864 = 4736 + 128 by rfl, Light.seed_add, seed_ok37]
  decide +kernel

def seed39 : ℕ := (tailInt% "39-seed.bin").toNat

theorem seed_ok39 : Light.seed 4992 = seed39 := by
  rw [show 4992 = 4864 + 128 by rfl, Light.seed_add, seed_ok38]
  decide +kernel

def seed40 : ℕ := (tailInt% "40-seed.bin").toNat

theorem seed_ok40 : Light.seed 5120 = seed40 := by
  rw [show 5120 = 4992 + 128 by rfl, Light.seed_add, seed_ok39]
  decide +kernel

def seed41 : ℕ := (tailInt% "41-seed.bin").toNat

theorem seed_ok41 : Light.seed 5248 = seed41 := by
  rw [show 5248 = 5120 + 128 by rfl, Light.seed_add, seed_ok40]
  decide +kernel

def seed42 : ℕ := (tailInt% "42-seed.bin").toNat

theorem seed_ok42 : Light.seed 5376 = seed42 := by
  rw [show 5376 = 5248 + 128 by rfl, Light.seed_add, seed_ok41]
  decide +kernel

def seed43 : ℕ := (tailInt% "43-seed.bin").toNat

theorem seed_ok43 : Light.seed 5504 = seed43 := by
  rw [show 5504 = 5376 + 128 by rfl, Light.seed_add, seed_ok42]
  decide +kernel

def seed44 : ℕ := (tailInt% "44-seed.bin").toNat

theorem seed_ok44 : Light.seed 5632 = seed44 := by
  rw [show 5632 = 5504 + 128 by rfl, Light.seed_add, seed_ok43]
  decide +kernel

def seed45 : ℕ := (tailInt% "45-seed.bin").toNat

theorem seed_ok45 : Light.seed 5760 = seed45 := by
  rw [show 5760 = 5632 + 128 by rfl, Light.seed_add, seed_ok44]
  decide +kernel

def seed46 : ℕ := (tailInt% "46-seed.bin").toNat

theorem seed_ok46 : Light.seed 5888 = seed46 := by
  rw [show 5888 = 5760 + 128 by rfl, Light.seed_add, seed_ok45]
  decide +kernel

def seed47 : ℕ := (tailInt% "47-seed.bin").toNat

theorem seed_ok47 : Light.seed 6016 = seed47 := by
  rw [show 6016 = 5888 + 128 by rfl, Light.seed_add, seed_ok46]
  decide +kernel

def seed48 : ℕ := (tailInt% "48-seed.bin").toNat

theorem seed_ok48 : Light.seed 6144 = seed48 := by
  rw [show 6144 = 6016 + 128 by rfl, Light.seed_add, seed_ok47]
  decide +kernel

def seed49 : ℕ := (tailInt% "49-seed.bin").toNat

theorem seed_ok49 : Light.seed 6272 = seed49 := by
  rw [show 6272 = 6144 + 128 by rfl, Light.seed_add, seed_ok48]
  decide +kernel

def seed50 : ℕ := (tailInt% "50-seed.bin").toNat

theorem seed_ok50 : Light.seed 6400 = seed50 := by
  rw [show 6400 = 6272 + 128 by rfl, Light.seed_add, seed_ok49]
  decide +kernel

def seed51 : ℕ := (tailInt% "51-seed.bin").toNat

theorem seed_ok51 : Light.seed 6528 = seed51 := by
  rw [show 6528 = 6400 + 128 by rfl, Light.seed_add, seed_ok50]
  decide +kernel

def seed52 : ℕ := (tailInt% "52-seed.bin").toNat

theorem seed_ok52 : Light.seed 6656 = seed52 := by
  rw [show 6656 = 6528 + 128 by rfl, Light.seed_add, seed_ok51]
  decide +kernel

def seed53 : ℕ := (tailInt% "53-seed.bin").toNat

theorem seed_ok53 : Light.seed 6784 = seed53 := by
  rw [show 6784 = 6656 + 128 by rfl, Light.seed_add, seed_ok52]
  decide +kernel

def seed54 : ℕ := (tailInt% "54-seed.bin").toNat

theorem seed_ok54 : Light.seed 6912 = seed54 := by
  rw [show 6912 = 6784 + 128 by rfl, Light.seed_add, seed_ok53]
  decide +kernel

def seed55 : ℕ := (tailInt% "55-seed.bin").toNat

theorem seed_ok55 : Light.seed 7040 = seed55 := by
  rw [show 7040 = 6912 + 128 by rfl, Light.seed_add, seed_ok54]
  decide +kernel

def seed56 : ℕ := (tailInt% "56-seed.bin").toNat

theorem seed_ok56 : Light.seed 7168 = seed56 := by
  rw [show 7168 = 7040 + 128 by rfl, Light.seed_add, seed_ok55]
  decide +kernel

def seed57 : ℕ := (tailInt% "57-seed.bin").toNat

theorem seed_ok57 : Light.seed 7296 = seed57 := by
  rw [show 7296 = 7168 + 128 by rfl, Light.seed_add, seed_ok56]
  decide +kernel

def seed58 : ℕ := (tailInt% "58-seed.bin").toNat

theorem seed_ok58 : Light.seed 7424 = seed58 := by
  rw [show 7424 = 7296 + 128 by rfl, Light.seed_add, seed_ok57]
  decide +kernel

def seed59 : ℕ := (tailInt% "59-seed.bin").toNat

theorem seed_ok59 : Light.seed 7552 = seed59 := by
  rw [show 7552 = 7424 + 128 by rfl, Light.seed_add, seed_ok58]
  decide +kernel

def seed60 : ℕ := (tailInt% "60-seed.bin").toNat

theorem seed_ok60 : Light.seed 7680 = seed60 := by
  rw [show 7680 = 7552 + 128 by rfl, Light.seed_add, seed_ok59]
  decide +kernel

def seed61 : ℕ := (tailInt% "61-seed.bin").toNat

theorem seed_ok61 : Light.seed 7808 = seed61 := by
  rw [show 7808 = 7680 + 128 by rfl, Light.seed_add, seed_ok60]
  decide +kernel

def seed62 : ℕ := (tailInt% "62-seed.bin").toNat

theorem seed_ok62 : Light.seed 7936 = seed62 := by
  rw [show 7936 = 7808 + 128 by rfl, Light.seed_add, seed_ok61]
  decide +kernel

def seed63 : ℕ := (tailInt% "63-seed.bin").toNat

theorem seed_ok63 : Light.seed 8064 = seed63 := by
  rw [show 8064 = 7936 + 128 by rfl, Light.seed_add, seed_ok62]
  decide +kernel

def seed64 : ℕ := (tailInt% "64-seed.bin").toNat

theorem seed_ok64 : Light.seed 8192 = seed64 := by
  rw [show 8192 = 8064 + 128 by rfl, Light.seed_add, seed_ok63]
  decide +kernel

end NextProof.Tail.Shards
