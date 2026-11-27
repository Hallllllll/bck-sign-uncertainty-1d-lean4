import NextProof.TailShardWindow

namespace NextProof.Tail.Shards

open Exterior.Data16384

set_option maxHeartbeats 0

set_option maxRecDepth 200000

def weights00 : List ℤ := chunk00

def weights01 : List ℤ := chunk01

def weights02 : List ℤ := chunk02

def weights03 : List ℤ := chunk03

def weights04 : List ℤ := chunk04

def weights05 : List ℤ := chunk05

def weights06 : List ℤ := chunk06

def weights07 : List ℤ := chunk07

def weights08 : List ℤ := chunk08

def weights09 : List ℤ := chunk09

def weights10 : List ℤ := chunk10

def weights11 : List ℤ := chunk11

def weights12 : List ℤ := chunk12

def weights13 : List ℤ := chunk13

def weights14 : List ℤ := chunk14

def weights15 : List ℤ := chunk15

def weights16 : List ℤ := chunk16

def weights17 : List ℤ := chunk17

def weights18 : List ℤ := chunk18

def weights19 : List ℤ := chunk19

def weights20 : List ℤ := chunk20

def weights21 : List ℤ := chunk21

def weights22 : List ℤ := chunk22

def weights23 : List ℤ := chunk23

def weights24 : List ℤ := chunk24

def weights25 : List ℤ := chunk25

def weights26 : List ℤ := chunk26

def weights27 : List ℤ := chunk27

def weights28 : List ℤ := chunk28

def weights29 : List ℤ := chunk29

def weights30 : List ℤ := chunk30

def weights31 : List ℤ := chunk31

def weights32 : List ℤ := chunk32

def weights33 : List ℤ := chunk33

def weights34 : List ℤ := chunk34

def weights35 : List ℤ := chunk35

def weights36 : List ℤ := chunk36 ++ chunk37.take 125

def weights37 : List ℤ := chunk37.drop 125 ++ chunk38.take 125

def weights38 : List ℤ := chunk38.drop 125 ++ chunk39.take 125

def weights39 : List ℤ := chunk39.drop 125 ++ chunk40.take 125

def weights40 : List ℤ := chunk40.drop 125 ++ chunk41.take 125

def weights41 : List ℤ := chunk41.drop 125 ++ chunk42.take 125

def weights42 : List ℤ := chunk42.drop 125 ++ chunk43.take 125

def weights43 : List ℤ := chunk43.drop 125 ++ chunk44.take 125

def weights44 : List ℤ := chunk44.drop 125 ++ chunk45.take 125

def weights45 : List ℤ := chunk45.drop 125 ++ chunk46.take 125

def weights46 : List ℤ := chunk46.drop 125 ++ chunk47.take 125

def weights47 : List ℤ := chunk47.drop 125 ++ chunk48.take 125

def weights48 : List ℤ := chunk48.drop 125 ++ chunk49.take 125

def weights49 : List ℤ := chunk49.drop 125 ++ chunk50.take 125

def weights50 : List ℤ := chunk50.drop 125 ++ chunk51.take 125

def weights51 : List ℤ := chunk51.drop 125 ++ chunk52.take 125

def weights52 : List ℤ := chunk52.drop 125 ++ chunk53.take 125

def weights53 : List ℤ := chunk53.drop 125 ++ chunk54.take 125

def weights54 : List ℤ := chunk54.drop 125 ++ chunk55.take 125

def weights55 : List ℤ := chunk55.drop 125 ++ chunk56.take 125

def weights56 : List ℤ := chunk56.drop 125 ++ chunk57.take 125

def weights57 : List ℤ := chunk57.drop 125 ++ chunk58.take 125

def weights58 : List ℤ := chunk58.drop 125 ++ chunk59.take 125

def weights59 : List ℤ := chunk59.drop 125 ++ chunk60.take 125

def weights60 : List ℤ := chunk60.drop 125 ++ chunk61.take 125

def weights61 : List ℤ := chunk61.drop 125 ++ chunk62.take 125

def weights62 : List ℤ := chunk62.drop 125 ++ chunk63.take 125

def weights63 : List ℤ := chunk63.drop 125 ++ chunk64

def weights64 : List ℤ := [lead]

def rest65 : List ℤ := []

def rest64 := weights64 ++ rest65

def rest63 := weights63 ++ rest64

def rest62 := weights62 ++ rest63

def rest61 := weights61 ++ rest62

def rest60 := weights60 ++ rest61

def rest59 := weights59 ++ rest60

def rest58 := weights58 ++ rest59

def rest57 := weights57 ++ rest58

def rest56 := weights56 ++ rest57

def rest55 := weights55 ++ rest56

def rest54 := weights54 ++ rest55

def rest53 := weights53 ++ rest54

def rest52 := weights52 ++ rest53

def rest51 := weights51 ++ rest52

def rest50 := weights50 ++ rest51

def rest49 := weights49 ++ rest50

def rest48 := weights48 ++ rest49

def rest47 := weights47 ++ rest48

def rest46 := weights46 ++ rest47

def rest45 := weights45 ++ rest46

def rest44 := weights44 ++ rest45

def rest43 := weights43 ++ rest44

def rest42 := weights42 ++ rest43

def rest41 := weights41 ++ rest42

def rest40 := weights40 ++ rest41

def rest39 := weights39 ++ rest40

def rest38 := weights38 ++ rest39

def rest37 := weights37 ++ rest38

def rest36 := weights36 ++ rest37

def rest35 := weights35 ++ rest36

def rest34 := weights34 ++ rest35

def rest33 := weights33 ++ rest34

def rest32 := weights32 ++ rest33

def rest31 := weights31 ++ rest32

def rest30 := weights30 ++ rest31

def rest29 := weights29 ++ rest30

def rest28 := weights28 ++ rest29

def rest27 := weights27 ++ rest28

def rest26 := weights26 ++ rest27

def rest25 := weights25 ++ rest26

def rest24 := weights24 ++ rest25

def rest23 := weights23 ++ rest24

def rest22 := weights22 ++ rest23

def rest21 := weights21 ++ rest22

def rest20 := weights20 ++ rest21

def rest19 := weights19 ++ rest20

def rest18 := weights18 ++ rest19

def rest17 := weights17 ++ rest18

def rest16 := weights16 ++ rest17

def rest15 := weights15 ++ rest16

def rest14 := weights14 ++ rest15

def rest13 := weights13 ++ rest14

def rest12 := weights12 ++ rest13

def rest11 := weights11 ++ rest12

def rest10 := weights10 ++ rest11

def rest09 := weights09 ++ rest10

def rest08 := weights08 ++ rest09

def rest07 := weights07 ++ rest08

def rest06 := weights06 ++ rest07

def rest05 := weights05 ++ rest06

def rest04 := weights04 ++ rest05

def rest03 := weights03 ++ rest04

def rest02 := weights02 ++ rest03

def rest01 := weights01 ++ rest02

def rest00 := weights00 ++ rest01

theorem drop00 : weights.drop 0 = rest00 := by
  have splitw (w t : List ℤ) : w.take 125 ++ (w.drop 125 ++ t) = w ++ t := by
    rw [← List.append_assoc, List.take_append_drop]
  simp only [List.drop_zero,weights,lowWeights,highWeights,rest00,rest01,rest02,rest03,rest04,rest05,rest06,rest07,rest08,rest09,rest10,rest11,rest12,rest13,rest14,rest15,rest16,rest17,rest18,rest19,rest20,rest21,rest22,rest23,rest24,rest25,rest26,rest27,rest28,rest29,rest30,rest31,rest32,rest33,rest34,rest35,rest36,rest37,rest38,rest39,rest40,rest41,rest42,rest43,rest44,rest45,rest46,rest47,rest48,rest49,rest50,rest51,rest52,rest53,rest54,rest55,rest56,rest57,rest58,rest59,rest60,rest61,rest62,rest63,rest64,rest65,weights00,weights01,weights02,weights03,weights04,weights05,weights06,weights07,weights08,weights09,weights10,weights11,weights12,weights13,weights14,weights15,weights16,weights17,weights18,weights19,weights20,weights21,weights22,weights23,weights24,weights25,weights26,weights27,weights28,weights29,weights30,weights31,weights32,weights33,weights34,weights35,weights36,weights37,weights38,weights39,weights40,weights41,weights42,weights43,weights44,weights45,weights46,weights47,weights48,weights49,weights50,weights51,weights52,weights53,weights54,weights55,weights56,weights57,weights58,weights59,weights60,weights61,weights62,weights63,weights64,List.append_nil,List.append_assoc,splitw]

theorem drop01 : weights.drop 128 = rest01 := by
  rw [show 128 = 0 + 128 by rfl, ← List.drop_drop, drop00]
  exact List.drop_left' (l₁ := weights00) (by decide +kernel)

theorem drop02 : weights.drop 256 = rest02 := by
  rw [show 256 = 128 + 128 by rfl, ← List.drop_drop, drop01]
  exact List.drop_left' (l₁ := weights01) (by decide +kernel)

theorem drop03 : weights.drop 384 = rest03 := by
  rw [show 384 = 256 + 128 by rfl, ← List.drop_drop, drop02]
  exact List.drop_left' (l₁ := weights02) (by decide +kernel)

theorem drop04 : weights.drop 512 = rest04 := by
  rw [show 512 = 384 + 128 by rfl, ← List.drop_drop, drop03]
  exact List.drop_left' (l₁ := weights03) (by decide +kernel)

theorem drop05 : weights.drop 640 = rest05 := by
  rw [show 640 = 512 + 128 by rfl, ← List.drop_drop, drop04]
  exact List.drop_left' (l₁ := weights04) (by decide +kernel)

theorem drop06 : weights.drop 768 = rest06 := by
  rw [show 768 = 640 + 128 by rfl, ← List.drop_drop, drop05]
  exact List.drop_left' (l₁ := weights05) (by decide +kernel)

theorem drop07 : weights.drop 896 = rest07 := by
  rw [show 896 = 768 + 128 by rfl, ← List.drop_drop, drop06]
  exact List.drop_left' (l₁ := weights06) (by decide +kernel)

theorem drop08 : weights.drop 1024 = rest08 := by
  rw [show 1024 = 896 + 128 by rfl, ← List.drop_drop, drop07]
  exact List.drop_left' (l₁ := weights07) (by decide +kernel)

theorem drop09 : weights.drop 1152 = rest09 := by
  rw [show 1152 = 1024 + 128 by rfl, ← List.drop_drop, drop08]
  exact List.drop_left' (l₁ := weights08) (by decide +kernel)

theorem drop10 : weights.drop 1280 = rest10 := by
  rw [show 1280 = 1152 + 128 by rfl, ← List.drop_drop, drop09]
  exact List.drop_left' (l₁ := weights09) (by decide +kernel)

theorem drop11 : weights.drop 1408 = rest11 := by
  rw [show 1408 = 1280 + 128 by rfl, ← List.drop_drop, drop10]
  exact List.drop_left' (l₁ := weights10) (by decide +kernel)

theorem drop12 : weights.drop 1536 = rest12 := by
  rw [show 1536 = 1408 + 128 by rfl, ← List.drop_drop, drop11]
  exact List.drop_left' (l₁ := weights11) (by decide +kernel)

theorem drop13 : weights.drop 1664 = rest13 := by
  rw [show 1664 = 1536 + 128 by rfl, ← List.drop_drop, drop12]
  exact List.drop_left' (l₁ := weights12) (by decide +kernel)

theorem drop14 : weights.drop 1792 = rest14 := by
  rw [show 1792 = 1664 + 128 by rfl, ← List.drop_drop, drop13]
  exact List.drop_left' (l₁ := weights13) (by decide +kernel)

theorem drop15 : weights.drop 1920 = rest15 := by
  rw [show 1920 = 1792 + 128 by rfl, ← List.drop_drop, drop14]
  exact List.drop_left' (l₁ := weights14) (by decide +kernel)

theorem drop16 : weights.drop 2048 = rest16 := by
  rw [show 2048 = 1920 + 128 by rfl, ← List.drop_drop, drop15]
  exact List.drop_left' (l₁ := weights15) (by decide +kernel)

theorem drop17 : weights.drop 2176 = rest17 := by
  rw [show 2176 = 2048 + 128 by rfl, ← List.drop_drop, drop16]
  exact List.drop_left' (l₁ := weights16) (by decide +kernel)

theorem drop18 : weights.drop 2304 = rest18 := by
  rw [show 2304 = 2176 + 128 by rfl, ← List.drop_drop, drop17]
  exact List.drop_left' (l₁ := weights17) (by decide +kernel)

theorem drop19 : weights.drop 2432 = rest19 := by
  rw [show 2432 = 2304 + 128 by rfl, ← List.drop_drop, drop18]
  exact List.drop_left' (l₁ := weights18) (by decide +kernel)

theorem drop20 : weights.drop 2560 = rest20 := by
  rw [show 2560 = 2432 + 128 by rfl, ← List.drop_drop, drop19]
  exact List.drop_left' (l₁ := weights19) (by decide +kernel)

theorem drop21 : weights.drop 2688 = rest21 := by
  rw [show 2688 = 2560 + 128 by rfl, ← List.drop_drop, drop20]
  exact List.drop_left' (l₁ := weights20) (by decide +kernel)

theorem drop22 : weights.drop 2816 = rest22 := by
  rw [show 2816 = 2688 + 128 by rfl, ← List.drop_drop, drop21]
  exact List.drop_left' (l₁ := weights21) (by decide +kernel)

theorem drop23 : weights.drop 2944 = rest23 := by
  rw [show 2944 = 2816 + 128 by rfl, ← List.drop_drop, drop22]
  exact List.drop_left' (l₁ := weights22) (by decide +kernel)

theorem drop24 : weights.drop 3072 = rest24 := by
  rw [show 3072 = 2944 + 128 by rfl, ← List.drop_drop, drop23]
  exact List.drop_left' (l₁ := weights23) (by decide +kernel)

theorem drop25 : weights.drop 3200 = rest25 := by
  rw [show 3200 = 3072 + 128 by rfl, ← List.drop_drop, drop24]
  exact List.drop_left' (l₁ := weights24) (by decide +kernel)

theorem drop26 : weights.drop 3328 = rest26 := by
  rw [show 3328 = 3200 + 128 by rfl, ← List.drop_drop, drop25]
  exact List.drop_left' (l₁ := weights25) (by decide +kernel)

theorem drop27 : weights.drop 3456 = rest27 := by
  rw [show 3456 = 3328 + 128 by rfl, ← List.drop_drop, drop26]
  exact List.drop_left' (l₁ := weights26) (by decide +kernel)

theorem drop28 : weights.drop 3584 = rest28 := by
  rw [show 3584 = 3456 + 128 by rfl, ← List.drop_drop, drop27]
  exact List.drop_left' (l₁ := weights27) (by decide +kernel)

theorem drop29 : weights.drop 3712 = rest29 := by
  rw [show 3712 = 3584 + 128 by rfl, ← List.drop_drop, drop28]
  exact List.drop_left' (l₁ := weights28) (by decide +kernel)

theorem drop30 : weights.drop 3840 = rest30 := by
  rw [show 3840 = 3712 + 128 by rfl, ← List.drop_drop, drop29]
  exact List.drop_left' (l₁ := weights29) (by decide +kernel)

theorem drop31 : weights.drop 3968 = rest31 := by
  rw [show 3968 = 3840 + 128 by rfl, ← List.drop_drop, drop30]
  exact List.drop_left' (l₁ := weights30) (by decide +kernel)

theorem drop32 : weights.drop 4096 = rest32 := by
  rw [show 4096 = 3968 + 128 by rfl, ← List.drop_drop, drop31]
  exact List.drop_left' (l₁ := weights31) (by decide +kernel)

theorem drop33 : weights.drop 4224 = rest33 := by
  rw [show 4224 = 4096 + 128 by rfl, ← List.drop_drop, drop32]
  exact List.drop_left' (l₁ := weights32) (by decide +kernel)

theorem drop34 : weights.drop 4352 = rest34 := by
  rw [show 4352 = 4224 + 128 by rfl, ← List.drop_drop, drop33]
  exact List.drop_left' (l₁ := weights33) (by decide +kernel)

theorem drop35 : weights.drop 4480 = rest35 := by
  rw [show 4480 = 4352 + 128 by rfl, ← List.drop_drop, drop34]
  exact List.drop_left' (l₁ := weights34) (by decide +kernel)

theorem drop36 : weights.drop 4608 = rest36 := by
  rw [show 4608 = 4480 + 128 by rfl, ← List.drop_drop, drop35]
  exact List.drop_left' (l₁ := weights35) (by decide +kernel)

theorem drop37 : weights.drop 4736 = rest37 := by
  rw [show 4736 = 4608 + 128 by rfl, ← List.drop_drop, drop36]
  exact List.drop_left' (l₁ := weights36) (by decide +kernel)

theorem drop38 : weights.drop 4864 = rest38 := by
  rw [show 4864 = 4736 + 128 by rfl, ← List.drop_drop, drop37]
  exact List.drop_left' (l₁ := weights37) (by decide +kernel)

theorem drop39 : weights.drop 4992 = rest39 := by
  rw [show 4992 = 4864 + 128 by rfl, ← List.drop_drop, drop38]
  exact List.drop_left' (l₁ := weights38) (by decide +kernel)

theorem drop40 : weights.drop 5120 = rest40 := by
  rw [show 5120 = 4992 + 128 by rfl, ← List.drop_drop, drop39]
  exact List.drop_left' (l₁ := weights39) (by decide +kernel)

theorem drop41 : weights.drop 5248 = rest41 := by
  rw [show 5248 = 5120 + 128 by rfl, ← List.drop_drop, drop40]
  exact List.drop_left' (l₁ := weights40) (by decide +kernel)

theorem drop42 : weights.drop 5376 = rest42 := by
  rw [show 5376 = 5248 + 128 by rfl, ← List.drop_drop, drop41]
  exact List.drop_left' (l₁ := weights41) (by decide +kernel)

theorem drop43 : weights.drop 5504 = rest43 := by
  rw [show 5504 = 5376 + 128 by rfl, ← List.drop_drop, drop42]
  exact List.drop_left' (l₁ := weights42) (by decide +kernel)

theorem drop44 : weights.drop 5632 = rest44 := by
  rw [show 5632 = 5504 + 128 by rfl, ← List.drop_drop, drop43]
  exact List.drop_left' (l₁ := weights43) (by decide +kernel)

theorem drop45 : weights.drop 5760 = rest45 := by
  rw [show 5760 = 5632 + 128 by rfl, ← List.drop_drop, drop44]
  exact List.drop_left' (l₁ := weights44) (by decide +kernel)

theorem drop46 : weights.drop 5888 = rest46 := by
  rw [show 5888 = 5760 + 128 by rfl, ← List.drop_drop, drop45]
  exact List.drop_left' (l₁ := weights45) (by decide +kernel)

theorem drop47 : weights.drop 6016 = rest47 := by
  rw [show 6016 = 5888 + 128 by rfl, ← List.drop_drop, drop46]
  exact List.drop_left' (l₁ := weights46) (by decide +kernel)

theorem drop48 : weights.drop 6144 = rest48 := by
  rw [show 6144 = 6016 + 128 by rfl, ← List.drop_drop, drop47]
  exact List.drop_left' (l₁ := weights47) (by decide +kernel)

theorem drop49 : weights.drop 6272 = rest49 := by
  rw [show 6272 = 6144 + 128 by rfl, ← List.drop_drop, drop48]
  exact List.drop_left' (l₁ := weights48) (by decide +kernel)

theorem drop50 : weights.drop 6400 = rest50 := by
  rw [show 6400 = 6272 + 128 by rfl, ← List.drop_drop, drop49]
  exact List.drop_left' (l₁ := weights49) (by decide +kernel)

theorem drop51 : weights.drop 6528 = rest51 := by
  rw [show 6528 = 6400 + 128 by rfl, ← List.drop_drop, drop50]
  exact List.drop_left' (l₁ := weights50) (by decide +kernel)

theorem drop52 : weights.drop 6656 = rest52 := by
  rw [show 6656 = 6528 + 128 by rfl, ← List.drop_drop, drop51]
  exact List.drop_left' (l₁ := weights51) (by decide +kernel)

theorem drop53 : weights.drop 6784 = rest53 := by
  rw [show 6784 = 6656 + 128 by rfl, ← List.drop_drop, drop52]
  exact List.drop_left' (l₁ := weights52) (by decide +kernel)

theorem drop54 : weights.drop 6912 = rest54 := by
  rw [show 6912 = 6784 + 128 by rfl, ← List.drop_drop, drop53]
  exact List.drop_left' (l₁ := weights53) (by decide +kernel)

theorem drop55 : weights.drop 7040 = rest55 := by
  rw [show 7040 = 6912 + 128 by rfl, ← List.drop_drop, drop54]
  exact List.drop_left' (l₁ := weights54) (by decide +kernel)

theorem drop56 : weights.drop 7168 = rest56 := by
  rw [show 7168 = 7040 + 128 by rfl, ← List.drop_drop, drop55]
  exact List.drop_left' (l₁ := weights55) (by decide +kernel)

theorem drop57 : weights.drop 7296 = rest57 := by
  rw [show 7296 = 7168 + 128 by rfl, ← List.drop_drop, drop56]
  exact List.drop_left' (l₁ := weights56) (by decide +kernel)

theorem drop58 : weights.drop 7424 = rest58 := by
  rw [show 7424 = 7296 + 128 by rfl, ← List.drop_drop, drop57]
  exact List.drop_left' (l₁ := weights57) (by decide +kernel)

theorem drop59 : weights.drop 7552 = rest59 := by
  rw [show 7552 = 7424 + 128 by rfl, ← List.drop_drop, drop58]
  exact List.drop_left' (l₁ := weights58) (by decide +kernel)

theorem drop60 : weights.drop 7680 = rest60 := by
  rw [show 7680 = 7552 + 128 by rfl, ← List.drop_drop, drop59]
  exact List.drop_left' (l₁ := weights59) (by decide +kernel)

theorem drop61 : weights.drop 7808 = rest61 := by
  rw [show 7808 = 7680 + 128 by rfl, ← List.drop_drop, drop60]
  exact List.drop_left' (l₁ := weights60) (by decide +kernel)

theorem drop62 : weights.drop 7936 = rest62 := by
  rw [show 7936 = 7808 + 128 by rfl, ← List.drop_drop, drop61]
  exact List.drop_left' (l₁ := weights61) (by decide +kernel)

theorem drop63 : weights.drop 8064 = rest63 := by
  rw [show 8064 = 7936 + 128 by rfl, ← List.drop_drop, drop62]
  exact List.drop_left' (l₁ := weights62) (by decide +kernel)

theorem drop64 : weights.drop 8192 = rest64 := by
  rw [show 8192 = 8064 + 128 by rfl, ← List.drop_drop, drop63]
  exact List.drop_left' (l₁ := weights63) (by decide +kernel)

end NextProof.Tail.Shards
