import NextProof.TailShards00

import NextProof.TailShards01

import NextProof.TailShards02

import NextProof.TailShards03

import NextProof.TailShards04

import NextProof.TailShards05

import NextProof.TailShards06

import NextProof.TailShards07

import NextProof.TailShards08

import NextProof.TailShards09

import NextProof.TailShards10

import NextProof.TailShards11

import NextProof.TailShards12

import NextProof.TailShards13

import NextProof.TailShards14

import NextProof.TailShards15

import NextProof.TailShards16

namespace NextProof.Tail.Shards

set_option maxRecDepth 200000

set_option maxHeartbeats 0

noncomputable def node00_02 : Piece := join p00 p01

noncomputable def node02_04 : Piece := join p02 p03

noncomputable def node00_04 : Piece := join node00_02 node02_04

noncomputable def node04_06 : Piece := join p04 p05

noncomputable def node06_08 : Piece := join p06 p07

noncomputable def node04_08 : Piece := join node04_06 node06_08

noncomputable def node00_08 : Piece := join node00_04 node04_08

noncomputable def node08_10 : Piece := join p08 p09

noncomputable def node10_12 : Piece := join p10 p11

noncomputable def node08_12 : Piece := join node08_10 node10_12

noncomputable def node12_14 : Piece := join p12 p13

noncomputable def node14_16 : Piece := join p14 p15

noncomputable def node12_16 : Piece := join node12_14 node14_16

noncomputable def node08_16 : Piece := join node08_12 node12_16

noncomputable def node00_16 : Piece := join node00_08 node08_16

noncomputable def node16_18 : Piece := join p16 p17

noncomputable def node18_20 : Piece := join p18 p19

noncomputable def node16_20 : Piece := join node16_18 node18_20

noncomputable def node20_22 : Piece := join p20 p21

noncomputable def node22_24 : Piece := join p22 p23

noncomputable def node20_24 : Piece := join node20_22 node22_24

noncomputable def node16_24 : Piece := join node16_20 node20_24

noncomputable def node24_26 : Piece := join p24 p25

noncomputable def node26_28 : Piece := join p26 p27

noncomputable def node24_28 : Piece := join node24_26 node26_28

noncomputable def node28_30 : Piece := join p28 p29

noncomputable def node30_32 : Piece := join p30 p31

noncomputable def node28_32 : Piece := join node28_30 node30_32

noncomputable def node24_32 : Piece := join node24_28 node28_32

noncomputable def node16_32 : Piece := join node16_24 node24_32

noncomputable def node00_32 : Piece := join node00_16 node16_32

noncomputable def node32_34 : Piece := join p32 p33

noncomputable def node34_36 : Piece := join p34 p35

noncomputable def node32_36 : Piece := join node32_34 node34_36

noncomputable def node36_38 : Piece := join p36 p37

noncomputable def node38_40 : Piece := join p38 p39

noncomputable def node36_40 : Piece := join node36_38 node38_40

noncomputable def node32_40 : Piece := join node32_36 node36_40

noncomputable def node40_42 : Piece := join p40 p41

noncomputable def node42_44 : Piece := join p42 p43

noncomputable def node40_44 : Piece := join node40_42 node42_44

noncomputable def node44_46 : Piece := join p44 p45

noncomputable def node46_48 : Piece := join p46 p47

noncomputable def node44_48 : Piece := join node44_46 node46_48

noncomputable def node40_48 : Piece := join node40_44 node44_48

noncomputable def node32_48 : Piece := join node32_40 node40_48

noncomputable def node48_50 : Piece := join p48 p49

noncomputable def node50_52 : Piece := join p50 p51

noncomputable def node48_52 : Piece := join node48_50 node50_52

noncomputable def node52_54 : Piece := join p52 p53

noncomputable def node54_56 : Piece := join p54 p55

noncomputable def node52_56 : Piece := join node52_54 node54_56

noncomputable def node48_56 : Piece := join node48_52 node52_56

noncomputable def node56_58 : Piece := join p56 p57

noncomputable def node58_60 : Piece := join p58 p59

noncomputable def node56_60 : Piece := join node56_58 node58_60

noncomputable def node60_62 : Piece := join p60 p61

noncomputable def node62_64 : Piece := join p62 p63

noncomputable def node62_65 : Piece := join node62_64 p64

noncomputable def node60_65 : Piece := join node60_62 node62_65

noncomputable def node56_65 : Piece := join node56_60 node60_65

noncomputable def node48_65 : Piece := join node48_56 node56_65

noncomputable def node32_65 : Piece := join node32_48 node48_65

noncomputable def node00_65 : Piece := join node00_32 node32_65

theorem whole_value : node00_65.inputVal=node00_65.outputVal := by decide +kernel

theorem whole_bound : node00_65.inputMajor+node00_65.outputMajor<radix := by decide +kernel

end NextProof.Tail.Shards
