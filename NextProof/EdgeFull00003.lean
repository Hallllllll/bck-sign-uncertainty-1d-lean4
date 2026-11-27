import NextProof.CompactEdge
import NextProof.OptThreeV000000000000000111101000001010011Data
import NextProof.LeftKernel
import NextProof.OptEdge00003R01Cert
import NextProof.OptEdge00003R02Cert
import NextProof.OptEdge00003R03Cert
import NextProof.OptEdge00003R04Cert
import NextProof.OptEdge00003R05Cert
import NextProof.OptEdge00003R06Cert
import NextProof.OptEdge00003R07Cert
import NextProof.OptEdge00003R08Cert
import NextProof.OptEdge00003R09Cert
import NextProof.OptEdge00003R10Cert
import NextProof.OptEdge00003R11Cert
import NextProof.OptEdge00003R12Cert
import NextProof.OptEdge00003R13Cert
import NextProof.OptEdge00003R14Cert
import NextProof.OptEdge00003R15Cert
import NextProof.OptEdge00003R16Cert
import NextProof.OptEdge00003R17Cert
import NextProof.OptEdge00003R18Cert
import NextProof.OptEdge00003R19Cert
import NextProof.OptEdge00003R20Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00002


namespace NextProof.TightLeaf
open Tail Compact

set_option maxRecDepth 150000
set_option maxHeartbeats 0

/-- Polynomial divided difference written in a form that includes x = a. -/
private def secant (a x : ℝ) : List ℤ → ℝ
  | [] => 0
  | _ :: ws => horner x ws + a * secant a x ws

private theorem secant_spec (a x : ℝ) (ws : List ℤ) :
    horner x ws - horner a ws = (x-a) * secant a x ws := by
  induction ws with
  | nil => simp [horner, secant]
  | cons w ws ih =>
    simp only [horner, secant]
    linear_combination a * ih

/-- Integer lower bound for every secant in the unit square. -/
private def slopeFloor : List ℤ → ℤ
  | [] => 0
  | _ :: ws => unitLower ws + min 0 (slopeFloor ws)

private theorem secant_ge {a x : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (ws : List ℤ) :
    (slopeFloor ws : ℝ) ≤ secant a x ws := by
  induction ws with
  | nil => simp [slopeFloor, secant]
  | cons w ws ih =>
    simp only [slopeFloor, secant, Int.cast_add, Int.cast_min, Int.cast_zero]
    apply add_le_add (unitLower_le ws hx hx')
    exact (show min 0 (slopeFloor ws : ℝ) ≤ a * (slopeFloor ws : ℝ) from by
      rcases le_total (slopeFloor ws : ℝ) 0 with h | h
      · rw [min_eq_right h]
        nlinarith only [mul_nonneg (sub_nonneg.mpr ha') (neg_nonneg.mpr h)]
      · rw [min_eq_left h]
        exact mul_nonneg ha h).trans (mul_le_mul_of_nonneg_left ih ha)

/-- The certified lower polynomial on the existing parent's local coordinate. -/
private def short : List ℤ :=
  [-68883814903437361137219495, 505231827911243023669168460,
    -90784335759796359808574, -264732781953925065, 697032056101313,
    -877291828, -3667654, 10, -4, -4, -4, -4, -4]

private noncomputable abbrev parent := EdgeRecovery.Shared.V000000000000000111101000001010011.data

private theorem short_eq : truncate 12 parent.list = short := by decide +kernel

private theorem slope_pos : 0 < slopeFloor short := by decide +kernel

/-- The physical cutoff maps to a parent coordinate through its recorded
left endpoint and width. -/
theorem coordinate :
    ((1906884279970892581/1000000000000000000 : ℚ) - 249939/131072) * 131072 =
      1040224798831/7629394531250 := by norm_num

private theorem endpoint :
    0 < horner (1040224798831/7629394531250 : ℝ) short := by
  norm_num [horner, short]

/-- Full parent coverage, including both halves above the new cutoff. -/
theorem parent_cover : Covers (1040224798831/7629394531250) parent := by
  intro x hx hx' hax
  let a : ℝ := 1040224798831/7629394531250
  have ha : 0 ≤ a := by norm_num [a]
  have ha' : a ≤ 1 := by norm_num [a]
  have hax' : a ≤ x := by simpa [a] using hax
  have hsec := secant_ge ha ha' hx hx' short
  have hs : (0:ℝ) ≤ slopeFloor short := by exact_mod_cast slope_pos.le
  have hd := mul_nonneg (sub_nonneg.mpr hax') (hs.trans hsec)
  rw [← secant_spec] at hd
  have h0 : 0 < horner a short := endpoint
  have hl := truncate_le 12 parent.list x hx hx'
  rw [short_eq] at hl
  exact (h0.le.trans (sub_nonneg.mp hd)).trans hl

end NextProof.TightLeaf
#print axioms NextProof.TightLeaf.parent_cover

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000000000011111111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111111-V-0000.bin"
noncomputable def vp00000000000000011111111 : Blocks := vp00000000000000011111111_0
theorem coverp00000000000000011111111 : Covers (-170599/15625 : ℚ) vp00000000000000011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000001111111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111011-V-0000.bin"
noncomputable def vp0000000000000001111111011 : Blocks := vp0000000000000001111111011_0
theorem coverp0000000000000001111111011 : Covers (-666771/15625 : ℚ) vp0000000000000001111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000011111110101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111110101-V-0000.bin"
noncomputable def vp00000000000000011111110101 : Blocks := vp00000000000000011111110101_0
theorem coverp00000000000000011111110101 : Covers (-1317917/15625 : ℚ) vp00000000000000011111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000011111110100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111110100-V-0000.bin"
noncomputable def vp00000000000000011111110100 : Blocks := vp00000000000000011111110100_0
theorem coverp00000000000000011111110100 : Covers (-1302292/15625 : ℚ) vp00000000000000011111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000001111111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111010-V-0000.bin"
noncomputable def vp0000000000000001111111010 : Blocks := vp0000000000000001111111010_0
private theorem bp00000000000000011111110100 : Branch 0 (-651146/15625 : ℚ) vp0000000000000001111111010 := by
  apply branch_left_normalized (c:=vp00000000000000011111110100) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-651146/15625 : ℚ) - ((0:ℤ):ℚ) = (-1302292/15625 : ℚ) by norm_num]
  exact coverp00000000000000011111110100
private noncomputable def ep00000000000000011111110101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111110101-E-0000.bin"
noncomputable def ep00000000000000011111110101 : Blocks := ep00000000000000011111110101_0
private theorem idp00000000000000011111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111111010.list =
    C ((2:ℤ)^11) * horner X vp00000000000000011111110101.list + horner X ep00000000000000011111110101.list := by
  exact edge_identity (B := (2:ℤ)^104) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000011111110101 : Branch 1 (-651146/15625 : ℚ) vp0000000000000001111111010 := by
  apply branch_checked idp00000000000000011111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-651146/15625 : ℚ) - ((1:ℤ):ℚ) = (-1317917/15625 : ℚ) by norm_num]
  exact coverp00000000000000011111110101
theorem coverp0000000000000001111111010 : Covers (-651146/15625 : ℚ) vp0000000000000001111111010 := join_branches bp00000000000000011111110100 bp00000000000000011111110101
private noncomputable def vp000000000000000111111101_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111101-V-0000.bin"
noncomputable def vp000000000000000111111101 : Blocks := vp000000000000000111111101_0
private theorem bp0000000000000001111111010 : Branch 0 (-325573/15625 : ℚ) vp000000000000000111111101 := by
  apply branch_left_normalized (c:=vp0000000000000001111111010) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-325573/15625 : ℚ) - ((0:ℤ):ℚ) = (-651146/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111111010
private noncomputable def ep0000000000000001111111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111011-E-0000.bin"
noncomputable def ep0000000000000001111111011 : Blocks := ep0000000000000001111111011_0
private theorem idp0000000000000001111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111111101.list =
    C ((2:ℤ)^13) * horner X vp0000000000000001111111011.list + horner X ep0000000000000001111111011.list := by
  exact edge_identity (B := (2:ℤ)^107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000001111111011 : Branch 1 (-325573/15625 : ℚ) vp000000000000000111111101 := by
  apply branch_checked idp0000000000000001111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-325573/15625 : ℚ) - ((1:ℤ):ℚ) = (-666771/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111111011
theorem coverp000000000000000111111101 : Covers (-325573/15625 : ℚ) vp000000000000000111111101 := join_branches bp0000000000000001111111010 bp0000000000000001111111011
private noncomputable def vp0000000000000001111111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111001-V-0000.bin"
noncomputable def vp0000000000000001111111001 : Blocks := vp0000000000000001111111001_0
theorem coverp0000000000000001111111001 : Covers (-635521/15625 : ℚ) vp0000000000000001111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000001111111000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111000-V-0000.bin"
noncomputable def vp0000000000000001111111000 : Blocks := vp0000000000000001111111000_0
theorem coverp0000000000000001111111000 : Covers (-619896/15625 : ℚ) vp0000000000000001111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000000111111100_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111100-V-0000.bin"
noncomputable def vp000000000000000111111100 : Blocks := vp000000000000000111111100_0
private theorem bp0000000000000001111111000 : Branch 0 (-309948/15625 : ℚ) vp000000000000000111111100 := by
  apply branch_left_normalized (c:=vp0000000000000001111111000) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-309948/15625 : ℚ) - ((0:ℤ):ℚ) = (-619896/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111111000
private noncomputable def ep0000000000000001111111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111001-E-0000.bin"
noncomputable def ep0000000000000001111111001 : Blocks := ep0000000000000001111111001_0
private theorem idp0000000000000001111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111111100.list =
    C ((2:ℤ)^12) * horner X vp0000000000000001111111001.list + horner X ep0000000000000001111111001.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000001111111001 : Branch 1 (-309948/15625 : ℚ) vp000000000000000111111100 := by
  apply branch_checked idp0000000000000001111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-309948/15625 : ℚ) - ((1:ℤ):ℚ) = (-635521/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111111001
theorem coverp000000000000000111111100 : Covers (-309948/15625 : ℚ) vp000000000000000111111100 := join_branches bp0000000000000001111111000 bp0000000000000001111111001
private noncomputable def vp00000000000000011111110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111110-V-0000.bin"
noncomputable def vp00000000000000011111110 : Blocks := vp00000000000000011111110_0
private theorem bp000000000000000111111100 : Branch 0 (-154974/15625 : ℚ) vp00000000000000011111110 := by
  apply branch_left_normalized (c:=vp000000000000000111111100) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-154974/15625 : ℚ) - ((0:ℤ):ℚ) = (-309948/15625 : ℚ) by norm_num]
  exact coverp000000000000000111111100
private noncomputable def ep000000000000000111111101_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111101-E-0000.bin"
noncomputable def ep000000000000000111111101 : Blocks := ep000000000000000111111101_0
private theorem idp000000000000000111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011111110.list =
    C ((2:ℤ)^15) * horner X vp000000000000000111111101.list + horner X ep000000000000000111111101.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000000111111101 : Branch 1 (-154974/15625 : ℚ) vp00000000000000011111110 := by
  apply branch_checked idp000000000000000111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-154974/15625 : ℚ) - ((1:ℤ):ℚ) = (-325573/15625 : ℚ) by norm_num]
  exact coverp000000000000000111111101
theorem coverp00000000000000011111110 : Covers (-154974/15625 : ℚ) vp00000000000000011111110 := join_branches bp000000000000000111111100 bp000000000000000111111101
private noncomputable def vp0000000000000001111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111-V-0000.bin"
noncomputable def vp0000000000000001111111 : Blocks := vp0000000000000001111111_0
private theorem bp00000000000000011111110 : Branch 0 (-77487/15625 : ℚ) vp0000000000000001111111 := by
  apply branch_left_normalized (c:=vp00000000000000011111110) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-77487/15625 : ℚ) - ((0:ℤ):ℚ) = (-154974/15625 : ℚ) by norm_num]
  exact coverp00000000000000011111110
private noncomputable def ep00000000000000011111111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111111-E-0000.bin"
noncomputable def ep00000000000000011111111 : Blocks := ep00000000000000011111111_0
private theorem idp00000000000000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111111.list =
    C ((2:ℤ)^18) * horner X vp00000000000000011111111.list + horner X ep00000000000000011111111.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000011111111 : Branch 1 (-77487/15625 : ℚ) vp0000000000000001111111 := by
  apply branch_checked idp00000000000000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-77487/15625 : ℚ) - ((1:ℤ):ℚ) = (-170599/15625 : ℚ) by norm_num]
  exact coverp00000000000000011111111
theorem coverp0000000000000001111111 : Covers (-77487/15625 : ℚ) vp0000000000000001111111 := join_branches bp00000000000000011111110 bp00000000000000011111111
private noncomputable def vp000000000000000111111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111011-V-0000.bin"
noncomputable def vp000000000000000111111011 : Blocks := vp000000000000000111111011_0
theorem coverp000000000000000111111011 : Covers (-294323/15625 : ℚ) vp000000000000000111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000000111111010_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111010-V-0000.bin"
noncomputable def vp000000000000000111111010 : Blocks := vp000000000000000111111010_0
theorem coverp000000000000000111111010 : Covers (-278698/15625 : ℚ) vp000000000000000111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000011111101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111101-V-0000.bin"
noncomputable def vp00000000000000011111101 : Blocks := vp00000000000000011111101_0
private theorem bp000000000000000111111010 : Branch 0 (-139349/15625 : ℚ) vp00000000000000011111101 := by
  apply branch_left_normalized (c:=vp000000000000000111111010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-139349/15625 : ℚ) - ((0:ℤ):ℚ) = (-278698/15625 : ℚ) by norm_num]
  exact coverp000000000000000111111010
private noncomputable def ep000000000000000111111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111011-E-0000.bin"
noncomputable def ep000000000000000111111011 : Blocks := ep000000000000000111111011_0
private theorem idp000000000000000111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011111101.list =
    C ((2:ℤ)^14) * horner X vp000000000000000111111011.list + horner X ep000000000000000111111011.list := by
  exact edge_identity (B := (2:ℤ)^112) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000000111111011 : Branch 1 (-139349/15625 : ℚ) vp00000000000000011111101 := by
  apply branch_checked idp000000000000000111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-139349/15625 : ℚ) - ((1:ℤ):ℚ) = (-294323/15625 : ℚ) by norm_num]
  exact coverp000000000000000111111011
theorem coverp00000000000000011111101 : Covers (-139349/15625 : ℚ) vp00000000000000011111101 := join_branches bp000000000000000111111010 bp000000000000000111111011
private noncomputable def vp00000000000000011111100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111100-V-0000.bin"
noncomputable def vp00000000000000011111100 : Blocks := vp00000000000000011111100_0
theorem coverp00000000000000011111100 : Covers (-123724/15625 : ℚ) vp00000000000000011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000001111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111110-V-0000.bin"
noncomputable def vp0000000000000001111110 : Blocks := vp0000000000000001111110_0
private theorem bp00000000000000011111100 : Branch 0 (-61862/15625 : ℚ) vp0000000000000001111110 := by
  apply branch_left_normalized (c:=vp00000000000000011111100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-61862/15625 : ℚ) - ((0:ℤ):ℚ) = (-123724/15625 : ℚ) by norm_num]
  exact coverp00000000000000011111100
private noncomputable def ep00000000000000011111101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000011111101-E-0000.bin"
noncomputable def ep00000000000000011111101 : Blocks := ep00000000000000011111101_0
private theorem idp00000000000000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111110.list =
    C ((2:ℤ)^17) * horner X vp00000000000000011111101.list + horner X ep00000000000000011111101.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000011111101 : Branch 1 (-61862/15625 : ℚ) vp0000000000000001111110 := by
  apply branch_checked idp00000000000000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-61862/15625 : ℚ) - ((1:ℤ):ℚ) = (-139349/15625 : ℚ) by norm_num]
  exact coverp00000000000000011111101
theorem coverp0000000000000001111110 : Covers (-61862/15625 : ℚ) vp0000000000000001111110 := join_branches bp00000000000000011111100 bp00000000000000011111101
private noncomputable def vp000000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111-V-0000.bin"
noncomputable def vp000000000000000111111 : Blocks := vp000000000000000111111_0
private theorem bp0000000000000001111110 : Branch 0 (-30931/15625 : ℚ) vp000000000000000111111 := by
  apply branch_left_normalized (c:=vp0000000000000001111110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-30931/15625 : ℚ) - ((0:ℤ):ℚ) = (-61862/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111110
private noncomputable def ep0000000000000001111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111111-E-0000.bin"
noncomputable def ep0000000000000001111111 : Blocks := ep0000000000000001111111_0
private theorem idp0000000000000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111111.list =
    C ((2:ℤ)^22) * horner X vp0000000000000001111111.list + horner X ep0000000000000001111111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000001111111 : Branch 1 (-30931/15625 : ℚ) vp000000000000000111111 := by
  apply branch_checked idp0000000000000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-30931/15625 : ℚ) - ((1:ℤ):ℚ) = (-77487/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111111
theorem coverp000000000000000111111 : Covers (-30931/15625 : ℚ) vp000000000000000111111 := join_branches bp0000000000000001111110 bp0000000000000001111111
private noncomputable def vp0000000000000001111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111101-V-0000.bin"
noncomputable def vp0000000000000001111101 : Blocks := vp0000000000000001111101_0
theorem coverp0000000000000001111101 : Covers (-46237/15625 : ℚ) vp0000000000000001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000001111100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111100-V-0000.bin"
noncomputable def vp0000000000000001111100 : Blocks := vp0000000000000001111100_0
theorem coverp0000000000000001111100 : Covers (-30612/15625 : ℚ) vp0000000000000001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000000111110_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111110-V-0000.bin"
noncomputable def vp000000000000000111110 : Blocks := vp000000000000000111110_0
private theorem bp0000000000000001111100 : Branch 0 (-15306/15625 : ℚ) vp000000000000000111110 := by
  apply branch_left_normalized (c:=vp0000000000000001111100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-15306/15625 : ℚ) - ((0:ℤ):ℚ) = (-30612/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111100
private noncomputable def ep0000000000000001111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000001111101-E-0000.bin"
noncomputable def ep0000000000000001111101 : Blocks := ep0000000000000001111101_0
private theorem idp0000000000000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111110.list =
    C ((2:ℤ)^21) * horner X vp0000000000000001111101.list + horner X ep0000000000000001111101.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000001111101 : Branch 1 (-15306/15625 : ℚ) vp000000000000000111110 := by
  apply branch_checked idp0000000000000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-15306/15625 : ℚ) - ((1:ℤ):ℚ) = (-46237/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111101
theorem coverp000000000000000111110 : Covers (-15306/15625 : ℚ) vp000000000000000111110 := join_branches bp0000000000000001111100 bp0000000000000001111101
noncomputable def vp00000000000000011111 : Blocks := NextProof.EdgeRecovery.R00000000000000011111.C.data
private theorem bp000000000000000111110 : Branch 0 (-7653/15625 : ℚ) vp00000000000000011111 := by
  apply branch_left_normalized (c:=vp000000000000000111110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-7653/15625 : ℚ) - ((0:ℤ):ℚ) = (-15306/15625 : ℚ) by norm_num]
  exact coverp000000000000000111110
private noncomputable def ep000000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000000111111-E-0000.bin"
noncomputable def ep000000000000000111111 : Blocks := ep000000000000000111111_0
private theorem idp000000000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011111.list =
    C ((2:ℤ)^31) * horner X vp000000000000000111111.list + horner X ep000000000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^135) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000000111111 : Branch 1 (-7653/15625 : ℚ) vp00000000000000011111 := by
  apply branch_checked idp000000000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-7653/15625 : ℚ) - ((1:ℤ):ℚ) = (-30931/15625 : ℚ) by norm_num]
  exact coverp000000000000000111111
theorem coverp00000000000000011111 : Covers (-7653/15625 : ℚ) vp00000000000000011111 := join_branches bp000000000000000111110 bp000000000000000111111
noncomputable def vp0000000000000001111011 : Blocks := NextProof.EdgeRecovery.R0000000000000001111011.C.data
theorem coverp0000000000000001111011 : Covers (-14987/15625 : ℚ) vp0000000000000001111011 := cover_leaf (by decide +kernel)
noncomputable def vp00000000000000011110101 : Blocks := NextProof.EdgeRecovery.R00000000000000011110101.C.data
theorem coverp00000000000000011110101 : Covers (-14349/15625 : ℚ) vp00000000000000011110101 := cover_leaf (by decide +kernel)
noncomputable def vp000000000000000111101001 : Blocks := NextProof.EdgeRecovery.R000000000000000111101001.C.data
theorem coverp000000000000000111101001 : Covers (-13073/15625 : ℚ) vp000000000000000111101001 := cover_leaf (by decide +kernel)
noncomputable def vp0000000000000001111010001 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010001.C.data
theorem coverp0000000000000001111010001 : Covers (-10521/15625 : ℚ) vp0000000000000001111010001 := cover_leaf (by decide +kernel)
noncomputable def vp00000000000000011110100001 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100001.C.data
theorem coverp00000000000000011110100001 : Covers (-5417/15625 : ℚ) vp00000000000000011110100001 := cover_leaf (by decide +kernel)
noncomputable def vp0000000000000001111010000011 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000011.C.data
theorem coverp0000000000000001111010000011 : Covers (-6043/15625 : ℚ) vp0000000000000001111010000011 := cover_leaf (by decide +kernel)
noncomputable def vp000000000000000111101000001011 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001011.C.data
theorem coverp000000000000000111101000001011 : Covers (-8547/15625 : ℚ) vp000000000000000111101000001011 := cover_leaf (by decide +kernel)
noncomputable def vp0000000000000001111010000010101 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000010101.C.data
theorem coverp0000000000000001111010000010101 : Covers (-1469/15625 : ℚ) vp0000000000000001111010000010101 := cover_leaf (by decide +kernel)
noncomputable def vp0000000000000001111010000010100111 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000010100111.C.data
theorem coverp0000000000000001111010000010100111 : Covers (3873/15625 : ℚ) vp0000000000000001111010000010100111 := cover_leaf (by decide +kernel)
noncomputable def vp000000000000000111101000001010011 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001010011.C.data
private theorem bp0000000000000001111010000010100110 : Branch 0 (9749/15625 : ℚ) vp000000000000000111101000001010011 := branch_skip (by decide +kernel)
noncomputable def ep0000000000000001111010000010100111 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000010100111.E.data
private theorem idp0000000000000001111010000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111101000001010011.list =
    C ((2:ℤ)^11008) * horner X vp0000000000000001111010000010100111.list + horner X ep0000000000000001111010000010100111.list := by
  exact NextProof.EdgeRecovery.R0000000000000001111010000010100111.identity
private theorem bp0000000000000001111010000010100111 : Branch 1 (9749/15625 : ℚ) vp000000000000000111101000001010011 := by
  apply branch_checked idp0000000000000001111010000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(9749/15625 : ℚ) - ((1:ℤ):ℚ) = (3873/15625 : ℚ) by norm_num]
  exact coverp0000000000000001111010000010100111
theorem coverp000000000000000111101000001010011 : Covers (1040224798831/7629394531250 : ℚ) vp000000000000000111101000001010011 := NextProof.TightLeaf.parent_cover
noncomputable def vp00000000000000011110100000101001 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100000101001.C.data
private theorem bp000000000000000111101000001010010 : Branch 0 (8669619330081/15258789062500 : ℚ) vp00000000000000011110100000101001 := branch_skip (by decide +kernel)
noncomputable def ep000000000000000111101000001010011 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001010011.E.data
private theorem idp000000000000000111101000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011110100000101001.list =
    C ((2:ℤ)^11136) * horner X vp000000000000000111101000001010011.list + horner X ep000000000000000111101000001010011.list := by
  exact NextProof.EdgeRecovery.R000000000000000111101000001010011.identity
private theorem bp000000000000000111101000001010011 : Branch 1 (8669619330081/15258789062500 : ℚ) vp00000000000000011110100000101001 := by
  apply branch_checked idp000000000000000111101000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(8669619330081/15258789062500 : ℚ) - ((1:ℤ):ℚ) = (1040224798831/7629394531250 : ℚ) by norm_num]
  exact coverp000000000000000111101000001010011
theorem coverp00000000000000011110100000101001 : Covers (8669619330081/15258789062500 : ℚ) vp00000000000000011110100000101001 := join_branches bp000000000000000111101000001010010 bp000000000000000111101000001010011
noncomputable def vp0000000000000001111010000010100 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100000101001.P.data
private theorem bp00000000000000011110100000101000 : Branch 0 (23928408392581/30517578125000 : ℚ) vp0000000000000001111010000010100 := branch_skip (by decide +kernel)
noncomputable def ep00000000000000011110100000101001 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100000101001.E.data
private theorem idp00000000000000011110100000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111010000010100.list =
    C ((2:ℤ)^11264) * horner X vp00000000000000011110100000101001.list + horner X ep00000000000000011110100000101001.list := by
  exact NextProof.EdgeRecovery.R00000000000000011110100000101001.identity
private theorem bp00000000000000011110100000101001 : Branch 1 (23928408392581/30517578125000 : ℚ) vp0000000000000001111010000010100 := by
  apply branch_checked idp00000000000000011110100000101001 (by positivity) (by decide +kernel)
  rw [show 2*(23928408392581/30517578125000 : ℚ) - ((1:ℤ):ℚ) = (8669619330081/15258789062500 : ℚ) by norm_num]
  exact coverp00000000000000011110100000101001
theorem coverp0000000000000001111010000010100 : Covers (23928408392581/30517578125000 : ℚ) vp0000000000000001111010000010100 := join_branches bp00000000000000011110100000101000 bp00000000000000011110100000101001
noncomputable def vp000000000000000111101000001010 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000010101.P.data
private theorem bp0000000000000001111010000010100 : Branch 0 (23928408392581/61035156250000 : ℚ) vp000000000000000111101000001010 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000000000000001111010000010100) (k:=0) (m:=11263) (by decide +kernel)
  rw [show 2*(23928408392581/61035156250000 : ℚ) - ((0:ℤ):ℚ) = (23928408392581/30517578125000 : ℚ) by norm_num]
  exact coverp0000000000000001111010000010100
noncomputable def ep0000000000000001111010000010101 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000010101.E.data
private theorem idp0000000000000001111010000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111101000001010.list =
    C ((2:ℤ)^11392) * horner X vp0000000000000001111010000010101.list + horner X ep0000000000000001111010000010101.list := by
  exact NextProof.EdgeRecovery.R0000000000000001111010000010101.identity
private theorem bp0000000000000001111010000010101 : Branch 1 (23928408392581/61035156250000 : ℚ) vp000000000000000111101000001010 := by
  apply branch_checked idp0000000000000001111010000010101 (by positivity) (by decide +kernel)
  rw [show 2*(23928408392581/61035156250000 : ℚ) - ((1:ℤ):ℚ) = (-6589169732419/30517578125000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0000000000000001111010000010101 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000000000000000111101000001010 : Covers (23928408392581/61035156250000 : ℚ) vp000000000000000111101000001010 := join_branches bp0000000000000001111010000010100 bp0000000000000001111010000010101
noncomputable def vp00000000000000011110100000101 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100000101.C.data
private theorem bp000000000000000111101000001010 : Branch 0 (23928408392581/122070312500000 : ℚ) vp00000000000000011110100000101 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000000000000000111101000001010) (k:=0) (m:=11391) (by decide +kernel)
  rw [show 2*(23928408392581/122070312500000 : ℚ) - ((0:ℤ):ℚ) = (23928408392581/61035156250000 : ℚ) by norm_num]
  exact coverp000000000000000111101000001010
noncomputable def ep000000000000000111101000001011 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001011.E.data
private theorem idp000000000000000111101000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011110100000101.list =
    C ((2:ℤ)^11520) * horner X vp000000000000000111101000001011.list + horner X ep000000000000000111101000001011.list := by
  exact NextProof.EdgeRecovery.R000000000000000111101000001011.identity
private theorem bp000000000000000111101000001011 : Branch 1 (23928408392581/122070312500000 : ℚ) vp00000000000000011110100000101 := by
  apply branch_checked idp000000000000000111101000001011 (by positivity) (by decide +kernel)
  rw [show 2*(23928408392581/122070312500000 : ℚ) - ((1:ℤ):ℚ) = (-37106747857419/61035156250000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp000000000000000111101000001011 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00000000000000011110100000101 : Covers (23928408392581/122070312500000 : ℚ) vp00000000000000011110100000101 := join_branches bp000000000000000111101000001010 bp000000000000000111101000001011
noncomputable def vp0000000000000001111010000010 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100000101.P.data
private theorem bp00000000000000011110100000100 : Branch 0 (145998720892581/244140625000000 : ℚ) vp0000000000000001111010000010 := branch_skip (by decide +kernel)
noncomputable def ep00000000000000011110100000101 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100000101.E.data
private theorem idp00000000000000011110100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111010000010.list =
    C ((2:ℤ)^11648) * horner X vp00000000000000011110100000101.list + horner X ep00000000000000011110100000101.list := by
  exact NextProof.EdgeRecovery.R00000000000000011110100000101.identity
private theorem bp00000000000000011110100000101 : Branch 1 (145998720892581/244140625000000 : ℚ) vp0000000000000001111010000010 := by
  apply branch_checked idp00000000000000011110100000101 (by positivity) (by decide +kernel)
  rw [show 2*(145998720892581/244140625000000 : ℚ) - ((1:ℤ):ℚ) = (23928408392581/122070312500000 : ℚ) by norm_num]
  exact coverp00000000000000011110100000101
theorem coverp0000000000000001111010000010 : Covers (145998720892581/244140625000000 : ℚ) vp0000000000000001111010000010 := join_branches bp00000000000000011110100000100 bp00000000000000011110100000101
noncomputable def vp000000000000000111101000001 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001.C.data
private theorem bp0000000000000001111010000010 : Branch 0 (145998720892581/488281250000000 : ℚ) vp000000000000000111101000001 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000000000000001111010000010) (k:=0) (m:=11647) (by decide +kernel)
  rw [show 2*(145998720892581/488281250000000 : ℚ) - ((0:ℤ):ℚ) = (145998720892581/244140625000000 : ℚ) by norm_num]
  exact coverp0000000000000001111010000010
noncomputable def ep0000000000000001111010000011 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010000011.E.data
private theorem idp0000000000000001111010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111101000001.list =
    C ((2:ℤ)^11776) * horner X vp0000000000000001111010000011.list + horner X ep0000000000000001111010000011.list := by
  exact NextProof.EdgeRecovery.R0000000000000001111010000011.identity
private theorem bp0000000000000001111010000011 : Branch 1 (145998720892581/488281250000000 : ℚ) vp000000000000000111101000001 := by
  apply branch_checked idp0000000000000001111010000011 (by positivity) (by decide +kernel)
  rw [show 2*(145998720892581/488281250000000 : ℚ) - ((1:ℤ):ℚ) = (-98141904107419/244140625000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0000000000000001111010000011 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000000000000000111101000001 : Covers (145998720892581/488281250000000 : ℚ) vp000000000000000111101000001 := join_branches bp0000000000000001111010000010 bp0000000000000001111010000011
noncomputable def vp00000000000000011110100000 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001.P.data
private theorem bp000000000000000111101000000 : Branch 0 (634279970892581/976562500000000 : ℚ) vp00000000000000011110100000 := branch_skip (by decide +kernel)
noncomputable def ep000000000000000111101000001 : Blocks := NextProof.EdgeRecovery.R000000000000000111101000001.E.data
private theorem idp000000000000000111101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011110100000.list =
    C ((2:ℤ)^11904) * horner X vp000000000000000111101000001.list + horner X ep000000000000000111101000001.list := by
  exact NextProof.EdgeRecovery.R000000000000000111101000001.identity
private theorem bp000000000000000111101000001 : Branch 1 (634279970892581/976562500000000 : ℚ) vp00000000000000011110100000 := by
  apply branch_checked idp000000000000000111101000001 (by positivity) (by decide +kernel)
  rw [show 2*(634279970892581/976562500000000 : ℚ) - ((1:ℤ):ℚ) = (145998720892581/488281250000000 : ℚ) by norm_num]
  exact coverp000000000000000111101000001
theorem coverp00000000000000011110100000 : Covers (634279970892581/976562500000000 : ℚ) vp00000000000000011110100000 := join_branches bp000000000000000111101000000 bp000000000000000111101000001
noncomputable def vp0000000000000001111010000 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100001.P.data
private theorem bp00000000000000011110100000 : Branch 0 (634279970892581/1953125000000000 : ℚ) vp0000000000000001111010000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp00000000000000011110100000) (k:=0) (m:=11903) (by decide +kernel)
  rw [show 2*(634279970892581/1953125000000000 : ℚ) - ((0:ℤ):ℚ) = (634279970892581/976562500000000 : ℚ) by norm_num]
  exact coverp00000000000000011110100000
noncomputable def ep00000000000000011110100001 : Blocks := NextProof.EdgeRecovery.R00000000000000011110100001.E.data
private theorem idp00000000000000011110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111010000.list =
    C ((2:ℤ)^12032) * horner X vp00000000000000011110100001.list + horner X ep00000000000000011110100001.list := by
  exact NextProof.EdgeRecovery.R00000000000000011110100001.identity
private theorem bp00000000000000011110100001 : Branch 1 (634279970892581/1953125000000000 : ℚ) vp0000000000000001111010000 := by
  apply branch_checked idp00000000000000011110100001 (by positivity) (by decide +kernel)
  rw [show 2*(634279970892581/1953125000000000 : ℚ) - ((1:ℤ):ℚ) = (-342282529107419/976562500000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp00000000000000011110100001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp0000000000000001111010000 : Covers (634279970892581/1953125000000000 : ℚ) vp0000000000000001111010000 := join_branches bp00000000000000011110100000 bp00000000000000011110100001
noncomputable def vp000000000000000111101000 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010001.P.data
private theorem bp0000000000000001111010000 : Branch 0 (634279970892581/3906250000000000 : ℚ) vp000000000000000111101000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000000000000001111010000) (k:=0) (m:=12031) (by decide +kernel)
  rw [show 2*(634279970892581/3906250000000000 : ℚ) - ((0:ℤ):ℚ) = (634279970892581/1953125000000000 : ℚ) by norm_num]
  exact coverp0000000000000001111010000
noncomputable def ep0000000000000001111010001 : Blocks := NextProof.EdgeRecovery.R0000000000000001111010001.E.data
private theorem idp0000000000000001111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111101000.list =
    C ((2:ℤ)^12160) * horner X vp0000000000000001111010001.list + horner X ep0000000000000001111010001.list := by
  exact NextProof.EdgeRecovery.R0000000000000001111010001.identity
private theorem bp0000000000000001111010001 : Branch 1 (634279970892581/3906250000000000 : ℚ) vp000000000000000111101000 := by
  apply branch_checked idp0000000000000001111010001 (by positivity) (by decide +kernel)
  rw [show 2*(634279970892581/3906250000000000 : ℚ) - ((1:ℤ):ℚ) = (-1318845029107419/1953125000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0000000000000001111010001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000000000000000111101000 : Covers (634279970892581/3906250000000000 : ℚ) vp000000000000000111101000 := join_branches bp0000000000000001111010000 bp0000000000000001111010001
noncomputable def vp00000000000000011110100 : Blocks := NextProof.EdgeRecovery.R000000000000000111101001.P.data
private theorem bp000000000000000111101000 : Branch 0 (634279970892581/7812500000000000 : ℚ) vp00000000000000011110100 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000000000000000111101000) (k:=0) (m:=12159) (by decide +kernel)
  rw [show 2*(634279970892581/7812500000000000 : ℚ) - ((0:ℤ):ℚ) = (634279970892581/3906250000000000 : ℚ) by norm_num]
  exact coverp000000000000000111101000
noncomputable def ep000000000000000111101001 : Blocks := NextProof.EdgeRecovery.R000000000000000111101001.E.data
private theorem idp000000000000000111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011110100.list =
    C ((2:ℤ)^12288) * horner X vp000000000000000111101001.list + horner X ep000000000000000111101001.list := by
  exact NextProof.EdgeRecovery.R000000000000000111101001.identity
private theorem bp000000000000000111101001 : Branch 1 (634279970892581/7812500000000000 : ℚ) vp00000000000000011110100 := by
  apply branch_checked idp000000000000000111101001 (by positivity) (by decide +kernel)
  rw [show 2*(634279970892581/7812500000000000 : ℚ) - ((1:ℤ):ℚ) = (-3271970029107419/3906250000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp000000000000000111101001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00000000000000011110100 : Covers (634279970892581/7812500000000000 : ℚ) vp00000000000000011110100 := join_branches bp000000000000000111101000 bp000000000000000111101001
noncomputable def vp0000000000000001111010 : Blocks := NextProof.EdgeRecovery.R00000000000000011110101.P.data
private theorem bp00000000000000011110100 : Branch 0 (634279970892581/15625000000000000 : ℚ) vp0000000000000001111010 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp00000000000000011110100) (k:=0) (m:=12287) (by decide +kernel)
  rw [show 2*(634279970892581/15625000000000000 : ℚ) - ((0:ℤ):ℚ) = (634279970892581/7812500000000000 : ℚ) by norm_num]
  exact coverp00000000000000011110100
noncomputable def ep00000000000000011110101 : Blocks := NextProof.EdgeRecovery.R00000000000000011110101.E.data
private theorem idp00000000000000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111010.list =
    C ((2:ℤ)^12416) * horner X vp00000000000000011110101.list + horner X ep00000000000000011110101.list := by
  exact NextProof.EdgeRecovery.R00000000000000011110101.identity
private theorem bp00000000000000011110101 : Branch 1 (634279970892581/15625000000000000 : ℚ) vp0000000000000001111010 := by
  apply branch_checked idp00000000000000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(634279970892581/15625000000000000 : ℚ) - ((1:ℤ):ℚ) = (-7178220029107419/7812500000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp00000000000000011110101 x hx hx' (le_trans (by norm_num) hx)
theorem coverp0000000000000001111010 : Covers (634279970892581/15625000000000000 : ℚ) vp0000000000000001111010 := join_branches bp00000000000000011110100 bp00000000000000011110101
noncomputable def vp000000000000000111101 : Blocks := NextProof.EdgeRecovery.R000000000000000111101.C.data
private theorem bp0000000000000001111010 : Branch 0 (634279970892581/31250000000000000 : ℚ) vp000000000000000111101 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000000000000001111010) (k:=0) (m:=12415) (by decide +kernel)
  rw [show 2*(634279970892581/31250000000000000 : ℚ) - ((0:ℤ):ℚ) = (634279970892581/15625000000000000 : ℚ) by norm_num]
  exact coverp0000000000000001111010
noncomputable def ep0000000000000001111011 : Blocks := NextProof.EdgeRecovery.R0000000000000001111011.E.data
private theorem idp0000000000000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111101.list =
    C ((2:ℤ)^12544) * horner X vp0000000000000001111011.list + horner X ep0000000000000001111011.list := by
  exact NextProof.EdgeRecovery.R0000000000000001111011.identity
private theorem bp0000000000000001111011 : Branch 1 (634279970892581/31250000000000000 : ℚ) vp000000000000000111101 := by
  apply branch_checked idp0000000000000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(634279970892581/31250000000000000 : ℚ) - ((1:ℤ):ℚ) = (-14990720029107419/15625000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0000000000000001111011 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000000000000000111101 : Covers (634279970892581/31250000000000000 : ℚ) vp000000000000000111101 := join_branches bp0000000000000001111010 bp0000000000000001111011
noncomputable def vp00000000000000011110 : Blocks := NextProof.EdgeRecovery.R000000000000000111101.P.data
private theorem bp000000000000000111100 : Branch 0 (31884279970892581/62500000000000000 : ℚ) vp00000000000000011110 := branch_skip (by decide +kernel)
noncomputable def ep000000000000000111101 : Blocks := NextProof.EdgeRecovery.R000000000000000111101.E.data
private theorem idp000000000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011110.list =
    C ((2:ℤ)^12672) * horner X vp000000000000000111101.list + horner X ep000000000000000111101.list := by
  exact NextProof.EdgeRecovery.R000000000000000111101.identity
private theorem bp000000000000000111101 : Branch 1 (31884279970892581/62500000000000000 : ℚ) vp00000000000000011110 := by
  apply branch_checked idp000000000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(31884279970892581/62500000000000000 : ℚ) - ((1:ℤ):ℚ) = (634279970892581/31250000000000000 : ℚ) by norm_num]
  exact coverp000000000000000111101
theorem coverp00000000000000011110 : Covers (31884279970892581/62500000000000000 : ℚ) vp00000000000000011110 := join_branches bp000000000000000111100 bp000000000000000111101
noncomputable def vp0000000000000001111 : Blocks := NextProof.EdgeRecovery.R0000000000000001111.C.data
private theorem bp00000000000000011110 : Branch 0 (31884279970892581/125000000000000000 : ℚ) vp0000000000000001111 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp00000000000000011110) (k:=0) (m:=12671) (by decide +kernel)
  rw [show 2*(31884279970892581/125000000000000000 : ℚ) - ((0:ℤ):ℚ) = (31884279970892581/62500000000000000 : ℚ) by norm_num]
  exact coverp00000000000000011110
noncomputable def ep00000000000000011111 : Blocks := NextProof.EdgeRecovery.R00000000000000011111.E.data
private theorem idp00000000000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001111.list =
    C ((2:ℤ)^12800) * horner X vp00000000000000011111.list + horner X ep00000000000000011111.list := by
  exact NextProof.EdgeRecovery.R00000000000000011111.identity
private theorem bp00000000000000011111 : Branch 1 (31884279970892581/125000000000000000 : ℚ) vp0000000000000001111 := by
  apply branch_checked idp00000000000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(31884279970892581/125000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-30615720029107419/62500000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp00000000000000011111 x hx hx' (le_trans (by norm_num) hx)
theorem coverp0000000000000001111 : Covers (31884279970892581/125000000000000000 : ℚ) vp0000000000000001111 := join_branches bp00000000000000011110 bp00000000000000011111
noncomputable def vp000000000000000111 : Blocks := NextProof.EdgeRecovery.R000000000000000111.C.data
private theorem bp0000000000000001110 : Branch 0 (156884279970892581/250000000000000000 : ℚ) vp000000000000000111 := branch_skip (by decide +kernel)
noncomputable def ep0000000000000001111 : Blocks := NextProof.EdgeRecovery.R0000000000000001111.E.data
private theorem idp0000000000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000111.list =
    C ((2:ℤ)^12928) * horner X vp0000000000000001111.list + horner X ep0000000000000001111.list := by
  exact NextProof.EdgeRecovery.R0000000000000001111.identity
private theorem bp0000000000000001111 : Branch 1 (156884279970892581/250000000000000000 : ℚ) vp000000000000000111 := by
  apply branch_checked idp0000000000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(156884279970892581/250000000000000000 : ℚ) - ((1:ℤ):ℚ) = (31884279970892581/125000000000000000 : ℚ) by norm_num]
  exact coverp0000000000000001111
theorem coverp000000000000000111 : Covers (156884279970892581/250000000000000000 : ℚ) vp000000000000000111 := join_branches bp0000000000000001110 bp0000000000000001111
noncomputable def vp00000000000000011 : Blocks := NextProof.EdgeRecovery.R00000000000000011.C.data
private theorem bp000000000000000110 : Branch 0 (406884279970892581/500000000000000000 : ℚ) vp00000000000000011 := branch_skip (by decide +kernel)
noncomputable def ep000000000000000111 : Blocks := NextProof.EdgeRecovery.R000000000000000111.E.data
private theorem idp000000000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000011.list =
    C ((2:ℤ)^13056) * horner X vp000000000000000111.list + horner X ep000000000000000111.list := by
  exact NextProof.EdgeRecovery.R000000000000000111.identity
private theorem bp000000000000000111 : Branch 1 (406884279970892581/500000000000000000 : ℚ) vp00000000000000011 := by
  apply branch_checked idp000000000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(406884279970892581/500000000000000000 : ℚ) - ((1:ℤ):ℚ) = (156884279970892581/250000000000000000 : ℚ) by norm_num]
  exact coverp000000000000000111
theorem coverp00000000000000011 : Covers (406884279970892581/500000000000000000 : ℚ) vp00000000000000011 := join_branches bp000000000000000110 bp000000000000000111
noncomputable def vp0000000000000001 : Blocks := NextProof.EdgeRecovery.R0000000000000001.C.data
private theorem bp00000000000000010 : Branch 0 (906884279970892581/1000000000000000000 : ℚ) vp0000000000000001 := branch_skip (by decide +kernel)
noncomputable def ep00000000000000011 : Blocks := NextProof.EdgeRecovery.R00000000000000011.E.data
private theorem idp00000000000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000001.list =
    C ((2:ℤ)^13184) * horner X vp00000000000000011.list + horner X ep00000000000000011.list := by
  exact NextProof.EdgeRecovery.R00000000000000011.identity
private theorem bp00000000000000011 : Branch 1 (906884279970892581/1000000000000000000 : ℚ) vp0000000000000001 := by
  apply branch_checked idp00000000000000011 (by positivity) (by decide +kernel)
  rw [show 2*(906884279970892581/1000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (406884279970892581/500000000000000000 : ℚ) by norm_num]
  exact coverp00000000000000011
theorem coverp0000000000000001 : Covers (906884279970892581/1000000000000000000 : ℚ) vp0000000000000001 := join_branches bp00000000000000010 bp00000000000000011
noncomputable def vp000000000000000 : Blocks := NextProof.EdgeRecovery.R0000000000000001.P.data
private theorem bp0000000000000000 : Branch 0 (1906884279970892581/2000000000000000000 : ℚ) vp000000000000000 := branch_skip (by decide +kernel)
noncomputable def ep0000000000000001 : Blocks := NextProof.EdgeRecovery.R0000000000000001.E.data
private theorem idp0000000000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000000.list =
    C ((2:ℤ)^13312) * horner X vp0000000000000001.list + horner X ep0000000000000001.list := by
  exact NextProof.EdgeRecovery.R0000000000000001.identity
private theorem bp0000000000000001 : Branch 1 (1906884279970892581/2000000000000000000 : ℚ) vp000000000000000 := by
  apply branch_checked idp0000000000000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/2000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (906884279970892581/1000000000000000000 : ℚ) by norm_num]
  exact coverp0000000000000001
theorem coverp000000000000000 : Covers (1906884279970892581/2000000000000000000 : ℚ) vp000000000000000 := join_branches bp0000000000000000 bp0000000000000001
noncomputable def vp00000000000000 : Blocks := NextProof.EdgeRecovery.R000000000000001.P.data
private theorem bp000000000000000 : Branch 0 (1906884279970892581/4000000000000000000 : ℚ) vp00000000000000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000000000000000) (k:=0) (m:=13311) (by decide +kernel)
  rw [show 2*(1906884279970892581/4000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/2000000000000000000 : ℚ) by norm_num]
  exact coverp000000000000000
noncomputable def ep000000000000001 : Blocks := NextProof.EdgeRecovery.R000000000000001.E.data
private theorem idp000000000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000.list =
    C ((2:ℤ)^13568) * horner X vp000000000000001.list + horner X ep000000000000001.list := by
  exact NextProof.EdgeRecovery.R000000000000001.identity
private theorem bp000000000000001 : Branch 1 (1906884279970892581/4000000000000000000 : ℚ) vp00000000000000 := by
  apply branch_checked idp000000000000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/4000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-93115720029107419/2000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp000000000000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00000000000000 : Covers (1906884279970892581/4000000000000000000 : ℚ) vp00000000000000 := join_branches bp000000000000000 bp000000000000001
end NextProof.EdgeFull

