module
public import QuantitativeFollowup.ScalarParameterConstants
public import FourPapersCommon.ParisiNoiseTemperature

@[expose] public section

/-! Genuine same-Wiener coupling, uniformly over a positive temperature
window. The random error is an integrable actual Brownian path norm. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def scalarStateParameterConstant (B : ℝ) : ℝ :=
  parisiStateL1Constant B+(1+B^2*scalarGradientTemperatureConstant B)*Real.exp (B^2)

def scalarStateNoiseConstant (B : ℝ) : ℝ := Real.exp (B^2)/B

theorem scalarStateParameterConstant_nonneg (B : ℝ) : 0≤ scalarStateParameterConstant B := by
  have hS := parisiStateL1Constant_nonneg B
  unfold scalarStateParameterConstant scalarGradientTemperatureConstant
  positivity

theorem abs_temperature_sub_le_square_window (B b e : ℝ) (hB : 0< B)
    (hb : 0≤ b) (he : 0≤ e) (hbL : B^2/2≤ b^2) (heL : B^2/2≤ e^2) :
    |b-e|≤|b^2-e^2|/B := by
  have hbl : B/2≤ b := by nlinarith [sq_nonneg (B/2-b)]
  have hel : B/2≤ e := by nlinarith [sq_nonneg (B/2-e)]
  have hsum : B≤ b+e := by linarith
  have heq : |b^2-e^2|=|b-e| *(b+e) := by
    rw [show b^2-e^2=(b-e)*(b+e) by ring,abs_mul,abs_of_nonneg (add_nonneg hb he)]
  apply (le_div_iff₀ hB).mpr
  rw [heq]
  exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

theorem selectedParisiState_parameter_window_bound (B b e : ℝ)
    (hB : 0< B) (hb : 0< b) (he : 0< e)
    (hbB : b^2∈Icc (B^2/2) (B^2)) (heB : e^2∈Icc (B^2/2) (B^2))
    (μ ν : Paper.ParisiMeasure) (h q : ℝ) (hq : q∈Icc (0 : ℝ) 1)
    (ω : Paper.BrownianSample) :
    ‖selectedParisiStateReal b h hb.ne' μ ω q-selectedParisiStateReal e h he.ne' ν ω q‖≤
      scalarStateParameterConstant B*(Paper.parisiCDFDistance μ ν+|b^2-e^2|)+
      scalarStateNoiseConstant B*‖canonicalBrownianPath ω‖*|b^2-e^2| := by
  have hM := selectedParisiState_CDF_L1_bound b h hb.ne' μ ν q hq ω
  have hMc := parisiStateL1Constant_le_of_sq_le B b hbB.2
  have hδ := FourPapersCommon.parisiCDFDistance_nonneg μ ν
  have hM' : ‖selectedParisiStateReal b h hb.ne' μ ω q-selectedParisiStateReal b h hb.ne' ν ω q‖≤
      parisiStateL1Constant B*Paper.parisiCDFDistance μ ν := by
    simpa only [FourPapersCommon.parisiCDFDistance,Paper.parisiCDFDistance,Real.norm_eq_abs] using
      hM.trans (mul_le_mul_of_nonneg_right hMc hδ)
  have hp := ContinuousMap.dist_apply_le_dist (f:=parisiNoiseStatePath b h ν (canonicalBrownianPath ω))
    (g:=parisiNoiseStatePath e h ν (canonicalBrownianPath ω)) (⟨q,hq⟩:Overlap)
  rw [parisiNoiseStatePath_canonical b h hb.ne',parisiNoiseStatePath_canonical e h he.ne',dist_eq_norm] at hp
  have hT := parisiNoiseStatePath_temperature_dist_le b e h ν (canonicalBrownianPath ω)
  have hG := parisiGradientBCF_temperature_square_bound b e hb.ne' he.ne' ν
  have hGc := scalarGradientTemperatureConstant_le_of_sq_le B b hbB.2
  have hG' := hG.trans (mul_le_mul_of_nonneg_right hGc (abs_nonneg _))
  have hab := abs_temperature_sub_le_square_window B b e hB hb.le he.le hbB.1 heB.1
  have hN := norm_nonneg (canonicalBrownianPath ω)
  have hnoise := mul_le_mul_of_nonneg_right hab hN
  have hGe := mul_le_mul heB.2 hG' (norm_nonneg _) (sq_nonneg B)
  have ht := add_le_add (add_le_add hnoise (le_refl (|b^2-e^2|))) hGe
  have ht0 : 0≤|b-e| *‖canonicalBrownianPath ω‖+|b^2-e^2|+
      e^2*‖parisiGradientBCF b ν-parisiGradientBCF e ν‖ := by positivity
  have htemp := mul_le_mul ht (Real.exp_le_exp.mpr heB.2) (Real.exp_pos _).le
    ((le_refl (0 : ℝ)).trans ht0 |>.trans ht)
  have hT' := (hp.trans hT).trans htemp
  have htotal := (norm_sub_le_norm_sub_add_norm_sub
    (selectedParisiStateReal b h hb.ne' μ ω q) (selectedParisiStateReal b h hb.ne' ν ω q)
    (selectedParisiStateReal e h he.ne' ν ω q)).trans (add_le_add hM' hT')
  apply htotal.trans
  have hSc := parisiStateL1Constant_nonneg B
  have hCc : 0≤1+B^2*scalarGradientTemperatureConstant B := by unfold scalarGradientTemperatureConstant;positivity
  have hD := Paper.parisiCDFDistance_nonneg μ ν
  dsimp only [scalarStateParameterConstant,scalarStateNoiseConstant]
  have heq : (parisiStateL1Constant B+(1+B^2*scalarGradientTemperatureConstant B)*Real.exp (B^2))*
        (Paper.parisiCDFDistance μ ν+|b^2-e^2|)+Real.exp (B^2)/B*‖canonicalBrownianPath ω‖*|b^2-e^2|=
      parisiStateL1Constant B*Paper.parisiCDFDistance μ ν+
        (|b^2-e^2|/B*‖canonicalBrownianPath ω‖+|b^2-e^2|+
          B^2*(scalarGradientTemperatureConstant B*|b^2-e^2|))*Real.exp (B^2)+
      ((1+B^2*scalarGradientTemperatureConstant B)*Real.exp (B^2))*Paper.parisiCDFDistance μ ν+
      parisiStateL1Constant B*|b^2-e^2| := by ring
  rw [heq]
  nlinarith only [mul_nonneg (mul_nonneg hCc (Real.exp_pos (B^2)).le) hD,
    mul_nonneg hSc (abs_nonneg (b^2-e^2))]

end QuantitativeFollowup
