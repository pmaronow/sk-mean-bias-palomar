module
public import QuantitativeFollowup.ScalarHessianTemperatureBound
public import FourPapersCommon.ParisiMomentL1

@[expose] public section

/-! Explicit constants uniform on a bounded inverse-temperature window. -/
noncomputable section
open Set Paper
namespace QuantitativeFollowup
open FourPapersCommon
set_option maxHeartbeats 900000

theorem parisiGradientL1Constant_le_of_sq_le (B b : ℝ) (h : b^2≤ B^2) :
    parisiGradientL1Constant b≤ parisiGradientL1Constant B := by
  have he := Real.exp_le_exp.mpr h
  have hp := mul_le_mul h he (Real.exp_pos _).le (sq_nonneg B)
  have hp2 : 2*b^2*Real.exp (b^2)≤2*B^2*Real.exp (B^2) := by nlinarith only [hp]
  exact mul_le_mul hp2 (Real.exp_le_exp.mpr hp2) (Real.exp_pos _).le (by positivity)

theorem parisiStateL1Constant_le_of_sq_le (B b : ℝ) (h : b^2≤ B^2) :
    parisiStateL1Constant b≤ parisiStateL1Constant B := by
  have hG := parisiGradientL1Constant_le_of_sq_le B b h
  have hG0 := parisiGradientL1Constant_nonneg b
  have hG1 := parisiGradientL1Constant_nonneg B
  unfold parisiStateL1Constant
  apply mul_le_mul
  · apply mul_le_mul h
    · nlinarith [mul_le_mul_of_nonneg_right hG (Real.exp_pos 1).le]
    · positivity
    · exact sq_nonneg B
  · exact Real.exp_le_exp.mpr h
  · exact (Real.exp_pos _).le
  · positivity

theorem parisiHessianL1Constant_le_of_sq_le (B b : ℝ) (h : b^2≤ B^2) :
    parisiHessianL1Constant b≤ parisiHessianL1Constant B := by
  have hG := parisiGradientL1Constant_le_of_sq_le B b h
  have hG0 := parisiGradientL1Constant_nonneg b
  have hG1 := parisiGradientL1Constant_nonneg B
  unfold parisiHessianL1Constant
  apply mul_le_mul
  · apply mul_le_mul
    · nlinarith
    · nlinarith
    · positivity
    · positivity
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · exact (Real.exp_pos _).le
  · positivity

theorem scalarGradientTemperatureConstant_le_of_sq_le (B b : ℝ) (h : b^2≤ B^2) :
    scalarGradientTemperatureConstant b≤ scalarGradientTemperatureConstant B :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by norm_num)

theorem scalarHessianTemperatureConstant_le_window (B b e : ℝ)
    (hb : b^2≤ B^2) (he : e^2≤ B^2) :
    scalarHessianTemperatureConstant b e≤ scalarHessianTemperatureConstant B B := by
  have hG := scalarGradientTemperatureConstant_le_of_sq_le B b hb
  have hG0 : 0≤ scalarGradientTemperatureConstant b := by unfold scalarGradientTemperatureConstant;positivity
  have hG1 : 0≤ scalarGradientTemperatureConstant B := by unfold scalarGradientTemperatureConstant;positivity
  have hp := mul_le_mul hb hG hG0 (sq_nonneg B)
  have h4 := scalarFourthJetBound_le_of_sq_le B e he
  have hsrc : scalarHessianTemperatureSourceConstant b e≤ scalarHessianTemperatureSourceConstant B B := by
    unfold scalarHessianTemperatureSourceConstant
    nlinarith only [hp,h4]
  unfold scalarHessianTemperatureConstant
  exact mul_le_mul (by nlinarith only [hsrc]) (Real.exp_le_exp.mpr (by nlinarith))
    (Real.exp_pos _).le (by have hc := scalarHessianTemperatureSourceConstant_pos B B;positivity)

def scalarPDEParameterConstant (B : ℝ) : ℝ :=
  parisiGradientL1Constant B+parisiHessianL1Constant B+
    scalarGradientTemperatureConstant B+scalarHessianTemperatureConstant B B

theorem scalarPDEParameterConstant_nonneg (B : ℝ) : 0≤ scalarPDEParameterConstant B := by
  have hG := parisiGradientL1Constant_nonneg B
  have hH : 0≤ parisiHessianL1Constant B := by unfold parisiHessianL1Constant FourPapersCommon.parisiGradientL1Constant;positivity
  have hT : 0≤ scalarGradientTemperatureConstant B := by unfold scalarGradientTemperatureConstant;positivity
  have hTH : 0≤ scalarHessianTemperatureConstant B B := by
    unfold scalarHessianTemperatureConstant
    have hp := scalarHessianTemperatureSourceConstant_pos B B
    positivity
  unfold scalarPDEParameterConstant
  positivity

theorem parisiHessian_parameter_window_bound (B b e : ℝ)
    (hb : b≠0) (he : e≠0) (hbB : b^2≤ B^2) (heB : e^2≤ B^2)
    (μ ν : Paper.ParisiMeasure) (q : ℝ) (hq : q∈Icc (0 : ℝ) 1) (x : ℝ) :
    ‖parisiHessian b μ (q,x)-parisiHessian e ν (q,x)‖≤
      (parisiHessianL1Constant B+scalarHessianTemperatureConstant B B)*
        (Paper.parisiCDFDistance μ ν+|b^2-e^2|) := by
  have hH := parisiHessian_CDF_L1_bound b hb μ ν q hq x
  have hT := parisiHessian_temperature_square_bound b e hb he ν q hq x
  have hHc := parisiHessianL1Constant_le_of_sq_le B b hbB
  have hTc := scalarHessianTemperatureConstant_le_window B b e hbB heB
  have hδ := Paper.parisiCDFDistance_nonneg μ ν
  have hH0 : 0≤ parisiHessianL1Constant B := by unfold parisiHessianL1Constant FourPapersCommon.parisiGradientL1Constant;positivity
  have hT0 : 0≤ scalarHessianTemperatureConstant B B := by
    unfold scalarHessianTemperatureConstant
    have hsrc := scalarHessianTemperatureSourceConstant_pos B B
    positivity
  have hh := (norm_sub_le_norm_sub_add_norm_sub
    (parisiHessian b μ (q,x)) (parisiHessian b ν (q,x)) (parisiHessian e ν (q,x))).trans
      (add_le_add (hH.trans (mul_le_mul_of_nonneg_right hHc hδ))
        (hT.trans (mul_le_mul_of_nonneg_right hTc (abs_nonneg _))))
  nlinarith [mul_nonneg hH0 (abs_nonneg (b^2-e^2)),mul_nonneg hT0 hδ]

end QuantitativeFollowup
