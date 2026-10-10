module
public import FourPapersCommon.GaussianTwoMaskScale

@[expose] public section

/-! Genuine uniform bounds on both Gaussian clocks and their derivatives
on a positive root/path variance cylinder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 1600000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_gaussianTwoMaskScale_le (pR pP : ι→Bool) (d alpha q u v : ℝ)
    (hqu : q≤u) (hbv : d-alpha*q≤v) (z : EuclideanSpace ℝ ι) :
    ‖gaussianTwoMaskScale pR pP d alpha q z‖≤
      (Fintype.card ι:ℝ)*(1+Real.sqrt u+Real.sqrt v)*‖z‖ := by
  rw [gaussianTwoMaskScale_apply]
  calc
    _≤∑i,‖(gaussianTwoMaskCoefficient pR pP d alpha q i*z i)•EuclideanSpace.basisFun ι ℝ i‖:=
      norm_sum_le _ _
    _≤∑_i:ι,(1+Real.sqrt u+Real.sqrt v)*‖z‖:=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one,Real.norm_eq_abs,abs_mul]
      have hc : |gaussianTwoMaskCoefficient pR pP d alpha q i|≤1+Real.sqrt u+Real.sqrt v:=by
        unfold gaussianTwoMaskCoefficient
        split_ifs
        · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          linarith [Real.sqrt_le_sqrt hqu,Real.sqrt_nonneg v]
        · rw [abs_of_nonneg (Real.sqrt_nonneg _)]
          linarith [Real.sqrt_le_sqrt hbv,Real.sqrt_nonneg u]
        · simp only [abs_one]
          linarith [Real.sqrt_nonneg u,Real.sqrt_nonneg v]
      exact mul_le_mul hc (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i)
        (abs_nonneg _) (by positivity)
    _=_:=by simp [mul_assoc]

theorem norm_gaussianTwoMaskScaleDerivative_le (pR pP : ι→Bool) (d alpha q l v : ℝ)
    (ha : 0≤alpha) (hl : 0<l) (hv : 0<v) (hlq : l≤q) (hvb : v≤d-alpha*q)
    (z : EuclideanSpace ℝ ι) :
    ‖gaussianTwoMaskScaleDerivative pR pP d alpha q z‖≤
      (Fintype.card ι:ℝ)*(1/(2*Real.sqrt l)+alpha/(2*Real.sqrt v))*‖z‖ := by
  rw [gaussianTwoMaskScaleDerivative_apply]
  calc
    _≤∑i,‖(gaussianTwoMaskCoefficientDerivative pR pP d alpha q i*z i)•EuclideanSpace.basisFun ι ℝ i‖:=
      norm_sum_le _ _
    _≤∑_i:ι,(1/(2*Real.sqrt l)+alpha/(2*Real.sqrt v))*‖z‖:=by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one,Real.norm_eq_abs,abs_mul]
      have hroot : 1/(2*Real.sqrt q)≤1/(2*Real.sqrt l):=
        one_div_le_one_div_of_le (by positivity) (by gcongr)
      have hpath : alpha/(2*Real.sqrt (d-alpha*q))≤alpha/(2*Real.sqrt v):=by
        exact div_le_div_of_nonneg_left ha (by positivity) (by gcongr)
      have hc : |gaussianTwoMaskCoefficientDerivative pR pP d alpha q i|≤
          1/(2*Real.sqrt l)+alpha/(2*Real.sqrt v):=by
        unfold gaussianTwoMaskCoefficientDerivative
        split_ifs
        · rw [abs_of_nonneg (by positivity)]
          linarith [div_nonneg ha (by positivity : 0≤2*Real.sqrt v)]
        · rw [neg_div,abs_neg,abs_of_nonneg (div_nonneg ha (by positivity))]
          linarith [show 0≤1/(2*Real.sqrt l) by positivity]
        · simp only [abs_zero]
          positivity
      exact mul_le_mul hc (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i)
        (abs_nonneg _) (by positivity)
    _=_:=by simp [mul_assoc]

end FourPapersCommon
