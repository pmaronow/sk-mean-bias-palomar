module
public import QuantitativePaper.VectorMeasureState
public import Paper.ParisiCDFIntegral

@[expose] public section

/-! The actual measurable Parisi drift has an L¹ time perturbation envelope.
CDF jumps are retained; only the gradient difference is uniformly bounded. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace QuantitativePaper
variable {n : ℕ}

theorem norm_vectorMeasureDrift_sub_le (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (D : ℝ) (hD : 0≤D)
    (hgrad : ∀ q p x,‖vectorMeasureGradient (n := n) μ β t q p x-
      vectorMeasureGradient ν β t q p x‖≤D)
    (r : ℝ≥0) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorMeasureDrift μ β t ht r p x-vectorMeasureDrift ν β t ht r p x‖≤
      ((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ r-Paper.parisiCDF ν r|+D) := by
  let c:ℝ:=(1-t)*β^2
  let a:ℝ:=Paper.parisiCDF μ r
  let b:ℝ:=Paper.parisiCDF ν r
  let v:Field n:=vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) p x
  let w:Field n:=vectorMeasureGradient ν β t (projIcc (0 : ℝ) 1 zero_le_one r) p x
  have hc : 0≤c := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have hb : 0≤b := Paper.parisiCDF_nonneg ν r
  have hb1 : b≤1 := Paper.parisiCDF_le_one ν r
  have hv : ‖v‖≤Real.sqrt n := norm_vectorMeasureGradient_le μ β t ht _ p x
  have hvw : ‖v-w‖≤D := hgrad _ p x
  change ‖(c*a) • v-(c*b) • w‖≤c*(Real.sqrt n*|a-b|+D)
  have he : (c*a) • v-(c*b) • w=(c*(a-b)) • v+(c*b) • (v-w) := by
    rw [smul_sub,mul_sub,sub_smul]
    abel
  rw [he]
  calc
    _≤‖(c*(a-b)) • v‖+‖(c*b) • (v-w)‖ := norm_add_le _ _
    _=c*|a-b| *‖v‖+(c*b)*‖v-w‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hc,
        Real.norm_of_nonneg (mul_nonneg hc hb)]
    _≤c*|a-b| *Real.sqrt n+(c*b)*D := add_le_add
      (mul_le_mul_of_nonneg_left hv (mul_nonneg hc (abs_nonneg _)))
      (mul_le_mul_of_nonneg_left hvw (mul_nonneg hc hb))
    _≤c*(Real.sqrt n*|a-b|+D) := by
      have hcb : c*b≤c := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hcb hD]

theorem vectorMeasureDrift_envelope_integral (μ ν : Paper.ParisiMeasure) (β t D : ℝ) :
    (∫r in (0 : ℝ)..1,((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ r-Paper.parisiCDF ν r|+D))=
      ((1-t)*β^2)*(Real.sqrt n*Paper.parisiCDFDistance μ ν+D) := by
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add
    ((Paper.parisiCDF_abs_diff_intervalIntegrable μ ν 0 1).const_mul (Real.sqrt n))
      intervalIntegrable_const,intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const,sub_zero,one_smul,Paper.parisiCDFDistance]

end QuantitativePaper
