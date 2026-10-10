module
public import QuantitativePaper.VectorMeasureDriftStability
public import QuantitativePaper.VectorFiniteState

@[expose] public section

/-! Actual L1 drift comparison between the genuine arbitrary-profile model
and a literal finite-profile model. Only a bounded spatial gradient error
is needed; no identification of their selected definitions is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace QuantitativePaper
variable {n k : ℕ}

theorem norm_vectorMeasureFiniteDrift_sub_le (μ : Paper.ParisiMeasure) (s : SpinGlass.Targets.RSBScheme k) (β t : ℝ) (ht : t≤1)
    (D : ℝ) (hD : 0≤D)
    (hgrad : ∀ q p x,‖vectorMeasureGradient (n := n) μ β t q p x-
      vectorFiniteTailGradient s β t q p x‖≤D)
    (r : ℝ≥0) (p : Couplings n×ℝ) (x : Field n) :
    ‖vectorMeasureDrift μ β t ht r p x-vectorFiniteDrift s β t r p x‖≤
      ((1-t)*β^2)*(Real.sqrt n*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|+D) := by
  let c:ℝ:=(1-t)*β^2
  let a:ℝ:=Paper.parisiCDF μ r
  let b:ℝ:=Paper.parisiCDF (Paper.parisiSchemeMeasure s) r
  let v:Field n:=vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) p x
  let w:Field n:=vectorFiniteTailGradient s β t (projIcc (0 : ℝ) 1 zero_le_one r) p x
  have hc : 0≤c := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have hb : 0≤b := Paper.parisiCDF_nonneg (Paper.parisiSchemeMeasure s) r
  have hb1 : b≤1 := Paper.parisiCDF_le_one (Paper.parisiSchemeMeasure s) r
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


end QuantitativePaper
