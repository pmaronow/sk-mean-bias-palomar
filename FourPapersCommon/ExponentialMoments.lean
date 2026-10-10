module
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.Variance

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Genuine first and second moments of the canonical exponential law.
The proof uses the actual Gamma densities and their checked normalizers. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem integrable_gammaPDFReal_all (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    Integrable (gammaPDFReal a r) := by
  refine ⟨(measurable_gammaPDFReal a r).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp_rw [Real.norm_eq_abs,abs_of_nonneg (gammaPDFReal_nonneg ha hr _)]
  change (∫⁻x,gammaPDF a r x) < ⊤
  rw [lintegral_gammaPDF_eq_one ha hr]
  norm_num

theorem integral_gammaPDFReal_all (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (∫x,gammaPDFReal a r x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (.of_forall fun x=>gammaPDFReal_nonneg ha hr x)
    (measurable_gammaPDFReal a r).aestronglyMeasurable]
  change (∫⁻x,gammaPDF a r x).toReal = 1
  rw [lintegral_gammaPDF_eq_one ha hr]
  norm_num

theorem exponentialPDFReal_mul_id (r : ℝ) (hr : 0 < r) (x : ℝ) :
    exponentialPDFReal r x*x = r⁻¹*gammaPDFReal 2 r x := by
  have hg : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  by_cases hx : 0 ≤ x
  · unfold exponentialPDFReal gammaPDFReal
    simp only [if_pos hx]
    norm_num [hg,Real.rpow_natCast]
    field_simp [hr.ne']
  · simp [exponentialPDFReal,gammaPDFReal,hx]

theorem exponentialPDFReal_mul_sq (r : ℝ) (hr : 0 < r) (x : ℝ) :
    exponentialPDFReal r x*x^2 = (2/r^2)*gammaPDFReal 3 r x := by
  have hg : Real.Gamma 3 = 2 := by
    simpa using Real.Gamma_nat_eq_factorial 2
  by_cases hx : 0 ≤ x
  · unfold exponentialPDFReal gammaPDFReal
    simp only [if_pos hx]
    norm_num [hg,Real.rpow_natCast]
    field_simp [hr.ne']
  · simp [exponentialPDFReal,gammaPDFReal,hx]

theorem integral_expMeasure_density (r : ℝ) (hr : 0 < r) (f : ℝ→ℝ) :
    (∫x,f x ∂expMeasure r) = ∫x,exponentialPDFReal r x*f x := by
  rw [expMeasure,gammaMeasure]
  unfold gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal 1 r).ennreal_ofReal (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [gammaPDF,ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _),
    exponentialPDFReal,smul_eq_mul]

theorem integrable_id_expMeasure (r : ℝ) (hr : 0 < r) :
    Integrable (id : ℝ→ℝ) (expMeasure r) := by
  rw [expMeasure,gammaMeasure]
  unfold gammaPDF
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gammaPDFReal 1 r).ennreal_ofReal (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [gammaPDF,ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _),smul_eq_mul,id_eq]
  change Integrable (fun x=>exponentialPDFReal r x*x)
  simp_rw [exponentialPDFReal_mul_id r hr]
  exact (integrable_gammaPDFReal_all 2 r (by norm_num) hr).const_mul _

theorem integrable_sq_expMeasure (r : ℝ) (hr : 0 < r) :
    Integrable (fun x : ℝ=>x^2) (expMeasure r) := by
  rw [expMeasure,gammaMeasure]
  unfold gammaPDF
  rw [integrable_withDensity_iff_integrable_smul'
    (measurable_gammaPDFReal 1 r).ennreal_ofReal (.of_forall fun _=>ENNReal.ofReal_lt_top)]
  simp only [gammaPDF,ENNReal.toReal_ofReal (gammaPDFReal_nonneg zero_lt_one hr _),smul_eq_mul]
  change Integrable (fun x=>exponentialPDFReal r x*x^2)
  simp_rw [exponentialPDFReal_mul_sq r hr]
  exact (integrable_gammaPDFReal_all 3 r (by norm_num) hr).const_mul _

theorem memLp_two_id_expMeasure (r : ℝ) (hr : 0 < r) :
    MemLp (id : ℝ→ℝ) 2 (expMeasure r) := by
  apply (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
  exact integrable_sq_expMeasure r hr

theorem integral_id_expMeasure (r : ℝ) (hr : 0 < r) :
    (∫x : ℝ,x ∂expMeasure r) = r⁻¹ := by
  rw [integral_expMeasure_density r hr]
  simp_rw [exponentialPDFReal_mul_id r hr]
  rw [integral_const_mul,integral_gammaPDFReal_all 2 r (by norm_num) hr,mul_one]

theorem integral_sq_expMeasure (r : ℝ) (hr : 0 < r) :
    (∫x : ℝ,x^2 ∂expMeasure r) = 2/r^2 := by
  rw [integral_expMeasure_density r hr]
  simp_rw [exponentialPDFReal_mul_sq r hr]
  rw [integral_const_mul,integral_gammaPDFReal_all 3 r (by norm_num) hr,mul_one]

theorem variance_id_expMeasure (r : ℝ) (hr : 0 < r) :
    variance (id : ℝ→ℝ) (expMeasure r) = r⁻¹^2 := by
  let _ := isProbabilityMeasure_expMeasure hr
  rw [variance_eq_sub (memLp_two_id_expMeasure r hr)]
  change (∫x : ℝ,x^2 ∂expMeasure r)-(∫x : ℝ,x ∂expMeasure r)^2 = _
  rw [integral_sq_expMeasure r hr,integral_id_expMeasure r hr]
  field_simp [hr.ne']
  ring

end FourPapersCommon
