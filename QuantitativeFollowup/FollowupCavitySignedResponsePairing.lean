module
public import QuantitativeFollowup.AnisotropicVarianceLiteral
public import QuantitativeFollowup.ScalarKernelBounds

@[expose] public section

/-! The signed Cauchy--Schwarz input for the native cavity response.
The self-overlap and covariance energy are actual full-profile anisotropic
observables. Their variance estimate is derived from the proved posterior
law, including arbitrary signed kernels. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128

def cavitySignedResponseCovarianceMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n)) (q : Paper.Overlap) : ℝ :=
  (∫sample, anisotropicProcessCovarianceEnergy D μ J q sample
    ∂anisotropicMeasureSampleLaw D μ a)/(J.card:ℝ)^2

def cavitySignedResponseWeightedJ (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (J : Finset (Fin n)) : ℝ :=
  ∫q : Paper.Overlap, Gamma β0 μ q*cavitySignedResponseCovarianceMoment D μ a J q
    ∂parisiFreeMeasure μ a

theorem cavitySignedResponseCovarianceMoment_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n)) (q : Paper.Overlap) :
    0 ≤ cavitySignedResponseCovarianceMoment D μ a J q := by
  apply div_nonneg _ (sq_nonneg _)
  apply integral_nonneg
  intro sample
  exact (anisotropicTailCovarianceQuadratic_bounds D μ q _ _).1

theorem measurable_cavitySignedResponseCovarianceMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n)) :
    Measurable (cavitySignedResponseCovarianceMoment D μ a J) := by
  exact ((measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J).stronglyMeasurable.integral_prod_right'
    (ν := anisotropicMeasureSampleLaw D μ a)).measurable.div_const _

private theorem covariance_moment_numerator_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n)) (q : Paper.Overlap) :
    ‖∫sample, anisotropicProcessCovarianceEnergy D μ J q sample
      ∂anisotropicMeasureSampleLaw D μ a‖ ≤ anisotropicProcessCovarianceEnergyBound J := by
  simpa using norm_integral_le_of_norm_le
    (integrable_const (μ := anisotropicMeasureSampleLaw D μ a) (anisotropicProcessCovarianceEnergyBound J))
    (.of_forall (norm_anisotropicProcessCovarianceEnergy_le D μ J q))

theorem cavitySignedResponseWeightedJ_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (J : Finset (Fin n)) :
    0 ≤ cavitySignedResponseWeightedJ D μ a β0 J :=
  integral_nonneg fun q => mul_nonneg (scalarGamma_nonneg β0 μ q)
    (cavitySignedResponseCovarianceMoment_nonneg D μ a J q)

theorem cavitySignedResponse_weighted_variance (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0)
    (ha : a ∈ Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (J : Finset (Fin n)) (hJ : J.Nonempty) (r : Paper.Overlap)
    (ψ : Paper.Overlap → ℝ) (hψ : Measurable ψ)
    (hb : ∀q, (ψ q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q) :
    variance (anisotropicWeightedSelfOverlap D μ a ψ J) (anisotropicMeasureSampleLaw D μ a) ≤
      4*Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J := by
  let E := fun q : Paper.Overlap => ∫sample, anisotropicProcessCovarianceEnergy D μ J q sample
    ∂anisotropicMeasureSampleLaw D μ a
  let B := anisotropicProcessCovarianceEnergyBound J
  have hEm : Measurable E :=
    ((measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J).stronglyMeasurable.integral_prod_right'
      (ν := anisotropicMeasureSampleLaw D μ a)).measurable
  have hEn (q : Paper.Overlap) : 0 ≤ E q := integral_nonneg fun sample =>
    (anisotropicTailCovarianceQuadratic_bounds D μ q _ _).1
  have hEb (q : Paper.Overlap) : ‖E q‖ ≤ B := covariance_moment_numerator_bound D μ a J q
  have hΓm : Measurable (fun q : Paper.Overlap => Gamma β0 μ q) :=
    ((continuousOn_Gamma β0 hβ0 μ).comp_continuous continuous_subtype_val
      (fun q => q.property)).measurable
  have hψb (q : Paper.Overlap) : |ψ q| ≤ 1 := by
    have hh := hb q
    have hr1 := scalarGamma_le_one β0 μ r r.property
    have hq1 := scalarGamma_le_one β0 μ q q.property
    have hprod : Gamma β0 μ r*Gamma β0 μ q ≤ 1 :=
      (mul_le_mul hr1 hq1 (scalarGamma_nonneg β0 μ q) zero_le_one).trans_eq (one_mul _)
    have hs : (ψ q)^2 ≤ 1 := hh.trans hprod
    nlinarith [sq_abs (ψ q), abs_nonneg (ψ q)]
  have hL : MemLp ψ 2 (parisiFreeMeasure μ a) :=
    MemLp.of_bound hψ.aestronglyMeasurable 1 (.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using hψb q)
  have hi0 : Integrable (fun q => (ψ q)^2*E q) (parisiFreeMeasure μ a) := by
    apply (integrable_const B).mono' ((hψ.pow_const 2).mul hEm).aestronglyMeasurable
    exact .of_forall fun q => by
      change ‖(ψ q)^2*E q‖ ≤ B
      rw [norm_mul, norm_pow, Real.norm_eq_abs, sq_abs]
      have hs : (ψ q)^2 ≤ 1 := by
        simpa only [sq_abs] using pow_le_one₀ (n := 2) (abs_nonneg (ψ q)) (hψb q)
      exact (mul_le_mul hs
        (hEb q) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hi1 : Integrable (fun q : Paper.Overlap => Gamma β0 μ q*E q) (parisiFreeMeasure μ a) := by
    apply (integrable_const B).mono' (hΓm.mul hEm).aestronglyMeasurable
    exact .of_forall fun q => by
      change ‖Gamma β0 μ q*E q‖ ≤ B
      rw [norm_mul, Real.norm_of_nonneg (scalarGamma_nonneg β0 μ q)]
      exact (mul_le_mul (scalarGamma_le_one β0 μ q q.property)
        (hEb q) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hmono := integral_mono hi0 (hi1.const_mul (Gamma β0 μ r)) (fun q => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb q) (hEn q))
  have hv := anisotropic_weighted_selfOverlap_variance_literal D μ a ha hμ ψ hL J hJ
  apply (hv.1.trans hv.2).trans
  rw [integral_const_mul] at hmono
  have hm := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 4/(J.card:ℝ)^2)
  calc
    _ ≤ (4/(J.card:ℝ)^2)*(Gamma β0 μ r*∫q, Gamma β0 μ q*E q ∂parisiFreeMeasure μ a) := hm
    _ = _ := by
      simp only [cavitySignedResponseWeightedJ, cavitySignedResponseCovarianceMoment]
      simp_rw [← mul_div_assoc]
      rw [integral_div]
      dsimp only [E]
      ring

theorem cavitySignedResponse_centered_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0)
    (ha : a ∈ Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (J : Finset (Fin n)) (hJ : J.Nonempty) (r : Paper.Overlap)
    (ψ : Paper.Overlap → ℝ) (hψ : Measurable ψ)
    (hb : ∀q, (ψ q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q)
    (ξ : AnisotropicDisorderBrownianSample n → ℝ)
    (hξ : MemLp ξ 2 (anisotropicMeasureSampleLaw D μ a))
    (hzero : (∫sample, ξ sample ∂anisotropicMeasureSampleLaw D μ a) = 0) :
    |∫sample, ξ sample*anisotropicWeightedSelfOverlap D μ a ψ J sample
      ∂anisotropicMeasureSampleLaw D μ a| ≤
      2*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J*
        (∫sample, (ξ sample)^2 ∂anisotropicMeasureSampleLaw D μ a)) := by
  let P := anisotropicMeasureSampleLaw D μ a
  let F := anisotropicWeightedSelfOverlap D μ a ψ J
  have hψb (q : Paper.Overlap) : |ψ q| ≤ 1 := by
    have hprod : Gamma β0 μ r*Gamma β0 μ q ≤ 1 :=
      (mul_le_mul (scalarGamma_le_one β0 μ r r.property) (scalarGamma_le_one β0 μ q q.property)
        (scalarGamma_nonneg β0 μ q) zero_le_one).trans_eq (one_mul _)
    have hs := (hb q).trans hprod
    nlinarith [sq_abs (ψ q), abs_nonneg (ψ q)]
  have hF : MemLp F 2 P := MemLp.of_bound
    (measurable_anisotropicWeightedSelfOverlap D μ a ψ hψ J).aestronglyMeasurable 1
    (.of_forall fun sample => norm_anisotropicWeightedSelfOverlap_le D μ a ha ψ J 1
      zero_le_one hψb sample)
  let Fc := fun sample => F sample-(∫sample, F sample ∂P)
  have hFc : MemLp Fc 2 P := hF.sub (memLp_const _)
  have hvar : (∫sample, (Fc sample)^2 ∂P) ≤
      4*Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J := by
    rw [← variance_eq_integral hF.aemeasurable]
    exact cavitySignedResponse_weighted_variance D μ a β0 hβ0 ha hμ J hJ r ψ hψ hb
  have hh := integral_mul_abs_le_sqrt_moment_bounds ξ Fc hξ hFc
    (∫sample, (ξ sample)^2 ∂P) _ le_rfl hvar
  have heq : (∫sample, ξ sample*Fc sample ∂P) = ∫sample, ξ sample*F sample ∂P := by
    simp only [Fc, mul_sub]
    rw [integral_sub (f := fun sample => ξ sample*F sample)
      (g := fun sample => ξ sample*(∫sample, F sample ∂P))
      (hξ.integrable_mul hF) ((hξ.integrable (by norm_num)).mul_const _), integral_mul_const]
    change _-(∫sample, ξ sample ∂anisotropicMeasureSampleLaw D μ a)*_ = _
    rw [hzero, zero_mul, sub_zero]
  rw [heq] at hh
  have he : (∫sample, (ξ sample)^2 ∂P)*(4*Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J) =
      4*(Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J*(∫sample, (ξ sample)^2 ∂P)) := by ring
  rw [he, Real.sqrt_mul (by norm_num)] at hh
  norm_num at hh
  exact hh

end QuantitativeFollowup
