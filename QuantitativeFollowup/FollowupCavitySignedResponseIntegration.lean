module
public import QuantitativeFollowup.FollowupCavitySignedResponsePairing
public import FourPapersCommon.L2CauchySchwarz

@[expose] public section

/-! The genuine free-measure square-root and two-level minimum integrals
used in the integrated signed response estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem norm_cavitySignedResponseCovarianceMoment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Finset (Fin n)) (q : Paper.Overlap) :
    ‖cavitySignedResponseCovarianceMoment D μ a J q‖ ≤
      anisotropicProcessCovarianceEnergyBound J/(J.card:ℝ)^2 := by
  rw [cavitySignedResponseCovarianceMoment,norm_div,Real.norm_of_nonneg (sq_nonneg _)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa using norm_integral_le_of_norm_le
    (integrable_const (μ := anisotropicMeasureSampleLaw D μ a) (anisotropicProcessCovarianceEnergyBound J))
    (.of_forall (norm_anisotropicProcessCovarianceEnergy_le D μ J q))

def cavitySignedResponseSqrtMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (J : Finset (Fin n)) (q : Paper.Overlap) : ℝ :=
  Real.sqrt (Gamma β0 μ q*cavitySignedResponseCovarianceMoment D μ a J q)

theorem measurable_cavitySignedResponseSqrtMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0) (J : Finset (Fin n)) :
    Measurable (cavitySignedResponseSqrtMoment D μ a β0 J) := by
  exact (((continuousOn_Gamma β0 hβ0 μ).comp_continuous continuous_subtype_val
    (fun q => q.property)).measurable.mul
      (measurable_cavitySignedResponseCovarianceMoment D μ a J)).sqrt

theorem norm_cavitySignedResponseSqrtMoment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (J : Finset (Fin n)) (q : Paper.Overlap) :
    ‖cavitySignedResponseSqrtMoment D μ a β0 J q‖ ≤
      Real.sqrt (anisotropicProcessCovarianceEnergyBound J/(J.card:ℝ)^2) := by
  rw [cavitySignedResponseSqrtMoment,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  have hj := norm_cavitySignedResponseCovarianceMoment_le D μ a J q
  rw [Real.norm_of_nonneg (cavitySignedResponseCovarianceMoment_nonneg D μ a J q)] at hj
  exact (mul_le_mul_of_nonneg_right (scalarGamma_le_one β0 μ q q.property)
    (cavitySignedResponseCovarianceMoment_nonneg D μ a J q)).trans (by simpa using hj)

theorem cavitySignedResponse_sqrt_free_integral_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hβ0 : β0 ≠ 0) (J : Finset (Fin n)) :
    (∫q,cavitySignedResponseSqrtMoment D μ a β0 J q ∂parisiFreeMeasure μ a) ≤
      Real.sqrt (cavitySignedResponseWeightedJ D μ a β0 J) := by
  let ν := parisiFreeMeasure μ a
  let f := cavitySignedResponseSqrtMoment D μ a β0 J
  have hf : MemLp f 2 ν := MemLp.of_bound
    (measurable_cavitySignedResponseSqrtMoment D μ a β0 hβ0 J).aestronglyMeasurable
    _ (.of_forall (norm_cavitySignedResponseSqrtMoment_le D μ a β0 J))
  have h1 : MemLp (fun _ : Paper.Overlap => (1:ℝ)) 2 ν := memLp_const _
  have hf2 : (∫q,(f q)^2 ∂ν) = cavitySignedResponseWeightedJ D μ a β0 J := by
    apply integral_congr_ae
    exact .of_forall fun q => Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ q)
      (cavitySignedResponseCovarianceMoment_nonneg D μ a J q))
  have hmass : (∫_q : Paper.Overlap,(1:ℝ)^2 ∂ν) ≤ 1 := by
    simp only [one_pow,integral_const,Measure.real,parisiFreeMeasure_univ,ν,
      ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2),smul_eq_mul,mul_one]
    linarith [ha.1]
  have h := integral_mul_abs_le_sqrt_moment_bounds f (fun _ => (1:ℝ)) hf h1
    (cavitySignedResponseWeightedJ D μ a β0 J) 1 hf2.le hmass
  have hf0 : 0 ≤ (∫q,f q ∂ν) := integral_nonneg fun q => Real.sqrt_nonneg _
  simpa only [mul_one,abs_of_nonneg hf0] using h

theorem cavitySignedResponse_minimum_free_integral_le (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (χ : Paper.Overlap → ℝ)
    (hχ : Measurable χ) (C : ℝ) (hC : 0 ≤ C)
    (hχ0 : ∀q,0 ≤ χ q) (hb : ∀q,‖χ q‖ ≤ C) :
    (∫r,∫l,χ (min r l) ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a) ≤
      2*(∫r,χ r ∂parisiFreeMeasure μ a) := by
  let ν := parisiFreeMeasure μ a
  have hν : ν.real Set.univ = 1-a := by
    simp only [ν,Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
  have hν0 : 0 ≤ ν.real Set.univ := ENNReal.toReal_nonneg
  have hν1 : ν.real Set.univ ≤ 1 := by rw [hν]; linarith [ha.1]
  have hχi : Integrable χ ν := (integrable_const C).mono' hχ.aestronglyMeasurable (.of_forall hb)
  have hmini (r : Paper.Overlap) : Integrable (fun l => χ (min r l)) ν :=
    (integrable_const C).mono' (hχ.comp (measurable_const.min measurable_id)).aestronglyMeasurable
      (.of_forall fun l => hb _)
  have hmin (r : Paper.Overlap) : (∫l,χ (min r l) ∂ν) ≤
      ν.real Set.univ*χ r+(∫l,χ l ∂ν) := by
    have h := integral_mono (hmini r) ((integrable_const (χ r)).add hχi) (fun l => by
      rcases le_total r l with hrl | hlr
      · rw [min_eq_left hrl]; exact le_add_of_nonneg_right (hχ0 l)
      · rw [min_eq_right hlr]; exact le_add_of_nonneg_left (hχ0 r))
    change (∫l,χ (min r l) ∂ν) ≤ (∫l,χ r+χ l ∂ν) at h
    rw [integral_add (integrable_const (χ r)) hχi,integral_const,smul_eq_mul] at h
    exact h
  have hlefti : Integrable (fun r => ∫l,χ (min r l) ∂ν) ν := by
    apply (integrable_const (ν.real Set.univ*C)).mono'
    · exact ((hχ.comp (measurable_fst.min measurable_snd)).stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    · exact .of_forall fun r => by
        simpa only [integral_const,smul_eq_mul] using norm_integral_le_of_norm_le
          (integrable_const C : Integrable _ ν) (.of_forall fun l => hb (min r l))
  have hrighti : Integrable (fun r => ν.real Set.univ*χ r+(∫l,χ l ∂ν)) ν :=
    (hχi.const_mul _).add (integrable_const _)
  have h := integral_mono hlefti hrighti hmin
  rw [integral_add (hχi.const_mul _) (integrable_const _),integral_const_mul,integral_const,
    smul_eq_mul] at h
  have hχint : 0 ≤ (∫r,χ r ∂ν) := integral_nonneg hχ0
  exact h.trans (by nlinarith)

end QuantitativeFollowup
