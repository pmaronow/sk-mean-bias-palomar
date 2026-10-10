module
public import QuantitativeFollowup.AnisotropicProcessCovarianceEnergy
public import QuantitativeFollowup.AnisotropicVarianceL2Representative

@[expose] public section

/-! Both averaged selected-self-overlap variance inequalities under the
actual full-profile anisotropic law, for every signed L² free-measure kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

def anisotropicWeightedProcessCovarianceEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (J : Finset (Fin n))
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  (∫q,(κ q)^2*anisotropicProcessCovarianceEnergy D μ J q sample ∂parisiFreeMeasure μ a)/((J.card:ℝ)/2)^2

theorem measurable_anisotropicWeightedProcessCovarianceEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (J : Finset (Fin n)) : Measurable (anisotropicWeightedProcessCovarianceEnergy D μ a κ J) := by
  have hm := ((hκ.comp measurable_fst).pow_const 2).mul
    (measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J)
  exact (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ a)).measurable.div_const _

theorem anisotropicWeightedProcessCovarianceEnergy_kernel_congr (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ η : Paper.Overlap→ℝ) (J : Finset (Fin n))
    (h : κ=ᵐ[parisiFreeMeasure μ a]η) :
    anisotropicWeightedProcessCovarianceEnergy D μ a κ J=anisotropicWeightedProcessCovarianceEnergy D μ a η J := by
  funext sample
  unfold anisotropicWeightedProcessCovarianceEnergy
  congr 1
  apply integral_congr_ae
  exact h.mono fun q hq=>by dsimp only;rw [hq]

private theorem integrable_weighted_process_energy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (E : Paper.Overlap→AnisotropicDisorderBrownianSample n→ℝ)
    (hE : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>E z.1 z.2))
    (C : ℝ) (hb : ∀q sample,‖E q sample‖ ≤ C) (sample : AnisotropicDisorderBrownianSample n) :
    Integrable (fun q=>(κ q)^2*E q sample) (parisiFreeMeasure μ a) := by
  have hm := hE.comp (measurable_id.prodMk (measurable_const (a:=sample)))
  apply (hL.integrable_sq.mul_const C).mono' ((hκ.pow_const 2).mul hm).aestronglyMeasurable
  exact .of_forall fun q=>by
    change ‖(κ q)^2*E q sample‖ ≤ (κ q)^2*C
    rw [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul_of_nonneg_left (hb q sample) (sq_nonneg _)

private theorem integrable_outer_weighted_process_energy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (E : Paper.Overlap→AnisotropicDisorderBrownianSample n→ℝ)
    (hE : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>E z.1 z.2))
    (C : ℝ) (hb : ∀q sample,‖E q sample‖ ≤ C) (J : Finset (Fin n)) :
    Integrable (fun sample=>(∫q,(κ q)^2*E q sample ∂parisiFreeMeasure μ a)/((J.card:ℝ)/2)^2)
      (anisotropicMeasureSampleLaw D μ a) := by
  have hm := ((hκ.comp measurable_fst).pow_const 2).mul hE
  have hi := (hm.stronglyMeasurable.integral_prod_left' (μ:=parisiFreeMeasure μ a)).measurable.div_const
    (((J.card:ℝ)/2)^2)
  apply (integrable_const ((∫q,(κ q)^2 ∂parisiFreeMeasure μ a)*C/((J.card:ℝ)/2)^2)).mono'
    hi.aestronglyMeasurable
  exact .of_forall fun sample=>by
    rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    change ‖∫q,(κ q)^2*E q sample ∂parisiFreeMeasure μ a‖ ≤ _
    have h := norm_integral_le_of_norm_le (f:=fun q=>(κ q)^2*E q sample)
      (hL.integrable_sq.mul_const C) (.of_forall fun q=>by
      rw [norm_mul,norm_pow,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_left (hb q sample) (sq_nonneg (κ q)))
    simpa only [integral_mul_const] using h

theorem anisotropicWeightedProcessHessianEnergy_le_covariance_L2 (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ)
    (hL : MemLp κ 2 (parisiFreeMeasure μ a)) (J : Finset (Fin n)) :
    (∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a) ≤
      ∫sample,anisotropicWeightedProcessCovarianceEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a := by
  have hiH := integrable_outer_weighted_process_energy D μ a κ hκ hL
    (anisotropicProcessHessianEnergy D μ J) (measurable_uncurry_anisotropicProcessHessianEnergy D μ J)
    (anisotropicProcessEnergyBound D J) (norm_anisotropicProcessHessianEnergy_le D μ J) J
  have hiC := integrable_outer_weighted_process_energy D μ a κ hκ hL
    (anisotropicProcessCovarianceEnergy D μ J) (measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J)
    (anisotropicProcessCovarianceEnergyBound J) (norm_anisotropicProcessCovarianceEnergy_le D μ J) J
  apply integral_mono hiH hiC
  intro sample
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have hH := integrable_weighted_process_energy D μ a κ hκ hL
    (anisotropicProcessHessianEnergy D μ J) (measurable_uncurry_anisotropicProcessHessianEnergy D μ J)
    (anisotropicProcessEnergyBound D J) (norm_anisotropicProcessHessianEnergy_le D μ J) sample
  have hC := integrable_weighted_process_energy D μ a κ hκ hL
    (anisotropicProcessCovarianceEnergy D μ J) (measurable_uncurry_anisotropicProcessCovarianceEnergy D μ J)
    (anisotropicProcessCovarianceEnergyBound J) (norm_anisotropicProcessCovarianceEnergy_le D μ J) sample
  apply integral_mono hH hC
  intro q
  exact mul_le_mul_of_nonneg_left (anisotropicProcessHessianEnergy_le_covariance D μ J q sample)
    (sq_nonneg (κ q))

theorem anisotropic_weighted_selfOverlap_variance_bounds_signedL2 (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a) ≤
      ∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a ∧
    (∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a) ≤
      ∫sample,anisotropicWeightedProcessCovarianceEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a := by
  constructor
  · exact anisotropic_weighted_selfOverlap_variance_signedL2 D μ a ha hμ κ hL J hJ
  · let η:=hL.aestronglyMeasurable.mk κ
    have hm : Measurable η:=hL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have he : κ=ᵐ[parisiFreeMeasure μ a]η:=hL.aestronglyMeasurable.ae_eq_mk
    have hη : MemLp η 2 (parisiFreeMeasure μ a):=(memLp_congr_ae he).mp hL
    rw [anisotropicWeightedProcessHessianEnergy_kernel_congr D μ a κ η J he,
      anisotropicWeightedProcessCovarianceEnergy_kernel_congr D μ a κ η J he]
    exact anisotropicWeightedProcessHessianEnergy_le_covariance_L2 D μ a η hm hη J

end QuantitativeFollowup
