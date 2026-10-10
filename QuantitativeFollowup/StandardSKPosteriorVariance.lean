module
public import QuantitativeFollowup.StandardSKEnergyBudget

@[expose] public section

/-! Both printed signed L²/subset variance estimates under the actual SK law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem standardSK_selfOverlap_variance (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (standardSKWeightedSelfOverlap μ β t a ht.le κ J) (vectorMeasureDisorderTilt μ β t a) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
        ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a) ∧
    ((4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a)) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample
        ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a) := by
  let D:=standardSKAnisotropicModel n β t hβ ht
  have hmap:=standardSKAnisotropicSampleLaw hn μ β t a hβ ht
  have hscore:=measurable_standardSKWeightedSelfOverlap_L2 μ β t a ht.le κ hL J
  have hvar : variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a)=
      variance (standardSKWeightedSelfOverlap μ β t a ht.le κ J) (vectorMeasureDisorderTilt μ β t a) := by
    rw [←hmap,variance_map hscore.aemeasurable measurable_standardSKSampleCompression.aemeasurable]
    congr 1
    funext sample
    exact standardSKAnisotropicWeightedSelfOverlap μ β t a hβ ht κ J sample
  have hH (q : Paper.Overlap) : (∫sample,anisotropicProcessHessianEnergy D μ J q sample
      ∂anisotropicMeasureSampleLaw D μ a)=
      ∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample ∂vectorMeasureDisorderTilt μ β t a := by
    have hm := (measurable_standardSKSelectedHessianEnergy_joint μ β t ht.le J).comp
      ((measurable_const (a:=q)).prodMk measurable_id)
    have he := integral_map measurable_standardSKSampleCompression.aemeasurable hm.aestronglyMeasurable
      (μ:=anisotropicMeasureSampleLaw D μ a)
    rw [hmap] at he
    calc
      _ = ∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q
          (standardSKSampleCompression sample) ∂anisotropicMeasureSampleLaw D μ a :=
        integral_congr_ae (.of_forall fun sample =>
          standardSKAnisotropicHessianEnergy μ β t hβ ht J q sample)
      _ = _ := he.symm
  constructor
  · have hv := (anisotropic_weighted_selfOverlap_variance_literal D μ a ha hμ κ hL J hJ).1
    rw [hvar] at hv
    simp_rw [hH] at hv
    exact hv
  · have hpoint (q : Paper.Overlap) :
        (∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample ∂vectorMeasureDisorderTilt μ β t a) ≤
          ∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample ∂vectorMeasureDisorderTilt μ β t a := by
      apply integral_mono_ae (integrable_standardSKSelectedHessianEnergy μ β t a ht.le J q)
        (integrable_standardSKSelectedCovarianceEnergy μ β t a ht.le J q)
      filter_upwards [vectorMeasureHessian_covariance_all_directions μ β t a hβ ht q] with sample hs
      simpa only [standardSKSelectedHessianEnergy,standardSKSelectedCovarianceEnergy,
        vectorMeasureHessianQuadratic,vectorMeasureHessianProcess,real_inner_comm] using
        (hs (standardSKSelectedMean μ β t ht.le J q sample)).2
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    obtain ⟨hHi,hCi⟩:=integrable_standardSKWeightedEnergyBudgets μ β t a hβ ht J κ hL
    apply integral_mono_ae hHi hCi
    exact .of_forall fun q=>mul_le_mul_of_nonneg_left (hpoint q) (sq_nonneg _)

theorem standardSK_marked_selfOverlap_variance (hn : 0<n) (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (fun p : VectorDisorderBrownianSample n×Configuration n=>standardSKWeightedSelfOverlap μ β t a ht.le κ J p.1)
      (vectorMeasureSpinPathLaw μ β t a ht.le) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
        ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a) ∧
    ((4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedHessianEnergy μ β t ht.le J q sample
      ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a)) ≤
      (4/(J.card:ℝ)^2)*(∫q,(κ q)^2*(∫sample,standardSKSelectedCovarianceEnergy μ β t a ht.le J q sample
        ∂vectorMeasureDisorderTilt μ β t a) ∂parisiFreeMeasure μ a) := by
  rw [(measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).variance_fun_comp
    (measurable_standardSKWeightedSelfOverlap_L2 μ β t a ht.le κ hL J).aemeasurable]
  exact standardSK_selfOverlap_variance hn μ β t a hβ ht ha hμ κ hL J hJ

end QuantitativeFollowup
