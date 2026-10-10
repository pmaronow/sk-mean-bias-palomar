module
public import QuantitativeFollowup.AnisotropicFiniteWienerRealization
public import QuantitativeFollowup.AnisotropicFiniteHistoryObservables

@[expose] public section

/-! The two selected-coordinate signed variance bounds now hold for the
 actual finite anisotropic diffusion on its genuine tilted disorder/Wiener
 probability space, through proved history-law identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativePaper
open scoped NNReal ENNReal
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
variable {n k : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem anisotropicEuclideanJointLaw_history_map (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) :
    (anisotropicEuclideanJointLaw D s a).map (fun p=>(anisotropicEuclideanJointMap D s p).1)=
      anisotropicFiniteHistoryLaw D s a := by
  change (anisotropicEuclideanJointLaw D s a).map (Prod.fst ∘ anisotropicEuclideanJointMap D s)=_
  rw [←Measure.map_map measurable_fst (measurable_anisotropicEuclideanJointMap D s),
    anisotropicEuclideanJointLaw_map]
  exact Measure.fst_compProd _ _

theorem anisotropicFiniteHistory_weighted_variance_bounds (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1)
    (kernel : ℝ→ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (anisotropicHistoryWeightedSelfOverlap D s a kernel J) (anisotropicFiniteHistoryLaw D s a) ≤
      ∫h,anisotropicHistoryWeightedHessianEnergy D s a kernel J h ∂anisotropicFiniteHistoryLaw D s a ∧
    (∫h,anisotropicHistoryWeightedHessianEnergy D s a kernel J h ∂anisotropicFiniteHistoryLaw D s a) ≤
      ∫h,anisotropicHistoryWeightedCovarianceEnergy D s a kernel J h ∂anisotropicFiniteHistoryLaw D s a := by
  letI : Nonempty (Fin n):=⟨Classical.choose hJ⟩
  have hmap:=anisotropicEuclideanJointLaw_history_map D s a
  have hm : Measurable (fun p => (anisotropicEuclideanJointMap D s p).1) :=
    measurable_fst.comp (measurable_anisotropicEuclideanJointMap D s)
  have hv : variance (anisotropicHistoryWeightedSelfOverlap D s a kernel J) (anisotropicFiniteHistoryLaw D s a)=
      variance (fun p : AnisotropicGaussianSpace n k×Configuration n=>
        anisotropicEuclideanWeightedSelfOverlapScore D s a kernel J p.1) (anisotropicEuclideanJointLaw D s a) := by
    rw [←hmap,variance_map (continuous_anisotropicHistoryWeightedSelfOverlap D s a kernel J).measurable.aemeasurable hm.aemeasurable]
    congr 1
    funext p
    exact anisotropicHistoryWeightedSelfOverlap_chart D s a kernel J p
  have hh : (∫h,anisotropicHistoryWeightedHessianEnergy D s a kernel J h ∂anisotropicFiniteHistoryLaw D s a)=
      ∫p : AnisotropicGaussianSpace n k×Configuration n,anisotropicWeightedHessianEnergy D s a kernel J p.1
        ∂anisotropicEuclideanJointLaw D s a := by
    rw [←hmap,integral_map hm.aemeasurable (continuous_anisotropicHistoryWeightedHessianEnergy D s a kernel J).aestronglyMeasurable]
    simp_rw [anisotropicHistoryWeightedHessianEnergy_chart]
  have hc : (∫h,anisotropicHistoryWeightedCovarianceEnergy D s a kernel J h ∂anisotropicFiniteHistoryLaw D s a)=
      ∫p : AnisotropicGaussianSpace n k×Configuration n,anisotropicWeightedCovarianceEnergy D s a kernel J p.1
        ∂anisotropicEuclideanJointLaw D s a := by
    rw [←hmap,integral_map hm.aemeasurable (continuous_anisotropicHistoryWeightedCovarianceEnergy D s a kernel J).aestronglyMeasurable]
    simp_rw [anisotropicHistoryWeightedCovarianceEnergy_chart]
  rw [hv,hh,hc]
  exact anisotropicJoint_weightedSelfOverlap_variance_bounds D s a hq ha kernel J hJ

theorem anisotropicFiniteWiener_weighted_variance_bounds (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1)
    (kernel : ℝ→ℝ) (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (fun sample=>anisotropicHistoryWeightedSelfOverlap D s a kernel J
      (anisotropicFiniteWienerHistory D s (k+2) sample)) (anisotropicFiniteWienerSampleLaw D s a) ≤
      ∫sample,anisotropicHistoryWeightedHessianEnergy D s a kernel J
        (anisotropicFiniteWienerHistory D s (k+2) sample) ∂anisotropicFiniteWienerSampleLaw D s a ∧
    (∫sample,anisotropicHistoryWeightedHessianEnergy D s a kernel J
      (anisotropicFiniteWienerHistory D s (k+2) sample) ∂anisotropicFiniteWienerSampleLaw D s a) ≤
      ∫sample,anisotropicHistoryWeightedCovarianceEnergy D s a kernel J
        (anisotropicFiniteWienerHistory D s (k+2) sample) ∂anisotropicFiniteWienerSampleLaw D s a := by
  have hmap:=anisotropicFiniteWiener_history_law D s a (k+2) le_rfl
  change (anisotropicFiniteWienerSampleLaw D s a).map (anisotropicFiniteWienerHistory D s (k+2))=
    anisotropicFiniteHistoryLaw D s a at hmap
  have hm:=measurable_anisotropicFiniteWienerHistory D s (k+2)
  have hbound:=anisotropicFiniteHistory_weighted_variance_bounds D s a hq ha kernel J hJ
  rw [←hmap,variance_map (continuous_anisotropicHistoryWeightedSelfOverlap D s a kernel J).measurable.aemeasurable hm.aemeasurable,
    integral_map hm.aemeasurable (continuous_anisotropicHistoryWeightedHessianEnergy D s a kernel J).aestronglyMeasurable,
    integral_map hm.aemeasurable (continuous_anisotropicHistoryWeightedCovarianceEnergy D s a kernel J).aestronglyMeasurable] at hbound
  exact hbound

end QuantitativeFollowup
