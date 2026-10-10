module
public import QuantitativeFollowup.AnisotropicVarianceL2

@[expose] public section

/-! The signed L2 anisotropic variance bound is independent of the kernel
representative; no pointwise Borel representative is required in the endpoint. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem anisotropicWeightedSelfOverlap_kernel_congr (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ η : Paper.Overlap→ℝ) (J : Finset (Fin n))
    (h : κ=ᵐ[parisiFreeMeasure μ a]η) :
    anisotropicWeightedSelfOverlap D μ a κ J=anisotropicWeightedSelfOverlap D μ a η J := by
  funext sample
  apply integral_congr_ae
  exact h.mono fun q hq=>by dsimp only;rw [hq]

theorem anisotropicWeightedProcessHessianEnergy_kernel_congr (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (κ η : Paper.Overlap→ℝ) (J : Finset (Fin n))
    (h : κ=ᵐ[parisiFreeMeasure μ a]η) :
    anisotropicWeightedProcessHessianEnergy D μ a κ J=anisotropicWeightedProcessHessianEnergy D μ a η J := by
  funext sample
  unfold anisotropicWeightedProcessHessianEnergy
  congr 1
  apply integral_congr_ae
  exact h.mono fun q hq=>by dsimp only;rw [hq]

theorem anisotropic_weighted_selfOverlap_variance_signedL2 (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) (hJ : J.Nonempty) :
    variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a)≤
      ∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a := by
  let η:=hL.aestronglyMeasurable.mk κ
  have hm : Measurable η:=hL.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have he : κ=ᵐ[parisiFreeMeasure μ a]η:=hL.aestronglyMeasurable.ae_eq_mk
  have hη : MemLp η 2 (parisiFreeMeasure μ a):=(memLp_congr_ae he).mp hL
  rw [anisotropicWeightedSelfOverlap_kernel_congr D μ a κ η J he,
    anisotropicWeightedProcessHessianEnergy_kernel_congr D μ a κ η J he]
  exact anisotropic_weighted_selfOverlap_variance_L2 D μ a ha hμ η hm hη J hJ

end QuantitativeFollowup
