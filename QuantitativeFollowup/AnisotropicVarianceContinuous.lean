module
public import QuantitativeFollowup.AnisotropicFreeEnergyLimits
public import QuantitativeFollowup.AnisotropicFreeHistory

@[expose] public section

/-! The actual arbitrary-profile anisotropic self-overlap variance bound
for continuous signed free-measure kernels. No finite diffusion or limit
identification is supplied as an assumption. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem anisotropic_weighted_selfOverlap_variance_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (κ : Paper.Overlap→ℝ) (hκ : Continuous κ) (J : Finset (Fin n)) (hJ : J.Nonempty)
    (K : ℝ) (hK : 0≤K) (hb : ∀q,|κ q|≤K) :
    variance (anisotropicWeightedSelfOverlap D μ a κ J) (anisotropicMeasureSampleLaw D μ a)≤
      ∫sample,anisotropicWeightedProcessHessianEnergy D μ a κ J sample ∂anisotropicMeasureSampleLaw D μ a := by
  apply le_of_tendsto_of_tendsto
    (tendsto_variance_anisotropicDyadicWeightedSelfOverlap D μ a ha κ hκ J K hK hb)
    (tendsto_integral_anisotropicDyadicWeightedProcessHessianEnergy D μ a ha κ hκ J K hb)
  apply Eventually.of_forall
  intro j
  have h:= (anisotropicFiniteWiener_weighted_variance_bounds D
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a
    (Paper.parisiGridSchemeOverlap_one _) (parisiGridRSBScheme_floor μ a hμ _)
    (fun q=>κ (projIcc 0 1 zero_le_one q)) J hJ).1
  have hs := funext (anisotropicDyadicWeightedSelfOverlap_eq_history D μ a ha hμ κ hκ.measurable J j)
  have hE := funext (anisotropicDyadicWeightedHessianEnergy_eq_history D μ a ha hμ κ hκ.measurable J j)
  rw [←hs,←hE] at h
  exact h

end QuantitativeFollowup
