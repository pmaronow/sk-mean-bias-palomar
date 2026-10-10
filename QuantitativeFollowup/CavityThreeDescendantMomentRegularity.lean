module
public import QuantitativeFollowup.ThreeDescendantNativeLaw
public import QuantitativeFollowup.AnisotropicBinaryFeatureRegularity

@[expose] public section

/-! Level regularity of genuine conditional three-terminal difference moments.
No regularity of an abstract conditional-kernel representative is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem measurable_cavityThreeDescendant_difference_square
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a:ℝ)
    (J:Finset (Fin n)) :
    Measurable (fun q:Paper.Overlap=>∫z,(cavitySpinDifferencePairing J z.2)^2
      ∂cavityThreeDescendantLaw D μ a q) := by
  simp_rw [cavityThreeDescendantLaw_difference_square]
  have hm : Measurable (fun z:Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      ∑i∈J,∑j∈J,anisotropicProcessSpinCovariance D μ z.1 z.2 i j*
        anisotropicProcessPairResponse D μ z.1 (anisotropicOrderedCoupling i j) z.2) :=
    Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
      (measurable_uncurry_cavityCovarianceEntry D μ i j).mul
        (measurable_uncurry_anisotropicProcessPairResponse D μ (anisotropicOrderedCoupling i j))
  exact measurable_const.mul
    (hm.stronglyMeasurable.integral_prod_right' (ν:=anisotropicMeasureSampleLaw D μ a)).measurable

theorem integrable_cavityThreeDescendant_normalized_difference_square
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (a d:ℝ)
    (J:Finset (Fin n)) (ν:Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q:Paper.Overlap=>∫z,(cavitySpinDifferencePairing J z.2/d)^2
      ∂cavityThreeDescendantLaw D μ a q) ν := by
  let F:=fun σ:CavityThreeTerminalSpins n=>(cavitySpinDifferencePairing J σ/d)^2
  let B:ℝ:=∑σ:CavityThreeTerminalSpins n,‖F σ‖
  have hm : Measurable (fun q:Paper.Overlap=>∫z,F z.2∂cavityThreeDescendantLaw D μ a q) := by
    simp only [F,div_pow,integral_div]
    exact (measurable_cavityThreeDescendant_difference_square D μ a J).div_const _
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  exact .of_forall fun q=>by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const (μ:=cavityThreeDescendantLaw D μ a q)
      (.of_forall fun z=>Finset.single_le_sum (fun σ _=>norm_nonneg (F σ)) (Finset.mem_univ z.2))

end QuantitativeFollowup
