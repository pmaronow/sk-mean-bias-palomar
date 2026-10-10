module
public import QuantitativeFollowup.AnisotropicSpinPathConditionals
public import QuantitativeFollowup.AnisotropicCovarianceMoments

@[expose] public section

/-! The full-profile response covariance is a genuine version of the
conditional terminal-spin covariance under the actual marked diffusion law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def anisotropicProcessSpinCovariance (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : Matrix (Fin n) (Fin n) ℝ :=
  anisotropicTailSpinCovariance D μ q (anisotropicProcessParameter D μ q sample)

theorem anisotropicMeasureSpinPathLaw_orderedPair_condExp (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i j : Fin n) :
    (anisotropicMeasureSpinPathLaw D μ a)[
      (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (p.2 i)*Paper.spinSign (p.2 j))|
        anisotropicSpinPast n (q:ℝ).toNNReal]=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) p.1 := by
  have h:=anisotropicMeasureSpinPathLaw_pair_condExp D μ a q (anisotropicOrderedCoupling i j)
  simp_rw [anisotropicOrderedCoupling_feature] at h
  exact h

theorem anisotropicProcessSpinCovariance_eq_conditional (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) (i j : Fin n) :
    (fun p : AnisotropicDisorderBrownianSample n×Configuration n=>
      (anisotropicMeasureSpinPathLaw D μ a)[
        (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (z.2 i)*Paper.spinSign (z.2 j))|
          anisotropicSpinPast n (q:ℝ).toNNReal] p-
      (anisotropicMeasureSpinPathLaw D μ a)[
        (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (z.2 i))|
          anisotropicSpinPast n (q:ℝ).toNNReal] p*
      (anisotropicMeasureSpinPathLaw D μ a)[
        (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>Paper.spinSign (z.2 j))|
          anisotropicSpinPast n (q:ℝ).toNNReal] p)=ᵐ[anisotropicMeasureSpinPathLaw D μ a]
      fun p=>anisotropicProcessSpinCovariance D μ q p.1 i j := by
  filter_upwards [anisotropicMeasureSpinPathLaw_orderedPair_condExp D μ a q i j,
    anisotropicMeasureSpinPathLaw_spin_condExp D μ a q i,
    anisotropicMeasureSpinPathLaw_spin_condExp D μ a q j] with p hp hi hj
  rw [hp,hi,hj]
  rfl

theorem anisotropicTailSpinCovariance_entry_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (P : AnisotropicParameter n) (i j : Fin n) :
    ‖anisotropicTailSpinCovariance D μ q P i j‖ ≤ 2 := by
  apply (norm_sub_le _ _).trans
  have hp:=anisotropicTailPairResponse_bound D μ q P (anisotropicOrderedCoupling i j)
  have hi:=anisotropicMeasureTailMagnetization_component_bound D μ q P i
  have hj:=anisotropicMeasureTailMagnetization_component_bound D μ q P j
  have hm : ‖anisotropicMeasureTailMagnetization D μ q P i*anisotropicMeasureTailMagnetization D μ q P j‖ ≤ 1 := by
    rw [norm_mul]
    simpa only [Real.norm_eq_abs,one_mul] using
      (mul_le_mul hi hj (abs_nonneg _) zero_le_one)
  exact (add_le_add hp hm).trans_eq (by ring)

end QuantitativeFollowup
