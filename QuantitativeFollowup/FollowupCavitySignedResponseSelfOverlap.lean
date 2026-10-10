module
public import QuantitativeFollowup.FollowupCavitySignedResponseConditionalPairing
public import QuantitativeFollowup.AnisotropicSpinMartingale

@[expose] public section

/-! Actual centered rest self-overlap and the whole-past cancellations
used in the literal original T1 formula. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def cavitySignedResponseSelfOverlap (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (p : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  anisotropicSelectedMeanSquare Finset.univ (anisotropicProcessMagnetization D μ p sample)

def cavitySignedResponseCenteredSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  cavitySignedResponseSelfOverlap D μ p sample-
    ∫z,cavitySignedResponseSelfOverlap D μ p z ∂anisotropicMeasureSampleLaw D μ a

theorem measurable_joint_cavitySignedResponseSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (Function.uncurry (cavitySignedResponseSelfOverlap D μ)) :=
  (continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp
    (measurable_uncurry_anisotropicProcessMagnetization D μ)

theorem measurable_joint_cavitySignedResponseCenteredSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (Function.uncurry (cavitySignedResponseCenteredSelfOverlap D μ a)) :=
  (measurable_joint_cavitySignedResponseSelfOverlap D μ).sub
    (((measurable_joint_cavitySignedResponseSelfOverlap D μ).stronglyMeasurable.integral_prod_right'
      (ν:=anisotropicMeasureSampleLaw D μ a)).measurable.comp measurable_fst)

theorem adapted_cavitySignedResponseSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) :
    Measurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal]
      (cavitySignedResponseSelfOverlap D μ p) :=
  (continuous_anisotropicSelectedMeanSquare Finset.univ).measurable.comp
    (adapted_anisotropicProcessMagnetization D μ p)

theorem adapted_cavitySignedResponseCenteredSelfOverlap (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal]
      (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
  (adapted_cavitySignedResponseSelfOverlap D μ p).sub measurable_const

theorem norm_cavitySignedResponseSelfOverlap_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseSelfOverlap D μ p sample‖≤1 := by
  apply anisotropicSelectedMeanSquare_bound
  intro i
  have h := anisotropicProcessSpinResponse_bound D μ p i sample
  simpa only [anisotropicProcessSpinResponse,Real.norm_eq_abs] using h

theorem norm_cavitySignedResponseCenteredSelfOverlap_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖cavitySignedResponseCenteredSelfOverlap D μ a p sample‖≤2 := by
  have h := norm_integral_le_of_norm_le_const (μ:=anisotropicMeasureSampleLaw D μ a)
    (.of_forall (norm_cavitySignedResponseSelfOverlap_le D μ p))
  simp only [probReal_univ,mul_one] at h
  exact (norm_sub_le _ _).trans (by linarith [norm_cavitySignedResponseSelfOverlap_le D μ p sample])

theorem cavitySignedResponse_terminal_centered_self_pairing_eq (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap) :
    (∫z,cavitySignedResponseTerminalResidual D μ r z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)=
      ∫z,cavitySignedResponseTerminalResidual D μ r z*
        cavitySignedResponseSelfOverlap D μ p z.1 ∂anisotropicMeasureSpinPathLaw D μ a := by
  have hA : Measurable (cavitySignedResponseSelfOverlap D μ p) :=
    (adapted_cavitySignedResponseSelfOverlap D μ p).mono ((anisotropicBrownianFiltration n).le _) le_rfl
  have hx := (memLp_two_cavitySignedResponseTerminalResidual D μ a r).integrable (by norm_num)
  have hi : Integrable (fun z=>cavitySignedResponseTerminalResidual D μ r z*
      cavitySignedResponseSelfOverlap D μ p z.1) (anisotropicMeasureSpinPathLaw D μ a) := by
    apply bounded_real_integrable _
      ((measurable_cavitySignedResponseTerminalResidual D μ r).mul (hA.comp measurable_fst)) 2
    intro z
    change ‖cavitySignedResponseTerminalResidual D μ r z*cavitySignedResponseSelfOverlap D μ p z.1‖≤2
    rw [norm_mul]
    exact (mul_le_mul (norm_cavitySignedResponseTerminalResidual_le D μ r z)
      (norm_cavitySignedResponseSelfOverlap_le D μ p z.1) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  simp only [cavitySignedResponseCenteredSelfOverlap,mul_sub]
  rw [integral_sub hi (hx.mul_const _),integral_mul_const,cavitySignedResponseTerminalResidual_centered,zero_mul,sub_zero]

theorem cavitySignedResponse_original_T1_diagonal_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (∫z,cavitySignedResponseTerminalResidual D μ p z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)=0 :=
  cavitySignedResponse_terminal_known_pairing_zero D μ a p _
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).stronglyMeasurable 2 (by norm_num)
    (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p)

theorem cavitySignedResponse_original_T1_two_time_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap) :
    (∫sample,cavitySignedResponseSymmetricMeanResidual D μ p r sample*
      cavitySignedResponseCenteredSelfOverlap D μ a p sample ∂anisotropicMeasureSampleLaw D μ a)=
      if r<p then (∫z,cavitySignedResponseTerminalResidual D μ r z*
        cavitySignedResponseSelfOverlap D μ p z.1 ∂anisotropicMeasureSpinPathLaw D μ a) else 0 := by
  rw [cavitySignedResponse_symmetric_residual_past_pairing D μ a r p _
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).stronglyMeasurable 2 (by norm_num)
    (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p)]
  rw [cavitySignedResponse_terminal_centered_self_pairing_eq]

end QuantitativeFollowup
