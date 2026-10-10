module
public import QuantitativeFollowup.FollowupCavitySignedResponseHessianPastPairing
public import QuantitativeFollowup.FollowupCavitySignedResponseTraceMoments

@[expose] public section

/-! Terminal-spin susceptibility is paired with the actual past Hessian.
The replacement uses the genuine whole-past terminal conditional law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponseHessianMeanCoordinate_eq_matrix_sum (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (p : Paper.Overlap) (i : Fin n)
    (sample : AnisotropicDisorderBrownianSample n) :
    cavitySignedResponseHessianMeanCoordinate D μ p i sample =
      ∑l : Fin n, anisotropicProcessMagnetization D μ p sample l *
        nativeAnisotropicProcessHessianMatrix D μ p sample l i := by
  let I := anisotropicFieldInjection n
  let m := anisotropicProcessMagnetization D μ p sample
  have hw : I m = ∑l : Fin n, m l • I (EuclideanSpace.single l 1) := by
    simp_rw [←map_smul]
    rw [←map_sum]
    congr 1
    ext l
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  unfold cavitySignedResponseHessianMeanCoordinate cavitySignedResponseFieldHessian
  rw [hw, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  change m l * nativeAnisotropicProcessHessianMatrix D μ p sample i l = _
  rw [nativeAnisotropicProcessHessianMatrix_symmetric]

theorem cavitySignedResponse_terminal_hessian_coordinate_pairing
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : Paper.Overlap) (i : Fin n) :
    (∫z, cavitySignedResponseHessianMeanCoordinate D μ p i z.1 * Paper.spinSign (z.2 i)
      ∂anisotropicMeasureSpinPathLaw D μ a) =
      ∫sample, cavitySignedResponseHessianMeanCoordinate D μ p i sample *
        anisotropicProcessMagnetization D μ p sample i ∂anisotropicMeasureSampleLaw D μ a := by
  have hm := (adapted_cavitySignedResponseHessianMeanCoordinate D μ p i).mono
    ((anisotropicBrownianFiltration n).le _) le_rfl
  have H := integral_anisotropicMeasureSpinPathLaw_terminal_weight D μ a
    (cavitySignedResponseHessianMeanCoordinate D μ p i) hm
    (cavitySignedResponseHessianMeanCoordinateBound D i)
    (norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i)
    (fun σ => Paper.spinSign (σ i))
  simp_rw [←anisotropicProcessSpinResponse_one D μ _ i] at H
  exact H.trans (anisotropic_native_terminalSpin_bounded_pairing D μ a p i _
    (adapted_cavitySignedResponseHessianMeanCoordinate D μ p i)
    (cavitySignedResponseHessianMeanCoordinateBound D i)
    (norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i))

theorem cavitySignedResponse_terminal_hessian_eq_mixed_diagonal
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    (∫z, (∑i : Fin n, Paper.spinSign (z.2 i) *
      ∑l : Fin n, anisotropicProcessMagnetization D μ p z.1 l *
        nativeAnisotropicProcessHessianMatrix D μ p z.1 l i) / (n : ℝ)^2
      ∂anisotropicMeasureSpinPathLaw D μ a) =
        cavitySignedResponseMixedHessianMoment D μ a p p := by
  have hi (i : Fin n) : Integrable
      (fun z : AnisotropicDisorderBrownianSample n × Configuration n =>
        cavitySignedResponseHessianMeanCoordinate D μ p i z.1 * Paper.spinSign (z.2 i))
      (anisotropicMeasureSpinPathLaw D μ a) := by
    have hm := (adapted_cavitySignedResponseHessianMeanCoordinate D μ p i).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
    apply bounded_real_integrable _ ((hm.comp measurable_fst).mul
      ((measurable_of_finite (fun σ : Configuration n => Paper.spinSign (σ i))).comp measurable_snd))
      (cavitySignedResponseHessianMeanCoordinateBound D i)
    intro z
    change ‖cavitySignedResponseHessianMeanCoordinate D μ p i z.1 * Paper.spinSign (z.2 i)‖≤_
    rw [norm_mul, Real.norm_eq_abs (Paper.spinSign _), Paper.abs_spinSign, mul_one]
    exact norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i z.1
  have hj (i : Fin n) : Integrable
      (fun sample => cavitySignedResponseHessianMeanCoordinate D μ p i sample *
        anisotropicProcessMagnetization D μ p sample i) (anisotropicMeasureSampleLaw D μ a) := by
    have hm := (adapted_cavitySignedResponseHessianMeanCoordinate D μ p i).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
    apply bounded_real_integrable _ (hm.mul (measurable_anisotropicProcessSpinResponse D μ p i))
      (cavitySignedResponseHessianMeanCoordinateBound D i)
    intro sample
    change ‖cavitySignedResponseHessianMeanCoordinate D μ p i sample *
      anisotropicProcessMagnetization D μ p sample i‖≤_
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (anisotropicProcessSpinResponse_bound D μ p i sample)
      (norm_nonneg _)).trans (by simpa only [mul_one] using
        norm_cavitySignedResponseHessianMeanCoordinate_le D μ p i sample)
  simp_rw [←cavitySignedResponseHessianMeanCoordinate_eq_matrix_sum, mul_comm (Paper.spinSign _)]
  rw [integral_div, integral_finset_sum _ (fun i _ => hi i)]
  unfold cavitySignedResponseMixedHessianMoment
  simp_rw [cavitySignedResponseMixedHessian_expand]
  rw [integral_finset_sum _ (fun i _ => hj i)]
  congr 1
  exact Finset.sum_congr rfl fun i _ =>
    cavitySignedResponse_terminal_hessian_coordinate_pairing D μ a p i

end QuantitativeFollowup
