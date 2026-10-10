module
public import QuantitativeFollowup.FollowupCavitySignedResponseDoublePairing
public import FourPapersCommon.WeightedConditionalIntegral

@[expose] public section

/-! Genuine whole-past pairings of terminal and two-time residuals.
They give the conditioning cancellations used in the original T1 formula. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponse_conditional_residual_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) (hrl : r≤l)
    (F : AnisotropicDisorderBrownianSample n→ℝ)
    (hF : StronglyMeasurable[anisotropicBrownianFiltration n (l:ℝ).toNNReal] F)
    (B : ℝ) (hB : 0≤B) (hb : ∀sample,‖F sample‖≤B) :
    (∫sample,cavitySignedResponseMeanResidual D μ r l sample*F sample ∂anisotropicMeasureSampleLaw D μ a)=
      ∫p,cavitySignedResponseTerminalResidual D μ r p*F p.1 ∂anisotropicMeasureSpinPathLaw D μ a := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let ambient : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := inferInstance
  let V := anisotropicSpinPast n (l:ℝ).toNNReal
  letI : MeasurableSpace (AnisotropicDisorderBrownianSample n×Configuration n) := ambient
  let Z := fun p : AnisotropicDisorderBrownianSample n×Configuration n => F p.1
  have hZ : StronglyMeasurable[V] Z := hF.comp_measurable (comap_measurable Prod.fst)
  have hZm : Measurable Z := (hZ.mono (anisotropicSpinPast_le n _)).measurable
  have hZi : Integrable (fun p=>Z p*cavitySignedResponseTerminalResidual D μ r p) P :=
    bounded_real_integrable _ (hZm.mul (measurable_cavitySignedResponseTerminalResidual D μ r)) (B*2)
      (fun p=>(norm_mul _ _).trans_le (mul_le_mul (hb p.1)
        (norm_cavitySignedResponseTerminalResidual_le D μ r p) (norm_nonneg _) hB))
  have h := integral_known_mul_condExp V (anisotropicSpinPast_le n _) Z
    (cavitySignedResponseTerminalResidual D μ r) hZ
    ((memLp_two_cavitySignedResponseTerminalResidual D μ a r).integrable (by norm_num)) hZi
  have hc := cavitySignedResponseTerminalResidual_condExp D μ a r l hrl
  have he := integral_congr_ae (hc.mono fun p hp=>congrArg (fun x : ℝ=>Z p*x) hp)
  rw [he] at h
  dsimp only [Z] at h
  have hFm : Measurable (fun sample=>F sample*cavitySignedResponseMeanResidual D μ r l sample) :=
    ((hF.mono ((anisotropicBrownianFiltration n).le _)).measurable).mul
      (measurable_cavitySignedResponseMeanResidual D μ r l)
  rw [integral_anisotropicMeasureSpinPathLaw_sample D μ a _ hFm] at h
  simpa only [mul_comm] using h

theorem cavitySignedResponse_terminal_known_pairing_zero (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap)
    (F : AnisotropicDisorderBrownianSample n→ℝ)
    (hF : StronglyMeasurable[anisotropicBrownianFiltration n (r:ℝ).toNNReal] F)
    (B : ℝ) (hB : 0≤B) (hb : ∀sample,‖F sample‖≤B) :
    (∫p,cavitySignedResponseTerminalResidual D μ r p*F p.1 ∂anisotropicMeasureSpinPathLaw D μ a)=0 := by
  have h := cavitySignedResponse_conditional_residual_pairing D μ a r r le_rfl F hF B hB hb
  simpa only [cavitySignedResponseMeanResidual,sub_self,mul_zero,Finset.sum_const_zero,zero_div,
    zero_mul,integral_zero] using h.symm

theorem cavitySignedResponse_symmetric_residual_past_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r p : Paper.Overlap)
    (F : AnisotropicDisorderBrownianSample n→ℝ)
    (hF : StronglyMeasurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal] F)
    (B : ℝ) (hB : 0≤B) (hb : ∀sample,‖F sample‖≤B) :
    (∫sample,cavitySignedResponseSymmetricMeanResidual D μ p r sample*F sample
      ∂anisotropicMeasureSampleLaw D μ a)=
      if r<p then (∫z,cavitySignedResponseTerminalResidual D μ r z*F z.1 ∂anisotropicMeasureSpinPathLaw D μ a) else 0 := by
  by_cases hrp : r<p
  · simp only [cavitySignedResponseSymmetricMeanResidual,min_eq_right hrp.le,max_eq_left hrp.le,if_pos hrp]
    exact cavitySignedResponse_conditional_residual_pairing D μ a r p hrp.le F hF B hB hb
  · have hpr : p≤r := le_of_not_gt hrp
    simp only [cavitySignedResponseSymmetricMeanResidual,min_eq_left hpr,max_eq_right hpr,if_neg hrp]
    have hFr := hF.mono ((anisotropicBrownianFiltration n).mono (Real.toNNReal_mono hpr))
    rw [cavitySignedResponse_conditional_residual_pairing D μ a p r hpr F hFr B hB hb]
    exact cavitySignedResponse_terminal_known_pairing_zero D μ a p F hF B hB hb

end QuantitativeFollowup
