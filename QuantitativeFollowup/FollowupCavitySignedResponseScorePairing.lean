module
public import QuantitativeFollowup.FollowupCavitySignedResponseScore
public import QuantitativeFollowup.FollowupCavitySignedResponseMarked

@[expose] public section

/-! Sharp signed pairings of the actual terminal, conditional and posterior
score residuals. Every residual is evaluated under the genuine native law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem measurable_cavitySignedResponseScore (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    Measurable (cavitySignedResponseScore D μ a r) :=
  (measurable_cavitySignedResponseTerminalResidual D μ r).sub
    ((measurable_cavitySignedResponseIntegratedFutureResidual D μ a r).comp measurable_fst)

theorem norm_cavitySignedResponseScore_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (r : Paper.Overlap) (p : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavitySignedResponseScore D μ a r p‖ ≤ 4 :=
  (norm_sub_le _ _).trans ((add_le_add
    (norm_cavitySignedResponseTerminalResidual_le D μ r p)
    (norm_cavitySignedResponseIntegratedFutureResidual_le D μ a ha r p.1)).trans_eq
      (by norm_num))

theorem memLp_two_cavitySignedResponseScore (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (r : Paper.Overlap) :
    MemLp (cavitySignedResponseScore D μ a r) 2 (anisotropicMeasureSpinPathLaw D μ a) :=
  MemLp.of_bound (measurable_cavitySignedResponseScore D μ a r).aestronglyMeasurable 4
    (.of_forall (norm_cavitySignedResponseScore_le D μ a ha r))

theorem cavitySignedResponse_terminal_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0)
    (ha : a ∈ Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (hn : 0<n) (r : Paper.Overlap) (ψ : Paper.Overlap→ℝ) (hψ : Measurable ψ)
    (hb : ∀q,(ψ q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q) :
    |∫p,cavitySignedResponseTerminalResidual D μ r p*
      anisotropicWeightedSelfOverlap D μ a ψ Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a| ≤
      2*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
        cavitySignedResponseCovarianceMoment D μ a Finset.univ r) := by
  have hJ : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have h := cavitySignedResponse_marked_centered_pairing D μ a β0 hβ0 ha hμ
    Finset.univ hJ r ψ hψ hb (cavitySignedResponseTerminalResidual D μ r)
    (memLp_two_cavitySignedResponseTerminalResidual D μ a r)
    (cavitySignedResponseTerminalResidual_centered D μ a r)
  rwa [cavitySignedResponseTerminalResidual_second_moment] at h

theorem cavitySignedResponse_mean_residual_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0)
    (ha : a ∈ Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (hn : 0<n) (r l : Paper.Overlap) (hrl : r≤l)
    (ψ : Paper.Overlap→ℝ) (hψ : Measurable ψ)
    (hb : ∀q,(ψ q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q) :
    |∫sample,cavitySignedResponseMeanResidual D μ r l sample*
      anisotropicWeightedSelfOverlap D μ a ψ Finset.univ sample
      ∂anisotropicMeasureSampleLaw D μ a| ≤
      2*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
        cavitySignedResponseCovarianceMoment D μ a Finset.univ r) := by
  have hJ : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have h := cavitySignedResponse_centered_pairing D μ a β0 hβ0 ha hμ
    Finset.univ hJ r ψ hψ hb (cavitySignedResponseMeanResidual D μ r l)
    (memLp_two_cavitySignedResponseMeanResidual D μ a r l)
    (cavitySignedResponseMeanResidual_centered D μ a r l hrl)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left (cavitySignedResponseMeanResidual_second_moment_le D μ a r l hrl)
      (mul_nonneg (scalarGamma_nonneg β0 μ r)
        (cavitySignedResponseWeightedJ_nonneg D μ a β0 _)))) (by norm_num))

theorem cavitySignedResponse_score_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0)
    (ha : a ∈ Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (hn : 0<n) (r : Paper.Overlap) (ψ : Paper.Overlap→ℝ) (hψ : Measurable ψ)
    (hb : ∀q,(ψ q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q) :
    |∫p,cavitySignedResponseScore D μ a r p*
      anisotropicWeightedSelfOverlap D μ a ψ Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a| ≤
      4*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
        cavitySignedResponseCovarianceMoment D μ a Finset.univ r) := by
  have hJ : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  have h := cavitySignedResponse_marked_centered_pairing D μ a β0 hβ0 ha hμ
    Finset.univ hJ r ψ hψ hb (cavitySignedResponseScore D μ a r)
    (memLp_two_cavitySignedResponseScore D μ a ha r)
    (cavitySignedResponseScore_centered D μ a ha r)
  have hm := mul_le_mul_of_nonneg_left
    (cavitySignedResponseScore_second_moment_le D μ a ha r)
    (mul_nonneg (scalarGamma_nonneg β0 μ r)
      (cavitySignedResponseWeightedJ_nonneg D μ a β0 Finset.univ))
  have hs := Real.sqrt_le_sqrt hm
  have he : Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
      (4*cavitySignedResponseCovarianceMoment D μ a Finset.univ r) =
      4*(Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
        cavitySignedResponseCovarianceMoment D μ a Finset.univ r) := by ring
  have hscale : Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
      (4*cavitySignedResponseCovarianceMoment D μ a Finset.univ r)) =
      2*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 Finset.univ*
        cavitySignedResponseCovarianceMoment D μ a Finset.univ r) := by
    rw [he,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  exact h.trans ((mul_le_mul_of_nonneg_left (hs.trans_eq hscale) (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))

end QuantitativeFollowup
