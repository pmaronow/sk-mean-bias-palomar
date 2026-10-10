module
public import QuantitativeFollowup.FollowupCavitySignedResponsePairing

@[expose] public section

/-! The native signed response pairing retains the genuinely sampled
terminal spin. This is needed for the centered terminal residual x_r;
an endpoint-mean surrogate is not used. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000

theorem cavitySignedResponse_marked_centered_pairing (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0 ≠ 0)
    (ha : a ∈ Icc (0:ℝ) 1) (hμ : μ ∈ scalarFloor a)
    (J : Finset (Fin n)) (hJ : J.Nonempty) (r : Paper.Overlap)
    (ψ : Paper.Overlap → ℝ) (hψ : Measurable ψ)
    (hb : ∀q, (ψ q)^2 ≤ Gamma β0 μ r*Gamma β0 μ q)
    (ξ : AnisotropicDisorderBrownianSample n×Configuration n → ℝ)
    (hξ : MemLp ξ 2 (anisotropicMeasureSpinPathLaw D μ a))
    (hzero : (∫p, ξ p ∂anisotropicMeasureSpinPathLaw D μ a) = 0) :
    |∫p, ξ p*anisotropicWeightedSelfOverlap D μ a ψ J p.1
      ∂anisotropicMeasureSpinPathLaw D μ a| ≤
      2*Real.sqrt (Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J*
        (∫p, (ξ p)^2 ∂anisotropicMeasureSpinPathLaw D μ a)) := by
  let P := anisotropicMeasureSpinPathLaw D μ a
  let F := fun p : AnisotropicDisorderBrownianSample n×Configuration n =>
    anisotropicWeightedSelfOverlap D μ a ψ J p.1
  have hψb (q : Paper.Overlap) : |ψ q| ≤ 1 := by
    have hprod : Gamma β0 μ r*Gamma β0 μ q ≤ 1 :=
      (mul_le_mul (scalarGamma_le_one β0 μ r r.property) (scalarGamma_le_one β0 μ q q.property)
        (scalarGamma_nonneg β0 μ q) zero_le_one).trans_eq (one_mul _)
    have hs := (hb q).trans hprod
    nlinarith [sq_abs (ψ q), abs_nonneg (ψ q)]
  have hFm : Measurable F :=
    (measurable_anisotropicWeightedSelfOverlap D μ a ψ hψ J).comp
      (measurable_fst : Measurable
        (Prod.fst : AnisotropicDisorderBrownianSample n×Configuration n →
          AnisotropicDisorderBrownianSample n))
  have hF : MemLp F 2 P := MemLp.of_bound hFm.aestronglyMeasurable 1
    (.of_forall fun p => norm_anisotropicWeightedSelfOverlap_le D μ a ha ψ J 1
      zero_le_one hψb p.1)
  let Fc := fun p => F p-(∫p, F p ∂P)
  have hFc : MemLp Fc 2 P := hF.sub (memLp_const _)
  have hvar : (∫p, (Fc p)^2 ∂P) ≤
      4*Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J := by
    rw [← variance_eq_integral hF.aemeasurable]
    change variance (fun p => anisotropicWeightedSelfOverlap D μ a ψ J p.1)
      (anisotropicMeasureSpinPathLaw D μ a) ≤ _
    rw [(measurePreserving_anisotropicMeasureSpinPathLaw_fst D μ a).variance_fun_comp
      (f := anisotropicWeightedSelfOverlap D μ a ψ J)
      (measurable_anisotropicWeightedSelfOverlap D μ a ψ hψ J).aemeasurable]
    exact cavitySignedResponse_weighted_variance D μ a β0 hβ0 ha hμ J hJ r ψ hψ hb
  have hh := integral_mul_abs_le_sqrt_moment_bounds ξ Fc hξ hFc
    (∫p, (ξ p)^2 ∂P) _ le_rfl hvar
  have heq : (∫p, ξ p*Fc p ∂P) = ∫p, ξ p*F p ∂P := by
    simp only [Fc, mul_sub]
    rw [integral_sub (f := fun p => ξ p*F p)
      (g := fun p => ξ p*(∫p, F p ∂P))
      (hξ.integrable_mul hF) ((hξ.integrable (by norm_num)).mul_const _), integral_mul_const]
    change _-(∫p, ξ p ∂anisotropicMeasureSpinPathLaw D μ a)*_ = _
    rw [hzero, zero_mul, sub_zero]
  rw [heq] at hh
  have he : (∫p, (ξ p)^2 ∂P)*(4*Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J) =
      4*(Gamma β0 μ r*cavitySignedResponseWeightedJ D μ a β0 J*(∫p, (ξ p)^2 ∂P)) := by ring
  rw [he, Real.sqrt_mul (by norm_num)] at hh
  norm_num at hh
  exact hh

end QuantitativeFollowup
