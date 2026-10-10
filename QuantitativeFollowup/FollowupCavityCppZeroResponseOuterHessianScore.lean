module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterScore
public import QuantitativeFollowup.FollowupCavityCppZeroResponseOuterLogJets
public import FourPapersCommon.ExponentialDensityHessian

@[expose] public section

/-! The actual outer posterior log-density Hessian is its genuine second
Stieltjes score. The field variable is differentiated before any concrete
cavity-model specialization; the actual normalizer Hessian is retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped BigOperators ContDiff
namespace QuantitativeFollowup
variable {S J : Type} [Fintype S] [Nonempty S] [Fintype J]
  [MeasurableSpace S] [MeasurableSingletonClass S] {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

theorem contDiff_cavityOuterPosteriorLogDensity_field (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field n →L[ℝ] FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (p : FiniteStateGaussianInput J × ((Fin N → Field n) × S)) :
    ContDiff ℝ ∞ (fun Q => cavityOuterPosteriorLogDensity V a L s N R Q p) := by
  exact (contDiff_cavityOuterPosteriorLogDensity_joint V a ha L s N R p.2.2).comp
    (contDiff_id.prodMk (contDiff_const (c := (p.1, p.2.1))))

theorem hessian_cavityOuterPosteriorLogDensity_stieltjes (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ i, 0 ≤ a i) (L : ℕ → Field n →L[ℝ] FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J × ((Fin (N+1) → Field n) × S)) :
    exponentialDensityHessian
      (fun Q => cavityOuterPosteriorLogDensity V a L s (N+1) R Q p) H K K =
      cavityOuterPosteriorSecondScore V a L s N R H K p := by
  let F := fun Q => cavityOuterPosteriorLogDensity V a L s (N+1) R Q p
  have hF : ContDiff ℝ 2 F :=
    (contDiff_cavityOuterPosteriorLogDensity_field V a ha L s (N+1) R p).of_le (by simp)
  calc
    _ = fderiv ℝ (fun Q => fderiv ℝ F Q K) H K := by
      rw [(hasFDerivAt_exponential_directional_field F hF H K).fderiv,
        ContinuousLinearMap.flip_apply]
    _ = _ := second_fderiv_cavityOuterPosteriorLogDensity_stieltjes V a ha L s N R H K p

theorem hessian_cavityOuterPosteriorLogDensity_stieltjes_expanded
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i)
    (L : ℕ → Field n →L[ℝ] FiniteStateField S) (s : ℝ) (N : ℕ)
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) (H K : FiniteStateField S)
    (p : FiniteStateGaussianInput J × ((Fin (N+1) → Field n) × S)) :
    exponentialDensityHessian
      (fun Q => cavityOuterPosteriorLogDensity V a L s (N+1) R Q p) H K K =
      -(∑ i, cavityOuterStieltjesWeight a s N i *
        fderiv ℝ (fun Q => fderiv ℝ
          (fun B => cascadePosteriorStieltjesPotential V a L N p.2.1 i (B + R p.1)) Q K) H K) -
        exponentialDensityHessian
          (fun Q => Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R Q)) H K K := by
  let Z := fun Q => Real.log (cavityOuterPosteriorNormalizer V a L s (N+1) R Q)
  have hZ : ContDiff ℝ 2 Z :=
    (contDiff_log_cavityOuterPosteriorNormalizer V a ha L s (N+1) R).of_le (by simp)
  have he : fderiv ℝ (fun Q => fderiv ℝ Z Q K) H K =
      exponentialDensityHessian Z H K K := by
    rw [(hasFDerivAt_exponential_directional_field Z hZ H K).fderiv,
      ContinuousLinearMap.flip_apply]
  rw [hessian_cavityOuterPosteriorLogDensity_stieltjes V a ha L s N R H K p]
  exact congrArg (fun z =>
    -(∑ i, cavityOuterStieltjesWeight a s N i *
      fderiv ℝ (fun Q => fderiv ℝ
        (fun B => cascadePosteriorStieltjesPotential V a L N p.2.1 i (B + R p.1)) Q K) H K) - z) he

end QuantitativeFollowup
