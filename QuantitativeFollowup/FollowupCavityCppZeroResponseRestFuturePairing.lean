module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestFutureAlias
public import QuantitativeFollowup.FollowupCavityRestTraceDiagonal
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap
public import FourPapersCommon.WeightedConditionalIntegral

@[expose] public section

/-! Whole-past conditioning pairs the actual future rest mean square with
  the centered present self-overlap. The result is the genuine covariance
  column. This uses the native conditional law, never a response identity
  or conditional-expectation conclusion as an input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option autoImplicit false
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

 theorem cavityRestFutureSquare_centered_integral_eq_covarianceColumn
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r : Paper.Overlap) (hpr : p ≤ r) :
    (∫sample, cavityRestFutureSquare D μ p r sample *
      cavitySignedResponseCenteredSelfOverlap D μ a p sample
      ∂anisotropicMeasureSampleLaw D μ a) = cavityRestCovarianceColumn D μ a p r := by
  let P := anisotropicMeasureSampleLaw D μ a
  let X := cavityRestSelfOverlap D μ p
  let Y := cavityRestSelfOverlap D μ r
  let Z := cavitySignedResponseCenteredSelfOverlap D μ a p
  have hX : MemLp X 2 P :=
    MemLp.of_bound ((measurable_uncurry_cavityRestSelfOverlap D μ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (.of_forall (cavityRestSelfOverlap_norm_le D μ p))
  have hY : MemLp Y 2 P :=
    MemLp.of_bound ((measurable_uncurry_cavityRestSelfOverlap D μ).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
      (.of_forall (cavityRestSelfOverlap_norm_le D μ r))
  have hZeq : Z = fun sample => X sample - ∫z, X z ∂P := rfl
  have hZ : MemLp Z 2 P := by
    rw [hZeq]
    exact hX.sub (memLp_const _)
  have hknown : StronglyMeasurable[anisotropicBrownianFiltration n (p:ℝ).toNNReal] Z :=
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).stronglyMeasurable
  have hweighted := integral_known_mul_condExp
    (anisotropicBrownianFiltration n (p:ℝ).toNNReal)
    ((anisotropicBrownianFiltration n).le _) Z Y hknown
    (hY.integrable (by norm_num)) (hZ.integrable_mul hY)
  have hCE := cavityRestFutureSquare_condExp D μ a p r hpr
  have hpull : (∫sample, Z sample * cavityRestFutureSquare D μ p r sample ∂P) =
      ∫sample, Z sample * Y sample ∂P := by
    calc
      _ = ∫sample, Z sample * P[Y|anisotropicBrownianFiltration n (p:ℝ).toNNReal] sample ∂P := by
        apply integral_congr_ae
        filter_upwards [hCE] with sample hs
        exact congrArg (fun v : ℝ => Z sample * v) hs.symm
      _ = _ := hweighted
  have hcenter : (∫sample, Z sample * Y sample ∂P) = covariance X Y P := by
    rw [hZeq, covariance_eq_sub hX hY]
    simp_rw [sub_mul]
    have hXY : Integrable (fun sample => X sample * Y sample) P := hX.integrable_mul hY
    have hCY : Integrable (fun sample => (∫z, X z ∂P) * Y sample) P :=
      (hY.integrable (by norm_num)).const_mul _
    simpa only [Pi.sub_apply, Pi.mul_apply, integral_const_mul] using integral_sub hXY hCY
  calc
    _ = ∫sample, Z sample * cavityRestFutureSquare D μ p r sample ∂P := by
      apply integral_congr_ae
      exact .of_forall fun sample => mul_comm _ _
    _ = ∫sample, Z sample * Y sample ∂P := hpull
    _ = covariance X Y P := hcenter
    _ = _ := (cavityRestCovarianceColumn_eq_covariance D μ a p r).symm

 theorem anisotropicRestartMeanSquare_centered_integral_eq_covarianceColumn
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r : Paper.Overlap) (hpr : p ≤ r) :
    (∫sample, anisotropicRestartMeanSquare D μ sample.1 p
      (anisotropicMeasureState D μ p sample) r *
      cavitySignedResponseCenteredSelfOverlap D μ a p sample
      ∂anisotropicMeasureSampleLaw D μ a) = cavityRestCovarianceColumn D μ a p r := by
  calc
    _ = ∫sample, cavityRestFutureSquare D μ p r sample *
        cavitySignedResponseCenteredSelfOverlap D μ a p sample
        ∂anisotropicMeasureSampleLaw D μ a := by
      apply integral_congr_ae
      exact .of_forall fun sample => congrArg
        (fun v : ℝ => v * cavitySignedResponseCenteredSelfOverlap D μ a p sample)
        (cavityRestFutureSquare_eq_restartMeanSquare D μ p r hpr sample).symm
    _ = _ := cavityRestFutureSquare_centered_integral_eq_covarianceColumn D μ a p r hpr

end QuantitativeFollowup
