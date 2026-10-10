module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseKernelContraction
public import QuantitativeFollowup.ScalarResponseSamples
public import QuantitativeFollowup.FollowupCavitySignedResponseSelfOverlap

@[expose] public section

/-! The final future term contracts under the complete independent marked
law to the literal scalar centered pairing and the actual rest conditional
projection. There is no order assumption between the test level and the
future start; both sides retain the genuine whole-past restart kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem projected_zero_mem : (0:ℝ)∈Icc 0 1 := ⟨le_rfl,zero_le_one⟩

theorem cavityRestFutureSquare_centered_integral_eq_projectedCovariance
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r l : Paper.Overlap) :
    (∫sample,cavityRestFutureSquare D μ r l sample*
      cavitySignedResponseCenteredSelfOverlap D μ a p sample
      ∂anisotropicMeasureSampleLaw D μ a)=cavityRestProjectedCovariance D μ a r l p :=by
  have hF:=cavityRestFutureSquare_memLp_two D μ a r l
  have hG:=cavityRestSelfOverlap_memLp_two D μ a p
  rw [cavityRestProjectedCovariance,covariance_eq_sub hF hG]
  change (∫sample,cavityRestFutureSquare D μ r l sample*
    (cavityRestSelfOverlap D μ p sample-∫z,cavityRestSelfOverlap D μ p z
      ∂anisotropicMeasureSampleLaw D μ a) ∂anisotropicMeasureSampleLaw D μ a)=_
  simp_rw [mul_sub]
  have hiFG : Integrable (fun sample=>cavityRestFutureSquare D μ r l sample*
      cavityRestSelfOverlap D μ p sample) (anisotropicMeasureSampleLaw D μ a) :=by
    simpa only [Pi.mul_def] using hF.integrable_mul hG
  have hiFC : Integrable (fun sample=>cavityRestFutureSquare D μ r l sample*
      (∫z,cavityRestSelfOverlap D μ p z ∂anisotropicMeasureSampleLaw D μ a))
      (anisotropicMeasureSampleLaw D μ a) := (hF.integrable (by norm_num)).mul_const _
  rw [integral_sub hiFG hiFC,integral_mul_const]
  simp only [Pi.mul_apply]

private theorem projected_future_centered_measurable
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p r l : Paper.Overlap) :
    Measurable (fun sample : AnisotropicDisorderBrownianSample n=>
      cavityRestFutureSquare D μ r l sample*cavitySignedResponseCenteredSelfOverlap D μ a p sample) :=by
  have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(r,(l,sample))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hFuture := (measurable_cavityRestFutureSquare D μ).comp hm
  have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
    (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
      ((anisotropicBrownianFiltration n).le _) le_rfl
  exact hFuture.mul hcenter

theorem cavityZeroMarked_future_scalarSample7_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (p r l : Paper.Overlap) (hrl : r≤l) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,(cavityRestFutureSquare D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1)*
      scalarResponseSample 7 B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 projected_zero_mem) μ a)=
      scalarFutureCenteredPairing B μ p r l*cavityRestProjectedCovariance D μ a r l p :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let F:=fun sample : AnisotropicDisorderBrownianSample n=>
    cavityRestFutureSquare D μ r l sample*cavitySignedResponseCenteredSelfOverlap D μ a p sample
  have hFC : Measurable F:=projected_future_centered_measurable D μ a p r l
  have hF : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      F z.1) :=hFC.comp measurable_fst
  have hprod:=integral_cavityZeroMarked_product μ n β ρ hβ hρ a
    (fun z=>F z.1) (scalarResponseSample 7 B μ p r l) hF
    (measurable_scalarResponseSample 7 B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p r l)
  have hr : (∫z,F z.1 ∂anisotropicMeasureSpinPathLaw D μ a)=
      cavityRestProjectedCovariance D μ a r l p :=
    (integral_anisotropicMeasureSpinPathLaw_sample D μ a F hFC).trans
      (cavityRestFutureSquare_centered_integral_eq_projectedCovariance D μ a p r l)
  calc
    _ = (∫z,F z.1 ∂anisotropicMeasureSpinPathLaw D μ a)*
        (∫z,scalarResponseSample 7 B μ p r l z
          ∂scalarMarkedSpinLaw B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ) :=hprod
    _ = cavityRestProjectedCovariance D μ a r l p*scalarResponseKernel7 B μ p r l :=by
      rw [hr,integral_scalarResponseSample]
      rfl
    _ = _ :=by
      rw [scalarFutureCenteredPairing_eq_kernel B μ p r l hrl]
      exact mul_comm _ _

end QuantitativeFollowup
