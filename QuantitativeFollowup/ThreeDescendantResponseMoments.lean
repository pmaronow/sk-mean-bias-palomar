module
public import QuantitativeFollowup.ThreeDescendantNativeLaw

@[expose] public section

/-! Exact normalized three-descendant representation of the actual covariance
trace and covariance energy. All profile atoms and singular coupling maps are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal Topology BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponse_pair_covariance_sum (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    (∑i : Fin n,∑j : Fin n,anisotropicProcessSpinCovariance D μ q sample i j*
      anisotropicProcessPairResponse D μ q (anisotropicOrderedCoupling i j) sample)=
    Matrix.trace (anisotropicProcessSpinCovariance D μ q sample*anisotropicProcessSpinCovariance D μ q sample)+
      anisotropicProcessCovarianceEnergy D μ Finset.univ q sample := by
  rw [anisotropicProcessCovarianceEnergy,anisotropicSelectedFieldMap_univ]
  simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,anisotropicTailCovarianceQuadratic,
    ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [←nativeAnisotropicProcessSpinCovariance_symmetric D μ q sample i j]
  unfold anisotropicProcessSpinCovariance anisotropicTailSpinCovariance anisotropicProcessPairResponse
    anisotropicProcessMagnetization
  ring

theorem cavityThreeDescendantLaw_normalized_difference_square (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    (∫z,(cavitySpinDifferencePairing Finset.univ z.2/(n:ℝ))^2 ∂cavityThreeDescendantLaw D μ a q)=
      2*(cavitySignedResponseCovarianceTraceMoment D μ a q+
        cavitySignedResponseCovarianceMoment D μ a Finset.univ q) := by
  simp_rw [div_pow]
  rw [integral_div,cavityThreeDescendantLaw_difference_square]
  simp_rw [cavitySignedResponse_pair_covariance_sum]
  have hmap : Measurable (fun sample : AnisotropicDisorderBrownianSample n=>(q,sample)) :=
    measurable_const.prodMk measurable_id
  have hmC := (measurable_uncurry_cavityCovarianceSquareTrace D μ).comp hmap
  dsimp only [Function.comp_def] at hmC
  have hiC := bounded_real_integrable (P:=anisotropicMeasureSampleLaw D μ a) _ hmC _
    (norm_cavityCovarianceSquareTrace_le D μ q)
  have hmE := (measurable_uncurry_anisotropicProcessCovarianceEnergy D μ Finset.univ).comp hmap
  dsimp only [Function.comp_def] at hmE
  have hiE := bounded_real_integrable (P:=anisotropicMeasureSampleLaw D μ a) _ hmE _
    (norm_anisotropicProcessCovarianceEnergy_le D μ Finset.univ q)
  rw [integral_add hiC hiE]
  simp only [cavitySignedResponseCovarianceTraceMoment,cavitySignedResponseCovarianceMoment,
    Finset.card_univ,Fintype.card_fin]
  ring

end QuantitativeFollowup
