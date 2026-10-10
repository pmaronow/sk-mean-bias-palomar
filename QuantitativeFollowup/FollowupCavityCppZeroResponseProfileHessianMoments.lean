module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileColumns
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileHessian
public import QuantitativeFollowup.FollowupCavitySignedResponseTraceMoments
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessian

@[expose] public section

/-! Actual Hessian moments along native same-driver paths. The genuine
weak-profile Hessian limit is evaluated at the true moving process input,
then integrated under the actual moving outer tilt. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128

theorem tendsto_cavitySignedResponseFieldHessian_profile_moving
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) {P : I→AnisotropicParameter n} {Q : AnisotropicParameter n}
    (hP : Tendsto P l (𝓝 Q)) {w v : I→Field n} {w₀ v₀ : Field n}
    (hw : Tendsto w l (𝓝 w₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun j=>cavitySignedResponseFieldHessian D (μ j) (q j) (P j) (w j) (v j)) l
      (𝓝 (cavitySignedResponseFieldHessian D ν r Q w₀ v₀)) := by
  have hH := tendsto_anisotropicMeasureTailSecondDifferential_of_weak_moving D μ ν hμ q r hq P Q hP
  have hHw := ((isBoundedBilinearMap_apply (𝕜:=ℝ) (E:=AnisotropicParameter n)
    (F:=AnisotropicParameter n→L[ℝ]ℝ)).continuous.tendsto _).comp
      (hH.prodMk_nhds ((anisotropicFieldInjection n).continuous.tendsto _ |>.comp hw))
  exact ((isBoundedBilinearMap_apply (𝕜:=ℝ) (E:=AnisotropicParameter n)
    (F:=ℝ)).continuous.tendsto _).comp
      (hHw.prodMk_nhds ((anisotropicFieldInjection n).continuous.tendsto _ |>.comp hv))

theorem tendsto_cavitySignedResponseMixedHessianMoment_profile_level
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) {r s : I→Paper.Overlap} {r₀ s₀ : Paper.Overlap}
    (hr : Tendsto r l (𝓝 r₀)) (hs : Tendsto s l (𝓝 s₀)) :
    Tendsto (fun j=>cavitySignedResponseMixedHessianMoment D (μ j) a (r j) (s j)) l
      (𝓝 (cavitySignedResponseMixedHessianMoment D ν a r₀ s₀)) := by
  apply Tendsto.div_const
  refine tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a _ _ ?_
    ((n:ℝ)^2) (sq_nonneg _) ?_ ?_
  · intro j
    exact (measurable_cavitySignedResponseMixedHessian D (μ j) (r j) (s j)).aestronglyMeasurable
  · intro j
    exact norm_cavitySignedResponseMixedHessian_le D (μ j) (r j) (s j)
  · exact .of_forall fun ω=>
      tendsto_cavitySignedResponseFieldHessian_profile_moving D hμ hs
        (tendsto_anisotropicProcessParameter_profile_time D hμ hs ω)
        (tendsto_anisotropicProcessMagnetization_profile_time D hμ hr ω)
        (tendsto_anisotropicProcessMagnetization_profile_time D hμ hs ω)

private theorem hessianEntry_limit {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) (ω : AnisotropicDisorderBrownianSample n) (i j : Fin n) :
    Tendsto (fun k=>nativeAnisotropicProcessHessianMatrix D (μ k) (q k) ω i j) l
      (𝓝 (nativeAnisotropicProcessHessianMatrix D ν r ω i j)) :=
  tendsto_cavitySignedResponseFieldHessian_profile_moving D hμ hq
    (tendsto_anisotropicProcessParameter_profile_time D hμ hq ω)
    tendsto_const_nhds tendsto_const_nhds

theorem tendsto_cavitySignedResponseHessianTraceMoment_profile_level
    {I : Type*} {l : Filter I} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel n) {μ : I→Paper.ParisiMeasure} {ν : Paper.ParisiMeasure}
    (hμ : Tendsto μ l (𝓝 ν)) (a : ℝ) {q : I→Paper.Overlap} {r : Paper.Overlap}
    (hq : Tendsto q l (𝓝 r)) :
    Tendsto (fun j=>cavitySignedResponseHessianTraceMoment D (μ j) a (q j)) l
      (𝓝 (cavitySignedResponseHessianTraceMoment D ν a r)) := by
  apply Tendsto.div_const
  refine tendsto_integral_anisotropicMeasureSampleLaw_profile_bounded D hμ a _ _ ?_
    (4*(n:ℝ)^2) (by positivity) ?_ ?_
  · intro j
    have hm : Measurable (fun ω : AnisotropicDisorderBrownianSample n=>(q j,ω)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_uncurry_cavityHessianSquareTrace D (μ j)).comp hm).aestronglyMeasurable
  · intro j
    exact norm_cavityHessianSquareTrace_le D (μ j) (q j)
  · exact .of_forall fun ω=>by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply]
      apply tendsto_finsetSum
      intro i _
      apply tendsto_finsetSum
      intro j _
      exact (hessianEntry_limit D hμ hq ω i j).mul (hessianEntry_limit D hμ hq ω j i)

end QuantitativeFollowup
