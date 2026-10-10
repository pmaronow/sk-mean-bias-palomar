module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileHessianMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileScalarKernels
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals

@[expose] public section

/-! The literal diagonal and final Hessian terms of T3 pass under the
prescribed-atom approximation. The diagonal right-CDF is preserved
exactly, rather than treated as a weak-continuity observable. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped Topology NNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 850000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem tendsto_cavitySignedResponseT3Diagonal_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (p : Paper.Overlap) (hp : p∈S)
    (a β : ℝ) (hβ : β≠0) :
    Tendsto (fun N=>cavitySignedResponseT3Diagonal D (FRSB.preservingMeasure μ S N) a β p)
      atTop (𝓝 (cavitySignedResponseT3Diagonal D μ a β p)) := by
  have hμ := FRSB.tendsto_preservingMeasure μ S
  have hV := (continuous_cavitySignedScalarVariance_profile β hβ).tendsto _ |>.comp
    (hμ.prodMk_nhds (tendsto_const_nhds (x:=p)))
  have hK := (continuous_cavitySignedScalarKernelOne_profile β hβ).tendsto _ |>.comp
    (hμ.prodMk_nhds (tendsto_const_nhds (x:=(p,p))))
  have hH := tendsto_cavitySignedResponseHessianTraceMoment_profile_level D hμ a
    (tendsto_const_nhds (x:=p))
  have hM := tendsto_cavitySignedResponseMixedHessianMoment_profile_level D hμ a
    (tendsto_const_nhds (x:=p)) (tendsto_const_nhds (x:=p))
  simp only [cavitySignedResponseT3Diagonal,cavitySignedScalarDiagonalCoefficient,
    FRSB.preservingMeasure_cdf_mass μ S _ p hp]
  exact (hV.mul hH).add (((hK.const_mul 4).add
    (hV.const_mul (2*(1-Paper.parisiCDF μ p)))).mul hM)

private theorem triple_norm (β : ℝ) (μ : Paper.ParisiMeasure) (p r : Paper.Overlap) :
    ‖cavitySignedScalarKernelTriple β μ (p,r) p‖≤1 := by
  have hs := cavitySignedScalarKernelTriple_square_le β μ p r p
  have hb : Gamma β μ (min p r)*Gamma β μ p≤1 :=
    (mul_le_mul (scalarGamma_le_one β μ (min p r) (min p r).property)
      (scalarGamma_le_one β μ p p.property) (scalarGamma_nonneg β μ p) zero_le_one).trans_eq
        (one_mul (1:ℝ))
  rw [Real.norm_eq_abs]
  nlinarith [hs.trans hb,sq_abs (cavitySignedScalarKernelTriple β μ (p,r) p),
    abs_nonneg (cavitySignedScalarKernelTriple β μ (p,r) p)]

theorem tendsto_cavitySignedResponseT3LastHessian_preserving (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (p : Paper.Overlap) (a β : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (hβ : β≠0) :
    Tendsto (fun N=>cavitySignedResponseT3LastHessian D (FRSB.preservingMeasure μ S N) a β p)
      atTop (𝓝 (cavitySignedResponseT3LastHessian D μ a β p)) := by
  simp only [cavitySignedResponseT3LastHessian]
  apply Tendsto.const_mul
  refine nativeStreaming_free_integral_tendsto μ S hzero a ha hfloor
    (fun N r=>cavitySignedScalarKernelTriple β (FRSB.preservingMeasure μ S N) (p,r) p*
      cavitySignedResponseMixedHessianMoment D (FRSB.preservingMeasure μ S N) a r p)
    (fun r=>cavitySignedScalarKernelTriple β μ (p,r) p*
      cavitySignedResponseMixedHessianMoment D μ a r p) ?_
    1 (by norm_num) ?_ ?_
  · intro N
    have hKmap : Measurable (fun r : Paper.Overlap=>((p,r),p)) :=
      (measurable_const.prodMk measurable_id).prodMk measurable_const
    have hMmap : Measurable (fun r : Paper.Overlap=>(r,p)) := measurable_id.prodMk measurable_const
    have hK := (continuous_cavitySignedScalarKernelTriple β hβ
      (FRSB.preservingMeasure μ S N)).measurable.comp hKmap
    have hM := (measurable_cavitySignedResponseMixedHessianMoment D
      (FRSB.preservingMeasure μ S N) a).comp hMmap
    dsimp only [Function.comp_def] at hK hM
    exact hK.mul hM
  · intro N r
    rw [←Real.norm_eq_abs,norm_mul]
    exact (mul_le_mul (triple_norm β _ p r)
      (norm_cavitySignedResponseMixedHessianMoment_le D _ a r p)
      (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  · intro r
    have hμ := FRSB.tendsto_preservingMeasure μ S
    have hr := FRSB.tendsto_preservingRound S r
    have hK := ((continuous_cavitySignedScalarKernelTriple_profile β hβ).tendsto (μ,((p,r),p))).comp
      (hμ.prodMk_nhds (((tendsto_const_nhds (x:=p)).prodMk_nhds hr).prodMk_nhds
        (tendsto_const_nhds (x:=p))))
    have hM := tendsto_cavitySignedResponseMixedHessianMoment_profile_level D hμ a hr
      (tendsto_const_nhds (x:=p))
    dsimp only [Function.comp_def] at hK
    exact hK.mul hM

end QuantitativeFollowup
