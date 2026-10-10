module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileGradientValues
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileHessianMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseProfileScalarKernels
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals
public import QuantitativeFollowup.FollowupCavitySignedResponseNativeEstimate

@[expose] public section

/-! Atom-preserving strict-future signed-gradient integration. The strict
mask is retained exactly at every prescribed start, including its atom;
no continuity of a strict indicator is used. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB Paper
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 950000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private def scoreOverlapMoment (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a : ℝ) (p l : Paper.Overlap) : ℝ :=
  ∫z,cavitySignedResponseScore D μ a p z*cavitySignedResponseSelfOverlap D μ l z.1
    ∂anisotropicMeasureSpinPathLaw D μ a

private theorem scoreOverlapMoment_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (scoreOverlapMoment D μ a p) := by
  have hAmap : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      (z.1,z.2.1)) := measurable_fst.prodMk measurable_snd.fst
  have hA := (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hAmap
  have hm := ((measurable_cavitySignedResponseScore D μ a p).comp measurable_snd).mul hA
  have hi := hm.stronglyMeasurable.integral_prod_right'
    (ν:=anisotropicMeasureSpinPathLaw D μ a)
  change Measurable (fun l=>∫z,cavitySignedResponseScore D μ a p z*
    cavitySignedResponseSelfOverlap D μ l z.1 ∂anisotropicMeasureSpinPathLaw D μ a)
  dsimp only [Function.comp_def] at hi
  exact hi.measurable

private theorem scoreOverlapMoment_norm_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (p l : Paper.Overlap) :
    ‖scoreOverlapMoment D μ a p l‖≤4 := by
  have hb (z : AnisotropicDisorderBrownianSample n×Configuration n) :
      ‖cavitySignedResponseScore D μ a p z*cavitySignedResponseSelfOverlap D μ l z.1‖≤4 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_cavitySignedResponseScore_le D μ a ha p z)
      (norm_cavitySignedResponseSelfOverlap_le D μ l z.1)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  unfold scoreOverlapMoment
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=anisotropicMeasureSpinPathLaw D μ a) (.of_forall hb)

private theorem strictGradient_score (D : AnisotropicSpinModel n) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (a β : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (p l : Paper.Overlap) :
    cavitySignedScalarStrictFutureKernel β μ p l*cavitySignedResponseFutureGradient D μ a p l=
      cavitySignedScalarStrictFutureKernel β μ p l*
        (2*cavitySignedResponseMixedHessianMoment D μ a p l+scoreOverlapMoment D μ a p l) := by
  by_cases hpl : p<l
  · rw [cavitySignedResponseFutureGradient_eq_score D hn μ a ha hfloor p l hpl.le]
    rfl
  · simp only [cavitySignedScalarStrictFutureKernel,if_neg hpl,zero_mul]

theorem measurable_cavitySignedResponseStrictGradient (D : AnisotropicSpinModel n) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (a β : ℝ) (hβ : β≠0) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (p : Paper.Overlap) :
    Measurable (fun l=>cavitySignedScalarStrictFutureKernel β μ p l*
      cavitySignedResponseFutureGradient D μ a p l) := by
  simp_rw [strictGradient_score D hn μ a β ha hfloor p]
  exact ((measurable_cavitySignedScalarStrictFutureKernel β hβ μ).comp
    (measurable_const.prodMk measurable_id)).mul
    ((((measurable_cavitySignedResponseMixedHessianMoment D μ a).comp
      (measurable_const.prodMk measurable_id)).const_mul 2).add
      (scoreOverlapMoment_measurable D μ a p))

private theorem strict_kernel_norm (β : ℝ) (μ : Paper.ParisiMeasure) (p l : Paper.Overlap) :
    ‖cavitySignedScalarStrictFutureKernel β μ p l‖≤1 := by
  have hb : Gamma β μ p*Gamma β μ l≤1 :=
    (mul_le_mul (scalarGamma_le_one β μ p p.property)
      (scalarGamma_le_one β μ l l.property) (scalarGamma_nonneg β μ l) zero_le_one).trans_eq (by norm_num)
  have hs := (cavitySignedScalarStrictFutureKernel_square_le β μ p l).trans hb
  rw [Real.norm_eq_abs]
  nlinarith [sq_abs (cavitySignedScalarStrictFutureKernel β μ p l),
    abs_nonneg (cavitySignedScalarStrictFutureKernel β μ p l)]

theorem norm_cavitySignedResponseStrictGradient_le (D : AnisotropicSpinModel n) (hn : 0<n)
    (μ : Paper.ParisiMeasure) (a β : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (p l : Paper.Overlap) :
    ‖cavitySignedScalarStrictFutureKernel β μ p l*cavitySignedResponseFutureGradient D μ a p l‖≤6 := by
  rw [strictGradient_score D hn μ a β ha hfloor p l,norm_mul]
  have hB : ‖2*cavitySignedResponseMixedHessianMoment D μ a p l+scoreOverlapMoment D μ a p l‖≤6 :=
    (norm_add_le _ _).trans ((add_le_add
      ((norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left
        (norm_cavitySignedResponseMixedHessianMoment_le D μ a p l) (norm_nonneg (2:ℝ))))
      (scoreOverlapMoment_norm_le D μ a ha p l)).trans_eq (by norm_num))
  exact (mul_le_mul (strict_kernel_norm β μ p l) hB (norm_nonneg _) zero_le_one).trans_eq (by norm_num)

theorem tendsto_cavitySignedResponseStrictGradientIntegral_preserving
    (D : AnisotropicSpinModel n) (hn : 0<n) (μ : Paper.ParisiMeasure)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S) (p : Paper.Overlap) (hp : p∈S)
    (a β : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : μ∈scalarFloor a) (hβ : β≠0) :
    Tendsto (fun N=>∫l,cavitySignedScalarStrictFutureKernel β (FRSB.preservingMeasure μ S N) p l*
      cavitySignedResponseFutureGradient D (FRSB.preservingMeasure μ S N) a p l
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫l,cavitySignedScalarStrictFutureKernel β μ p l*cavitySignedResponseFutureGradient D μ a p l
        ∂parisiFreeMeasure μ a)) := by
  refine nativeStreaming_free_integral_tendsto μ S hzero a ha hfloor
    (fun N l=>cavitySignedScalarStrictFutureKernel β (FRSB.preservingMeasure μ S N) p l*
      cavitySignedResponseFutureGradient D (FRSB.preservingMeasure μ S N) a p l)
    (fun l=>cavitySignedScalarStrictFutureKernel β μ p l*
      cavitySignedResponseFutureGradient D μ a p l) ?_ 6 (by norm_num) ?_ ?_
  · intro N
    exact measurable_cavitySignedResponseStrictGradient D hn _ a β hβ ha
      (nativeStreaming_preserving_floor μ S hzero a hfloor N) p
  · intro N l
    simpa only [←Real.norm_eq_abs] using norm_cavitySignedResponseStrictGradient_le D hn _ a β ha
      (nativeStreaming_preserving_floor μ S hzero a hfloor N) p l
  · intro l
    have he (N : ℕ) : p<FRSB.preservingRound S N l ↔p<l :=
      FRSB.preservingRound_gt_iff S N l p hp
    by_cases hpl : p<l
    · have hk : Tendsto (fun N=>cavitySignedScalarStrictFutureKernel β (FRSB.preservingMeasure μ S N) p
          (FRSB.preservingRound S N l)) atTop (𝓝 (cavitySignedScalarStrictFutureKernel β μ p l)) := by
        have hmap : Tendsto (fun N=>(FRSB.preservingMeasure μ S N,
            (p,FRSB.preservingRound S N l))) atTop (𝓝 (μ,(p,l))) :=
          (FRSB.tendsto_preservingMeasure μ S).prodMk_nhds
            ((tendsto_const_nhds (x:=p)).prodMk_nhds (FRSB.tendsto_preservingRound S l))
        have hh := ((continuous_cavitySignedScalarFutureCovarianceKernel_profile β hβ).tendsto
          (μ,(p,l))).comp hmap
        dsimp only [Function.comp_def] at hh
        simpa only [cavitySignedScalarStrictFutureKernel,he,ite_eq_left hpl] using hh
      have hg := tendsto_cavitySignedResponseFutureGradient_profile_level D
        (q:=fun _ : ℕ=>p) (FRSB.tendsto_preservingMeasure μ S) a tendsto_const_nhds
        (FRSB.tendsto_preservingRound S l) (fun N=>((he N).mpr hpl).le) hpl.le
      exact hk.mul hg
    · simpa only [cavitySignedScalarStrictFutureKernel,he,if_neg hpl,zero_mul] using
        (tendsto_const_nhds (x:=(0:ℝ)))

end QuantitativeFollowup
