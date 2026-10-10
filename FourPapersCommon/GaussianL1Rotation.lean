module
public import FourPapersCommon.GaussianAbsoluteMoment

@[expose] public section

/-! Rotation and projection estimates for the actual finite-dimensional
standard Gaussian. No dimension-dependent Cauchy--Schwarz replacement is
used: the inner Gaussian absolute moment is evaluated exactly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1500000
variable {ι:Type*} [Fintype ι]

@[simp] theorem SYK_standardGaussian_eq_stdGaussian :
    SYK.standardGaussianMeasureOnEuclidean ι=stdGaussian (EuclideanSpace ℝ ι) :=
  map_pi_eq_stdGaussian

private theorem continuous_gradient_of_contDiff (g:EuclideanSpace ℝ ι→ℝ)
    (hg:ContDiff ℝ 1 g) : Continuous (gradient g) := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
    (hg.continuous_fderiv (by norm_num))

theorem integral_abs_inner_gradient_gaussian (g:EuclideanSpace ℝ ι→ℝ)
    (hg:ContDiff ℝ 1 g) (M:ℝ) (hM:∀x,‖gradient g x‖≤M) :
    (∫ p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι,|inner ℝ (gradient g p.1) p.2|
      ∂(SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean ι))=
      Real.sqrt (2/Real.pi)*(∫ x,‖gradient g x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  let μ:=SYK.standardGaussianMeasureOnEuclidean ι
  have hMc : 0≤M:=(norm_nonneg (gradient g 0)).trans (hM 0)
  have hgrad:=continuous_gradient_of_contDiff g hg
  have hi:Integrable (fun p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι=>
      |inner ℝ (gradient g p.1) p.2|) (μ.prod μ) := by
    apply ((IsGaussian.integrable_id (μ:=μ)).norm.comp_snd μ).const_mul M |>.mono'
      (by fun_prop)
    filter_upwards with p
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hM p.1) (norm_nonneg _))
  rw [integral_prod _ hi]
  simp_rw [show μ=stdGaussian (EuclideanSpace ℝ ι) from SYK_standardGaussian_eq_stdGaussian,
    integral_abs_stdGaussian_inner,integral_const_mul]
  rw [SYK_standardGaussian_eq_stdGaussian]

theorem integral_abs_inner_gradient_rotation (g:EuclideanSpace ℝ ι→ℝ)
    (hg:ContDiff ℝ 1 g) (M:ℝ) (hM:∀x,‖gradient g x‖≤M) (θ:ℝ) :
    (∫ p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι,
      |inner ℝ (gradient g (Real.cos θ • p.1+Real.sin θ • p.2))
        (-Real.sin θ • p.1+Real.cos θ • p.2)|
      ∂(SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean ι))=
      Real.sqrt (2/Real.pi)*(∫ x,‖gradient g x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hgrad:=continuous_gradient_of_contDiff g hg
  have hmap: ((SYK.standardGaussianMeasureOnEuclidean ι).prod
      (SYK.standardGaussianMeasureOnEuclidean ι)).map (ContinuousLinearMap.rotation θ)=
      (SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean ι) :=
    (SYK.rotation_measurePreserving θ).map_eq
  have hh:=integral_map (ContinuousLinearMap.rotation θ).continuous.aemeasurable
    (show AEStronglyMeasurable (fun p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι=>
      |inner ℝ (gradient g p.1) p.2|) (((SYK.standardGaussianMeasureOnEuclidean ι).prod
      (SYK.standardGaussianMeasureOnEuclidean ι)).map (ContinuousLinearMap.rotation θ)) from by fun_prop)
  rw [hmap] at hh
  have he:= (hh.symm).trans (integral_abs_inner_gradient_gaussian g hg M hM)
  simpa only [ContinuousLinearMap.rotation_apply] using he

end FourPapersCommon
