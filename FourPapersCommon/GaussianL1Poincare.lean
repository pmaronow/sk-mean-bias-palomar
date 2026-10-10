module
public import FourPapersCommon.GaussianL1Rotation

@[expose] public section

/-! Dimension-independent Gaussian L¹ Poincaré from the actual Gaussian
rotation path and the exact absolute projection moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace NNReal
namespace FourPapersCommon
set_option maxHeartbeats 2000000
variable {ι:Type*} [Fintype ι]

private def rotationGradientAbs (g:EuclideanSpace ℝ ι→ℝ)
    (p:(EuclideanSpace ℝ ι×EuclideanSpace ℝ ι)×ℝ) : ℝ :=
  |inner ℝ (gradient g (Real.cos p.2 • p.1.1+Real.sin p.2 • p.1.2))
    (-Real.sin p.2 • p.1.1+Real.cos p.2 • p.1.2)|

private theorem integrable_rotationGradientAbs (g:EuclideanSpace ℝ ι→ℝ)
    (hg:ContDiff ℝ 1 g) (M:ℝ) (hM:∀x,‖gradient g x‖≤M) :
    Integrable (rotationGradientAbs g)
      (((SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean ι)).prod
        (volume.restrict (Ioc 0 (Real.pi/2)))) := by
  let μ:=SYK.standardGaussianMeasureOnEuclidean ι
  have hMc : 0≤M:=(norm_nonneg (gradient g 0)).trans (hM 0)
  have hgrad:Continuous (gradient g):=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ ι)).symm.continuous.comp
      (hg.continuous_fderiv (by norm_num))
  have hbase : Integrable (fun p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι=>
      M*(‖p.1‖+‖p.2‖)) (μ.prod μ) :=
    (((IsGaussian.integrable_id (μ:=μ)).norm.comp_fst μ).add
      ((IsGaussian.integrable_id (μ:=μ)).norm.comp_snd μ)).const_mul M
  apply (hbase.comp_fst (volume.restrict (Ioc 0 (Real.pi/2)))).mono' (by
    unfold rotationGradientAbs
    fun_prop)
  filter_upwards with p
  unfold rotationGradientAbs
  rw [Real.norm_eq_abs,abs_abs]
  apply (abs_real_inner_le_norm _ _).trans
  apply (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)).trans
  apply mul_le_mul_of_nonneg_left _ hMc
  calc
    ‖-Real.sin p.2 • p.1.1+Real.cos p.2 • p.1.2‖≤
        |Real.sin p.2| * ‖p.1.1‖+|Real.cos p.2| * ‖p.1.2‖ := by
      simpa only [norm_smul,Real.norm_eq_abs,abs_neg] using norm_add_le
        (-Real.sin p.2 • p.1.1) (Real.cos p.2 • p.1.2)
    _≤‖p.1.1‖+‖p.1.2‖ := by
      exact add_le_add (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (Real.abs_sin_le_one p.2) (norm_nonneg p.1.1))
        (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (Real.abs_cos_le_one p.2) (norm_nonneg p.1.2))

private theorem gaussian_rotation_total_abs (g:EuclideanSpace ℝ ι→ℝ)
    (hg:ContDiff ℝ 1 g) (M:ℝ) (hM:∀x,‖gradient g x‖≤M) :
    (∫ p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι,
      (∫ θ in Ioc 0 (Real.pi/2),rotationGradientAbs g (p,θ))
      ∂(SYK.standardGaussianMeasureOnEuclidean ι).prod (SYK.standardGaussianMeasureOnEuclidean ι))=
      Real.sqrt (Real.pi/2)*(∫ x,‖gradient g x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hf:=integrable_rotationGradientAbs g hg M hM
  rw [integral_integral_swap (f:=fun p θ=>rotationGradientAbs g (p,θ)) hf]
  have hp:0≤Real.pi/2:=by positivity
  simp_rw [rotationGradientAbs,integral_abs_inner_gradient_rotation g hg M hM]
  rw [←intervalIntegral.integral_of_le hp,intervalIntegral.integral_const]
  simp only [sub_zero,smul_eq_mul]
  have hc : Real.pi/2*Real.sqrt (2/Real.pi)=Real.sqrt (Real.pi/2) := by
    have h1:=Real.sq_sqrt (show 0≤2/Real.pi by positivity)
    have h2:=Real.sq_sqrt (show 0≤Real.pi/2 by positivity)
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
    rw [mul_pow,h1,h2]
    field_simp
  rw [←mul_assoc,hc]

/-- Gaussian L¹ inequality with the literal sharp rotation constant √(π/2).
The gradient bound ensures every integral/Fubini passage is genuine. -/
theorem gaussian_L1_poincare (g:EuclideanSpace ℝ ι→ℝ)
    (hg:ContDiff ℝ 1 g) (M:ℝ) (hM:∀x,‖gradient g x‖≤M) :
    (∫ x,|g x-(∫ y,g y ∂SYK.standardGaussianMeasureOnEuclidean ι)|
      ∂SYK.standardGaussianMeasureOnEuclidean ι)≤
      Real.sqrt (Real.pi/2)*(∫ x,‖gradient g x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  let μ:=SYK.standardGaussianMeasureOnEuclidean ι
  have hMc : 0≤M:=(norm_nonneg (gradient g 0)).trans (hM 0)
  have hgi:Integrable g μ := by
    apply ((integrable_const |g 0|).add ((IsGaussian.integrable_id (μ:=μ)).norm.const_mul M)).mono'
      hg.continuous.aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs,Pi.add_apply,id_eq] using SYK.contDiff_abs_le_of_gradient_le g M hMc hg hM x
  have hpair : Integrable (fun p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι=>|g p.1-g p.2|) (μ.prod μ) :=
    (hgi.comp_fst μ |>.sub (hgi.comp_snd μ)).abs
  have hcenter:Integrable (fun x:EuclideanSpace ℝ ι=>|g x-(∫y,g y∂μ)|) μ:=
    (hgi.sub (integrable_const _)).abs
  have hrotation:=integrable_rotationGradientAbs g hg M hM
  have hrotintegral:=hrotation.integral_prod_left
  have hpoint (p:EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) :
      |g p.1-g p.2|≤∫ θ in Ioc 0 (Real.pi/2),rotationGradientAbs g (p,θ) := by
    rw [SYK.gaussian_path_ftc g hg p.1 p.2,abs_neg]
    have h:=intervalIntegral.abs_integral_le_integral_abs (μ:=volume) (by positivity : (0:ℝ)≤Real.pi/2)
      (f:=fun θ=>inner ℝ (gradient g (Real.cos θ • p.1+Real.sin θ • p.2))
        (-Real.sin θ • p.1+Real.cos θ • p.2))
    simpa only [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤Real.pi/2),
      rotationGradientAbs] using h
  have hJ (x:EuclideanSpace ℝ ι) : |g x-(∫y,g y∂μ)|≤∫y,|g x-g y|∂μ := by
    have he : g x-(∫y,g y∂μ)=∫y,g x-g y∂μ := by
      rw [integral_sub (integrable_const _) hgi,integral_const,probReal_univ,one_smul]
    rw [he]
    exact abs_integral_le_integral_abs
  apply (integral_mono hcenter hpair.integral_prod_left hJ).trans
  rw [←integral_prod _ hpair]
  exact (integral_mono hpair hrotintegral hpoint).trans_eq
    (gaussian_rotation_total_abs g hg M hM)

end FourPapersCommon
