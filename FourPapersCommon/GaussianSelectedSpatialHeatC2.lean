module
public import QuantitativeFollowup.FollowupCavityRootNormalizerHeat
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Selected Gaussian heat for a genuine spatial C2 test, including
continuity at zero variance. No covariance-parameter smoothness is required. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 2200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gaussianSelectedSpatialHeat (p : ι→Bool) (F : EuclideanSpace ℝ ι→ℝ) (u : ℝ) : ℝ :=
  ∫z : EuclideanSpace ℝ ι,F (gaussianSelectedScale p u z) ∂stdGaussian (EuclideanSpace ℝ ι)

theorem continuous_gaussianSelectedScale_apply (p : ι→Bool) (z : EuclideanSpace ℝ ι) :
    Continuous (fun u : ℝ=>gaussianSelectedScale p u z) := by
  simp_rw [gaussianSelectedScale_apply]
  apply continuous_finsetSum
  intro i _
  by_cases hi : p i=true
  · simp only [hi,ite_true]
    fun_prop
  · simp only [if_neg hi,one_mul]
    exact continuous_const

theorem continuous_gaussianSelectedSpatialHeat (p : ι→Bool) (F : EuclideanSpace ℝ ι→ℝ)
    (hF : Continuous F) (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h0 : ∀y,‖F y‖ ≤ B*Real.exp (K*‖y‖)) :
    Continuous (gaussianSelectedSpatialHeat p F) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let A : ℝ := (Fintype.card ι:ℝ)*(1+Real.sqrt (u+1))
  apply continuousAt_of_dominated (bound:=fun z : EuclideanSpace ℝ ι=>B*Real.exp ((K*A)*‖z‖))
  · exact .of_forall fun v=>(hF.comp (gaussianSelectedScale p v).continuous).aestronglyMeasurable
  · have hv : ∀ᶠ v : ℝ in 𝓝 u,v<u+1 := Iio_mem_nhds (by linarith)
    filter_upwards [hv] with v hv
    exact .of_forall fun z=>by
      apply (h0 _).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
      exact (mul_le_mul_of_nonneg_left
        (norm_gaussianSelectedScale_le p v (u+1) hv.le z) hK).trans_eq (by ring)
  · exact (integrable_exp_mul_norm_gaussian (stdGaussian (EuclideanSpace ℝ ι)) (K*A)).const_mul B
  · exact .of_forall fun z=>(hF.comp (continuous_gaussianSelectedScale_apply p z)).continuousAt

theorem hasDerivAt_gaussianSelectedSpatialHeat (p : ι→Bool) (F : EuclideanSpace ℝ ι→ℝ)
    (hF : ContDiff ℝ 2 F) (B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (h0 : ∀y,‖F y‖ ≤ B*Real.exp (K*‖y‖))
    (h1 : ∀y,‖fderiv ℝ F y‖ ≤ B*Real.exp (K*‖y‖))
    (h2 : ∀y,‖fderiv ℝ (fderiv ℝ F) y‖ ≤ B*Real.exp (K*‖y‖))
    (u : ℝ) (hu : 0 < u) :
    HasDerivAt (gaussianSelectedSpatialHeat p F)
      ((1/2:ℝ)*∫z : EuclideanSpace ℝ ι,∑i,if p i then
        fderiv ℝ (fderiv ℝ F) (gaussianSelectedScale p u z)
          (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0
        ∂stdGaussian (EuclideanSpace ℝ ι)) u := by
  let l := u/2
  let r := u+1
  let A : ℝ := (Fintype.card ι:ℝ)*(1+Real.sqrt r)
  let C : ℝ := (Fintype.card ι:ℝ)/(2*Real.sqrt l)
  have hl : 0 < l := by dsimp only [l]; positivity
  have hub : u ∈ Ioo l r := by dsimp only [l,r]; constructor <;> linarith
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hm (v : ℝ) : Measurable (fun z : EuclideanSpace ℝ ι=>F (gaussianSelectedScale p v z)) :=
    (hF.continuous.comp (gaussianSelectedScale p v).continuous).measurable
  have hDm (v : ℝ) : Measurable (fun z : EuclideanSpace ℝ ι=>
      fderiv ℝ F (gaussianSelectedScale p v z) (gaussianSelectedScaleDerivative p v z)) :=
    (((hF.continuous_fderiv (by norm_num)).comp (gaussianSelectedScale p v).continuous).clm_apply
      (gaussianSelectedScaleDerivative p v).continuous).measurable
  have hval (z : EuclideanSpace ℝ ι) : ‖F (gaussianSelectedScale p u z)‖ ≤
      B*Real.exp ((K*A)*‖z‖) := by
    apply (h0 _).trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
    exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p u r hub.2.le z) hK).trans_eq (by ring)
  have hder (z : EuclideanSpace ℝ ι) (v : ℝ) (hv : v ∈ Ioo l r) :
      HasDerivAt (fun q=>F (gaussianSelectedScale p q z))
        (fderiv ℝ F (gaussianSelectedScale p v z) (gaussianSelectedScaleDerivative p v z)) v :=
    (hF.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt v
      (hasDerivAt_gaussianSelectedScale p v (hl.trans hv.1) z)
  have hdBound (z : EuclideanSpace ℝ ι) (v : ℝ) (hv : v ∈ Ioo l r) :
      ‖fderiv ℝ F (gaussianSelectedScale p v z) (gaussianSelectedScaleDerivative p v z)‖ ≤
        (B*C)*Real.exp ((K*A+1)*‖z‖) := by
    have he : ‖z‖ ≤ Real.exp ‖z‖ := by linarith [Real.add_one_le_exp ‖z‖]
    calc
      _ ≤ ‖fderiv ℝ F (gaussianSelectedScale p v z)‖*‖gaussianSelectedScaleDerivative p v z‖ :=
        (fderiv ℝ F _).le_opNorm _
      _ ≤ (B*Real.exp (K*‖gaussianSelectedScale p v z‖))*(C*‖z‖) :=
        mul_le_mul (h1 _) (norm_gaussianSelectedScaleDerivative_le p v l hl hv.1.le z)
          (norm_nonneg _) (by positivity)
      _ ≤ (B*Real.exp ((K*A)*‖z‖))*(C*Real.exp ‖z‖) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
          exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p v r hv.2.le z) hK).trans_eq (by ring)
        · exact mul_le_mul_of_nonneg_left he hC
        · positivity
        · positivity
      _ = _ := by
        rw [show (K*A+1)*‖z‖=(K*A)*‖z‖+‖z‖ by ring,Real.exp_add]
        ring
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=stdGaussian (EuclideanSpace ℝ ι)) (s:=Ioo l r)
    (F:=fun v z=>F (gaussianSelectedScale p v z))
    (F':=fun v z=>fderiv ℝ F (gaussianSelectedScale p v z) (gaussianSelectedScaleDerivative p v z))
    (bound:=fun z=>(B*C)*Real.exp ((K*A+1)*‖z‖))
    (isOpen_Ioo.mem_nhds hub) (.of_forall fun v=>(hm v).aestronglyMeasurable)
    (integrable_gaussian_exponential_bound _ _ (hm u) B (K*A) hB hval)
    (hDm u).aestronglyMeasurable (.of_forall hdBound)
    ((integrable_exp_mul_norm_gaussian (stdGaussian (EuclideanSpace ℝ ι)) (K*A+1)).const_mul (B*C))
    (.of_forall hder)).2
  rw [QuantitativeFollowup.gaussianSelected_integral_spatial_response p u hu F hF B K hB hK h1 h2] at hd
  exact hd

end FourPapersCommon
