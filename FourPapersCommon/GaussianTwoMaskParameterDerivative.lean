module
public import FourPapersCommon.GaussianTwoMaskScaleBounds
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Differentiating an actual moving Gaussian test after selected-coordinate
scaling. All domination is proved from local exponential jet bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_gaussianTwoMask_parameter_integral (pR pP : ι→Bool) (d alpha : ℝ)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (l u lb ub b B K : ℝ)
    (ha : 0≤alpha) (hl : 0<l) (hlb : 0<lb) (hb : b∈Ioo l u)
    (hqb : ∀q∈Ioo l u,d-alpha*q∈Ioo lb ub) (hB : 0≤B) (hK : 0≤K)
    (hF : ContDiffOn ℝ ∞ F ((Ioo lb ub)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (h0 : ∀q∈Ioo lb ub,∀y,‖F (q,y)‖≤B*Real.exp (K*‖y‖))
    (h1 : ∀q∈Ioo lb ub,∀y,‖fderiv ℝ F (q,y)‖≤B*Real.exp (K*‖y‖)) :
    Integrable (fun z : EuclideanSpace ℝ ι=>fderiv ℝ F (d-alpha*b,gaussianTwoMaskScale pR pP d alpha b z)
      (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha b z)) (stdGaussian (EuclideanSpace ℝ ι)) ∧
    HasDerivAt (fun q=>∫z : EuclideanSpace ℝ ι,F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)
      ∂stdGaussian (EuclideanSpace ℝ ι))
      (∫z : EuclideanSpace ℝ ι,fderiv ℝ F (d-alpha*b,gaussianTwoMaskScale pR pP d alpha b z)
        (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha b z)∂stdGaussian (EuclideanSpace ℝ ι)) b := by
  let A : ℝ:=(Fintype.card ι:ℝ)*(1+Real.sqrt u+Real.sqrt ub)
  let C : ℝ:=(Fintype.card ι:ℝ)*(1/(2*Real.sqrt l)+alpha/(2*Real.sqrt lb))
  have hA : 0≤A:=by dsimp [A];positivity
  have hC : 0≤C:=by dsimp [C];positivity
  have hAt (q : ℝ) (hq : q∈Ioo l u) (y : EuclideanSpace ℝ ι) :
      ContDiffAt ℝ ∞ F (d-alpha*q,y):=hF.contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hqb q hq,mem_univ y⟩)
  have hmeas (q : ℝ) (hq : q∈Ioo l u) :
      Measurable (fun z : EuclideanSpace ℝ ι=>F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)):=by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    have hm : ContinuousAt (fun w : EuclideanSpace ℝ ι=>(d-alpha*q,gaussianTwoMaskScale pR pP d alpha q w)) z:=
      (continuous_const.prodMk (gaussianTwoMaskScale pR pP d alpha q).continuous).continuousAt
    exact ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(d-alpha*q,gaussianTwoMaskScale pR pP d alpha q w))
      (g:=F) (hAt q hq (gaussianTwoMaskScale pR pP d alpha q z)).continuousAt hm
  have hDmeas (q : ℝ) (hq : q∈Ioo l u) :
      Measurable (fun z : EuclideanSpace ℝ ι=>fderiv ℝ F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)
        (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha q z)):=by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    have hm : ContinuousAt (fun w : EuclideanSpace ℝ ι=>(d-alpha*q,gaussianTwoMaskScale pR pP d alpha q w)) z:=
      (continuous_const.prodMk (gaussianTwoMaskScale pR pP d alpha q).continuous).continuousAt
    have hdf := ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(d-alpha*q,gaussianTwoMaskScale pR pP d alpha q w))
      (g:=fderiv ℝ F)
      ((hAt q hq (gaussianTwoMaskScale pR pP d alpha q z)).fderiv_right (m:=∞) (by simp)).continuousAt hm
    exact hdf.clm_apply
        (continuous_const.prodMk (gaussianTwoMaskScaleDerivative pR pP d alpha q).continuous).continuousAt
  have hval (q : ℝ) (hq : q∈Ioo l u) (z : EuclideanSpace ℝ ι) :
      ‖F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)‖≤B*Real.exp ((K*A)*‖z‖):=by
    calc
      _≤B*Real.exp (K*‖gaussianTwoMaskScale pR pP d alpha q z‖):=h0 (d-alpha*q) (hqb q hq) _
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left
          (norm_gaussianTwoMaskScale_le pR pP d alpha q u ub hq.2.le (hqb q hq).2.le z) hK).trans_eq (by ring)
  have hder (q : ℝ) (hq : q∈Ioo l u) (z : EuclideanSpace ℝ ι) :
      HasDerivAt (fun r=>F (d-alpha*r,gaussianTwoMaskScale pR pP d alpha r z))
        (fderiv ℝ F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)
          (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha q z)) q:=by
    have hx : HasDerivAt (fun r=>(d-alpha*r,gaussianTwoMaskScale pR pP d alpha r z))
        (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha q z) q:=by
      convert (((hasDerivAt_const q d).sub ((hasDerivAt_id q).const_mul alpha)).prodMk
        (hasDerivAt_gaussianTwoMaskScale pR pP d alpha q (hl.trans hq.1)
          (hlb.trans (hqb q hq).1) z)) using 1 <;> simp
    exact ((hAt q hq _).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q hx
  have hdBound (q : ℝ) (hq : q∈Ioo l u) (z : EuclideanSpace ℝ ι) :
      ‖fderiv ℝ F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)
        (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha q z)‖≤
      B*(1+alpha+C)*Real.exp ((K*A+1)*‖z‖):=by
    have hn : ‖((-alpha:ℝ),gaussianTwoMaskScaleDerivative pR pP d alpha q z)‖≤(1+alpha+C)*(1+‖z‖):=by
      rw [Prod.norm_def,norm_neg,Real.norm_of_nonneg ha]
      apply max_le
      · nlinarith [norm_nonneg z]
      · exact (norm_gaussianTwoMaskScaleDerivative_le pR pP d alpha q l lb ha hl hlb hq.1.le (hqb q hq).1.le z).trans (by nlinarith [norm_nonneg z])
    have he : 1+‖z‖≤Real.exp ‖z‖:=by linarith [Real.add_one_le_exp ‖z‖]
    calc
      _≤‖fderiv ℝ F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)‖*
        ‖(-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha q z)‖:=
          (fderiv ℝ F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)).le_opNorm _
      _≤(B*Real.exp (K*‖gaussianTwoMaskScale pR pP d alpha q z‖))*((1+alpha+C)*(1+‖z‖)):=
        mul_le_mul (h1 (d-alpha*q) (hqb q hq) _) hn (norm_nonneg _) (by positivity)
      _≤(B*Real.exp ((K*A)*‖z‖))*((1+alpha+C)*Real.exp ‖z‖):=by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
          exact (mul_le_mul_of_nonneg_left
            (norm_gaussianTwoMaskScale_le pR pP d alpha q u ub hq.2.le (hqb q hq).2.le z) hK).trans_eq (by ring)
        · exact mul_le_mul_of_nonneg_left he (by positivity)
        · positivity
        · positivity
      _=_:=by
        rw [show (K*A+1)*‖z‖=K*A*‖z‖+‖z‖ by ring,Real.exp_add]
        ring
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=stdGaussian (EuclideanSpace ℝ ι)) (s:=Ioo l u)
    (F:=fun q z=>F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z))
    (F':=fun q z=>fderiv ℝ F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)
      (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha q z))
    (bound:=fun z=>B*(1+alpha+C)*Real.exp ((K*A+1)*‖z‖))
    (isOpen_Ioo.mem_nhds hb)
    (by filter_upwards [isOpen_Ioo.mem_nhds hb] with q hq;exact (hmeas q hq).aestronglyMeasurable)
    (integrable_gaussian_exponential_bound _ _ (hmeas b hb) B (K*A) hB (hval b hb))
    (hDmeas b hb).aestronglyMeasurable
    (.of_forall fun z q hq=>hdBound q hq z)
    ((integrable_exp_mul_norm_gaussian (stdGaussian (EuclideanSpace ℝ ι)) (K*A+1)).const_mul (B*(1+alpha+C)))
    (.of_forall fun z q hq=>hder q hq z)

end FourPapersCommon
