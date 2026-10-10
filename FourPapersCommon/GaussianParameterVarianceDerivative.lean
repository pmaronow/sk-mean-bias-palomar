module
public import FourPapersCommon.GaussianSelectedCoordinateScale
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

theorem hasDerivAt_gaussianSelected_parameter_integral (p : ι→Bool)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (l u b B K : ℝ)
    (hl : 0<l) (hb : b∈Ioo l u) (hB : 0≤B) (hK : 0≤K)
    (hF : ContDiffOn ℝ ∞ F ((Ioo l u)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (h0 : ∀q∈Ioo l u,∀y,‖F (q,y)‖≤B*Real.exp (K*‖y‖))
    (h1 : ∀q∈Ioo l u,∀y,‖fderiv ℝ F (q,y)‖≤B*Real.exp (K*‖y‖)) :
    Integrable (fun z : EuclideanSpace ℝ ι=>fderiv ℝ F (b,gaussianSelectedScale p b z)
      (1,gaussianSelectedScaleDerivative p b z)) (stdGaussian (EuclideanSpace ℝ ι)) ∧
    HasDerivAt (fun q=>∫z : EuclideanSpace ℝ ι,F (q,gaussianSelectedScale p q z)
      ∂stdGaussian (EuclideanSpace ℝ ι))
      (∫z : EuclideanSpace ℝ ι,fderiv ℝ F (b,gaussianSelectedScale p b z)
        (1,gaussianSelectedScaleDerivative p b z)∂stdGaussian (EuclideanSpace ℝ ι)) b := by
  let A : ℝ:=(Fintype.card ι:ℝ)*(1+Real.sqrt u)
  let C : ℝ:=(Fintype.card ι:ℝ)/(2*Real.sqrt l)
  have hA : 0≤A:=by dsimp [A];positivity
  have hC : 0≤C:=by dsimp [C];positivity
  have hAt (q : ℝ) (hq : q∈Ioo l u) (y : EuclideanSpace ℝ ι) :
      ContDiffAt ℝ ∞ F (q,y):=hF.contDiffAt
        ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hq,mem_univ y⟩)
  have hmeas (q : ℝ) (hq : q∈Ioo l u) :
      Measurable (fun z : EuclideanSpace ℝ ι=>F (q,gaussianSelectedScale p q z)):=by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    have hm : ContinuousAt (fun w : EuclideanSpace ℝ ι=>(q,gaussianSelectedScale p q w)) z:=
      (continuous_const.prodMk (gaussianSelectedScale p q).continuous).continuousAt
    exact ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(q,gaussianSelectedScale p q w))
      (g:=F) (hAt q hq (gaussianSelectedScale p q z)).continuousAt hm
  have hDmeas (q : ℝ) (hq : q∈Ioo l u) :
      Measurable (fun z : EuclideanSpace ℝ ι=>fderiv ℝ F (q,gaussianSelectedScale p q z)
        (1,gaussianSelectedScaleDerivative p q z)):=by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    have hm : ContinuousAt (fun w : EuclideanSpace ℝ ι=>(q,gaussianSelectedScale p q w)) z:=
      (continuous_const.prodMk (gaussianSelectedScale p q).continuous).continuousAt
    have hdf := ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(q,gaussianSelectedScale p q w))
      (g:=fderiv ℝ F)
      ((hAt q hq (gaussianSelectedScale p q z)).fderiv_right (m:=∞) (by simp)).continuousAt hm
    exact hdf.clm_apply
        (continuous_const.prodMk (gaussianSelectedScaleDerivative p q).continuous).continuousAt
  have hval (q : ℝ) (hq : q∈Ioo l u) (z : EuclideanSpace ℝ ι) :
      ‖F (q,gaussianSelectedScale p q z)‖≤B*Real.exp ((K*A)*‖z‖):=by
    calc
      _≤B*Real.exp (K*‖gaussianSelectedScale p q z‖):=h0 q hq _
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left
          (norm_gaussianSelectedScale_le p q u hq.2.le z) hK).trans_eq (by ring)
  have hder (q : ℝ) (hq : q∈Ioo l u) (z : EuclideanSpace ℝ ι) :
      HasDerivAt (fun r=>F (r,gaussianSelectedScale p r z))
        (fderiv ℝ F (q,gaussianSelectedScale p q z)
          (1,gaussianSelectedScaleDerivative p q z)) q:=
    ((hAt q hq _).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt q
      ((hasDerivAt_id q).prodMk (hasDerivAt_gaussianSelectedScale p q (hl.trans hq.1) z))
  have hdBound (q : ℝ) (hq : q∈Ioo l u) (z : EuclideanSpace ℝ ι) :
      ‖fderiv ℝ F (q,gaussianSelectedScale p q z)
        (1,gaussianSelectedScaleDerivative p q z)‖≤
      B*(1+C)*Real.exp ((K*A+1)*‖z‖):=by
    have hn : ‖((1:ℝ),gaussianSelectedScaleDerivative p q z)‖≤(1+C)*(1+‖z‖):=by
      rw [Prod.norm_def,norm_one]
      apply max_le
      · nlinarith [norm_nonneg z]
      · exact (norm_gaussianSelectedScaleDerivative_le p q l hl hq.1.le z).trans (by nlinarith [norm_nonneg z])
    have he : 1+‖z‖≤Real.exp ‖z‖:=by linarith [Real.add_one_le_exp ‖z‖]
    calc
      _≤‖fderiv ℝ F (q,gaussianSelectedScale p q z)‖*
        ‖(1,gaussianSelectedScaleDerivative p q z)‖:=
          (fderiv ℝ F (q,gaussianSelectedScale p q z)).le_opNorm _
      _≤(B*Real.exp (K*‖gaussianSelectedScale p q z‖))*((1+C)*(1+‖z‖)):=
        mul_le_mul (h1 q hq _) hn (norm_nonneg _) (by positivity)
      _≤(B*Real.exp ((K*A)*‖z‖))*((1+C)*Real.exp ‖z‖):=by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
          exact (mul_le_mul_of_nonneg_left
            (norm_gaussianSelectedScale_le p q u hq.2.le z) hK).trans_eq (by ring)
        · exact mul_le_mul_of_nonneg_left he (by positivity)
        · positivity
        · positivity
      _=_:=by
        rw [show (K*A+1)*‖z‖=K*A*‖z‖+‖z‖ by ring,Real.exp_add]
        ring
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=stdGaussian (EuclideanSpace ℝ ι)) (s:=Ioo l u)
    (F:=fun q z=>F (q,gaussianSelectedScale p q z))
    (F':=fun q z=>fderiv ℝ F (q,gaussianSelectedScale p q z)
      (1,gaussianSelectedScaleDerivative p q z))
    (bound:=fun z=>B*(1+C)*Real.exp ((K*A+1)*‖z‖))
    (isOpen_Ioo.mem_nhds hb)
    (by filter_upwards [isOpen_Ioo.mem_nhds hb] with q hq;exact (hmeas q hq).aestronglyMeasurable)
    (integrable_gaussian_exponential_bound _ _ (hmeas b hb) B (K*A) hB (hval b hb))
    (hDmeas b hb).aestronglyMeasurable
    (.of_forall fun z q hq=>hdBound q hq z)
    ((integrable_exp_mul_norm_gaussian (stdGaussian (EuclideanSpace ℝ ι)) (K*A+1)).const_mul (B*(1+C)))
    (.of_forall fun z q hq=>hder q hq z)

end FourPapersCommon
