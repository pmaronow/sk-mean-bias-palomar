module
public import FourPapersCommon.ExponentialParameterHeatBounds
public import FourPapersCommon.GaussianSelectedParameterHeat

@[expose] public section

/-! Integrability of the genuine selected-coordinate moving heat generator
from exponential jet bounds. This permits actual probability normalization. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ContDiff Topology
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def gaussianSelectedHeatGenerator (p : ι→Bool) (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (b : ℝ) (y : EuclideanSpace ℝ ι) : ℝ :=
  fderiv ℝ F (b,y) (1,0)+(1/2:ℝ)*∑i,if p i then
    fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y
      (EuclideanSpace.basisFun _ ℝ i) (EuclideanSpace.basisFun _ ℝ i) else 0

theorem continuous_gaussianSelectedHeatGenerator (p : ι→Bool) (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (l u b : ℝ) (hb : b∈Ioo l u)
    (hF : ContDiffOn ℝ ∞ F ((Ioo l u)×ˢ(univ : Set (EuclideanSpace ℝ ι)))) :
    Continuous (gaussianSelectedHeatGenerator p F b) := by
  have hAt (y : EuclideanSpace ℝ ι) : ContDiffAt ℝ ∞ F (b,y):=
    hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hb,mem_univ y⟩)
  have hG : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ ι=>F (b,y)):=
    contDiff_iff_contDiffAt.mpr fun y=>
      ContDiffAt.comp (f:=fun z : EuclideanSpace ℝ ι=>(b,z)) (g:=F) y (hAt y) (by fun_prop)
  have hP : Continuous (fun y : EuclideanSpace ℝ ι=>fderiv ℝ F (b,y) (1,0)):=by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ((ContinuousAt.comp (f:=fun z : EuclideanSpace ℝ ι=>(b,z)) (g:=fderiv ℝ F)
      ((hAt y).fderiv_right (m:=∞) (by simp)).continuousAt
        (continuous_const.prodMk continuous_id).continuousAt).clm_apply continuous_const.continuousAt)
  have hDG : ContDiff ℝ 1 (fderiv ℝ (fun y : EuclideanSpace ℝ ι=>F (b,y))):=
    (hG.of_le (by norm_num) : ContDiff ℝ 2 _).fderiv_right (by norm_num)
  unfold gaussianSelectedHeatGenerator
  apply hP.add
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i _
  by_cases hi:p i=true
  · simp only [if_pos hi]
    exact ((hDG.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  · simp only [if_neg hi]
    exact continuous_const

theorem integrable_gaussianSelectedHeatGenerator (p : ι→Bool) (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (l u b : ℝ) (hl : 0<l) (hb : b∈Ioo l u)
    (hF : ExponentialSmoothOn F ((Ioo l u)×ˢ(univ : Set (EuclideanSpace ℝ ι)))) :
    Integrable (fun z : EuclideanSpace ℝ ι=>
      gaussianSelectedHeatGenerator p F b (gaussianSelectedScale p b z))
        (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨B,K,hB,hK,h0,h1,h2⟩:=hF.parameter_heat_bounds F l u
  let A:ℝ:=(Fintype.card ι:ℝ)*(1+Real.sqrt b)
  have hP : Integrable (fun z : EuclideanSpace ℝ ι=>fderiv ℝ F (b,gaussianSelectedScale p b z) (1,0))
      (stdGaussian (EuclideanSpace ℝ ι)):=by
    have hm : Measurable (fun z : EuclideanSpace ℝ ι=>fderiv ℝ F (b,gaussianSelectedScale p b z) (1,0)):=by
      have hAt (y : EuclideanSpace ℝ ι) := hF.smooth (b,y) ⟨hb,mem_univ y⟩
      apply Continuous.measurable
      apply continuous_iff_continuousAt.mpr
      intro z
      exact ((ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(b,gaussianSelectedScale p b w))
        (g:=fderiv ℝ F) ((hAt _).fderiv_right (m:=∞) (by simp)).continuousAt
          (continuous_const.prodMk (gaussianSelectedScale p b).continuous).continuousAt).clm_apply
            continuous_const.continuousAt)
    apply integrable_gaussian_exponential_bound _ _ hm B (K*A) hB
    intro z
    calc
      _≤‖fderiv ℝ F (b,gaussianSelectedScale p b z)‖*‖((1:ℝ),(0 : EuclideanSpace ℝ ι))‖:=
        (fderiv ℝ F (b,gaussianSelectedScale p b z)).le_opNorm _
      _≤B*Real.exp (K*‖gaussianSelectedScale p b z‖):=by
        simp only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,mul_one]
        exact h1 b hb _
      _≤B*Real.exp ((K*A)*‖z‖):=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p b b le_rfl z) hK).trans_eq (by ring)
  have hG : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ ι=>F (b,y)):=
    contDiff_iff_contDiffAt.mpr fun y=>
      ContDiffAt.comp (f:=fun z : EuclideanSpace ℝ ι=>(b,z)) (g:=F) y
        (hF.smooth (b,y) ⟨hb,mem_univ y⟩) (by fun_prop)
  have hDG : ContDiff ℝ 1 (fderiv ℝ (fun y : EuclideanSpace ℝ ι=>F (b,y))):=
    (hG.of_le (by norm_num) : ContDiff ℝ 2 _).fderiv_right (by norm_num)
  have hH (i : ι) : Integrable (fun z : EuclideanSpace ℝ ι=>
      if p i then fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (gaussianSelectedScale p b z)
        (EuclideanSpace.basisFun _ ℝ i) (EuclideanSpace.basisFun _ ℝ i) else 0)
        (stdGaussian (EuclideanSpace ℝ ι)):=by
    by_cases hi:p i=true
    · simp only [if_pos hi]
      have hm : Measurable (fun z : EuclideanSpace ℝ ι=>
          fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (gaussianSelectedScale p b z)
            (EuclideanSpace.basisFun _ ℝ i) (EuclideanSpace.basisFun _ ℝ i)):=
        ((((hDG.continuous_fderiv (by norm_num)).comp (gaussianSelectedScale p b).continuous).clm_apply
        continuous_const).clm_apply continuous_const).measurable
      apply integrable_gaussian_exponential_bound _ _ hm B (K*A) hB
      intro z
      calc
        _≤‖fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (gaussianSelectedScale p b z)‖*
          ‖EuclideanSpace.basisFun _ ℝ i‖*‖EuclideanSpace.basisFun _ ℝ i‖:=by
          exact ((fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (gaussianSelectedScale p b z)
            (EuclideanSpace.basisFun _ ℝ i)).le_opNorm _).trans
              (mul_le_mul_of_nonneg_right
                ((fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (gaussianSelectedScale p b z)).le_opNorm _)
                  (norm_nonneg _))
        _≤B*Real.exp (K*‖gaussianSelectedScale p b z‖):=by
          rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one,mul_one]
          exact h2 b hb _
        _≤B*Real.exp ((K*A)*‖z‖):=by
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
          exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p b b le_rfl z) hK).trans_eq (by ring)
    · simp only [if_neg hi]
      exact integrable_const 0
  exact hP.add ((integrable_finsetSum _ (fun i _=>hH i)).const_mul (1/2))

end FourPapersCommon
