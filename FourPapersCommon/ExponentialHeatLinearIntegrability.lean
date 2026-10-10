module
public import FourPapersCommon.GaussianSelectedHeatIntegrability

@[expose] public section

/-! Exponential jet bounds give actual Gaussian integrability after any
fixed linear map, including degenerate coordinate clocks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ContDiff BigOperators
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem integrable_parameter_fderiv_linear (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (l u b : ℝ) (hb : b∈Ioo l u)
    (hF : ExponentialSmoothOn F ((Ioo l u)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (S : EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι) :
    Integrable (fun z=>fderiv ℝ F (b,S z) (1,0)) (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨B,K,hB,hK,h0,h1,h2⟩:=hF.parameter_heat_bounds F l u
  have hm : Measurable (fun z=>fderiv ℝ F (b,S z) (1,0)) := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    exact ((ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(b,S w))
      (g:=fderiv ℝ F) ((hF.smooth _ ⟨hb,mem_univ _⟩).fderiv_right (m:=∞) (by simp)).continuousAt
        (continuous_const.prodMk S.continuous).continuousAt).clm_apply continuous_const.continuousAt)
  apply integrable_gaussian_exponential_bound _ _ hm B (K*‖S‖) hB
  intro z
  calc
    _≤‖fderiv ℝ F (b,S z)‖*‖((1:ℝ),(0 : EuclideanSpace ℝ ι))‖:=
      (fderiv ℝ F (b,S z)).le_opNorm _
    _≤B*Real.exp (K*‖S z‖):=by
      simp only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,mul_one]
      exact h1 b hb _
    _≤_:=by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
      exact (mul_le_mul_of_nonneg_left (S.le_opNorm z) hK).trans_eq (by ring)

theorem integrable_parameter_hessian_linear_basis (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (l u b : ℝ) (hb : b∈Ioo l u)
    (hF : ExponentialSmoothOn F ((Ioo l u)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (S : EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι) (e : ι) :
    Integrable (fun z=>fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (S z)
      (EuclideanSpace.basisFun ι ℝ e) (EuclideanSpace.basisFun ι ℝ e))
        (stdGaussian (EuclideanSpace ℝ ι)) := by
  obtain ⟨B,K,hB,hK,h0,h1,h2⟩:=hF.parameter_heat_bounds F l u
  have hG : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ ι=>F (b,y)):=
    contDiff_iff_contDiffAt.mpr fun y=>
      ContDiffAt.comp (f:=fun z : EuclideanSpace ℝ ι=>(b,z)) (g:=F) y
        (hF.smooth (b,y) ⟨hb,mem_univ y⟩) (by fun_prop)
  have hDG : ContDiff ℝ 1 (fderiv ℝ (fun y : EuclideanSpace ℝ ι=>F (b,y))):=
    (hG.of_le (by norm_num) : ContDiff ℝ 2 _).fderiv_right (by norm_num)
  have hm : Measurable (fun z=>fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (S z)
      (EuclideanSpace.basisFun ι ℝ e) (EuclideanSpace.basisFun ι ℝ e)):=
    (((hDG.continuous_fderiv (by norm_num)).comp S.continuous).clm_apply
      continuous_const |>.clm_apply continuous_const).measurable
  apply integrable_gaussian_exponential_bound _ _ hm B (K*‖S‖) hB
  intro z
  calc
    _≤‖fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (S z) (EuclideanSpace.basisFun ι ℝ e)‖*
        ‖EuclideanSpace.basisFun ι ℝ e‖:=
      (fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (S z) (EuclideanSpace.basisFun ι ℝ e)).le_opNorm _
    _≤B*Real.exp (K*‖S z‖):=by
      rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one]
      exact ((fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (S z)).le_opNorm _).trans
        (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one];exact h2 b hb _)
    _≤_:=by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
      exact (mul_le_mul_of_nonneg_left (S.le_opNorm z) hK).trans_eq (by ring)

end FourPapersCommon
