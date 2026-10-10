module
public import FourPapersCommon.GaussianSelectedParameterHeat

@[expose] public section

/-! Genuine integrability of coordinate-gradient moments under every
retained linear Gaussian realization with actual exponential jet bounds. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem integrable_gaussianLinear_coordinate_gradient
    (D : EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι)
    (F : EuclideanSpace ℝ ι→ℝ) (hF : ContDiff ℝ 2 F)
    (B K : ℝ) (hB : 0≤B) (hK : 0≤K)
    (h1 : ∀y,‖fderiv ℝ F y‖≤B*Real.exp (K*‖y‖)) (i : ι) :
    Integrable (fun z : EuclideanSpace ℝ ι=>z i*fderiv ℝ F (D z)
      (EuclideanSpace.basisFun ι ℝ i)) (stdGaussian (EuclideanSpace ℝ ι)) := by
  let A : ℝ:=‖D‖
  let T : EuclideanSpace ℝ ι→ℝ:=fun z=>fderiv ℝ F (D z)
    (EuclideanSpace.basisFun ι ℝ i)
  have hm : Measurable T:=
    (((hF.continuous_fderiv (by norm_num)).comp D.continuous).clm_apply
      continuous_const).measurable
  have hb (z : EuclideanSpace ℝ ι) : ‖T z‖≤B*Real.exp ((K*A)*‖z‖):=by
    calc
      _≤‖fderiv ℝ F (D z)‖*
        ‖EuclideanSpace.basisFun ι ℝ i‖:=
          (fderiv ℝ F (D z)).le_opNorm _
      _≤B*Real.exp (K*‖D z‖):=by
        rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one]
        exact h1 _
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left
          (D.le_opNorm z) hK).trans_eq (by ring)
  simpa only [EuclideanSpace.inner_basisFun_real,T] using
    integrable_inner_mul_gaussian_exponential_bound (stdGaussian (EuclideanSpace ℝ ι))
      T hm B (K*A) hB hb (EuclideanSpace.basisFun ι ℝ i)


end FourPapersCommon
