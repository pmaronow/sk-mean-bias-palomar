module
public import FourPapersCommon.GaussianSelectedParameterHeat

@[expose] public section

/-! Coordinate heat contraction for a genuine C² Gaussian test. This only
uses spatial C² regularity, so it applies to the constructed arbitrary-profile
potential without asserting smooth dependence on its covariance parameters. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon OverlapPaper
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianSelected_integral_spatial_response (p : ι→Bool) (u : ℝ) (hu : 0<u)
    (F : EuclideanSpace ℝ ι→ℝ) (hF : ContDiff ℝ 2 F) (B K : ℝ)
    (hB : 0≤B) (hK : 0≤K)
    (h1 : ∀y,‖fderiv ℝ F y‖≤B*Real.exp (K*‖y‖))
    (h2 : ∀y,‖fderiv ℝ (fderiv ℝ F) y‖≤B*Real.exp (K*‖y‖)) :
    (∫z : EuclideanSpace ℝ ι,fderiv ℝ F (gaussianSelectedScale p u z)
      (gaussianSelectedScaleDerivative p u z)∂stdGaussian (EuclideanSpace ℝ ι))=
      (1/2:ℝ)*∫z : EuclideanSpace ℝ ι,(∑i,if p i then
        fderiv ℝ (fderiv ℝ F) (gaussianSelectedScale p u z)
          (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0)
          ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let W:=fun i (z : EuclideanSpace ℝ ι)=>z i*fderiv ℝ F (gaussianSelectedScale p u z)
    (EuclideanSpace.basisFun ι ℝ i)
  let H:=fun i (z : EuclideanSpace ℝ ι)=>fderiv ℝ (fderiv ℝ F) (gaussianSelectedScale p u z)
    (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)
  let A : ℝ:=(Fintype.card ι:ℝ)*(1+Real.sqrt u)
  have hWi (i : ι) : Integrable (W i) (stdGaussian (EuclideanSpace ℝ ι)):=
    integrable_gaussianSelectedScale_coordinate_gradient p u F hF B K hB hK h1 i
  have hHi (i : ι) : Integrable (H i) (stdGaussian (EuclideanSpace ℝ ι)) := by
    have hDG : ContDiff ℝ 1 (fderiv ℝ F):=hF.fderiv_right (by norm_num)
    have hm : Measurable (H i):=
      (((hDG.continuous_fderiv (by norm_num)).comp (gaussianSelectedScale p u).continuous).clm_apply
        continuous_const |>.clm_apply continuous_const).measurable
    apply integrable_gaussian_exponential_bound _ _ hm B (K*A) hB
    intro z
    calc
      _≤‖fderiv ℝ (fderiv ℝ F) (gaussianSelectedScale p u z) (EuclideanSpace.basisFun ι ℝ i)‖*
        ‖EuclideanSpace.basisFun ι ℝ i‖:=
          (fderiv ℝ (fderiv ℝ F) (gaussianSelectedScale p u z) (EuclideanSpace.basisFun ι ℝ i)).le_opNorm _
      _≤B*Real.exp (K*‖gaussianSelectedScale p u z‖):=by
        rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one]
        exact ((fderiv ℝ (fderiv ℝ F) (gaussianSelectedScale p u z)).le_opNorm
          (EuclideanSpace.basisFun ι ℝ i)).trans
            (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one];exact h2 _)
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p u u le_rfl z) hK).trans_eq (by ring)
  have hIfHi (i : ι) : Integrable (fun z=>if p i then H i z else 0)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    cases hi:p i <;> simp only [hi,Bool.false_eq_true,ite_false,ite_true]
    · exact integrable_const 0
    · exact hHi i
  have hraw (z : EuclideanSpace ℝ ι) :
      fderiv ℝ F (gaussianSelectedScale p u z) (gaussianSelectedScaleDerivative p u z)=
        ∑i,(if p i then 1/(2*Real.sqrt u) else 0)*W i z := by
    rw [gaussianSelectedScaleDerivative_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul,smul_eq_mul,W]
    ring
  have hcoeff (i : ι) :
      (if p i then 1/(2*Real.sqrt u) else 0)*(∫z,W i z∂stdGaussian (EuclideanSpace ℝ ι))=
        (1/2:ℝ)*(∫z,if p i then H i z else 0∂stdGaussian (EuclideanSpace ℝ ι)) := by
    rw [gaussianSelectedScale_coordinate_heat_ibp p u F hF B K hB hK h1 h2 i]
    cases hi:p i
    · simp [hi]
    · simp only [hi,ite_true]
      have hs : Real.sqrt u≠0:=(Real.sqrt_pos.mpr hu).ne'
      field_simp
      rfl
  simp_rw [hraw]
  rw [integral_finsetSum _ (fun i _=>(hWi i).const_mul _)]
  simp_rw [integral_const_mul,hcoeff]
  rw [←Finset.mul_sum,←integral_finsetSum _ (fun i _=>hIfHi i)]

end QuantitativeFollowup
