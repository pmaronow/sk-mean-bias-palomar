module
public import FourPapersCommon.GaussianSelectedHeatIBP

@[expose] public section

/-! True coordinate Stein contraction for an actual diagonal linear Gaussian
map, including zero columns and exponential-growth spatial tests. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem gaussianDiagonal_coordinate_heat_ibp
    (D : EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι) (c : ι→ℝ)
    (hBasis : ∀i,D (EuclideanSpace.basisFun ι ℝ i)=c i•EuclideanSpace.basisFun ι ℝ i)
    (F : EuclideanSpace ℝ ι→ℝ) (hF : ContDiff ℝ 2 F)
    (B K : ℝ) (hB : 0≤B) (hK : 0≤K)
    (h1 : ∀y,‖fderiv ℝ F y‖≤B*Real.exp (K*‖y‖))
    (h2 : ∀y,‖fderiv ℝ (fderiv ℝ F) y‖≤B*Real.exp (K*‖y‖)) (i : ι) :
    (∫z : EuclideanSpace ℝ ι,z i*fderiv ℝ F (D z)
      (EuclideanSpace.basisFun ι ℝ i)∂stdGaussian (EuclideanSpace ℝ ι))=
    c i*
      ∫z : EuclideanSpace ℝ ι,fderiv ℝ (fderiv ℝ F) (D z)
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let e:=EuclideanSpace.basisFun ι ℝ i
  let A : ℝ:=‖D‖
  have hA : 0≤A:=by dsimp [A];positivity
  have hDnorm (z : EuclideanSpace ℝ ι) : ‖D z‖≤A*‖z‖:=
    D.le_opNorm z
  have he : ‖e‖=1:=(EuclideanSpace.basisFun ι ℝ).norm_eq_one i
  let T : EuclideanSpace ℝ ι→ℝ:=fun z=>fderiv ℝ F (D z) e
  have hfd : ContDiff ℝ 1 (fderiv ℝ F):=hF.fderiv_right (by norm_num)
  have hT : ContDiff ℝ 1 T:=(hfd.comp D.contDiff).clm_apply contDiff_const
  have hdT (z w : EuclideanSpace ℝ ι) : fderiv ℝ T z w=
      fderiv ℝ (fderiv ℝ F) (D z) (D w) e:=by
    have hh:=((hfd.differentiable_one (D z)).hasFDerivAt.comp z D.hasFDerivAt).clm_apply
      (hasFDerivAt_const e z)
    have hh' : HasFDerivAt T
        ((fderiv ℝ (fderiv ℝ F) (D z)).comp D |>.flip e) z:=by
      simpa [T,Function.comp_def] using hh
    rw [hh'.fderiv]
    rfl
  have hbound (z : EuclideanSpace ℝ ι) :
      ‖T z‖≤B*(1+A)*Real.exp ((K*A)*‖z‖):=by
    calc
      _≤‖fderiv ℝ F (D z)‖*‖e‖:=(fderiv ℝ F (D z)).le_opNorm e
      _≤B*Real.exp (K*‖D z‖):=by rw [he,mul_one];exact h1 _
      _≤B*Real.exp (K*(A*‖z‖)):=by gcongr;exact hDnorm z
      _≤_:=by rw [←mul_assoc];gcongr;nlinarith
  have hdbound (z : EuclideanSpace ℝ ι) :
      ‖fderiv ℝ T z‖≤B*(1+A)*Real.exp ((K*A)*‖z‖):=by
    apply (fderiv ℝ T z).opNorm_le_bound (by positivity)
    intro w
    rw [hdT]
    calc
      _≤‖fderiv ℝ (fderiv ℝ F) (D z) (D w)‖*‖e‖:=
        (fderiv ℝ (fderiv ℝ F) (D z) (D w)).le_opNorm e
      _≤(B*Real.exp (K*‖D z‖))*‖D w‖:=by
        rw [he,mul_one]
        exact (fderiv ℝ (fderiv ℝ F) (D z)).le_opNorm (D w) |>.trans
          (mul_le_mul_of_nonneg_right (h2 _) (norm_nonneg _))
      _≤(B*Real.exp (K*(A*‖z‖)))*(A*‖w‖):=by gcongr <;> exact hDnorm _
      _≤(B*(1+A)*Real.exp ((K*A)*‖z‖))*‖w‖:=by
        rw [←mul_assoc K A]
        calc
          _=(B*A)*(Real.exp ((K*A)*‖z‖)*‖w‖):=by ring
          _≤(B*(1+A))*(Real.exp ((K*A)*‖z‖)*‖w‖):=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith : A≤1+A) hB) (by positivity)
          _=_:=by ring
  have hh:=cavityGaussian_covariant_ibp (stdGaussian (EuclideanSpace ℝ ι))
    integral_id_stdGaussian T hT (B*(1+A)) (K*A) (by positivity) hbound hdbound e
  simp only [covarianceOperator_stdGaussian_id,hdT] at hh
  change (∫z : EuclideanSpace ℝ ι,inner ℝ z e*T z∂stdGaussian (EuclideanSpace ℝ ι))=
    ∫z : EuclideanSpace ℝ ι,fderiv ℝ (fderiv ℝ F) (D z) (D e) e
      ∂stdGaussian (EuclideanSpace ℝ ι) at hh
  dsimp only [e,T] at hh
  simp only [EuclideanSpace.inner_basisFun_real,hBasis,map_smul,
    ContinuousLinearMap.smul_apply,smul_eq_mul] at hh
  rw [integral_const_mul] at hh
  exact hh


end FourPapersCommon
