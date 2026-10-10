module
public import FourPapersCommon.GaussianTwoMaskParameterDerivative
public import FourPapersCommon.GaussianDiagonalCoordinateIBP
public import FourPapersCommon.GaussianDiagonalMomentIntegrability

@[expose] public section

/-! The actual two-clock moving Gaussian heat identity. Root coordinates
have variance u; disjoint path coordinates have variance d-alpha*u.
The parameter derivative and both Stein contractions are proved internally. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hasDerivAt_gaussianTwoMask_heat_integral (pR pP : ι→Bool) (d alpha : ℝ)
    (hdis : ∀i,pR i=true→pP i=false)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (l u lb ub b B K : ℝ)
    (ha : 0≤alpha) (hl : 0<l) (hlb : 0<lb) (hb : b∈Ioo l u)
    (hqb : ∀q∈Ioo l u,d-alpha*q∈Ioo lb ub) (hB : 0≤B) (hK : 0≤K)
    (hF : ContDiffOn ℝ ∞ F ((Ioo lb ub)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (h0 : ∀q∈Ioo lb ub,∀y,‖F (q,y)‖≤B*Real.exp (K*‖y‖))
    (h1 : ∀q∈Ioo lb ub,∀y,‖fderiv ℝ F (q,y)‖≤B*Real.exp (K*‖y‖))
    (h2 : ∀y,‖fderiv ℝ (fderiv ℝ (fun z=>F (d-alpha*b,z))) y‖≤B*Real.exp (K*‖y‖)) :
    HasDerivAt (fun q=>∫z : EuclideanSpace ℝ ι,F (d-alpha*q,gaussianTwoMaskScale pR pP d alpha q z)
      ∂stdGaussian (EuclideanSpace ℝ ι))
      (∫z : EuclideanSpace ℝ ι,
        -alpha*fderiv ℝ F (d-alpha*b,gaussianTwoMaskScale pR pP d alpha b z) (1,0)+
        (1/2:ℝ)*(∑i,if pR i then
          fderiv ℝ (fderiv ℝ (fun y=>F (d-alpha*b,y))) (gaussianTwoMaskScale pR pP d alpha b z)
            (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0)-
        (alpha/2)*(∑i,if pP i then
          fderiv ℝ (fderiv ℝ (fun y=>F (d-alpha*b,y))) (gaussianTwoMaskScale pR pP d alpha b z)
            (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0)
        ∂stdGaussian (EuclideanSpace ℝ ι)) b := by
  let theta:=d-alpha*b
  let D:=gaussianTwoMaskScale pR pP d alpha b
  let G : EuclideanSpace ℝ ι→ℝ:=fun y=>F (theta,y)
  let P : EuclideanSpace ℝ ι→ℝ:=fun z=>fderiv ℝ F (theta,D z) (-alpha,0)
  let H : ι→EuclideanSpace ℝ ι→ℝ:=fun i z=>
    fderiv ℝ (fderiv ℝ G) (D z) (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)
  let W : ι→EuclideanSpace ℝ ι→ℝ:=fun i z=>z i*fderiv ℝ G (D z) (EuclideanSpace.basisFun ι ℝ i)
  let A : ℝ:=‖D‖
  have hAt (y : EuclideanSpace ℝ ι) : ContDiffAt ℝ ∞ F (theta,y):=
    hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hqb b hb,mem_univ y⟩)
  have hG : ContDiff ℝ ∞ G:=contDiff_iff_contDiffAt.mpr fun y=>
    ContDiffAt.comp (f:=fun z : EuclideanSpace ℝ ι=>(theta,z)) (g:=F) y (hAt y) (by fun_prop)
  have hG2 : ContDiff ℝ 2 G:=hG.of_le (by simp)
  have hGrad (y : EuclideanSpace ℝ ι) : ‖fderiv ℝ G y‖≤B*Real.exp (K*‖y‖):=
    (norm_fderiv_parameter_spatial_le F theta y ((hAt y).differentiableAt (by simp))).trans
      (h1 theta (hqb b hb) y)
  have hPm : Measurable P:=by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    have hm : ContinuousAt (fun w : EuclideanSpace ℝ ι=>(theta,D w)) z:=
      (continuous_const.prodMk D.continuous).continuousAt
    exact (ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(theta,D w))
      (g:=fderiv ℝ F) ((hAt (D z)).fderiv_right (m:=∞) (by simp)).continuousAt hm).clm_apply
        continuous_const.continuousAt
  have hPb (z : EuclideanSpace ℝ ι) : ‖P z‖≤(B*alpha)*Real.exp ((K*A)*‖z‖):=by
    have hp : ‖((-alpha:ℝ),(0 : EuclideanSpace ℝ ι))‖=alpha:=by
      rw [Prod.norm_def,norm_neg,Real.norm_of_nonneg ha,norm_zero,max_eq_left ha]
    calc
      _≤‖fderiv ℝ F (theta,D z)‖*alpha:=by
        simpa only [P,hp] using (fderiv ℝ F (theta,D z)).le_opNorm ((-alpha:ℝ),(0 : EuclideanSpace ℝ ι))
      _≤(B*Real.exp (K*‖D z‖))*alpha:=mul_le_mul_of_nonneg_right (h1 theta (hqb b hb) _) ha
      _≤(B*Real.exp ((K*A)*‖z‖))*alpha:=by
        apply mul_le_mul_of_nonneg_right _ ha
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left (D.le_opNorm z) hK).trans_eq (by ring)
      _=_:=by ring
  have hPi : Integrable P (stdGaussian (EuclideanSpace ℝ ι)):=
    integrable_gaussian_exponential_bound _ P hPm (B*alpha) (K*A) (mul_nonneg hB ha) hPb
  have hWi (i : ι) : Integrable (W i) (stdGaussian (EuclideanSpace ℝ ι)):=
    integrable_gaussianLinear_coordinate_gradient D G hG2 B K hB hK hGrad i
  have hHi (i : ι) : Integrable (H i) (stdGaussian (EuclideanSpace ℝ ι)):=by
    have hDG : ContDiff ℝ 1 (fderiv ℝ G):=hG2.fderiv_right (by norm_num)
    have hm : Measurable (H i):=
      (((hDG.continuous_fderiv (by norm_num)).comp D.continuous).clm_apply
        continuous_const |>.clm_apply continuous_const).measurable
    apply integrable_gaussian_exponential_bound _ _ hm B (K*A) hB
    intro z
    calc
      _≤‖fderiv ℝ (fderiv ℝ G) (D z) (EuclideanSpace.basisFun ι ℝ i)‖*
        ‖EuclideanSpace.basisFun ι ℝ i‖:=
          (fderiv ℝ (fderiv ℝ G) (D z) (EuclideanSpace.basisFun ι ℝ i)).le_opNorm _
      _≤B*Real.exp (K*‖D z‖):=by
        rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one]
        exact ((fderiv ℝ (fderiv ℝ G) (D z)).le_opNorm (EuclideanSpace.basisFun ι ℝ i)).trans
          (by rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one];exact h2 _)
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left (D.le_opNorm z) hK).trans_eq (by ring)
  have hraw (z : EuclideanSpace ℝ ι) :
      fderiv ℝ F (theta,D z) (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha b z)=
      P z+∑i,gaussianTwoMaskCoefficientDerivative pR pP d alpha b i*W i z:=by
    have hp : ((-alpha:ℝ),gaussianTwoMaskScaleDerivative pR pP d alpha b z)=
        ((-alpha:ℝ),(0 : EuclideanSpace ℝ ι))+((0:ℝ),gaussianTwoMaskScaleDerivative pR pP d alpha b z):=by
      ext <;> simp
    rw [hp,map_add,←fderiv_parameter_spatial_apply F theta (D z) _
      ((hAt (D z)).differentiableAt (by simp)),gaussianTwoMaskScaleDerivative_apply,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul,smul_eq_mul,W,G]
    ring
  have hcoeff (i : ι) :
      gaussianTwoMaskCoefficientDerivative pR pP d alpha b i*
        (∫z,W i z∂stdGaussian (EuclideanSpace ℝ ι))=
      (1/2:ℝ)*(if pR i then ∫z,H i z∂stdGaussian (EuclideanSpace ℝ ι) else 0)-
        (alpha/2)*(if pP i then ∫z,H i z∂stdGaussian (EuclideanSpace ℝ ι) else 0):=by
    rw [gaussianDiagonal_coordinate_heat_ibp D (gaussianTwoMaskCoefficient pR pP d alpha b)
      (fun j=>gaussianTwoMaskScale_basis pR pP d alpha b j) G hG2 B K hB hK hGrad h2 i,
      ←mul_assoc,gaussianTwoMaskCoefficient_rate_product pR pP d alpha b
        (hl.trans hb.1) (hlb.trans (hqb b hb).1) i]
    by_cases hr:pR i=true
    · have hp:=hdis i hr
      simp [hr,hp,H]
    · have hr0:pR i=false:=Bool.eq_false_iff.mpr hr
      cases hp:pP i <;> simp [hr0,hp,H] <;> ring
  have hIf (p : ι→Bool) (i : ι) : Integrable (fun z=>if p i then H i z else 0)
      (stdGaussian (EuclideanSpace ℝ ι)):=by
    cases hp:p i <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true]
    · exact integrable_const 0
    · exact hHi i
  let Q : ι→EuclideanSpace ℝ ι→ℝ:=fun i z=>(1/2:ℝ)*(if pR i then H i z else 0)-
    (alpha/2)*(if pP i then H i z else 0)
  have hQi (i : ι) : Integrable (Q i) (stdGaussian (EuclideanSpace ℝ ι)):=
    ((hIf pR i).const_mul (1/2)).sub ((hIf pP i).const_mul (alpha/2))
  have heq : (∫z : EuclideanSpace ℝ ι,fderiv ℝ F (theta,D z)
        (-alpha,gaussianTwoMaskScaleDerivative pR pP d alpha b z)∂stdGaussian (EuclideanSpace ℝ ι))=
      ∫z : EuclideanSpace ℝ ι,P z+∑i,Q i z∂stdGaussian (EuclideanSpace ℝ ι) := by
    simp_rw [hraw]
    rw [integral_add hPi (integrable_finsetSum _ (fun i _=>(hWi i).const_mul _)),
      integral_finsetSum _ (fun i _=>(hWi i).const_mul _),
      integral_add hPi (integrable_finsetSum _ (fun i _=>hQi i)),
      integral_finsetSum _ (fun i _=>hQi i)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,hcoeff]
    dsimp only [Q]
    rw [integral_sub ((hIf pR i).const_mul (1/2)) ((hIf pP i).const_mul (alpha/2)),
      integral_const_mul,integral_const_mul]
    cases hr:pR i <;> cases hp:pP i <;> simp [hr,hp]
  have hPe (z : EuclideanSpace ℝ ι) : P z=-alpha*fderiv ℝ F (theta,D z) (1,0):=by
    have hp : ((-alpha:ℝ),(0 : EuclideanSpace ℝ ι))=(-alpha)•((1:ℝ),(0 : EuclideanSpace ℝ ι)):=by
      ext <;> simp
    rw [show P z=fderiv ℝ F (theta,D z) (-alpha,0) from rfl,hp,map_smul,smul_eq_mul]
  have hd:=(hasDerivAt_gaussianTwoMask_parameter_integral pR pP d alpha F l u lb ub b B K
    ha hl hlb hb hqb hB hK hF h0 h1).2
  rw [heq] at hd
  convert hd using 1
  apply integral_congr_ae
  exact .of_forall fun z=>by
    dsimp only
    rw [hPe]
    dsimp only [Q,H,G,D,theta]
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum]
    ring

end FourPapersCommon
