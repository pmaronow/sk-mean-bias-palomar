module
public import FourPapersCommon.GaussianSelectedHeatIBP
public import FourPapersCommon.GaussianParameterVarianceDerivative

@[expose] public section

/-! The actual selected-coordinate moving-test heat formula. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fderiv_parameter_spatial_apply (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (b : ℝ) (y v : EuclideanSpace ℝ ι) (hF : DifferentiableAt ℝ F (b,y)) :
    fderiv ℝ (fun z=>F (b,z)) y v=fderiv ℝ F (b,y) (0,v) := by
  have hh:=hF.hasFDerivAt.comp y ((hasFDerivAt_const b y).prodMk (hasFDerivAt_id y))
  simp only [Function.comp_def] at hh
  rw [hh.fderiv]
  simp

theorem norm_fderiv_parameter_spatial_le (F : ℝ×EuclideanSpace ℝ ι→ℝ)
    (b : ℝ) (y : EuclideanSpace ℝ ι) (hF : DifferentiableAt ℝ F (b,y)) :
    ‖fderiv ℝ (fun z=>F (b,z)) y‖≤‖fderiv ℝ F (b,y)‖ := by
  apply (fderiv ℝ (fun z=>F (b,z)) y).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [fderiv_parameter_spatial_apply F b y v hF]
  simpa using (fderiv ℝ F (b,y)).le_opNorm ((0:ℝ),v)

theorem integrable_gaussianSelectedScale_coordinate_gradient (p : ι→Bool) (b : ℝ)
    (F : EuclideanSpace ℝ ι→ℝ) (hF : ContDiff ℝ 2 F)
    (B K : ℝ) (hB : 0≤B) (hK : 0≤K)
    (h1 : ∀y,‖fderiv ℝ F y‖≤B*Real.exp (K*‖y‖)) (i : ι) :
    Integrable (fun z : EuclideanSpace ℝ ι=>z i*fderiv ℝ F (gaussianSelectedScale p b z)
      (EuclideanSpace.basisFun ι ℝ i)) (stdGaussian (EuclideanSpace ℝ ι)) := by
  let A : ℝ:=(Fintype.card ι:ℝ)*(1+Real.sqrt b)
  let T : EuclideanSpace ℝ ι→ℝ:=fun z=>fderiv ℝ F (gaussianSelectedScale p b z)
    (EuclideanSpace.basisFun ι ℝ i)
  have hm : Measurable T:=
    (((hF.continuous_fderiv (by norm_num)).comp (gaussianSelectedScale p b).continuous).clm_apply
      continuous_const).measurable
  have hb (z : EuclideanSpace ℝ ι) : ‖T z‖≤B*Real.exp ((K*A)*‖z‖):=by
    calc
      _≤‖fderiv ℝ F (gaussianSelectedScale p b z)‖*
        ‖EuclideanSpace.basisFun ι ℝ i‖:=
          (fderiv ℝ F (gaussianSelectedScale p b z)).le_opNorm _
      _≤B*Real.exp (K*‖gaussianSelectedScale p b z‖):=by
        rw [(EuclideanSpace.basisFun ι ℝ).norm_eq_one,mul_one]
        exact h1 _
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left
          (norm_gaussianSelectedScale_le p b b le_rfl z) hK).trans_eq (by ring)
  simpa only [EuclideanSpace.inner_basisFun_real,T] using
    integrable_inner_mul_gaussian_exponential_bound (stdGaussian (EuclideanSpace ℝ ι))
      T hm B (K*A) hB hb (EuclideanSpace.basisFun ι ℝ i)

theorem hasDerivAt_gaussianSelected_parameter_heat_integral (p : ι→Bool)
    (F : ℝ×EuclideanSpace ℝ ι→ℝ) (l u b B K : ℝ)
    (hl : 0<l) (hb : b∈Ioo l u) (hB : 0≤B) (hK : 0≤K)
    (hF : ContDiffOn ℝ ∞ F ((Ioo l u)×ˢ(univ : Set (EuclideanSpace ℝ ι))))
    (h0 : ∀q∈Ioo l u,∀y,‖F (q,y)‖≤B*Real.exp (K*‖y‖))
    (h1 : ∀q∈Ioo l u,∀y,‖fderiv ℝ F (q,y)‖≤B*Real.exp (K*‖y‖))
    (h2 : ∀y,‖fderiv ℝ (fderiv ℝ (fun z=>F (b,z))) y‖≤B*Real.exp (K*‖y‖)) :
    HasDerivAt (fun q=>∫z : EuclideanSpace ℝ ι,F (q,gaussianSelectedScale p q z)
      ∂stdGaussian (EuclideanSpace ℝ ι))
      (∫z : EuclideanSpace ℝ ι,fderiv ℝ F (b,gaussianSelectedScale p b z) (1,0)+
        (1/2:ℝ)*(∑i,if p i then
          fderiv ℝ (fderiv ℝ (fun y=>F (b,y))) (gaussianSelectedScale p b z)
            (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)
          else 0)∂stdGaussian (EuclideanSpace ℝ ι)) b := by
  let G : EuclideanSpace ℝ ι→ℝ:=fun y=>F (b,y)
  let D:=gaussianSelectedScale p b
  let P : EuclideanSpace ℝ ι→ℝ:=fun z=>fderiv ℝ F (b,D z) (1,0)
  let H : ι→EuclideanSpace ℝ ι→ℝ:=fun i z=>
    fderiv ℝ (fderiv ℝ G) (D z) (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i)
  let W : ι→EuclideanSpace ℝ ι→ℝ:=fun i z=>z i*fderiv ℝ G (D z) (EuclideanSpace.basisFun ι ℝ i)
  let A : ℝ:=(Fintype.card ι:ℝ)*(1+Real.sqrt b)
  have hAt (y : EuclideanSpace ℝ ι) : ContDiffAt ℝ ∞ F (b,y):=
    hF.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hb,mem_univ y⟩)
  have hG : ContDiff ℝ ∞ G:=contDiff_iff_contDiffAt.mpr fun y=>
    ContDiffAt.comp (f:=fun z : EuclideanSpace ℝ ι=>(b,z)) (g:=F) y (hAt y) (by fun_prop)
  have hG2 : ContDiff ℝ 2 G:=hG.of_le (by simp)
  have hGrad (y : EuclideanSpace ℝ ι) : ‖fderiv ℝ G y‖≤B*Real.exp (K*‖y‖):=
    (norm_fderiv_parameter_spatial_le F b y ((hAt y).differentiableAt (by simp))).trans (h1 b hb y)
  have hPm : Measurable P:=by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro z
    have hm : ContinuousAt (fun w : EuclideanSpace ℝ ι=>(b,D w)) z:=
      (continuous_const.prodMk D.continuous).continuousAt
    exact (ContinuousAt.comp (f:=fun w : EuclideanSpace ℝ ι=>(b,D w))
      (g:=fderiv ℝ F) ((hAt (D z)).fderiv_right (m:=∞) (by simp)).continuousAt hm).clm_apply
        continuous_const.continuousAt
  have hPb (z : EuclideanSpace ℝ ι) : ‖P z‖≤B*Real.exp ((K*A)*‖z‖):=by
    calc
      _≤‖fderiv ℝ F (b,D z)‖*‖((1:ℝ),(0 : EuclideanSpace ℝ ι))‖:=
        (fderiv ℝ F (b,D z)).le_opNorm _
      _≤B*Real.exp (K*‖D z‖):=by simp only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,mul_one];exact h1 b hb _
      _≤_:=by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
        exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p b b le_rfl z) hK).trans_eq (by ring)
  have hPi : Integrable P (stdGaussian (EuclideanSpace ℝ ι)):=
    integrable_gaussian_exponential_bound _ P hPm B (K*A) hB hPb
  have hWi (i : ι) : Integrable (W i) (stdGaussian (EuclideanSpace ℝ ι)):=
    integrable_gaussianSelectedScale_coordinate_gradient p b G hG2 B K hB hK hGrad i
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
        exact (mul_le_mul_of_nonneg_left (norm_gaussianSelectedScale_le p b b le_rfl z) hK).trans_eq (by ring)
  have hraw (z : EuclideanSpace ℝ ι) :
      fderiv ℝ F (b,D z) (1,gaussianSelectedScaleDerivative p b z)=
      P z+∑i,(if p i then 1/(2*Real.sqrt b) else 0)*W i z:=by
    have hp : ((1:ℝ),gaussianSelectedScaleDerivative p b z)=
        ((1:ℝ),(0 : EuclideanSpace ℝ ι))+((0:ℝ),gaussianSelectedScaleDerivative p b z):=by ext <;> simp
    rw [hp,map_add,←fderiv_parameter_spatial_apply F b (D z) _
      ((hAt (D z)).differentiableAt (by simp)),gaussianSelectedScaleDerivative_apply,map_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul,smul_eq_mul,W,G]
    ring
  have hcoeff (i : ι) :
      (if p i then 1/(2*Real.sqrt b) else 0)*(∫z,W i z∂stdGaussian (EuclideanSpace ℝ ι))=
      (1/2:ℝ)*(if p i then ∫z,H i z∂stdGaussian (EuclideanSpace ℝ ι) else 0):=by
    rw [gaussianSelectedScale_coordinate_heat_ibp p b G hG2 B K hB hK hGrad h2 i]
    cases hp : p i
    · simp [hp]
    · simp only [hp,ite_true]
      have hs : Real.sqrt b≠0:=(Real.sqrt_pos.mpr (hl.trans hb.1)).ne'
      field_simp
      rfl
  have hIfHi (i : ι) : Integrable (fun z=>if p i then H i z else 0)
      (stdGaussian (EuclideanSpace ℝ ι)):=by
    cases hp : p i <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true]
    · exact integrable_const 0
    · exact hHi i
  have heq :
      (∫z : EuclideanSpace ℝ ι,fderiv ℝ F (b,D z) (1,gaussianSelectedScaleDerivative p b z)
        ∂stdGaussian (EuclideanSpace ℝ ι))=
      ∫z : EuclideanSpace ℝ ι,P z+(1/2:ℝ)*(∑i,if p i then H i z else 0)
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
    simp_rw [hraw]
    rw [integral_add hPi (integrable_finsetSum _ (fun i _=>(hWi i).const_mul _)),
      integral_finsetSum _ (fun i _=>(hWi i).const_mul _),
      integral_add hPi ((integrable_finsetSum _ (fun i _=>hIfHi i)).const_mul (1/2)),
      integral_const_mul,integral_finsetSum _ (fun i _=>hIfHi i),Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,hcoeff]
    cases hp : p i <;> simp [hp]
  have hd:=(hasDerivAt_gaussianSelected_parameter_integral p F l u b B K hl hb hB hK hF h0 h1).2
  rw [heq] at hd
  exact hd

end FourPapersCommon
