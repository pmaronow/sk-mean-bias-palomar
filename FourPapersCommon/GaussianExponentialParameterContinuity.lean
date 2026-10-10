module
public import FourPapersCommon.ExponentialPartialJets
public import FourPapersCommon.ExponentialParameterHeatBounds
public import OverlapPaper.CavityGaussianIBP
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

/-! Genuine dominated Gaussian continuity for a locally exponentially
bounded smooth observable and continuously moving linear noise coordinates. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuousAt_gaussian_exponential_parameter_integral
    (F:ℝ×EuclideanSpace ℝ ι→ℝ)(l r:ℝ)
    (hF:ExponentialSmoothOn F ((Ioo l r)×ˢ(univ:Set (EuclideanSpace ℝ ι))))
    (b:ℝ→ℝ)(S:ℝ→EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι)(v:ℝ)
    (hb:b v∈Ioo l r)(hbc:ContinuousAt b v)
    (hSc:∀z,ContinuousAt (fun u=>S u z) v)(M:ℝ)(hM:0≤M)
    (hbound:∀ᶠu in 𝓝 v,∀z,‖S u z‖≤M*‖z‖):
    ContinuousAt (fun u=>∫z : EuclideanSpace ℝ ι,F (b u,S u z)∂stdGaussian (EuclideanSpace ℝ ι)) v:=by
  obtain ⟨B,K,hB,hK,h0,h1,h2⟩:=hF.parameter_heat_bounds F l r
  have hbI:∀ᶠu in 𝓝 v,b u∈Ioo l r:=hbc.eventually (isOpen_Ioo.mem_nhds hb)
  apply continuousAt_of_dominated (bound:=fun z : EuclideanSpace ℝ ι=>B*Real.exp ((K*M)*‖z‖))
  · filter_upwards [hbI] with u hu
    have hc:Continuous (fun y : EuclideanSpace ℝ ι=>F (b u,y)):=by
      apply continuous_iff_continuousAt.mpr
      intro y
      exact ContinuousAt.comp (f:=fun x : EuclideanSpace ℝ ι=>(b u,x)) (g:=F)
        (hF.smooth (b u,y) ⟨hu,mem_univ _⟩).continuousAt
        (continuous_const.prodMk continuous_id).continuousAt
    exact (hc.comp (S u).continuous).aestronglyMeasurable
  · filter_upwards [hbI,hbound] with u hu hSu
    exact .of_forall fun z=>by
      apply (h0 _ hu _).trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hB
      exact (mul_le_mul_of_nonneg_left (hSu z) hK).trans_eq (by ring)
  · exact (integrable_exp_mul_norm_gaussian (stdGaussian (EuclideanSpace ℝ ι)) (K*M)).const_mul B
  · exact .of_forall fun z=>
      ContinuousAt.comp (f:=fun u : ℝ=>(b u,S u z)) (g:=F)
        (hF.smooth (b v,S v z) ⟨hb,mem_univ _⟩).continuousAt (hbc.prodMk (hSc z))

def gaussianSpatialHessianTraceCLM (p:ι→Bool):
    (EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι→L[ℝ]ℝ)→L[ℝ]ℝ:=
  ∑i,if p i then (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.basisFun ι ℝ i)).comp
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ ι→L[ℝ]ℝ) (EuclideanSpace.basisFun ι ℝ i)) else 0

theorem gaussianSpatialHessianTraceCLM_apply (p:ι→Bool)
    (H:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ ι→L[ℝ]ℝ):
    gaussianSpatialHessianTraceCLM p H=
      ∑i,if p i then H (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0:=by
  simp only [gaussianSpatialHessianTraceCLM,ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases hi:p i <;> simp [hi]

theorem exponentialSmoothOn_parameter_heat_generator
    (pR pP:ι→Bool)(F:ℝ×EuclideanSpace ℝ ι→ℝ)(alpha l r:ℝ)
    (hF:ExponentialSmoothOn F ((Ioo l r)×ˢ(univ:Set (EuclideanSpace ℝ ι)))):
    ExponentialSmoothOn (fun z : ℝ×EuclideanSpace ℝ ι=>
      -alpha*fderiv ℝ F z (1,0)+
      (1/2:ℝ)*(∑i,if pR i then fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0)-
      (alpha/2)*(∑i,if pP i then fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2
        (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ i) else 0))
        ((Ioo l r)×ˢ(univ:Set (EuclideanSpace ℝ ι))):=by
  have hopen:IsOpen ((Ioo l r)×ˢ(univ:Set (EuclideanSpace ℝ ι))):=isOpen_Ioo.prod isOpen_univ
  have hT:=(hF.directional ((1:ℝ),(0:EuclideanSpace ℝ ι))).compCLM
    ((-alpha) • ContinuousLinearMap.id ℝ ℝ)
  have hH:=(hF.partialFDeriv hopen).partialFDeriv hopen
  have hR:=hH.compCLM ((1/2:ℝ) • gaussianSpatialHessianTraceCLM pR)
  have hP:=hH.compCLM ((alpha/2) • gaussianSpatialHessianTraceCLM pP)
  have hg:=(hT.add hR).sub hP
  simpa only [Function.comp_def,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,
    smul_eq_mul,gaussianSpatialHessianTraceCLM_apply] using hg

end FourPapersCommon
