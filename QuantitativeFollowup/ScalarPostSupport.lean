module
public import QuantitativeFollowup.ScalarTailEquality
public import FRSB.ConstantMassLaw
public import FRSB.SupportGeometry
public import Paper.ParisiDiracIdentification
public import Paper.DoobHeat

@[expose] public section

/-! Literal tail PDE and transition kernel above the support of an
arbitrary actual scalar overlap measure. The constant mass is one and
the resulting stochastic kernel is the actual cosh transform. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FRSB
open scoped NNReal ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem parisiCDF_one_after_support_interval (μ : Paper.ParisiMeasure) (q : ℝ)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (x : ℝ) (hx : q≤x) :
    parisiCDF μ x=1 := by
  apply parisiCDF_eq_one_above_support μ _ hx
  intro z hz
  have hz' : z∈parisiSupport μ := hz
  rw [hsupp] at hz'
  exact hz'.2

theorem parisiPotential_after_support_interval (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q r x : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (hr : r∈Icc q 1) :
    parisiPotential beta μ (r,x)=Real.log (Real.cosh x)+beta^2*(1-r)/2 := by
  have he := parisiPotential_eq_of_cdf_tail beta hb.ne' μ (diracOverlap 0 (by norm_num))
    r ⟨hq.trans hr.1,hr.2⟩ (by
      intro s hs
      rw [parisiCDF_one_after_support_interval μ q hsupp s (hr.1.trans hs.1),
        parisiCDF_dirac,ite_eq_left (hq.trans (hr.1.trans hs.1))]) x
  rw [he,parisiPotential_dirac_hard beta 0 hb (by norm_num) r x ⟨hq.trans hr.1,hr.2⟩]
  unfold rsHardPotential
  ring

theorem parisiGradient_after_support_interval (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q r x : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (hr : r∈Icc q 1) :
    parisiGradient beta μ (r,x)=Real.tanh x := by
  have he : (fun y=>parisiPotential beta μ (r,y))=
      fun y=>Real.log (Real.cosh y)+beta^2*(1-r)/2 :=
    funext fun y=>parisiPotential_after_support_interval beta hb μ q r y hq hsupp hr
  rw [←(hasDerivAt_parisiPotential_spatial_all beta μ r x ⟨hq.trans hr.1,hr.2⟩).deriv,he]
  exact (hasDerivAt_log_cosh x |>.add_const _).deriv

theorem parisiHessian_after_support_interval (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q r x : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q) (hr : r∈Icc q 1) :
    parisiHessian beta μ (r,x)=sech x^2 := by
  have he : (fun y=>parisiGradient beta μ (r,y))=Real.tanh :=
    funext fun y=>parisiGradient_after_support_interval beta hb μ q r y hq hsupp hr
  rw [←(hasDerivAt_parisiGradient_spatial_all beta μ r x).deriv,he]
  exact (hasDerivAt_tanh x).deriv

theorem parisiConstantMassKernel_after_support (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q)
    (a T : ℝ≥0) (ha : q≤a) (hT : 0<T) (haT : (a : ℝ)+T≤1) :
    parisiConstantMassKernel beta μ a T 1=coshStateKernel (beta^2*(T : ℝ)).toNNReal := by
  apply Kernel.ext
  intro x
  rw [parisiConstantMassKernel_apply_actual beta hb.ne' μ a T hT haT 1
    (fun r hr=>parisiCDF_one_after_support_interval μ q hsupp r (ha.trans hr.1)),
    coshStateKernel_apply]
  apply congrArg ((gaussianReal x (beta^2*(T : ℝ)).toNNReal).withDensity)
  funext y
  rw [parisiPotential_after_support_interval beta hb μ q _ y hq hsupp ⟨by linarith,haT⟩,
    parisiPotential_after_support_interval beta hb μ q _ x hq hsupp ⟨ha,by linarith⟩]
  congr 1
  unfold coshStateDensity
  rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg beta) T.coe_nonneg)]
  have he : 1*(Real.log (Real.cosh y)+beta^2*(1-((a : ℝ)+T))/2-
      (Real.log (Real.cosh x)+beta^2*(1-(a : ℝ))/2))=
      -beta^2*(T : ℝ)/2+Real.log (Real.cosh y)-Real.log (Real.cosh x) := by ring
  rw [he,Real.exp_sub,Real.exp_add,Real.exp_log (Real.cosh_pos y),Real.exp_log (Real.cosh_pos x)]
  ring

theorem selectedState_after_support_doob_expectation (beta : ℝ) (hb : 0<beta)
    (μ : Paper.ParisiMeasure) (q : ℝ) (hq : 0≤q)
    (hsupp : parisiSupport μ=Icc (0 : ℝ) q)
    (a T : ℝ≥0) (ha : q≤a) (hT : 0<T) (haT : (a : ℝ)+T≤1)
    (ψ : ℝ→ℝ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀x,‖ψ x‖≤C) :
    (∫sample,ψ (selectedParisiItoState beta 0 hb.ne' μ (a+T) sample)∂canonicalBrownianMeasure)=
      ∫sample,doobOperator (beta^2*(T : ℝ)).toNNReal ψ
        (selectedParisiItoState beta 0 hb.ne' μ a sample)∂canonicalBrownianMeasure := by
  have he := selectedParisiState_constantMass_weighted_borel beta 0 hb.ne' μ a T hT haT 1
    (fun r hr=>parisiCDF_one_after_support_interval μ q hsupp r (ha.trans hr.1)) ψ hψ C hC
    (fun _=>1) stronglyMeasurable_const 1 (fun _=>by simp)
  rw [parisiConstantMassKernel_after_support beta hb μ q hq hsupp a T ha hT haT] at he
  simpa only [one_mul,integral_coshStateKernel] using he

end QuantitativeFollowup
