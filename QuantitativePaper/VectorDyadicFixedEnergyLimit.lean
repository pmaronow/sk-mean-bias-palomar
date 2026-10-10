module
public import QuantitativePaper.VectorDyadicFixedEnergyMeasurable

@[expose] public section

/-! Actual fractional-tilt expected squared-Hessian sources converge
uniformly and in every time interval. Both the finite and limiting Bochner
integrals are justified by genuine measurability and dimension-only bounds. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem intervalIntegrable_vectorDyadicFixedEnergySource (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (j : ℕ) (r q : ℝ) :
    IntervalIntegrable (fun x=>((1-t)*β^2)/(n : ℝ)*
      vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht (projIcc (0 : ℝ) 1 zero_le_one x) j) volume r q := by
  let c:ℝ:=((1-t)*β^2)/(n : ℝ)
  have hc:0≤c:=div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)) (Nat.cast_nonneg n)
  have hm:Measurable (fun x : ℝ=>c*vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht
      (projIcc (0 : ℝ) 1 zero_le_one x) j):=
    ((measurable_vectorDyadicFixedEnergyExpectation μ β t a ht j).comp continuous_projIcc.measurable).const_mul c
  apply (intervalIntegrable_const (c:=c*(n : ℝ)^3)).mono_fun' hm.aestronglyMeasurable
  exact .of_forall fun x=>by
    dsimp only
    rw [norm_mul,Real.norm_of_nonneg hc,Real.norm_eq_abs,
      abs_of_nonneg (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t a ht _ j).1]
    exact mul_le_mul_of_nonneg_left (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t a ht _ j).2 hc

theorem tendstoUniformly_vectorDyadicFixedEnergyExpectation (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    TendstoUniformly (fun j q=>vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht q j)
      (fun q=>∫sample,vectorMeasureHessianEnergy μ β t ht q sample
        ∂vectorMeasureDisorderTilt (n:=n) μ β t a) atTop := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he:=(Metric.tendstoUniformly_iff.mp
    (tendstoUniformly_vectorDyadicFixedHessianEnergy (n:=n) μ β t ht)) (ε/2) (by positivity)
  filter_upwards [he] with j hj
  intro q
  rw [dist_eq_norm]
  change ‖(∫sample,vectorMeasureHessianEnergy μ β t ht q sample ∂vectorMeasureDisorderTilt μ β t a)-
    (∫sample,vectorDyadicFixedHessianEnergy μ β t ht q j sample ∂vectorMeasureDisorderTilt μ β t a)‖<ε
  rw [←integral_sub (integrable_vectorMeasureHessianEnergy μ β t a ht q)
    (integrable_vectorDyadicFixedHessianEnergy μ β t a ht q j)]
  have hb:∀ᵐsample ∂vectorMeasureDisorderTilt (n:=n) μ β t a,
      ‖vectorMeasureHessianEnergy μ β t ht q sample-vectorDyadicFixedHessianEnergy μ β t ht q j sample‖≤ε/2 :=
    .of_forall fun sample=>by simpa only [dist_eq_norm] using (hj (q,sample)).le
  have hnorm:=norm_integral_le_of_norm_le_const (μ:=vectorMeasureDisorderTilt (n:=n) μ β t a) hb
  have hbound:‖∫sample : VectorDisorderBrownianSample n,vectorMeasureHessianEnergy μ β t ht q sample-
      vectorDyadicFixedHessianEnergy μ β t ht q j sample ∂vectorMeasureDisorderTilt μ β t a‖≤ε/2:=by
    simpa only [probReal_univ,mul_one] using hnorm
  exact hbound.trans_lt (by linarith)

theorem tendstoUniformly_vectorDyadicFixedEnergySource (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    TendstoUniformly (fun j q=>((1-t)*β^2)/(n : ℝ)*
      vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht q j)
      (vectorMeanOverlapDerivative (n:=n) μ β t a ht) atTop := by
  let L:ℝ→L[ℝ]ℝ:=ContinuousLinearMap.lsmul ℝ ℝ (((1-t)*β^2)/(n : ℝ))
  have h:=(L.uniformContinuous).comp_tendstoUniformly
    (tendstoUniformly_vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht)
  unfold vectorMeanOverlapDerivative
  simpa only [L,ContinuousLinearMap.lsmul_apply,smul_eq_mul,
    Function.comp_def] using h

theorem tendsto_integral_vectorDyadicFixedEnergySource (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (r q : ℝ) :
    Tendsto (fun j=>∫x in r..q,((1-t)*β^2)/(n : ℝ)*
      vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht (projIcc (0 : ℝ) 1 zero_le_one x) j)
      atTop (𝓝 (∫x in r..q,vectorMeanOverlapDerivative (n:=n) μ β t a ht
        (projIcc (0 : ℝ) 1 zero_le_one x))) := by
  let c:ℝ:=((1-t)*β^2)/(n : ℝ)
  have hc:0≤c:=div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)) (Nat.cast_nonneg n)
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound:=fun _=>c*(n : ℝ)^3)
  · exact .of_forall fun j=>
      ((measurable_vectorDyadicFixedEnergyExpectation (n:=n) μ β t a ht j).comp
        continuous_projIcc.measurable).const_mul c |>.aestronglyMeasurable
  · exact .of_forall fun j=>.of_forall fun x _=>by
      rw [norm_mul,Real.norm_of_nonneg hc,Real.norm_eq_abs,
        abs_of_nonneg (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t a ht _ j).1]
      exact mul_le_mul_of_nonneg_left
        (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t a ht _ j).2 hc
  · exact intervalIntegrable_const
  · exact .of_forall fun x _=>(tendstoUniformly_vectorDyadicFixedEnergySource (n:=n) μ β t a ht).tendsto_at _

end QuantitativePaper
