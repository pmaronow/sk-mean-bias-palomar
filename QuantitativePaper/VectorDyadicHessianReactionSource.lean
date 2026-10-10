module
public import QuantitativePaper.VectorDyadicFixedEnergyLimit
public import FRSB.ParisiGridTopology

@[expose] public section

/-! The literal negative Hessian-square reaction sources, including atoms
of the actual profile. Their integrals converge by genuine weak CDF limits
at almost every null threshold and uniformly convergent Hessian energies. -/
noncomputable section
open MeasureTheory Set Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open Paper
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def vectorDyadicFixedHessianSource (μ : ParisiMeasure) (β t outer : ℝ) (ht : t≤1)
    (j : ℕ) (r : ℝ) : ℝ :=
  -parisiCDF (parisiGridMeasure μ (vectorDyadicIndex j)) (projIcc 0 1 zero_le_one r)*
    (((1-t)*β^2)/(n : ℝ)*vectorDyadicFixedEnergyExpectation (n:=n) μ β t outer ht
      (projIcc 0 1 zero_le_one r) j)

theorem vectorDyadicFixedHessianSource_intervalIntegrable (μ : ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (vectorDyadicFixedHessianSource (n:=n) μ β t outer ht j) volume a b := by
  let c:ℝ:=((1-t)*β^2)/(n : ℝ)
  have hc:0≤c:=div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hmap : Measurable (fun r : ℝ=>(projIcc 0 1 zero_le_one r : ℝ)):=by fun_prop
  have hm : Measurable (vectorDyadicFixedHessianSource (n:=n) μ β t outer ht j):=
    (((parisiCDF_measurable _).comp hmap).neg).mul
      (((measurable_vectorDyadicFixedEnergyExpectation μ β t outer ht j).comp
        continuous_projIcc.measurable).const_mul c)
  apply (intervalIntegrable_const (c:=c*(n : ℝ)^3)).mono_fun' hm.aestronglyMeasurable
  exact .of_forall fun r=>by
    unfold vectorDyadicFixedHessianSource
    dsimp only
    rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (parisiCDF_nonneg _ _),
      norm_mul,Real.norm_of_nonneg hc,Real.norm_eq_abs,
      abs_of_nonneg (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t outer ht _ j).1]
    calc
      _≤1*(c*(n : ℝ)^3):=mul_le_mul (parisiCDF_le_one _ _)
        (mul_le_mul_of_nonneg_left (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t outer ht _ j).2 hc)
        (mul_nonneg hc (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t outer ht _ j).1) zero_le_one
      _=_:=one_mul _

theorem tendsto_integral_vectorDyadicFixedHessianSource (μ : ParisiMeasure)
    (β t outer : ℝ) (ht : t≤1) {r q : ℝ}
    (hr : r∈Icc (0 : ℝ) 1) (hq : q∈Icc (0 : ℝ) 1) :
    Tendsto (fun j=>∫x in r..q,vectorDyadicFixedHessianSource (n:=n) μ β t outer ht j x)
      atTop (𝓝 (∫x in r..q,-parisiCDF μ x*
        vectorMeanOverlapDerivative (n:=n) μ β t outer ht (projIcc 0 1 zero_le_one x))) := by
  let c:ℝ:=((1-t)*β^2)/(n : ℝ)
  have hc:0≤c:=div_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hweak : Tendsto (fun j=>parisiGridMeasure μ (vectorDyadicIndex j)) atTop (𝓝 μ):=
    (FRSB.tendsto_parisiGridMeasure μ).comp tendsto_vectorDyadicIndex
  have hmap : Measurable (fun x : ℝ=>(projIcc 0 1 zero_le_one x : ℝ)):=by fun_prop
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound:=fun _=>c*(n : ℝ)^3)
  · exact .of_forall fun j=>
      ((((parisiCDF_measurable _).comp hmap).neg).mul
        (((measurable_vectorDyadicFixedEnergyExpectation μ β t outer ht j).comp
          continuous_projIcc.measurable).const_mul c)).aestronglyMeasurable
  · exact .of_forall fun j=>.of_forall fun x _=>by
      unfold vectorDyadicFixedHessianSource
      rw [norm_mul,Real.norm_eq_abs,abs_neg,abs_of_nonneg (parisiCDF_nonneg _ _),
        norm_mul,Real.norm_of_nonneg hc,Real.norm_eq_abs,
        abs_of_nonneg (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t outer ht _ j).1]
      exact (mul_le_mul (parisiCDF_le_one _ _)
        (mul_le_mul_of_nonneg_left (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t outer ht _ j).2 hc)
        (mul_nonneg hc (vectorDyadicFixedEnergyExpectation_nonneg_le μ β t outer ht _ j).1) zero_le_one).trans_eq (one_mul _)
  · exact intervalIntegrable_const
  · filter_upwards [FRSB.ae_parisi_level_null μ]
      with x hx
    intro hmem
    have hx01 : x∈Icc (0 : ℝ) 1:=by
      have hm:=Set.uIoc_subset_uIcc hmem
      rcases (show min r q ≤ x ∧ x ≤ max r q from hm) with ⟨hl,hu⟩
      exact ⟨(le_min hr.1 hq.1).trans hl,hu.trans (max_le hr.2 hq.2)⟩
    have hCDF:=FRSB.tendsto_parisiCDF_of_level_null hweak hx
    have hE:=(tendstoUniformly_vectorDyadicFixedEnergySource (n:=n) μ β t outer ht).tendsto_at
      (projIcc 0 1 zero_le_one x)
    simpa only [vectorDyadicFixedHessianSource,projIcc_of_mem zero_le_one hx01] using hCDF.neg.mul hE

end QuantitativePaper
